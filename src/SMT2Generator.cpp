#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>
#include<sstream>
#include<iostream>
#include<iomanip>
#include<unistd.h> 
#include<sys/types.h>
#include<signal.h>
#ifdef _OPENMP
	#include<omp.h>
#endif
#include<regex>
#include "pugixml.hpp"
#include "SMT2Generator.h"
#include "Box.h"

using namespace std;
using namespace capd;
using namespace pugi;

// Constructor of the class
//
// @param template of the problem,
// template of the inverted problem,
// settings used for the verification 
SMT2Generator::SMT2Generator(string xml_path)
{
	this->xml_path = xml_path;
	parse_xml();
}

//parsing input xml file
void SMT2Generator::parse_xml()
{
	xml_document doc;
	xml_parse_result result = doc.load_file(xml_path.c_str());

	if(result.status != status_ok) throw result.description();

	xml_node data_node = doc.child("data");
	if(data_node.empty()) throw "<data> node is not defined or empty";
	
	xml_node declare_node = data_node.child("declare");
	if(declare_node.empty()) throw "<declare> node is not defined or empty";
	
	vector<DInterval> var_dim;
	vector<DInterval> param_dim; 
	for(xml_node_iterator it = declare_node.begin(); it != declare_node.end(); it++)
	{
		if(strcmp(it->attribute("type").value(),"var") == 0)
		{
			string var_name = it->child("name").text().as_string();
			if(var_name.empty()) throw "one of the variables is not defined";
			if(std::find(this->var.begin(), this->var.end(), var_name) != this->var.end()) throw string("variable " + var_name + " was already declared").c_str();
			this->var.push_back(var_name);
			if(it->child("domain").child("left").empty()) throw string("left bound for the variable " + var_name + " is not specified").c_str();
			if(it->child("domain").child("right").empty()) throw string("right bound for the variable " + var_name + " is not specified").c_str();
			var_dim.push_back(DInterval(it->child("domain").child("left").text().as_double(), it->child("domain").child("right").text().as_double()));
		}
		if(strcmp(it->attribute("type").value(),"param") == 0)
		{
			string param_name = it->child("name").text().as_string();
			if(param_name.empty()) throw "one of the parameters is not defined";
			if(std::find(this->param.begin(), this->param.end(), param_name) != this->param.end()) throw string("parameter " + param_name + " was already declared").c_str();
			this->param.push_back(param_name);
			if(it->child("domain").child("left").empty()) throw string("left bound for the parameter " + param_name + " is not specified").c_str();
			if(it->child("domain").child("right").empty()) throw string("right bound for the parameter " + param_name + " is not specified").c_str();
			param_dim.push_back(DInterval(it->child("domain").child("left").text().as_double(), it->child("domain").child("right").text().as_double()));
			odes.push_back(string("(= d/dt[" + param_name + "] 0.0)"));
		}
		if(strcmp(it->attribute("type").value(),"time") == 0)
		{
			this->time_var = it->child("name").text().as_string();
			odes.push_back(string("(= d/dt[" + time_var + "] 1.0)"));
		}
	}

	if(this->var.size() == 0) throw "variables are not declared";
	if(this->param.size() == 0)	throw "parameters are not declared";
	if(this->time_var.empty()) throw "time variable is not defined";
	
	this->var_domain = Box(var_dim);
	this->param_domain = Box(param_dim);

	xml_node odes_node = data_node.child("odes");
	for(xml_node_iterator it = odes_node.begin(); it != odes_node.end(); it++)
	{
		this->odes.push_back(it->text().as_string());
	}
	if(this->odes.size() != this->param.size() + this->var.size() + 1) throw "ODE list is incomplete";

	xml_node series_node = data_node.child("series");
	
	if(series_node.empty()) throw "<series> node is not defined or empty";
	
	for(xml_node_iterator it = series_node.begin(); it != series_node.end(); it++)
	{
		if(it->attribute("time").empty()) throw "time value for one of the points is not specified";
		if(it->attribute("time").as_double() < 0) throw "time value cannot be negative";
		string time_value_str = it->attribute("time").as_string();
		vector<DInterval> box_dim;
		for(xml_node_iterator point_it = it->begin(); point_it != it->end(); point_it++)
		{
			if(point_it->child("left").empty()) throw string("left bound in one of dimensions for t=" + time_value_str + " is not specified").c_str();
			if(point_it->child("right").empty()) throw string("right bound in one of dimensions for t=" + time_value_str + " is not specified").c_str();
			box_dim.push_back(DInterval(point_it->child("left").text().as_double(), point_it->child("right").text().as_double()));
		}
		//if(box_dim.size() != this->var.size()) throw string("check number of dimensions at t=" + time_value_str).c_str();
		this->time_value.push_back(it->attribute("time").as_double());
		this->time_box.push_back(Box(box_dim));
	}
	
	if(data_node.child("delta").empty()) throw "<delta> is not specified";
	
	this->delta = data_node.child("delta").text().as_double();
	
	if(this->delta <= 0) throw "<delta> should be positive";

	if(data_node.child("epsilon").empty()) throw "<epsilon> is not specified";
	
	this->epsilon = data_node.child("epsilon").text().as_double();

	if(this->epsilon <= 0) throw "<epsilon> should be positive";
}

// used to estimate a big formula
vector<string> SMT2Generator::generate_smt2(Box box)
{
	stringstream s;

	char cur_dir[FILENAME_MAX];
	getcwd(cur_dir, sizeof(cur_dir));

	s << cur_dir << "/phi";
	string smt2_filename = s.str();
	s << "_C";
	string smt2_c_filename = s.str();

	stringstream smt2_string, smt2_c_string;

	smt2_string << "(set-logic QF_NRA_ODE)" << endl;
	for(int i = 0; i < this->var.size(); i++)
	{
		smt2_string << "(declare-fun " << this->var.at(i) << " () Real)" << endl;
		for(int j = 0; j < time_value.size(); j++)
		{
			smt2_string << "(declare-fun " << this->var.at(i) << "_" << j << "_0 () Real)" << endl;
			smt2_string << "(declare-fun " << this->var.at(i) << "_" << j << "_t () Real)" << endl;
		}
	}

	for(int i = 0; i < this->param.size(); i++)
	{
		smt2_string << "(declare-fun " << this->param.at(i) << " () Real)" << endl;
		for(int j = 0; j < time_value.size(); j++)
		{
			smt2_string << "(declare-fun " << this->param.at(i) << "_" << j << "_0 () Real)" << endl;
			smt2_string << "(declare-fun " << this->param.at(i) << "_" << j << "_t () Real)" << endl;
		}
	}

	smt2_string << "(declare-fun " << this->time_var << " () Real)" << endl;
	for(int j = 0; j < time_value.size(); j++)
	{
		smt2_string << "(declare-fun " << this->time_var << "_" << j << "_0 () Real)" << endl;
		smt2_string << "(declare-fun " << this->time_var << "_" << j << "_t () Real)" << endl;
		smt2_string << "(declare-fun time_" << j << " () Real)" << endl;
	}

	smt2_string << "(define-ode flow_1 (";
	for(int i = 0; i < this->odes.size(); i++)
	{
		smt2_string << this->odes.at(i);
	}
	smt2_string << "))" << endl;

	for(int j = 0; j < time_value.size(); j++)
	{
		for (int i = 0; i < this->var.size(); i++)
		{
			smt2_string << "(assert (>= " << this->var.at(i) << "_" << j << "_0 " << var_domain.get_dimension(i).leftBound() << "))" << endl;
			smt2_string << "(assert (<= " << this->var.at(i) << "_" << j << "_0 " << var_domain.get_dimension(i).rightBound() << "))" << endl;
			smt2_string << "(assert (>= " << this->var.at(i) << "_" << j << "_t " << var_domain.get_dimension(i).leftBound() << "))" << endl;
			smt2_string << "(assert (<= " << this->var.at(i) << "_" << j << "_t " << var_domain.get_dimension(i).rightBound() << "))" << endl;
		}
	}

	for(int j = 0; j < time_value.size(); j++)
	{
		for (int i = 0; i < this->param.size(); i++)
		{
			smt2_string << "(assert (>= " << this->param.at(i) << "_" << j << "_0 " << box.get_dimension(i).leftBound() << "))" << endl;
			smt2_string << "(assert (<= " << this->param.at(i) << "_" << j << "_0 " << box.get_dimension(i).rightBound() << "))" << endl;
			smt2_string << "(assert (>= " << this->param.at(i) << "_" << j << "_t " << box.get_dimension(i).leftBound() << "))" << endl;
			smt2_string << "(assert (<= " << this->param.at(i) << "_" << j << "_t " << box.get_dimension(i).rightBound() << "))" << endl;
		}

		smt2_string << "(assert (>= time_" << j << " " << time_value.at(0) << "))" << endl;
		smt2_string << "(assert (<= time_" << j << " " << time_value.at(time_value.size() - 1) << "))" << endl;
		smt2_string << "(assert (>= " << this->time_var << "_" << j << "_0 " << time_value.at(0) << "))" << endl;
		smt2_string << "(assert (<= " << this->time_var << "_" << j << "_0 " << time_value.at(time_value.size() - 1) << "))" << endl;
		smt2_string << "(assert (>= " << this->time_var << "_" << j << "_t " << time_value.at(0) << "))" << endl;
		smt2_string << "(assert (<= " << this->time_var << "_" << j << "_t " << time_value.at(time_value.size() - 1) << "))" << endl;
	}

	smt2_string << "(assert " << endl;
	smt2_string << "(and " << endl;

	// solvers for ODE system
	for(int j = 0; j < time_value.size(); j++)
	{
		smt2_string << "(= [";
		for (int i = 0; i < this->var.size(); i++)
		{
			smt2_string << this->var.at(i) << "_" << j << "_t ";
		}
		for (int i = 0; i < this->param.size(); i++)
		{
			smt2_string << this->param.at(i) << "_" << j << "_t ";
		}
		smt2_string << this->time_var << "_" << j << "_t] (integral 0. time_" << j << " [";

		for (int i = 0; i < this->var.size(); i++)
		{
			smt2_string << this->var.at(i) << "_" << j << "_0 ";
		}
		for (int i = 0; i < this->param.size(); i++)
		{
			smt2_string << this->param.at(i) << "_" << j << "_0 ";
		}
		smt2_string << this->time_var << "_" << j << "_0] flow_1))" << endl;
	}

	// chaining time points, parameters and variables j+1_0 and j_t
	for(int j = 0; j < time_value.size() - 1; j++)
	{
		for (int i = 0; i < this->param.size(); i++)
		{
			smt2_string << "(= " << this->param.at(i) << "_" << j + 1 << "_0 " << this->param.at(i) << "_" << j << "_t)" << endl;
		}
		for (int i = 0; i < this->var.size(); i++)
		{
			smt2_string << "(= " << this->var.at(i) << "_" << j + 1 << "_0 " << this->var.at(i) << "_" << j << "_t)" << endl;
		}
		smt2_string << "(= " << this->time_var << "_" << j + 1 << "_0 " << this->time_var << "_" << j << "_t)" << endl;
	}

	// time points
	for(int j = 0; j < time_value.size(); j++)
	{
		smt2_string << "(= " << this->time_var << "_" << j << "_0 " << this->time_value.at(j) << ")" << endl;
	}

	for (int i = 0; i < time_box.at(0).get_dimension_size(); i++)
	{
		smt2_string << "(>= " << this->var.at(i) << "_0_0 " << time_box.at(0).get_dimension(i).leftBound() << ")" << endl;
		smt2_string << "(<= " << this->var.at(i) << "_0_0 " << time_box.at(0).get_dimension(i).rightBound() << ")" << endl;
	}

	smt2_c_string << smt2_string.str();

	// time series for phi.smt2
	for(int j = 1; j < time_value.size(); j++)
	{
		for (int i = 0; i < time_box.at(j).get_dimension_size(); i++)
		{
			smt2_string << "(>= " << this->var.at(i) << "_" << j << "_0 " << time_box.at(j).get_dimension(i).leftBound() << ")" << endl;
			smt2_string << "(<= " << this->var.at(i) << "_" << j << "_0 " << time_box.at(j).get_dimension(i).rightBound() << ")" << endl;
		}
	}
	smt2_string << ")" << endl;
	smt2_string << ")" << endl;
	smt2_string << "(check-sat)" << endl;
	smt2_string << "(exit)" << endl;


	// time series for phi_C.smt2
	smt2_c_string << "(or" << endl;
	for(int j = 1; j < time_value.size(); j++)
	{
		for (int i = 0; i < time_box.at(j).get_dimension_size(); i++)
		{
			smt2_c_string << "(< " << this->var.at(i) << "_" << j << "_0 " << time_box.at(j).get_dimension(i).leftBound() << ")" << endl;
			smt2_c_string << "(> " << this->var.at(i) << "_" << j << "_0 " << time_box.at(j).get_dimension(i).rightBound() << ")" << endl;
		}
	}
	smt2_c_string << ")" << endl;

	smt2_c_string << ")" << endl;
	smt2_c_string << ")" << endl;
	smt2_c_string << "(check-sat)" << endl;
	smt2_c_string << "(exit)" << endl;

	ofstream smt2_file, smt2_c_file;
	smt2_file.open(string(smt2_filename + ".smt2").c_str());
	smt2_c_file.open(string(smt2_c_filename + ".smt2").c_str());
	if(smt2_file.is_open() && smt2_c_file.is_open())
	{
		smt2_file << smt2_string.str();
		smt2_c_file << smt2_c_string.str();

		smt2_file.close();
		smt2_c_file.close();
	}
	else
	{
		throw string("Error creating smt2 files").c_str();
	}

	vector<string> res;
	res.push_back(smt2_filename);
	res.push_back(smt2_c_filename);

	return res;
}

// used for estimating series of formulas
vector<string> SMT2Generator::generate_smt2(int index, Box box)
{
	if(index <= 0) throw string("index should be greater than 0").c_str();

	stringstream s;

	char cur_dir[FILENAME_MAX];
	getcwd(cur_dir, sizeof(cur_dir));

	#ifdef _OPENMP
		thread_num = omp_get_thread_num();
	#endif

	s << cur_dir << "/phi_" << index << "_" << thread_num;
	string smt2_filename = s.str();
	s << "_C";
	string smt2_c_filename = s.str();

	stringstream smt2_string, smt2_c_string;

	smt2_string << "(set-logic QF_NRA_ODE)" << endl;
	for(int i = 0; i < this->var.size(); i++)
	{
		smt2_string << "(declare-fun " << this->var.at(i) << " () Real)" << endl;
		smt2_string << "(declare-fun " << this->var.at(i) << "_0_0 () Real)" << endl;
		smt2_string << "(declare-fun " << this->var.at(i) << "_0_t () Real)" << endl;
	}

	for(int i = 0; i < this->param.size(); i++)
	{
		smt2_string << "(declare-fun " << this->param.at(i) << " () Real)" << endl;
		smt2_string << "(declare-fun " << this->param.at(i) << "_0_0 () Real)" << endl;
		smt2_string << "(declare-fun " << this->param.at(i) << "_0_t () Real)" << endl;
	}

	smt2_string << "(declare-fun " << this->time_var << " () Real)" << endl;
	smt2_string << "(declare-fun " << this->time_var << "_0_0 () Real)" << endl;
	smt2_string << "(declare-fun " << this->time_var << "_0_t () Real)" << endl;
	smt2_string << "(declare-fun time_0 () Real)" << endl;
	smt2_string << "(define-ode flow_1 (";
	for(int i = 0; i < this->odes.size(); i++)
	{
		smt2_string << this->odes.at(i);
	}
	smt2_string << "))" << endl;

	for(int i = 0; i < this->var.size(); i++)
	{
		smt2_string << "(assert (>= " << this->var.at(i) << "_0_0 " << var_domain.get_dimension(i).leftBound() << "))" << endl;
		smt2_string << "(assert (<= " << this->var.at(i) << "_0_0 " << var_domain.get_dimension(i).rightBound() << "))" << endl;
		smt2_string << "(assert (>= " << this->var.at(i) << "_0_t " << var_domain.get_dimension(i).leftBound() << "))" << endl;
		smt2_string << "(assert (<= " << this->var.at(i) << "_0_t " << var_domain.get_dimension(i).rightBound() << "))" << endl;
	}

	for(int i = 0; i < this->param.size(); i++)
	{
		smt2_string << "(assert (>= " << this->param.at(i) << "_0_0 " << box.get_dimension(i).leftBound() << "))" << endl;
		smt2_string << "(assert (<= " << this->param.at(i) << "_0_0 " << box.get_dimension(i).rightBound() << "))" << endl;
		smt2_string << "(assert (>= " << this->param.at(i) << "_0_t " << box.get_dimension(i).leftBound() << "))" << endl;
		smt2_string << "(assert (<= " << this->param.at(i) << "_0_t " << box.get_dimension(i).rightBound() << "))" << endl;
	}

	smt2_string << "(assert (>= time_0 " << time_value.at(0) << "))" << endl;
	smt2_string << "(assert (<= time_0 " << time_value.at(index) << "))" << endl;
	smt2_string << "(assert (>= " << this->time_var << "_0_0 " << time_value.at(0) << "))" << endl;
	smt2_string << "(assert (<= " << this->time_var << "_0_0 " << time_value.at(index) << "))" << endl;
	smt2_string << "(assert (>= " << this->time_var << "_0_t " << time_value.at(0) << "))" << endl;
	smt2_string << "(assert (<= " << this->time_var << "_0_t " << time_value.at(index) << "))" << endl;

	smt2_string << "(assert " << endl;
	smt2_string << "(and " << endl;
	smt2_string << "(= [";
	for(int i = 0; i < this->var.size(); i++)
	{
		smt2_string << this->var.at(i) << "_0_t ";
	}
	for(int i = 0; i < this->param.size(); i++)
	{
		smt2_string << this->param.at(i) << "_0_t ";
	}
	smt2_string << this->time_var << "_0_t] (integral 0. time_0 [";

	for(int i = 0; i < this->var.size(); i++)
	{
		smt2_string << this->var.at(i) << "_0_0 ";
	}
	for(int i = 0; i < this->param.size(); i++)
	{
		smt2_string << this->param.at(i) << "_0_0 ";
	}
	smt2_string << this->time_var << "_0_0] flow_1))" << endl;

	for(int i = 0; i < this->param.size(); i++)
	{
		smt2_string << "(= " << this->param.at(i) << "_0_0 " << this->param.at(i) << "_0_t)" << endl;
	}

	//cout << "Before initial condition" << endl;
	//initial condition for both problems
	smt2_string << "(= " << this->time_var << "_0_0 " << this->time_value.at(0) << ")" << endl;
	for(int i = 0; i < time_box.at(0).get_dimension_size(); i++)
	{
		smt2_string << "(>= " << this->var.at(i) << "_0_0 " << time_box.at(0).get_dimension(i).leftBound() << ")" << endl;
		smt2_string << "(<= " << this->var.at(i) << "_0_0 " << time_box.at(0).get_dimension(i).rightBound() << ")" << endl;
	}

	//cout << "After initial condition" << endl;

	smt2_c_string << smt2_string.str();

	//conjunction for the *.smt2 file
	smt2_string << "(= " << this->time_var << "_0_t " << this->time_value.at(index) << ")" << endl;
	for(int i = 0; i < time_box.at(index).get_dimension_size(); i++)
	{
		smt2_string << "(>= " << this->var.at(i) << "_0_t " << time_box.at(index).get_dimension(i).leftBound() << ")" << endl;
		smt2_string << "(<= " << this->var.at(i) << "_0_t " << time_box.at(index).get_dimension(i).rightBound() << ")" << endl;
	}
	smt2_string << ")" << endl;
	smt2_string << ")" << endl;
	smt2_string << "(check-sat)" << endl;
	smt2_string << "(exit)" << endl;

	//disjunction for the *_C.smt2 file
	smt2_c_string << "(= " << this->time_var << "_0_t " << this->time_value.at(index) << ")" << endl;
	smt2_c_string << "(or" << endl;
	for(int i = 0; i < time_box.at(index).get_dimension_size(); i++)
	{
		smt2_c_string << "(< " << this->var.at(i) << "_0_t " << time_box.at(index).get_dimension(i).leftBound() << ")" << endl;
		smt2_c_string << "(> " << this->var.at(i) << "_0_t " << time_box.at(index).get_dimension(i).rightBound() << ")" << endl;
	}
	smt2_c_string << ")" << endl;
	smt2_c_string << ")" << endl;
	smt2_c_string << ")" << endl;
	smt2_c_string << "(check-sat)" << endl;
	smt2_c_string << "(exit)" << endl;

	ofstream smt2_file, smt2_c_file;
	smt2_file.open(string(smt2_filename + ".smt2").c_str());
	smt2_c_file.open(string(smt2_c_filename + ".smt2").c_str());
	if(smt2_file.is_open() && smt2_c_file.is_open())
	{
		smt2_file << smt2_string.str();
		smt2_c_file << smt2_c_string.str();		
		
		smt2_file.close();
		smt2_c_file.close();
	}
	else
	{
		throw string("Error creating smt2 files").c_str();
	}
	
	vector<string> res;
	res.push_back(smt2_filename);
	res.push_back(smt2_c_filename);
	
	return res;
}

//GETTERS AND SETTERS
string SMT2Generator::get_xml_path()
{
	return this->xml_path;
}

Box SMT2Generator::get_var_domain()
{
	return var_domain;
}

vector<string> SMT2Generator::get_vars()
{
	return var;
}

Box SMT2Generator::get_param_domain()
{
	return param_domain;
}

vector<string> SMT2Generator::get_params()
{
	return param;
}

string SMT2Generator::get_time_var()
{
	return time_var;
}

vector<string> SMT2Generator::get_odes()
{
	return odes;
}

vector<double> SMT2Generator::get_time_values()
{
	return time_value;
}

vector<Box> SMT2Generator::get_time_boxes()
{
	return time_box;
}

double SMT2Generator::get_delta()
{
	return delta;
}

double SMT2Generator::get_epsilon()
{
	return epsilon;
}