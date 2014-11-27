#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>
#include<sstream>
#include<iostream>
#include<iomanip>
#include<unistd.h> 
#include<sys/types.h>
#include<signal.h>
#include<omp.h>
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

//!!! ADD ERROR HANDLING !!!
void SMT2Generator::parse_xml()
{
	xml_document doc;
	xml_parse_result result = doc.load_file(xml_path.c_str());

	xml_node data_node = doc.child("data");
	xml_node declare_node = data_node.child("declare");
	vector<DInterval> var_dim;
	vector<DInterval> param_dim; 
	for(xml_node_iterator it = declare_node.begin(); it != declare_node.end(); it++)
	{
		if(strcmp(it->attribute("type").value(),"var") == 0)
		{
			this->var.push_back(it->child("name").text().as_string());
			var_dim.push_back(DInterval(it->child("domain").child("left").text().as_double(), it->child("domain").child("right").text().as_double()));
		}
		if(strcmp(it->attribute("type").value(),"param") == 0)
		{
			string name = it->child("name").text().as_string();
			this->param.push_back(name);
			param_dim.push_back(DInterval(it->child("domain").child("left").text().as_double(), it->child("domain").child("right").text().as_double()));
			odes.push_back(string("(= d/dt[" + name + "] 0.0)"));
		}
		if(strcmp(it->attribute("type").value(),"time") == 0)
		{
			this->time_var = it->child("name").text().as_string();
			odes.push_back(string("(= d/dt[" + time_var + "] 1.0)"));
		}
	}
	this->var_domain = Box(var_dim);
	this->param_domain = Box(param_dim);

	xml_node odes_node = data_node.child("odes");
	for(xml_node_iterator it = odes_node.begin(); it != odes_node.end(); it++)
	{
		this->odes.push_back(it->text().as_string());
	}

	xml_node series_node = data_node.child("series");
	for(xml_node_iterator it = series_node.begin(); it != series_node.end(); it++)
	{
		vector<DInterval> box_dim;
		for(xml_node_iterator point_it = it->begin(); point_it != it->end(); point_it++)
		{
			box_dim.push_back(DInterval(point_it->child("left").text().as_double(), point_it->child("right").text().as_double()));
		}
		this->time_series[it->attribute("time").as_double()] = Box(box_dim);
	}
	
	this->delta = data_node.child("delta").text().as_double();
	this->epsilon = data_node.child("epsilon").text().as_double();
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

std::map<double, Box> SMT2Generator::get_time_series()
{
	return time_series;
}

double SMT2Generator::get_delta()
{
	return delta;
}

double SMT2Generator::get_epsilon()
{
	return epsilon;
}