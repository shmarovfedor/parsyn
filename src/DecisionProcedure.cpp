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

#include "DecisionProcedure.h"
#include "Box.h"

using namespace std;
using namespace capd;

// Default constructor of the class
DecisionProcedure::DecisionProcedure()
{
	
}

// Constructor of the class
//
// @param template of the problem,
// template of the inverted problem,
// settings used for the verification 
DecisionProcedure::DecisionProcedure(vector<string> temp, vector<string> temp_c, vector<string> params, double delta)
{
	this->temp = temp;
	this->temp_c = temp_c;
	this->delta = delta;
	this->params = params;
}

// The method get a Box and a flag as input parameters and 
// generates the DRH model for the problem if flag is true and 
// creates a DRH model for the inverted problem is the flag is false.
// The methods returns a full path to the generated DRH file.
//
// @param box from the domain of random variables, flag triggering
// generation of the inverse model
string DecisionProcedure::generate_smt2(Box box, bool flag)
{
	stringstream s;

	if(flag)
	{
		s << get_current_dir_name() << setprecision(16) << "/phi_";
	}
	else
	{
		s << get_current_dir_name() << setprecision(16) << "/phi_C_";
	}

	for(int i = 0; i < box.get_dimension_size() - 1; i++)
	{
		s << setprecision(12) << box.get_dimension(i).leftBound() << "_" << box.get_dimension(i).rightBound() << "x";
	}
	s << setprecision(12) << box.get_dimension(box.get_dimension_size() - 1).leftBound() << "_" << box.get_dimension(box.get_dimension_size() - 1).rightBound() ;
	
	string smt2_filename_base = s.str();
	file_base.push_back(smt2_filename_base);

	s << ".smt2";
	string smt2_filename = s.str();

	ofstream smt2_file;
	smt2_file.open(smt2_filename.c_str());
	if (smt2_file.is_open())
	{
		/*
		for(int i = 0; i < box.get_dimension_size(); i++)
		{
			smt2_file << "#define " << box.get_var_of(i) << "_a " << box.get_interval_of(i).leftBound() << endl;
			drh_file << "#define " << box.get_var_of(i) << "_b " << box.get_interval_of(i).rightBound() << endl;
			double radius = 100 * (rv.at(i)->get_domain().rightBound() - rv.at(i)->get_domain().leftBound());
			drh_file << "[" << rv.at(i)->get_domain().leftBound() - radius << ", " << rv.at(i)->get_domain().rightBound() + radius << "] " << box.get_var_of(i) << ";" << endl;
		}
		*/

		const regex declare_fun("\\s*\\(declare-fun\\s+(([A-Za-z]+[A-Za-z0-9]*)_[0-9]+)\\s+\\(\\)\\s+Real\\s*\\)\\s*");
		smatch matches;

		if(flag)
		{
			for(int i = 0; i < temp.size(); i++)
			{
				smt2_file << temp.at(i) << endl;
				if(regex_match(temp.at(i), matches, declare_fun))
				{
					for(int j = 0; j < params.size(); j++)
					{
						if(params.at(j) == matches[2].str())
						{
							smt2_file << setprecision(16) << "(assert (<= " << box.get_dimension(j).leftBound() << " " << matches[1].str() << "))" << endl;
							smt2_file << setprecision(16) << "(assert (<= " << matches[1].str() << " " << box.get_dimension(j).rightBound() << "))" << endl;
						}
					}
				}
			}
		}
		else
		{
			for(int i = 0; i < temp_c.size(); i++)
			{
				smt2_file << temp_c.at(i) << endl;
				if(regex_match(temp_c.at(i), matches, declare_fun))
				{
					for(int j = 0; j < params.size(); j++)
					{
						if(params.at(j) == matches[2].str())
						{
							smt2_file << setprecision(16) << "(assert (<= " << box.get_dimension(j).leftBound() << " " << matches[1].str() << "))" << endl;
							smt2_file << setprecision(16)<< "(assert (<= " << matches[1].str() << " " << box.get_dimension(j).rightBound() << "))" << endl;
						}
					}
				}
			}
		}
		
		smt2_file.close();
	}
	return smt2_filename_base;
}

// The method gets a full path to the DRH model and a precision
// which are then used to call dReach. The method returns true
// if dReach returns "sat" and false if dReach returns "unsat".
//
// @param DRH filename, precision used by dReach for verifying
// the model
bool DecisionProcedure::call_dreal(string smt2_filename_base)
{
	stringstream s;
	
	s << "dReal --precision=" << delta << " " << smt2_filename_base << ".smt2 > " << smt2_filename_base << ".output";
	//s << "dReach -k " << opt["depth"] << " " << drh_filename_base << ".drh -precision=" << precision << endl;

	system(s.str().c_str());

	s.str("");
	s << smt2_filename_base << ".output";
	ifstream output;
	output.open(s.str().c_str());

	if (output.is_open())
	{
		string line;
		getline(output, line);
		output.close();
		if (line == "sat")
		{
    		remove_aux_file(smt2_filename_base);
			return true;
		} 
		else
		{
			if (line == "unsat")
			{
    			remove_aux_file(smt2_filename_base);
				return false;
			}
			else
			{
				remove_aux_files();
    			cout << "Error reading dReal output!!!" << endl;
    			exit(EXIT_FAILURE);
			}
		}
	}
	else
	{
    	remove_aux_files();
    	cout << "FAULT!!!" << endl;
    	exit(EXIT_FAILURE);
	}
}

// The methods gets an arbitrary Box as an input parameter
// and return 1 if the indicator function over this box equals 1,
// -1 if indicator function equals to 0 and 0 if the box contains
// both values where the indicator function takes both values
//
// @param box from the domain of random variables. 
int DecisionProcedure::evaluate(Box box)
{
	string phi;
	string phi_c;
	#pragma omp critical
	{
		phi = generate_smt2(box, true);
		//cout << "PHI: " << phi << endl;
	}
	if(call_dreal(phi))
	{
		#pragma omp critical
		{
			phi_c = generate_smt2(box, false);
			//cout << "PHI_C: " << phi_c << endl;
		}
		if(call_dreal(phi_c))
		{
			return 0;
		}
		else
		{
			return 1;
		}
	}
	else
	{
		return -1;
	}
}

// The method returns the list of the auxiliary filenames
vector<string> DecisionProcedure::get_file_base()
{
	return file_base;
}

// The method gets a name of the file as a parameter and returns
// true  if the file exists and false otherwise
bool DecisionProcedure::file_exists(const char *filename)
{
	FILE* file;
	file = fopen(filename, "r");
	if(file != NULL)
	{
		fclose(file);
		return true;
	}
	else
	{
		return false;
	}
}

// The method removes auxiliary file
//
// @param filename base
void DecisionProcedure::remove_aux_file(string filename_base)
{
	string smt2 = filename_base + ".smt2";
	string output = filename_base + ".output";
		
	if(file_exists(smt2.c_str())) remove(smt2.c_str());
	if(file_exists(output.c_str())) remove(output.c_str());
}

// The method removes all the auxiliary files generated by dReach 
void DecisionProcedure::remove_aux_files()
{
	stringstream s;
	for(int i = 0; i < file_base.size(); i++)
	{
		remove_aux_file(file_base.at(i));
	}
	file_base.clear();
}

