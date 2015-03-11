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

#include "DecisionProcedure.h"
#include "Box.h"

using namespace std;
using namespace capd;

// The method gets a full path to the DRH model and a precision
// which are then used to call dReach. The method returns true
// if dReach returns "sat" and false if dReach returns "unsat".
//
// @param DRH filename, precision used by dReach for verifying
// the model
bool DecisionProcedure::call_dreal(string smt2_filename_base, string opt, string dreal_bin)
{
	stringstream s;
	
	s << dreal_bin << " " << opt << " " << smt2_filename_base << ".smt2 > " << smt2_filename_base << ".output";
	//s << "dReal --precision=" << delta << " " << smt2_filename_base << ".smt2 > " << smt2_filename_base << ".output";
	
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
			return true;
		} 
		else
		{
			if (line == "unsat")
			{
				return false;
			}
			else
			{
    			throw string("error reading dReal output!!!").c_str();
			}
		}
	}
	else
	{
    	throw string("error obtaining dReal output!!!").c_str();
	}
}

// The methods gets an arbitrary Box as an input parameter
// and return 1 if the indicator function over this box equals 1,
// -1 if indicator function equals to 0 and 0 if the box contains
// both values where the indicator function takes both values
//
// @param box from the domain of random variables. 
int DecisionProcedure::evaluate(vector<string> smt2_filename_base, string opt, string dreal_bin)
{
	try
	{
		if(DecisionProcedure::call_dreal(smt2_filename_base.at(0), opt, dreal_bin))
		{
			if(DecisionProcedure::call_dreal(smt2_filename_base.at(1), opt, dreal_bin))
			{
				DecisionProcedure::remove_aux_file(smt2_filename_base.at(0));
				DecisionProcedure::remove_aux_file(smt2_filename_base.at(1));
				return 0;
			}
			else
			{
				DecisionProcedure::remove_aux_file(smt2_filename_base.at(0));
				DecisionProcedure::remove_aux_file(smt2_filename_base.at(1));
				return 1;
			}
		}
		else
		{
			DecisionProcedure::remove_aux_file(smt2_filename_base.at(0));
			DecisionProcedure::remove_aux_file(smt2_filename_base.at(1));
			return -1;
		}
	}
	catch(const char* e)
	{
		DecisionProcedure::remove_aux_file(smt2_filename_base.at(0));
		DecisionProcedure::remove_aux_file(smt2_filename_base.at(1));
		throw e;
	}
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
		
	if(DecisionProcedure::file_exists(smt2.c_str())) remove(smt2.c_str());
	if(DecisionProcedure::file_exists(output.c_str())) remove(output.c_str());
}
