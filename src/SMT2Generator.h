// DecisionProcedure class implements a decision procedure 
// using dReach tool
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#ifndef SMT2GENERATOR_H 
#define SMT2GENERATOR_H  

#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>
#include "Box.h"

using namespace std;

// DecisionProcedure class declaration
class SMT2Generator
{
	private:

		string xml_path;

		void parse_xml();

		vector<string> var;
		vector<string> param; 
		Box var_domain;
		Box param_domain;
		string time_var;
		vector<string> odes;
		std::map<double, Box> time_series;
		double delta;
		double epsilon;


		
	public:

		SMT2Generator(string);

		

		//GETTERS AND SETTERS
		string get_xml_path();

		Box get_var_domain();

		Box get_param_domain();

		vector<string> get_vars();

		vector<string> get_params();

		string get_time_var();

		vector<string> get_odes();

		std::map<double, Box> get_time_series();

		double get_delta();

		double get_epsilon();

};
#endif 