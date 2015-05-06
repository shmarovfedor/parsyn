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
#include "pugixml.hpp"

using namespace std;
using namespace pugi;

// DecisionProcedure class declaration
class SMT2Generator
{
	private:

		string xml_path;

		string output_path;

		void parse_xml();

		vector<string> var;
		vector<string> param; 
		Box var_domain;
		Box param_domain;
		string time_var;
		vector<string> odes;
		vector<double> time_value;
		vector<Box> time_box;
		double delta;
		double epsilon;
		int thread_num = 0;

		xml_document output;
		
	public:

		SMT2Generator(string);

		vector<string> generate_smt2(int, Box);

		vector<string> generate_smt2(Box);

		//GETTERS AND SETTERS
		string get_xml_path();

		Box get_var_domain();

		Box get_param_domain();

		vector<string> get_vars();

		vector<string> get_params();

		string get_time_var();

		vector<string> get_odes();

		vector<double> get_time_values();

		vector<Box> get_time_boxes();

		double get_delta();

		double get_epsilon();

		void init_output(string);

		void modify_output(double, int, vector<Box>, vector<Box>, vector<Box>);

		void modify_output(double, vector<Box>, vector<Box>, vector<Box>);

};
#endif 