#include<regex>
#include<iostream>
#include<fstream>
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>
#include<iomanip>
#include<fstream>
#include<math.h>
#include<time.h>
#include<omp.h>
#include<exception>
#include<typeinfo>
#include<unistd.h> 
#include<sys/types.h>
#include<signal.h>
#include "BoxFactory.h"
#include "Box.h"
#include "DecisionProcedure.h"
#include "pugixml.hpp"
#include "SMT2Generator.h"

using namespace std;
using namespace capd;
using namespace pugi;

ostream& operator<<(ostream& strm, Box& box)
{
	for(int i = 0; i < box.get_dimension_size() - 1; i++)
	{
		strm << box.get_dimension(i) << "x";
	}
	strm << box.get_dimension(box.get_dimension_size() - 1);
	
	return strm;
}

vector< vector<Box> > ParSyn(string phi_path, string phi_c_path, vector<string> params, vector<Box> boxes, double delta, double epsilon)
{
	vector<string> temp, temp_c;

	ifstream phi_file, phi_c_file;
	phi_file.open(phi_path.c_str());
	if(phi_file.is_open())
	{
		string line;
		while (getline(phi_file, line))
		{
			temp.push_back(line);
		}
		phi_file.close();
	}
	else
	{
		cout << "Could not open " << phi_path << endl;
		//return EXIT_FAILURE;
		exit(0);
	}

	phi_c_file.open(phi_c_path.c_str());
	if(phi_c_file.is_open())
	{
		string line;
		while (getline(phi_c_file, line))
		{
			temp_c.push_back(line);
		}
		phi_c_file.close();
	}
	else
	{
		cout << "Could not open " << phi_c_path << endl;
		//return EXIT_FAILURE;
		exit(0);
	}

	

	DecisionProcedure dec_proc(temp, temp_c, params, delta);

	vector<Box> undec_boxes, sat_boxes, unsat_boxes, mixed_boxes;

	double prev_volume = 0;

	while(boxes.size() > 0)
	{
		for(int i = 0; i < boxes.size(); i++)
		{
			if(prev_volume != boxes.at(i).get_volume().leftBound())
			{
				prev_volume = boxes.at(i).get_volume().leftBound();
				cout << "Evaluating boxes of size : " << prev_volume << " ---> " << epsilon << endl;
			}

			int result = dec_proc.evaluate(boxes.at(i));
			if(result == 1)
			{
				sat_boxes.push_back(boxes.at(i));
			}
			if(result == 0)
			{
				vector<Box> tmp_vector = BoxFactory::branch_box(boxes.at(i));
				if(tmp_vector.at(0).get_volume() <= epsilon)
				{
					for(int j = 0; j < tmp_vector.size(); j++)
					{
						undec_boxes.push_back(tmp_vector.at(j));
					}
				}
				else
				{
					for(int j = 0; j < tmp_vector.size(); j++)
					{
						mixed_boxes.push_back(tmp_vector.at(j));
					}
				}
			}
			if(result == -1)
			{
				unsat_boxes.push_back(boxes.at(i));
			}
		}

		boxes.clear();

		for(int i = 0; i < mixed_boxes.size(); i++)
		{
			boxes.push_back(mixed_boxes.at(i));
		}

		mixed_boxes.clear();
	}

	sat_boxes = BoxFactory::merge_boxes(sat_boxes);
	undec_boxes = BoxFactory::merge_boxes(undec_boxes);
	unsat_boxes = BoxFactory::merge_boxes(unsat_boxes);

	vector< vector<Box> > output;
	output.push_back(sat_boxes);
	output.push_back(undec_boxes);
	output.push_back(unsat_boxes);

	return output;
}

void solve_three_points()
{
	//inout parameters
	string phi_path = "/home/b2049657/ParSyn/model/parabola-3-points/phi.smt2";
	string phi_c_path = "/home/b2049657/ParSyn/model/parabola-3-points/phi-c.smt2";
	double delta = 0.000001;
	double epsilon = 0.000001;

	vector<DInterval> dimensions;
	dimensions.push_back(DInterval(0.0, 4.0));
	Box param_domain(dimensions);
	vector<Box> boxes;
	boxes.push_back(param_domain);
	
	vector<string> params;
	params.push_back("k");
	
	cout << "======Old ParSyn for 3 time points:===========" << endl;
	double start_time = time(NULL);
	cout << scientific << setprecision(12) << endl;
	vector< vector<Box> > output = ParSyn(phi_path, phi_c_path, params, boxes, delta, epsilon);
	vector<Box> sat_boxes = output.at(0);
	vector<Box> undec_boxes = output.at(1);
	vector<Box> unsat_boxes = output.at(2);

	cout << "=====================SAT BOXES:===================" << endl;
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		cout << i << ") " << sat_boxes.at(i) << endl;
	}

	cout << "====================UNDEC BOXES:==================" << endl;
	for(int i = 0; i < undec_boxes.size(); i++)
	{
		cout << i << ") " << undec_boxes.at(i) << endl;
	}

	cout << "====================UNSAT BOXES:==================" << endl;
	for(int i = 0; i < unsat_boxes.size(); i++)
	{
		cout << i << ") " << unsat_boxes.at(i) << endl;
	}
	
	cout << "======================TIME:========================" << endl;
	cout << time(NULL) - start_time << " seconds" << endl;
	cout << "===================================================" << endl;

	start_time = time(NULL);

	cout << endl;
	cout << endl;
	cout << "======New ParSyn for the second time points:===========" << endl;

	phi_path = "/home/b2049657/ParSyn/model/parabola-3-points/phi-2.smt2";
	phi_c_path = "/home/b2049657/ParSyn/model/parabola-3-points/phi-c-2.smt2";
	cout << scientific << setprecision(12) << endl;
	output = ParSyn(phi_path, phi_c_path, params, boxes, delta, epsilon);
	sat_boxes = output.at(0);
	undec_boxes = output.at(1);
	unsat_boxes = output.at(2);

	cout << "=====================SAT BOXES:===================" << endl;
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		cout << i << ") " << sat_boxes.at(i) << endl;
	}

	cout << "====================UNDEC BOXES:==================" << endl;
	for(int i = 0; i < undec_boxes.size(); i++)
	{
		cout << i << ") " << undec_boxes.at(i) << endl;
	}

	cout << "====================UNSAT BOXES:==================" << endl;
	for(int i = 0; i < unsat_boxes.size(); i++)
	{
		cout << i << ") " << unsat_boxes.at(i) << endl;
	}

	vector<Box> sat_boxes_2 = sat_boxes;

	boxes.clear();
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		boxes.push_back(sat_boxes.at(i));
	}

	
	cout << endl;
	cout << endl;
	cout << "======New ParSyn for the third time points:===========" << endl;

	phi_path = "/home/b2049657/ParSyn/model/parabola-3-points/phi-3.smt2";
	phi_c_path = "/home/b2049657/ParSyn/model/parabola-3-points/phi-c-3.smt2";
	cout << scientific << setprecision(12) << endl;
	output = ParSyn(phi_path, phi_c_path, params, boxes, delta, epsilon);
	sat_boxes = output.at(0);
	undec_boxes = output.at(1);
	unsat_boxes = output.at(2);

	cout << "=====================SAT BOXES:===================" << endl;
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		cout << i << ") " << sat_boxes.at(i) << endl;
	}

	cout << "====================UNDEC BOXES:==================" << endl;
	for(int i = 0; i < undec_boxes.size(); i++)
	{
		cout << i << ") " << undec_boxes.at(i) << endl;
	}

	cout << "====================UNSAT BOXES:==================" << endl;
	for(int i = 0; i < unsat_boxes.size(); i++)
	{
		cout << i << ") " << unsat_boxes.at(i) << endl;
	}

	vector<Box> sat_boxes_3 = sat_boxes;

	boxes.clear();
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		boxes.push_back(sat_boxes.at(i));
	}

	vector<Box> res_sat_boxes = BoxFactory::vectors_intersection(sat_boxes_2, sat_boxes_3);
	cout << "================RESULTING INTERSECTION============" << endl;
	for(int i = 0; i < res_sat_boxes.size(); i++)
	{
		cout << i << ") " << res_sat_boxes.at(i) << endl;
	}

	cout << "======================TIME:========================" << endl;
	cout << time(NULL) - start_time << " seconds" << endl;
	cout << "===================================================" << endl;
}

void solve_four_points()
{
	//inout parameters
	string phi_path = "/home/b2049657/ParSyn/model/parabola-4-points/phi.smt2";
	string phi_c_path = "/home/b2049657/ParSyn/model/parabola-4-points/phi-c.smt2";
	double delta = 0.000001;
	double epsilon = 0.000001;

	vector<DInterval> dimensions;
	dimensions.push_back(DInterval(0.0, 4.0));
	Box param_domain(dimensions);
	vector<Box> boxes;
	boxes.push_back(param_domain);
	
	vector<string> params;
	params.push_back("k");
	
	cout << "======Old ParSyn for 4 time points:===========" << endl;
	double start_time = time(NULL);
	cout << scientific << setprecision(12) << endl;
	vector< vector<Box> > output = ParSyn(phi_path, phi_c_path, params, boxes, delta, epsilon);
	vector<Box> sat_boxes = output.at(0);
	vector<Box> undec_boxes = output.at(1);
	vector<Box> unsat_boxes = output.at(2);

	cout << "=====================SAT BOXES:===================" << endl;
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		cout << i << ") " << sat_boxes.at(i) << endl;
	}

	cout << "====================UNDEC BOXES:==================" << endl;
	for(int i = 0; i < undec_boxes.size(); i++)
	{
		cout << i << ") " << undec_boxes.at(i) << endl;
	}

	cout << "====================UNSAT BOXES:==================" << endl;
	for(int i = 0; i < unsat_boxes.size(); i++)
	{
		cout << i << ") " << unsat_boxes.at(i) << endl;
	}
	
	cout << "======================TIME:========================" << endl;
	cout << time(NULL) - start_time << " seconds" << endl;
	cout << "===================================================" << endl;

	start_time = time(NULL);

	cout << endl;
	cout << endl;
	cout << "======New ParSyn for the second time points:===========" << endl;

	phi_path = "/home/b2049657/ParSyn/model/parabola-4-points/phi-2.smt2";
	phi_c_path = "/home/b2049657/ParSyn/model/parabola-4-points/phi-c-2.smt2";
	cout << scientific << setprecision(12) << endl;
	output = ParSyn(phi_path, phi_c_path, params, boxes, delta, epsilon);
	sat_boxes = output.at(0);
	undec_boxes = output.at(1);
	unsat_boxes = output.at(2);

	cout << "=====================SAT BOXES:===================" << endl;
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		cout << i << ") " << sat_boxes.at(i) << endl;
	}

	cout << "====================UNDEC BOXES:==================" << endl;
	for(int i = 0; i < undec_boxes.size(); i++)
	{
		cout << i << ") " << undec_boxes.at(i) << endl;
	}

	cout << "====================UNSAT BOXES:==================" << endl;
	for(int i = 0; i < unsat_boxes.size(); i++)
	{
		cout << i << ") " << unsat_boxes.at(i) << endl;
	}

	vector<Box> sat_boxes_2 = sat_boxes;

	boxes.clear();
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		boxes.push_back(sat_boxes.at(i));
	}

	
	cout << endl;
	cout << endl;
	cout << "======New ParSyn for the third time points:===========" << endl;

	phi_path = "/home/b2049657/ParSyn/model/parabola-4-points/phi-3.smt2";
	phi_c_path = "/home/b2049657/ParSyn/model/parabola-4-points/phi-c-3.smt2";
	cout << scientific << setprecision(12) << endl;
	output = ParSyn(phi_path, phi_c_path, params, boxes, delta, epsilon);
	sat_boxes = output.at(0);
	undec_boxes = output.at(1);
	unsat_boxes = output.at(2);

	cout << "=====================SAT BOXES:===================" << endl;
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		cout << i << ") " << sat_boxes.at(i) << endl;
	}

	cout << "====================UNDEC BOXES:==================" << endl;
	for(int i = 0; i < undec_boxes.size(); i++)
	{
		cout << i << ") " << undec_boxes.at(i) << endl;
	}

	cout << "====================UNSAT BOXES:==================" << endl;
	for(int i = 0; i < unsat_boxes.size(); i++)
	{
		cout << i << ") " << unsat_boxes.at(i) << endl;
	}

	vector<Box> sat_boxes_3 = sat_boxes;

	boxes.clear();
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		boxes.push_back(sat_boxes.at(i));
	}

	cout << endl;
	cout << endl;
	cout << "======New ParSyn for the fourth time points:===========" << endl;

	phi_path = "/home/b2049657/ParSyn/model/parabola-4-points/phi-4.smt2";
	phi_c_path = "/home/b2049657/ParSyn/model/parabola-4-points/phi-c-4.smt2";
	cout << scientific << setprecision(12) << endl;
	output = ParSyn(phi_path, phi_c_path, params, boxes, delta, epsilon);
	sat_boxes = output.at(0);
	undec_boxes = output.at(1);
	unsat_boxes = output.at(2);

	cout << "=====================SAT BOXES:===================" << endl;
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		cout << i << ") " << sat_boxes.at(i) << endl;
	}

	cout << "====================UNDEC BOXES:==================" << endl;
	for(int i = 0; i < undec_boxes.size(); i++)
	{
		cout << i << ") " << undec_boxes.at(i) << endl;
	}

	cout << "====================UNSAT BOXES:==================" << endl;
	for(int i = 0; i < unsat_boxes.size(); i++)
	{
		cout << i << ") " << unsat_boxes.at(i) << endl;
	}

	vector<Box> sat_boxes_4 = sat_boxes;	

	vector<Box> res_sat_boxes = BoxFactory::vectors_intersection(sat_boxes_2, sat_boxes_3);
	res_sat_boxes = BoxFactory::vectors_intersection(res_sat_boxes, sat_boxes_4);
	cout << "================RESULTING INTERSECTION============" << endl;
	for(int i = 0; i < res_sat_boxes.size(); i++)
	{
		cout << i << ") " << res_sat_boxes.at(i) << endl;
	}

	cout << "======================TIME:========================" << endl;
	cout << time(NULL) - start_time << " seconds" << endl;
	cout << "===================================================" << endl;
}

void solve_five_points()
{
	//inout parameters
	string phi_path = "/home/b2049657/ParSyn/model/parabola-5-points/phi.smt2";
	string phi_c_path = "/home/b2049657/ParSyn/model/parabola-5-points/phi-c.smt2";
	double delta = 0.000001;
	double epsilon = 0.000001;

	vector<DInterval> dimensions;
	dimensions.push_back(DInterval(0.0, 4.0));
	Box param_domain(dimensions);
	vector<Box> boxes;
	boxes.push_back(param_domain);
	
	vector<string> params;
	params.push_back("k");
	
	cout << "======Old ParSyn for 5 time points:===========" << endl;
	double start_time = time(NULL);
	cout << scientific << setprecision(12) << endl;
	vector< vector<Box> > output = ParSyn(phi_path, phi_c_path, params, boxes, delta, epsilon);
	vector<Box> sat_boxes = output.at(0);
	vector<Box> undec_boxes = output.at(1);
	vector<Box> unsat_boxes = output.at(2);

	cout << "=====================SAT BOXES:===================" << endl;
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		cout << i << ") " << sat_boxes.at(i) << endl;
	}

	cout << "====================UNDEC BOXES:==================" << endl;
	for(int i = 0; i < undec_boxes.size(); i++)
	{
		cout << i << ") " << undec_boxes.at(i) << endl;
	}

	cout << "====================UNSAT BOXES:==================" << endl;
	for(int i = 0; i < unsat_boxes.size(); i++)
	{
		cout << i << ") " << unsat_boxes.at(i) << endl;
	}
	
	cout << "======================TIME:========================" << endl;
	cout << time(NULL) - start_time << " seconds" << endl;
	cout << "===================================================" << endl;

	start_time = time(NULL);

	cout << endl;
	cout << endl;
	cout << "======New ParSyn for the second time points:===========" << endl;

	phi_path = "/home/b2049657/ParSyn/model/parabola-5-points/phi-2.smt2";
	phi_c_path = "/home/b2049657/ParSyn/model/parabola-5-points/phi-c-2.smt2";
	cout << scientific << setprecision(12) << endl;
	output = ParSyn(phi_path, phi_c_path, params, boxes, delta, epsilon);
	sat_boxes = output.at(0);
	undec_boxes = output.at(1);
	unsat_boxes = output.at(2);

	cout << "=====================SAT BOXES:===================" << endl;
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		cout << i << ") " << sat_boxes.at(i) << endl;
	}

	cout << "====================UNDEC BOXES:==================" << endl;
	for(int i = 0; i < undec_boxes.size(); i++)
	{
		cout << i << ") " << undec_boxes.at(i) << endl;
	}

	cout << "====================UNSAT BOXES:==================" << endl;
	for(int i = 0; i < unsat_boxes.size(); i++)
	{
		cout << i << ") " << unsat_boxes.at(i) << endl;
	}

	vector<Box> sat_boxes_2 = sat_boxes;

	boxes.clear();
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		boxes.push_back(sat_boxes.at(i));
	}

	
	cout << endl;
	cout << endl;
	cout << "======New ParSyn for the third time points:===========" << endl;

	phi_path = "/home/b2049657/ParSyn/model/parabola-5-points/phi-3.smt2";
	phi_c_path = "/home/b2049657/ParSyn/model/parabola-5-points/phi-c-3.smt2";
	cout << scientific << setprecision(12) << endl;
	output = ParSyn(phi_path, phi_c_path, params, boxes, delta, epsilon);
	sat_boxes = output.at(0);
	undec_boxes = output.at(1);
	unsat_boxes = output.at(2);

	cout << "=====================SAT BOXES:===================" << endl;
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		cout << i << ") " << sat_boxes.at(i) << endl;
	}

	cout << "====================UNDEC BOXES:==================" << endl;
	for(int i = 0; i < undec_boxes.size(); i++)
	{
		cout << i << ") " << undec_boxes.at(i) << endl;
	}

	cout << "====================UNSAT BOXES:==================" << endl;
	for(int i = 0; i < unsat_boxes.size(); i++)
	{
		cout << i << ") " << unsat_boxes.at(i) << endl;
	}

	vector<Box> sat_boxes_3 = sat_boxes;

	boxes.clear();
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		boxes.push_back(sat_boxes.at(i));
	}

	cout << endl;
	cout << endl;
	cout << "======New ParSyn for the fourth time points:===========" << endl;

	phi_path = "/home/b2049657/ParSyn/model/parabola-5-points/phi-4.smt2";
	phi_c_path = "/home/b2049657/ParSyn/model/parabola-5-points/phi-c-4.smt2";
	cout << scientific << setprecision(12) << endl;
	output = ParSyn(phi_path, phi_c_path, params, boxes, delta, epsilon);
	sat_boxes = output.at(0);
	undec_boxes = output.at(1);
	unsat_boxes = output.at(2);

	cout << "=====================SAT BOXES:===================" << endl;
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		cout << i << ") " << sat_boxes.at(i) << endl;
	}

	cout << "====================UNDEC BOXES:==================" << endl;
	for(int i = 0; i < undec_boxes.size(); i++)
	{
		cout << i << ") " << undec_boxes.at(i) << endl;
	}

	cout << "====================UNSAT BOXES:==================" << endl;
	for(int i = 0; i < unsat_boxes.size(); i++)
	{
		cout << i << ") " << unsat_boxes.at(i) << endl;
	}

	vector<Box> sat_boxes_4 = sat_boxes;

	boxes.clear();
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		boxes.push_back(sat_boxes.at(i));
	}	

	cout << endl;
	cout << endl;
	cout << "======New ParSyn for the fifth time points:===========" << endl;

	phi_path = "/home/b2049657/ParSyn/model/parabola-5-points/phi-5.smt2";
	phi_c_path = "/home/b2049657/ParSyn/model/parabola-5-points/phi-c-5.smt2";
	cout << scientific << setprecision(12) << endl;
	output = ParSyn(phi_path, phi_c_path, params, boxes, delta, epsilon);
	sat_boxes = output.at(0);
	undec_boxes = output.at(1);
	unsat_boxes = output.at(2);

	cout << "=====================SAT BOXES:===================" << endl;
	for(int i = 0; i < sat_boxes.size(); i++)
	{
		cout << i << ") " << sat_boxes.at(i) << endl;
	}

	cout << "====================UNDEC BOXES:==================" << endl;
	for(int i = 0; i < undec_boxes.size(); i++)
	{
		cout << i << ") " << undec_boxes.at(i) << endl;
	}

	cout << "====================UNSAT BOXES:==================" << endl;
	for(int i = 0; i < unsat_boxes.size(); i++)
	{
		cout << i << ") " << unsat_boxes.at(i) << endl;
	}

	vector<Box> sat_boxes_5 = sat_boxes;	

	vector<Box> res_sat_boxes = BoxFactory::vectors_intersection(sat_boxes_2, sat_boxes_3);
	res_sat_boxes = BoxFactory::vectors_intersection(res_sat_boxes, sat_boxes_4);
	res_sat_boxes = BoxFactory::vectors_intersection(res_sat_boxes, sat_boxes_5);
	cout << "================RESULTING INTERSECTION============" << endl;
	for(int i = 0; i < res_sat_boxes.size(); i++)
	{
		cout << i << ") " << res_sat_boxes.at(i) << endl;
	}

	cout << "======================TIME:========================" << endl;
	cout << time(NULL) - start_time << " seconds" << endl;
	cout << "===================================================" << endl;
}

int main(int argc, char* argv[])
{

	/*
	xml_document doc;
	xml_parse_result result = doc.load_file("tree.xml");

    cout << "Load result: " << result.description() << ", mesh name: " << doc.child("mesh").attribute("name").value() << std::endl;

    cout << doc.child("mesh").child("node").attribute("attr1").value() << endl;
	*/

    SMT2Generator gen("data.xml");

    vector<string> var = gen.get_vars();
    Box var_domain = gen.get_var_domain();

    vector<string> param = gen.get_params();
    Box param_domain = gen.get_param_domain();

    string time_var = gen.get_time_var();
    vector<string> odes = gen.get_odes();

    std::map<double, Box> time_series = gen.get_time_series();

    cout << "Vars:" << endl;    
    for(int i = 0; i < var.size(); i++)
    {
    	cout << i << ") " << var.at(i) << endl;
    }

    cout << "Var domain: " << var_domain << endl;

    cout << "Params:" << endl;    
    for(int i = 0; i < param.size(); i++)
    {
    	cout << i << ") " << param.at(i) << endl;
    }

    cout << "Param domain: " << param_domain << endl;

    cout << "Time var: " << time_var << endl;

    cout << "ODEs:" << endl;
    for(int i = 0; i < odes.size(); i++)
    {
    	cout << i << ") " << odes.at(i) << endl;
    }

    cout << "Time series:" << endl;
    cout << "Time --- Box" << endl;
    for(std::map<double, Box>::iterator map_it = time_series.begin(); map_it != time_series.end(); map_it++)
    {
    	cout << map_it->first << " --- " << map_it->second << endl;
    }

    cout << "Delta = " << gen.get_delta() << endl;
    cout << "Epsilon = " << gen.get_epsilon() << endl;

	//solve_three_points();
	//solve_four_points();
	//solve_five_points();


	/*
	undec_boxes = BoxFactory::merge_boxes(undec_boxes);
	cout << "=============SAT AND UNDEC BOXES MERGED:==========" << endl;
	for(int i = 0; i < undec_boxes.size(); i++)
	{
		cout << i << ") " << undec_boxes.at(i) << endl;
	}
	cout << "==================================================" << endl;
	*/

	/*
	cout << "Merging boxes:" << endl; 
	dimensions.clear();
	dimensions.push_back(DInterval(0, 4));
	dimensions.push_back(DInterval(0, 4));
	dimensions.push_back(DInterval(0, 4));
	dimensions.push_back(DInterval(0, 4));

	Box init_box(dimensions);

	cout << "Initial box: " << init_box << endl;

	vector<Box> input = BoxFactory::branch_box(init_box);

	cout << "Branching:" << endl;
	for(int i = 0; i < input.size(); i++)
	{
		cout << i << ") " << input.at(i) << endl;
	}

	vector<Box> output = BoxFactory::merge_boxes(input);

	cout << "Merging:" << endl;

	for(int i = 0; i < output.size(); i++)
	{
		cout << i << ") " << output.at(i) << endl;
	}
	*/

	/*
	cout << "Merging boxes:" << endl; 
	dimensions.clear();
	dimensions.push_back(DInterval(0, 4));
	dimensions.push_back(DInterval(0, 4));
	dimensions.push_back(DInterval(0, 4));
	dimensions.push_back(DInterval(0, 4));

	Box init_box(dimensions);

	cout << "Initial box: " << init_box << endl;

	vector<Box> inter_boxes = BoxFactory::branch_box(init_box);
	*/
	/*
	cout << "Boxes intersection:" << endl; 
	dimensions.clear();
	dimensions.push_back(DInterval(-1, 4));
	dimensions.push_back(DInterval(-1, 4));
	dimensions.push_back(DInterval(-1, 4));

	inter_boxes.push_back(Box(dimensions));

	dimensions.clear();
	dimensions.push_back(DInterval(-4, 1));
	dimensions.push_back(DInterval(-4, 1));
	dimensions.push_back(DInterval(-4, 1));

	inter_boxes.push_back(Box(dimensions));

	dimensions.clear();
	dimensions.push_back(DInterval(-2, 3));
	dimensions.push_back(DInterval(-2, 3));
	dimensions.push_back(DInterval(-2, 3));

	inter_boxes.push_back(Box(dimensions));

	dimensions.clear();
	dimensions.push_back(DInterval(-3, 2));
	dimensions.push_back(DInterval(-3, 2));
	dimensions.push_back(DInterval(-3, 2));

	inter_boxes.push_back(Box(dimensions));
	*/
	/*
	cout << "INITIAL BOXES:" << endl;
	for(int i = 0; i < inter_boxes.size(); i++)
	{
		cout << i << ") " << inter_boxes.at(i) << endl;
	}

	Box inter_box = BoxFactory::boxes_intersection(inter_boxes);

	if(inter_box.get_dimension_size() > 0)
	{
		cout << "Given boxes intersect at: " << inter_box << endl;
	}
	else
	{
		cout << "Given boxes do not intersect" << endl;
	}
	*/

	return EXIT_SUCCESS;
}




