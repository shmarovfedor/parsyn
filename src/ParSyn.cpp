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
#ifdef _OPENMP
	#include<omp.h>
#endif
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

string dreal_bin = "";
int max_num_threads = 1;
int num_threads = max_num_threads;
string filename = "";
string parsyn_version("1.0");
string dreal_options = "";
bool verbose = false;
bool est = false;
double epsilon = 1e-3;

void print_help()
{
	cout << endl;
	cout << "Help message:" << endl;
	cout << endl;
	cout << "	Run ./ProbReach <options> <model-file.xml>" << endl;
	cout << endl;
	cout << "options:" << endl;
	cout << "	-l <string> - full path to dReal binary (default dReal)" << endl;
	cout << "	-t <int> - number of CPU cores (default " << max_num_threads << ") (max " << max_num_threads << ")" << endl;
	cout << "	-h/--help - help message" << endl;
	cout << "	--dreal - delimits dReal options (e.g. precision, ode step)" << endl;
	cout << "	--est - apply parameter estimation" << endl;
	cout << endl;
}

void print_version()
{
	cout << "ParSyn " << parsyn_version << endl;
}

void parse_cmd(int argc, char* argv[])
{
	//no arguments are input
	if(argc < 2)
	{
		print_help();
		exit(EXIT_FAILURE);
	}

	//only one -h/--help or --version is provided
	if(argc == 2)
	{
		if((strcmp(argv[1], "-h") == 0) || (strcmp(argv[1], "--help") == 0))
		{
			print_help();
			exit(EXIT_SUCCESS);
		}
		else if((strcmp(argv[1], "--version") == 0))
		{
			print_version();
			exit(EXIT_SUCCESS);
		}
	}
	// parsing --dreal options
	int opt_end = argc;
	stringstream s;
	for(int i = 1; i < argc; i++)
	{
		//reached --dreal flag
		if(strcmp(argv[i], "--dreal") == 0)
		{
			//indicating the end of ProbReach options
			opt_end = i;
			while(true)
			{
				//reached the end of command line
				if(i == argc - 1) break;
				//next arg after --dreal flag
				i++;
				s << argv[i] << " ";
			}
			//composing dReal options
			dreal_options = s.str();
		}

	}
	//parsing ParSyn options
	cmatch matches;
	for(int i = 1; i < opt_end; i++)
	{
		//extracting a file name
		if(regex_match(argv[i], matches, regex("(.*/)*(.*).xml")))
		{
			filename = matches[0].str();
		}
		//help
		else if((strcmp(argv[i], "-h") == 0) || (strcmp(argv[i], "--help") == 0))
		{
			print_help();
		}
		//dReal binary
		else if(strcmp(argv[i], "-l") == 0)
		{
			i++;
			ostringstream os;
			os << argv[i];
			dreal_bin = os.str();
		}
		//estimation flag
		else if(strcmp(argv[i], "--est") == 0)
		{
			est = true;
		}
		//verbose
		else if(strcmp(argv[i], "--verbose") == 0)
		{
			verbose = true;
		}
		//version
		else if(strcmp(argv[i], "--version") == 0)
		{
			print_version();
		}
		//epsilon
		else if(strcmp(argv[i], "-e") == 0)
		{
			i++;
			istringstream is(argv[i]);
			is >> epsilon;
			if(epsilon <= 0)
			{
				cerr << "Value specified in -e should be positive" << endl;
				exit(EXIT_FAILURE);
			}
		}
		//number of cores
		else if(strcmp(argv[i], "-t") == 0)
		{
			i++;
			istringstream is(argv[i]);
			is >> num_threads;
			if(num_threads <= max_num_threads)
			{
				if(num_threads > 0)
				{
					#ifdef _OPENMP
						omp_set_num_threads(num_threads);
					#endif
				}
				else
				{
					cerr << "Number of cores should be positive" << endl;
					exit(EXIT_FAILURE);
				}
			}
			else
			{
				cerr << "Max number of cores available is " << max_num_threads << ". You specified " << num_threads << endl;
				exit(EXIT_FAILURE);
			}
		}
		else
		{
			cerr << "Unrecognized option: " << argv[i] << endl;
			print_help();
			exit(EXIT_FAILURE);
		}
	}
	// case if dReal binary is not specified
	if(strcmp(dreal_bin.c_str(), "") == 0)
	{
		dreal_bin = "dReal";
	}

	//case if filename is not specified
	if(strcmp(filename.c_str(), "") == 0)
	{
		cerr << "input XML file is not specified" << endl;
		print_help();
		exit(EXIT_FAILURE);
	}
}

void print_result(vector<Box> sat_boxes, vector<Box> undec_boxes, vector<Box> unsat_boxes)
{
	cout << "=====================SAT BOXES:===================" << endl;
	cout << setprecision(16);
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
	cout << "==================================================" << endl;
}


int main(int argc, char* argv[])
{

	// setting max number of threads by default
	#ifdef _OPENMP
		max_num_threads = omp_get_max_threads();
		num_threads = max_num_threads;
		omp_set_num_threads(num_threads);
	#endif

	parse_cmd(argc, argv);

	string xml_file_path = filename;

    try
    {
    	double start_time = time(NULL);

	    SMT2Generator gen(xml_file_path);

	    vector<Box> undec_boxes, sat_boxes, unsat_boxes, mixed_boxes;

	    vector<Box> boxes;
	    boxes.push_back(gen.get_param_domain());

		if(est)
		{
			vector<string> file_base_name = gen.generate_smt2(boxes.at(0));
			int result = DecisionProcedure::evaluate(file_base_name, dreal_options, dreal_bin);
			if(result == -1)
			{
				unsat_boxes.push_back(boxes.at(0));
				print_result(sat_boxes, undec_boxes, unsat_boxes);
				cout << "THE PROBLEM IS UNSAT!!!" << endl;
				cout << "==================================================" << endl;
				cout << fixed << "TIME: " << time(NULL) - start_time << " SECONDS" << endl;
				exit(EXIT_SUCCESS);
			}
			if(result == 1)
			{
				sat_boxes.push_back(boxes.at(0));
				print_result(sat_boxes, undec_boxes, unsat_boxes);
				cout << "==================================================" << endl;
				cout << fixed << "TIME: " << time(NULL) - start_time << " SECONDS" << endl;
				exit(EXIT_SUCCESS);
			}
			if(result == 0)
			{
				undec_boxes.push_back(boxes.at(0));
				print_result(sat_boxes, undec_boxes, unsat_boxes);
				undec_boxes.clear();
				cout << endl;
				cout << "Parameter estimation is undecidable. Starting parameter synthesis" << endl;
				cout << endl;
			}
		}

		cout << "==================================================" << endl;
		cout << "==============PARAMETER SYNTHESIS:================" << endl;
	    for(int j = 0; j < gen.get_time_values().size() - 1; j++)
	    {
			sat_boxes.clear();
			undec_boxes.clear();
			unsat_boxes.clear();
	    	//additional partitioning
		    while(boxes.size() < num_threads)
		    {
		    	Box tmp_box = boxes.front();
		    	boxes.erase(boxes.begin());
		    	vector<Box> tmp_vector = BoxFactory::branch_box(tmp_box);
		    	//if(tmp_vector.at(0).get_volume() <= gen.get_epsilon())
				//if(tmp_vector.at(0).get_volume() <= epsilon)
				//{
				//	break;
				//}
				//else
				//{
					for(int i = 0; i < tmp_vector.size(); i++)
					{
						boxes.push_back(tmp_vector.at(i));
					}
				//}

		    }
		    
			cout << "=====================TIME POINT " << (j + 1) << " :===============" << endl;
			DInterval max_progress = 0;
			for(int i = 0; i < boxes.size(); i++)
			{
				max_progress += boxes.at(i).get_volume();
			}
			DInterval current_progress = 0;
		    while(boxes.size() > 0)
			{
				#pragma omp parallel
				{
					#pragma omp for
					for(int i = 0; i < boxes.size(); i++)
					{
						#pragma omp critical
						{
							if(max_progress.leftBound() > 0)
							{
								cout << setprecision(8) << fixed << "PROGRESS: " << (current_progress.leftBound() / max_progress.leftBound()) * 100 << " %\r";
							}
						}

						vector<string> file_base_name = gen.generate_smt2(j + 1, boxes.at(i));
						//int result = DecisionProcedure::evaluate(file_base_name, gen.get_delta(), dreal_bin);
						int result = DecisionProcedure::evaluate(file_base_name, dreal_options, dreal_bin);

						#pragma omp critical
						{
							if(result == 1)
							{
								sat_boxes.push_back(boxes.at(i));
								current_progress += boxes.at(i).get_volume();
							}
							if(result == 0)
							{
								if(boxes.at(i).get_volume().rightBound() <= epsilon)
								{
									undec_boxes.push_back(boxes.at(i));
									current_progress += boxes.at(i).get_volume();
								}
								else
								{
									vector<Box> tmp_vector = BoxFactory::branch_box(boxes.at(i));
									for(int j = 0; j < tmp_vector.size(); j++)
									{
										mixed_boxes.push_back(tmp_vector.at(j));
									}
								}

								/*
								if(tmp_vector.at(0).get_volume() <= gen.get_epsilon())
								{
									for(int j = 0; j < tmp_vector.size(); j++)
									{
										undec_boxes.push_back(tmp_vector.at(j));
										current_progress += tmp_vector.at(j).get_volume();
									}
								}
								else
								{
									for(int j = 0; j < tmp_vector.size(); j++)
									{
										mixed_boxes.push_back(tmp_vector.at(j));
									}
								}
								*/
							}
							if(result == -1)
							{
								unsat_boxes.push_back(boxes.at(i));
								current_progress += boxes.at(i).get_volume();
							}

						}
					}
				}
				if(max_progress.leftBound() > 0)
				{
					cout << setprecision(8) << fixed << "PROGRESS: " << (current_progress.leftBound() / max_progress.leftBound()) * 100 << " %\r";
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
			print_result(sat_boxes, undec_boxes, unsat_boxes);
			if(sat_boxes.size() == 0)
			{
				cout << "THE PROBLEM IS UNSAT!!!" << endl;
				break;
			}

			for(int i = 0; i < sat_boxes.size(); i++)
			{
				boxes.push_back(sat_boxes.at(i));
			}
		}
		cout << "==================================================" << endl;
		cout << fixed << "TIME: " << time(NULL) - start_time << " SECONDS" << endl;

	}
	catch(char const* e)
	{
		cerr << "Error parsing the file " << xml_file_path << ". Reason: " << e << endl;
		return EXIT_FAILURE;
	}
	
	return EXIT_SUCCESS;
}




