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
bool output = false;
bool exhaustive = false;
bool est = false;
bool full_syn = false;
bool partition_flag = false;
bool merge_flag = false;
double epsilon = 1e-3;
vector<double> epsilon_vector;
stringstream parsyn_out;

void term_app() 
{
	stringstream term_code;
    term_code << "#!/bin/bash\n";
	term_code << "function get_children {\n";
	term_code << "clist=`pgrep -P $1`\n";
	term_code << "plist=\"$plist $1\"\n";
	term_code << "if [ -n \"$clist\" ]\n";
	term_code << "then\n";
	term_code << "for c in $clist\n";
	term_code << "do\n";
	term_code << "get_children $c\n";
	term_code << "done\n";
	term_code << "fi\n";
	term_code << "}\n";
	term_code << "\n";
	term_code << "fclist=`pgrep -P $1`\n";

	term_code << "plist=\"$plist $fclist\"\n";
	term_code << "for fc in $fclist\n";
	term_code << "do\n";
	term_code << "get_children $fc\n";
	term_code << "done\n";
	term_code << "\n";
	term_code << "for p in $plist\n";
	term_code << "do\n";
	term_code << "kill -9 $p > /dev/null 2> /dev/null\n";
	term_code << "done\n";
	term_code << "sleep 1\n";

    ofstream term_script;
    term_script.open("term_app.sh");
    term_script << term_code.str();
    term_script.close();

    stringstream term_command;
	term_command << "/bin/bash term_app.sh " << getpid();
    system(term_command.str().c_str());

    remove("term_app.sh");
}

void print_help(ostream& stream)
{
	stream << endl;
	stream << "Help message:" << endl;
	stream << endl;
	stream << "	Run ./ParSyn <options> <model-file.xml>" << endl;
	stream << endl;
	stream << "options:" << endl;
	stream << "	-l <string> - full path to dReal binary (default dReal)" << endl;
	stream << "	-t <int> - number of CPU cores (default " << max_num_threads << ") (max " << max_num_threads << ")" << endl;
	stream << "	-h/--help - help message" << endl;
	stream << "	--dreal - delimits dReal options (e.g. precision, ode step)" << endl;
	stream << "	--partition - partition the entire parameter space before evaluating" << endl;
	stream << "	--full-synthesis - perform full parameter synthesis" << endl;
	stream << "	--exhaustive - perform exhaustive search for each time point (works only with --full-synthesis)" << endl;
	stream << endl;
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
		cerr << "Not enough arguments" << endl;
		print_help(cerr);
		exit(EXIT_FAILURE);
	}

	//only one -h/--help or --version is provided
	if(argc == 2)
	{
		if((strcmp(argv[1], "-h") == 0) || (strcmp(argv[1], "--help") == 0))
		{
			print_help(cout);
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
			print_help(cout);
		}
		//dReal binary
		else if(strcmp(argv[i], "-l") == 0)
		{
			i++;
			ostringstream os;
			os << argv[i];
			dreal_bin = os.str();
		}
		//exhaustive flag
		else if(strcmp(argv[i], "--exhaustive") == 0)
		{
			exhaustive = true;
		}
		//verbose
		else if(strcmp(argv[i], "--verbose") == 0)
		{
			verbose = true;
		}
		//verbose
		else if(strcmp(argv[i], "--merge") == 0)
		{
			merge_flag = true;
		}
		//--full-synthesis
		else if(strcmp(argv[i], "--full-synthesis") == 0)
		{
			full_syn = true;
		}
		//partition
		else if(strcmp(argv[i], "--partition") == 0)
		{
			partition_flag = true;
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
				cerr << "Precision value -e should be positive" << endl;
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
			cerr << "Unrecognized option: " << argv[i] << ". Use --help" << endl;
			print_help(cerr);
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

vector<Box> prepartition(vector<Box> boxes, double epsilon)
{
	vector<Box> tmp_list;
	for(long int i = 0; i < boxes.size(); i++)
	{
		tmp_list.push_back(boxes.at(i));
	}
	boxes.clear();

	while(tmp_list.size() > 0)
    {
    	Box tmp_box = tmp_list.front();
		tmp_list.erase(tmp_list.begin());
    	if (width(tmp_box.get_max_dimension()) > 0)
    	{
	    	vector<Box> tmp_vector = BoxFactory::branch_box(tmp_box, epsilon_vector);
	    	//vector<Box> tmp_vector = BoxFactory::branch_box(tmp_box, epsilon);
	    	//vector<Box> tmp_vector = BoxFactory::branch_box(tmp_box);
			if(tmp_vector.size() == 1)
			{
				boxes.push_back(tmp_box);
			}
			else
			{
				for(long int i = 0; i < tmp_vector.size(); i++)
				{
					tmp_list.push_back(tmp_vector.at(i));
				}
			}
		}
		else
		{
			boxes.push_back(tmp_box);
		}
	}

	return boxes;
}

int main(int argc, char* argv[])
{
	// setting max number of threads by default
	#ifdef _OPENMP
		max_num_threads = omp_get_max_threads();
		num_threads = max_num_threads;
		omp_set_num_threads(num_threads);
	#endif
	
	// parsing command line		
	parse_cmd(argc, argv);
	string xml_file_path = filename;

	// algorithms
	try
    {
	    SMT2Generator gen(xml_file_path);
	    epsilon_vector = gen.get_epsilon();
		gen.init_output(filename + ".output");
	    vector<Box> undec_boxes, sat_boxes, unsat_boxes, mixed_boxes, boxes;
	    boxes.push_back(gen.get_param_domain());

	    if(!full_syn)
	    {
		    boxes = prepartition(boxes, epsilon);

			long int count = 0;
			bool exit_flag = false;
			#pragma omp parallel
			{
				#pragma omp for
				for(long int i = 0; i < boxes.size(); i++)
				{
					#pragma omp flush
					if(!exit_flag)
					{
						bool sat_box_flag = true;
						for(int j = 0; j < gen.get_time_values().size() - 1; j++)
						{
							#pragma omp flush
							if(sat_box_flag)
							{
								vector<string> file_base_name = gen.generate_smt2(j + 1, boxes.at(i));
								int result = DecisionProcedure::evaluate(file_base_name, dreal_options, dreal_bin);

								#pragma omp critical
								{
									if(result == 1)
									{

									}
									if(result == 0)
									{
										undec_boxes.push_back(boxes.at(i));
										count++;
										gen.modify_output((double) count / boxes.size(), sat_boxes, unsat_boxes, undec_boxes);
										sat_box_flag = false;
									}
									if(result == -1)
									{
										unsat_boxes.push_back(boxes.at(i));
										count++;
										gen.modify_output((double) count / boxes.size(), sat_boxes, unsat_boxes, undec_boxes);
										sat_box_flag = false;
									}
								}
							}
						}
						#pragma omp flush
						#pragma omp critical
						{
							if(sat_box_flag)
							{
								sat_box_flag = false;
								sat_boxes.push_back(boxes.at(i));
								gen.modify_output(1, sat_boxes, unsat_boxes, undec_boxes);
								exit_flag = true;
								term_app();
								exit(EXIT_SUCCESS);
							}
						}
					}	
				}
			}	
	    }
	    else
	    {
	    	// regular algorithm
		    for(int j = 0; j < gen.get_time_values().size() - 1; j++)
		    {
		    	// resetting the stack
				sat_boxes.clear();
				undec_boxes.clear();
				unsat_boxes.clear();

				// complete partitioning of entire parameter space
				if(partition_flag)
				{
					boxes = prepartition(boxes, epsilon);
				}

				// making all threads busy
			    while(boxes.size() < num_threads)
			    {
			    	Box tmp_box = boxes.front();
			    	boxes.erase(boxes.begin());
			    	if (width(tmp_box.get_max_dimension()) > 0)
			    	{
			    		// here we ignore epsilon_vector
			    		vector<Box> tmp_vector = BoxFactory::branch_box(tmp_box);
						//vector<Box> tmp_vector = BoxFactory::branch_box(tmp_box, epsilon);
						for(int i = 0; i < tmp_vector.size(); i++)
						{
							boxes.push_back(tmp_vector.at(i));
						}
					}
					else
					{
						boxes.push_back(tmp_box);
					}
			    }
			    
			    // calculating max progress for the time point
				double max_progress = 0;
				for(long int i = 0; i < boxes.size(); i++)
				{
					double vol = 1;
					for(int j = 0; j < boxes.at(i).get_dimension_size(); j++)
					{
						if (width(boxes.at(i).get_dimension(j)) > 0) vol *= width(boxes.at(i).get_dimension(j));
					}
					max_progress += vol;
				}

				// processing all boxes for the time points
				double current_progress = 0;
			    while(boxes.size() > 0)
				{
					#pragma omp parallel
					{
						#pragma omp for
						for(long int i = 0; i < boxes.size(); i++)
						{
							vector<string> file_base_name = gen.generate_smt2(j + 1, boxes.at(i));
							int result = DecisionProcedure::evaluate(file_base_name, dreal_options, dreal_bin);
							
							#pragma omp critical
							{
								if(result == 1)
								{
									sat_boxes.push_back(boxes.at(i));
									double vol = 1;
									for(int j = 0; j < boxes.at(i).get_dimension_size(); j++)
									{
										if (width(boxes.at(i).get_dimension(j)) > 0) vol *= width(boxes.at(i).get_dimension(j));
									}
									current_progress += vol;
								}
								if(result == 0)
								{
									vector<Box> tmp_vector = BoxFactory::branch_box(boxes.at(i), epsilon_vector);
									if(tmp_vector.size() == 1)
									{
										undec_boxes.push_back(boxes.at(i));
										double vol = 1;
										for(int j = 0; j < boxes.at(i).get_dimension_size(); j++)
										{
											if (width(boxes.at(i).get_dimension(j)) > 0) vol *= width(boxes.at(i).get_dimension(j));
										}
										current_progress += vol;
									}
									else
									{
										for(long int i = 0; i < tmp_vector.size(); i++)
										{
											mixed_boxes.push_back(tmp_vector.at(i));
										}
									}
								}
								if(result == -1)
								{
									unsat_boxes.push_back(boxes.at(i));
									double vol = 1;
									for(int j = 0; j < boxes.at(i).get_dimension_size(); j++)
									{
										if (width(boxes.at(i).get_dimension(j)) > 0) vol *= width(boxes.at(i).get_dimension(j));
									}
									current_progress += vol;
								}

								double progress = 1;
								if (max_progress > 0) progress = current_progress / max_progress;
								gen.modify_output(progress, j + 1, sat_boxes, unsat_boxes, undec_boxes);
							}
						}
					}
					boxes.clear();
					for(long int i = 0; i < mixed_boxes.size(); i++)
					{
						boxes.push_back(mixed_boxes.at(i));
					}
					mixed_boxes.clear();
				}
				if(merge_flag)
				{
					sat_boxes = BoxFactory::merge_boxes(BoxFactory::sort_boxes(sat_boxes));
					undec_boxes = BoxFactory::merge_boxes(BoxFactory::sort_boxes(undec_boxes));
					unsat_boxes = BoxFactory::merge_boxes(BoxFactory::sort_boxes(unsat_boxes));
				}
				double progress = 1;
				if (max_progress > 0) progress = current_progress / max_progress;
				gen.modify_output(progress, j + 1, sat_boxes, unsat_boxes, undec_boxes);
				if(sat_boxes.size() == 0)
				{
					cout << "no SAT boxes" << endl;
					break;
				}

				boxes.clear();
				if(exhaustive)
				{
					boxes.push_back(gen.get_param_domain());
				}
				else
				{
					for(long int i = 0; i < sat_boxes.size(); i++)
					{
						boxes.push_back(sat_boxes.at(i));
					}
				}
			}
	    }
	}
	catch(char const* e)
	{
		cerr << "Error parsing the file " << xml_file_path << ". Reason: " << e << endl;
		exit(EXIT_FAILURE);
	}
	
	return EXIT_SUCCESS;
}




