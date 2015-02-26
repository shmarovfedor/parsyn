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

string dreal_bin = "dReal";

ostream& operator<<(ostream& strm, Box& box)
{
	for(int i = 0; i < box.get_dimension_size() - 1; i++)
	{
		strm << box.get_dimension(i) << "x";
	}
	strm << box.get_dimension(box.get_dimension_size() - 1);
	
	return strm;
}

int main(int argc, char* argv[])
{

	if(argc < 2)
	{
		cout << "There must be exactly one input file" << endl;
		return EXIT_FAILURE;
	}
	else
	{
		for(int i = 1; i < argc - 1; i++)
		{
			if(strcmp(argv[i], "-l") == 0)
			{

				ostringstream os;
				os << argv[i + 1] << "dReal";
				dreal_bin = os.str();
			}
		}
	}

	int num_threads = 1;

    #ifdef _OPENMP
    	if(omp_get_max_threads() > 8)
    	{ 
    		num_threads = omp_get_max_threads() - 8;
    		omp_set_num_threads(num_threads);
    	}
    	else
    	{
    		omp_set_num_threads(num_threads);
    	}
 	#endif

	string xml_file_path = argv[argc - 1];

    try
    {
    	double start_time = time(NULL);

	    SMT2Generator gen(xml_file_path);

	    vector<Box> undec_boxes, sat_boxes, unsat_boxes, mixed_boxes;

	    vector<Box> boxes;
	    boxes.push_back(gen.get_param_domain());

	    for(int j = 0; j < gen.get_time_values().size() - 1; j++)
	    {
	    	//additional partitioning
		    while(boxes.size() < num_threads)
		    {
		    	Box tmp_box = boxes.front();
		    	boxes.erase(boxes.begin());
		    	vector<Box> tmp_vector = BoxFactory::branch_box(tmp_box);
		    	if(tmp_vector.at(0).get_volume() <= gen.get_epsilon())
				{
					break;
				}
				else
				{
					for(int i = 0; i < tmp_vector.size(); i++)
					{
						boxes.push_back(tmp_vector.at(i));
					}
				}

		    }
		    
			cout << "=====================TIME POINT " << (j + 1) << " :===================" << endl;
			DInterval max_progress = 0;
			for(int i = 0; i < boxes.size(); i++)
			{
				max_progress += boxes.at(i).get_volume();
			}
			DInterval current_progress = 0;
			//double prev_volume = 0;
		    while(boxes.size() > 0)
			{
				#pragma omp parallel
				{
					#pragma omp for
					for(int i = 0; i < boxes.size(); i++)
					{
						#pragma omp critical
						{
							cout << setprecision(2) << fixed << "PROGRESS: " << (current_progress.leftBound() / max_progress.leftBound()) * 100 << "%\r";
						}

						vector<string> file_base_name = gen.generate_smt2(j + 1, boxes.at(i));
						int result = DecisionProcedure::evaluate(file_base_name, gen.get_delta(), dreal_bin);
						
						#pragma omp critical
						{
							if(result == 1)
							{
								sat_boxes.push_back(boxes.at(i));
								current_progress += boxes.at(i).get_volume();
							}
							if(result == 0)
							{
								vector<Box> tmp_vector = BoxFactory::branch_box(boxes.at(i));
								if(tmp_vector.at(0).get_volume() <= gen.get_epsilon())
								{
									for(int j = 0; j < tmp_vector.size(); j++)
									{
										undec_boxes.push_back(tmp_vector.at(j));
										current_progress += boxes.at(i).get_volume();
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
								current_progress += boxes.at(i).get_volume();
							}

						}
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
			if(sat_boxes.size() == 0)
			{
				cout << "THE PROBLEM IS UNSAT!!!" << endl;
				break;
			}

			for(int i = 0; i < sat_boxes.size(); i++)
			{
				boxes.push_back(sat_boxes.at(i));
			}
			sat_boxes.clear();
			undec_boxes.clear();
			unsat_boxes.clear();
		}
		cout << "===============================================" << endl;
		cout << fixed << "TIME: " << time(NULL) - start_time << " SECONDS" << endl;

	}
	catch(char const* e)
	{
		cerr << "Error parsing the file " << xml_file_path << ". Reason: " << e << endl;
		return EXIT_FAILURE;
	}
	
	return EXIT_SUCCESS;
}




