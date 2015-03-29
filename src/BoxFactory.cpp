// BoxFactory class implements static methods for manipulating Boxes
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#include<string.h>
#include<sstream>
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include "BoxFactory.h"
#include "Box.h"

using namespace std;
using namespace capd;

// The method gets a vector of vectors of PartialSum as an input parameter
// and return a Cartesian product of the vectors
vector<Box> BoxFactory::calculate_cart_prod(vector< vector<DInterval> > intervals, vector<string> vars)
{
	int elem = 1;
	vector<Box> cart_prod;
	for(int i = 0; i < intervals.size(); i++) elem *= intervals.at(i).size();
	
	for(int i = 0; i < elem; i++)
	{
		int index = i;
		vector<DInterval> tmp_vector;
		for(int j = 0; j < intervals.size(); j++)
		{
			int mult = 1;
			for(int k = intervals.size() - 1; k > j; k--)
			{
				mult *= intervals.at(k).size();
			}
			int tmp_index = index / mult;
			tmp_vector.push_back(intervals.at(j).at(tmp_index));
			index -= tmp_index * mult;
		}
		cart_prod.push_back(Box(tmp_vector, vars));
	}
	return cart_prod;
}

// The method gets a Box of n demensions as an input parameter and returns 
// a vector of 2^n boxes obtained by dividing each edge of the primary 
// box in halves
vector<Box> BoxFactory::branch_box(Box box)
{
	vector<DInterval> dimensions = box.get_dimensions();
	vector <vector<DInterval> > intervals;
	for(int i = 0; i < dimensions.size(); i++)
	{
		vector <DInterval> tmp;
		DInterval left_interval(dimensions.at(i).leftBound(), dimensions.at(i).mid().rightBound());
		DInterval right_interval(dimensions.at(i).mid().leftBound(), dimensions.at(i).rightBound());
		tmp.push_back(left_interval);
		tmp.push_back(right_interval);
		intervals.push_back(tmp);
	}
	return BoxFactory::calculate_cart_prod(intervals, box.get_vars());
}

bool BoxFactory::compare_boxes_des(Box left, Box right)
{
	return (left.get_volume().leftBound() > right.get_volume().leftBound());
}

vector<Box> BoxFactory::merge_boxes(vector<Box> input)
{
	//vector<Box> output;
	int i = 0;
	while(i < input.size())
	{
		int previous_size = input.size();
		for(int j = i + 1; j < input.size(); j++)
		{
			Box temp_box = merge_two_boxes(input.at(i), input.at(j));
			if(temp_box.get_dimension_size() != 0)
			{
				input.at(i) = temp_box;
				input.erase(input.begin() + j);
				i = 0;
				break;
			}
		}
		if(input.size() == previous_size)
		{
			i++;
		}
	}
	return input;
}


Box BoxFactory::merge_two_boxes(Box left, Box right)
{
	if((left.get_dimension_size() == 0) || (right.get_dimension_size() == 0) || (left.get_dimension_size() != right.get_dimension_size()))
	{
		cerr << "Error merging boxes. Reason: length of dimensions vectors is not the same" << endl;
		exit(EXIT_FAILURE);
	}

	vector<string> left_vars = left.get_vars();
	vector<string> right_vars = right.get_vars();

	for(int i = 0; i < left_vars.size(); i++)
	{
		if(strcmp(left_vars.at(i).c_str(), right_vars.at(i).c_str()) != 0)
		{
			cerr << "Error merging boxes. Reason: vector of variables is not the same for two boxes" << endl;
			exit(EXIT_FAILURE);
		}
	}

	int not_eq_dim = 0;
	int not_eq_index = 0;

	for(int i = 0; i < left.get_dimension_size(); i++)
	{
		if(left.get_dimension(i) != right.get_dimension(i))
		{
			not_eq_dim++;
			not_eq_index = i;
		}

		if(not_eq_dim > 1)
		{
			return Box();
		}
	}

	//checking for the inclusion
	/*
	Box inter = two_boxes_intersection(left, right);
	if(inter.get_dimension_size() == 0)
	{
		return Box();
	}
	
	if(inter.get_volume() == left.get_volume())
	{
		return right;
	}

	if(inter.get_volume() == right.get_volume())
	{
		return left;
	}
	*/
	
	//in this case boxes overlap
	if(left.get_dimension(not_eq_index).rightBound() == right.get_dimension(not_eq_index).leftBound())
	{
		vector<DInterval> dimensions = left.get_dimensions();
		dimensions.at(not_eq_index) = DInterval(left.get_dimension(not_eq_index).leftBound(), right.get_dimension(not_eq_index).rightBound());
		return Box(dimensions, left_vars);
	}
	else
	{
		if(left.get_dimension(not_eq_index).leftBound() == right.get_dimension(not_eq_index).rightBound())
		{
			vector<DInterval> dimensions = left.get_dimensions();
			dimensions.at(not_eq_index) = DInterval(right.get_dimension(not_eq_index).leftBound(), left.get_dimension(not_eq_index).rightBound());
			return Box(dimensions, left_vars);
		}
		else
		{
			return Box();
		}
	}
}

Box BoxFactory::two_boxes_intersection(Box left, Box right)
{
	if((left.get_dimension_size() == 0) || (right.get_dimension_size() == 0) || (left.get_dimension_size() != right.get_dimension_size()))
	{
		cerr << "Error merging boxes. Reason: length of dimensions vectors is not the same" << endl;
		exit(EXIT_FAILURE);
	}

	vector<string> left_vars = left.get_vars();
	vector<string> right_vars = right.get_vars();

	for(int i = 0; i < left_vars.size(); i++)
	{
		if(strcmp(left_vars.at(i).c_str(), right_vars.at(i).c_str()) != 0)
		{
			cerr << "Error merging boxes. Reason: vector of variables is not the same for two boxes" << endl;
			exit(EXIT_FAILURE);
		}
	}

	vector<DInterval> dimensions;
	for(int i = 0; i < left.get_dimension_size(); i++)
	{
		DInterval temp_int;
		if(intersection(left.get_dimension(i), right.get_dimension(i), temp_int))
		{
			dimensions.push_back(temp_int);
		}
		else
		{
			return Box();
		}
	}
	return Box(dimensions, left_vars);
}

Box BoxFactory::boxes_intersection(vector<Box> input)
{
	Box temp_box = input.at(0);
	for(int i = 1; i < input.size(); i++)
	{
		temp_box = BoxFactory::two_boxes_intersection(temp_box, input.at(i));
		if(temp_box.get_dimension_size() == 0)
		{
			return temp_box;
		}
	}
	return temp_box;
}

//for disjoint boxes only
vector<Box> BoxFactory::vectors_intersection(vector<Box> left, vector<Box> right)
{
	vector<Box> output;
	for(int i = 0; i < left.size(); i++)
	{
		for(int j = 0; j < right.size(); j++)
		{
			Box temp_box = BoxFactory::two_boxes_intersection(left.at(i), right.at(j));
			if(temp_box.get_dimension_size() != 0)
			{
				output.push_back(temp_box);
			}
		}
	}
	return output;
}
