// Box class implements a generic n dimensional box
// where each dimension is a partial sum of a random variable
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#include<string>
#include<sstream>
#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include "Box.h"

using namespace std;
using namespace capd;

// Constructor of the class
//
// @param the dimensions of the box	
Box::Box(vector<DInterval> dimensions)
{
	this->dimensions = dimensions;
	if(dimensions.size() > 0)
	{
		calculate_params();
	}
	else
	{
		Box();
	}
	
}

Box::Box()
{
	
}

// Method for calculating parameters such as 
// box value and width of the shortest and
// the longest intervals
void Box::calculate_params()
{
	min_dimension = dimensions.at(0);
	max_dimension = min_dimension;
	volume = width(dimensions.at(0));
	for(int i = 1; i < dimensions.size(); i++)
	{
		if(width(min_dimension) >= width(dimensions.at(i)))
		{
			min_dimension = dimensions.at(i);
		}
		if(width(max_dimension) <= width(dimensions.at(i)))
		{
			max_dimension = dimensions.at(i);
		} 
		volume *= width(dimensions.at(i));
	}
}

// The method returns the dimension
// 
// @param dimension index
DInterval Box::get_dimension(int index)
{
	return dimensions.at(index);
}

// The method returns the box dimensions
vector<DInterval> Box::get_dimensions()
{
	return dimensions;
}

// The methods return the box value
DInterval Box::get_volume()
{
	return volume;
}

// The method returns the width of the shortest
// interval in the box dimensions
DInterval Box::get_min_dimension()
{
	return min_dimension;
}

// The method returns the width of the longest
// interval in the box dimensions
DInterval Box::get_max_dimension()
{
	return max_dimension;
}

// The method returns the number of dimensions
// in the box
int Box::get_dimension_size()
{
	return dimensions.size();
}
