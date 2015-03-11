// DecisionProcedure class implements a decision procedure 
// using dReach tool
//
// @author: Fedor Shmarov
// @e-mail: f.shmarov@ncl.ac.uk
#ifndef DECISIONPROCEDURE_H 
#define DECISIONPROCEDURE_H  

#include<capd/capdlib.h>
#include<capd/intervals/lib.h>
#include<string>
#include "Box.h"

using namespace std;

// DecisionProcedure class declaration
class DecisionProcedure
{
	private:

		// The method gets a name of the file as a parameter and returns
		// true  if the file exists and false otherwise
		static bool file_exists(const char*);

		// The method gets a full path to the DRH model and a precision
		// which are then used to call dReach. The method returns true
		// if dReach returns "sat" and false if dReach returns "unsat".
		//
		// @param DRH filename, precision used by dReach for verifying
		// the model
		static bool call_dreal(string, string, string);

		// The method removes auxiliary file
		//
		// @param filename base
		static void remove_aux_file(string);

	public:
		
		// The methods gets an arbitrary Box as an input parameter
		// and return 1 if the indicator function over this box equals 1,
		// -1 if indicator function equals to 0 and 0 if the box contains
		// both values where the indicator function takes both values
		//
		// @param box from the domain of random variables. 
		static int evaluate(vector<string>, string, string);

};
#endif 