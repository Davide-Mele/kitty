/* kitty: C++ truth table library
 * Copyright (C) 2017-2020  EPFL
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use,
 * copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following
 * conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
 * OTHER DEALINGS IN THE SOFTWARE.
 */

/*!
	\file threshold_identification.hpp
	\brief Threshold logic function identification

	\author CS-472 2020 Fall students
*/

#pragma once

#include <vector>
#include <lpsolve/lp_lib.h> /* uncomment this line to include lp_solve */
#include "traits.hpp"
#include "operations.hpp"
#include "isop.hpp"

namespace kitty
{

/*! \brief Threshold logic function identification

	Given a truth table, this function determines whether it is a threshold logic function (TF)
	and finds a linear form if it is. A Boolean function is a TF if it can be expressed as

	f(x_1, ..., x_n) = \sum_{i=1}^n w_i x_i >= T

	where w_i are the weight values and T is the threshold value.
	The linear form of a TF is the vector [w_1, ..., w_n; T].

	\param tt The truth table
	\param plf Pointer to a vector that will hold a linear form of tt if it is a TF.
			 The linear form has tt.num_vars() weight values and the threshold value
			 in the end.
	\return true if tt is a TF; false if tt is a non-TF.
*/
template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_threshold( const TT& tt, std::vector<int64_t>* plf = nullptr )
{
	TT tt2 = tt;
	std::vector<int64_t> inverted_variables;

	if ( !is_monotone_fix_negative_unate( tt2, &inverted_variables ) )
		return false;

	std::vector<cube> on_set = isop( tt2 );
	std::vector<cube> off_set = isop( unary_not( tt2 ) );

	if ( !lp_problem( tt2, on_set, off_set, plf, &inverted_variables ) )
		return false;

	return true;
}

template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool lp_problem( TT& tt, std::vector<cube> on_set, std::vector<cube> off_set, std::vector<int64_t>* plf, std::vector<int64_t>* inverted )
{
	lprec* lp;
	int num_column, *var_vector = NULL, j;
	REAL* weight_vector = NULL;

	num_column = tt.num_vars() + 1;
	const int T = num_column;

	// Start lp problem configurations
	lp = make_lp( 0, num_column );

	if ( lp == NULL )
		return false;

	var_vector = (int*)malloc( num_column * sizeof( *var_vector ) );
	weight_vector = (REAL*)malloc( num_column * sizeof( *weight_vector ) );

	if ( ( var_vector == NULL ) || ( weight_vector == NULL ) )
		return false;

	set_add_rowmode( lp, TRUE );

	/* Compute the constrains for each cube in the on_set */
	for ( cube c : on_set )
	{
		j = 0;
		for ( unsigned int i = 0; i < tt.num_vars(); i++ )
		{
			if ( c.get_mask( i ) ) //Check if the variable is in the cube
			{
				var_vector[j] = i + 1;
				weight_vector[j] = 1;
				j++;
			}
		}
		//Add T
		var_vector[j] = T; 
		weight_vector[j] = -1; 
		j++;
		// Finally add the constrain to the model
		add_constraintex( lp, j, weight_vector, var_vector, GE, 0 );
	}

	/* Compute the constrains for each cube in the on_set */
	for ( cube c : off_set )
	{
		j = 0;
		for ( unsigned int i = 0; i < tt.num_vars(); i++ )
		{
			if ( !c.get_mask( i ) ) //Check if the variable is NOT in the cube
			{
				var_vector[j] = i + 1;
				weight_vector[j] = 1;
				j++;
			}
		}
		//Add T
		var_vector[j] = T;
		weight_vector[j] = -1;
		j++;
		// Finally add the constrain to the model
		add_constraintex( lp, j, weight_vector, var_vector, LE, -1 );
	}

	set_add_rowmode( lp, FALSE );

	/* Set the objective function ad the sum of all weights + T */
	for ( int i = 0; i < num_column; i++ )
	{
		var_vector[i] = i + 1;
		weight_vector[i] = 1;
	}
	set_obj_fnex( lp, num_column, weight_vector, var_vector );

	/* Tell lp this is a minimization problem */
	set_minim( lp );
	set_verbose(lp,0);
	/* Do the trick */
	if ( solve( lp ) != OPTIMAL ) //This is not a Threshold function if LP doesn't give an optimal solution
		return false;

	/* Construct the linear form of f*
	   To do that, we have to invert the weight value of all negative unate variables in f and subtract that value to
	   the threshold value T. We keep a vector containing the index of the negative unate variables in f.
	*/
	get_variables( lp, weight_vector );
	int inverted_sum = 0;

	for ( j = 0; j < num_column; j++ )
	{
		if ( inverted->size() != 0 && inverted->at( 0 ) == j )
		{
			inverted_sum += weight_vector[j];
			weight_vector[j] = -weight_vector[j];
			inverted->erase( inverted->begin() );
		}

		if ( j == T - 1 )
			plf->push_back( weight_vector[j] - inverted_sum );
		else
			plf->push_back( weight_vector[j] );
	}

	if ( weight_vector != NULL )
		free( weight_vector );
	if ( var_vector != NULL )
		free( var_vector );

	if ( lp != NULL )
		delete_lp( lp );

	return true;
}

template<typename TT, typename = std::enable_if_t<is_complete_truth_table<TT>::value>>
bool is_monotone_fix_negative_unate( TT& tt, std::vector<int64_t>* inverted_variables )
{
	auto numvars = tt.num_vars();
	bool is_increasing = false;
	bool is_decreasing = false;

	for ( auto i = 0u; i < numvars; i++ )
	{
		is_increasing = false;
		is_decreasing = false;

		auto const tt1 = cofactor0( tt, i );
		auto const tt2 = cofactor1( tt, i );
		for ( auto bit = 0; bit < ( 2 << ( numvars - 1 ) ); bit++ )
		{
			if ( get_bit( tt1, bit ) < get_bit( tt2, bit ) )
				is_increasing = true;
			else if ( get_bit( tt1, bit ) > get_bit( tt2, bit ) )
				is_decreasing = true;
		}

		//Is binate
		if ( is_decreasing && is_increasing )
			return false;

		//Is negative unate
		if ( is_decreasing )
		{
			inverted_variables-> push_back( i ); 			//Keep track of the negative unate variable for the linear form transformation
			int sub_block_dimension = pow( 2, i );         //For each variable, the number of variable equals in the block
			int block_dimension = 2 * sub_block_dimension; //For each variable, the dimension of the block where it repeats

			for ( int k = sub_block_dimension; k < pow( 2, numvars ); k = k + block_dimension )
				for ( int j = 0; j < sub_block_dimension; j++ )
				{
					int actual_bit = k + j;
					int corresponding_bit = k + j - sub_block_dimension;

					if ( get_bit( tt, actual_bit ) != get_bit( tt, corresponding_bit ) )
					{
						flip_bit( tt, actual_bit );
						flip_bit( tt, corresponding_bit );
					}
				}
		}
	}
	return true;
}

} /* namespace kitty */