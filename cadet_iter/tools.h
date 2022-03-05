/*
CADET Iteration Analyzer
BASED ON
Graph Features Computation for SAT instances.
Version 2.2
Authors:
  - Carlos Ansótegui (DIEI - UdL)
  - María Luisa Bonet (LSI - UPC)
  - Jesús Giráldez-Cru (IIIA-CSIC)
  - Jordi Levy (IIIA-CSIC)
  - Ziv Avissar (OpenU Israel) Added

Contact: jgiraldez@iiia.csic.es

    Copyright (C) 2014  C. Ansótegui, M.L. Bonet, J. Giráldez-Cru, J. Levy

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <math.h>
#include <vector>
#include <map>
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <string>
#include "graph_vector.h"

#ifndef TOOLS_H
#define TOOLS_H

using namespace std;

extern bool verbose;





//-----------------------------------------------------------------------------
double powlawc(int x, int xmin, double alpha) {
//-----------------------------------------------------------------------------
// Computes sum_{i=x}^{\infty} x^{alpha} / sum_{i=xmin}^{\infty} x^{alpha} 
// or approximates it as (x/xmin)^(alpha+1)
//-----------------------------------------------------------------------------
	assert(alpha < -1);
	assert(xmin <= x);
	#define MAXITER 10000
	double num = 0, den = 0;
	int i;
	
	if (xmin < 25) {
    
    for (i=xmin; i<x; i++)
		den += pow(i, alpha);
    
    double pold = -2, p = -1;
    int n = 0;
    
    while (abs(p - pold) > 0.00000001 && n < MAXITER) {
		den += pow((double)i, alpha);
		num += pow((double)i, alpha);
		i++;
		n++;
		pold = p;
		p = num/den;
    }
    if (n < MAXITER)
		return p;
	}
	return pow((double)x/xmin, alpha + 1);
}


bool binary_search_find_index(vector<int> v, int data, int * index=nullptr) {
    auto it = lower_bound(v.begin(), v.end(), data);
	if (nullptr != index)
		*index = distance(v.begin(), it);
    return (it!=v.end() && !(data<*it));
}

//-----------------------------------------------------------------------------
double exponc(int x, int xmin, double beta) {
//-----------------------------------------------------------------------------
	return exp(beta*(xmin - x)) ;
}


//-----------------------------------------------------------------------------
double mostlikely(vector <pair <int,int> > v, int maxxmin, bool var) {
//-----------------------------------------------------------------------------

  //---- Compute vectors x, y, sxy, sylogx ------------------

	int n=v.size();
	vector <double> x(n), y(n+1), syx(n+1), sylogx(n+1);

	double Sy = 0;
	for (int i=0; i<n; i++) Sy += v[i].second;

	syx[n] = 0;
	sylogx[n] = 0;
	y[n] = 0;
	for(int i=n-1; i>=0; i--) {
		x[i]      = v[i].first;
		y[i]      = y[i+1] + v[i].second / Sy;
		sylogx[i] = sylogx[i+1] + v[i].second / Sy * log(x[i]);
		syx[i]    = syx[i+1] + v[i].second / Sy *     x[i];
    }

  //------ Compute, for powerlaw (a) and exponential (b), 
  //       the best alpha, xmin, dif and where is located--------------------

	double bestalpha, bestbeta;
	int bestxmina=0, bestxminb=0;
	double bestdifa = 1, bestdifb = 1;
	int bestinda, bestindb;
	int wherea, whereb;
	int ind = 0;
	int xmin;

	for (int ind=1; ind<=maxxmin && ind<n-3; ind++) {
		xmin = (int)x[ind];
    
		double alpha = -1 - 1 / (sylogx[ind] / y[ind] - log((double)xmin - 0.5));
		double beta = log(1 / (syx[ind] / y[ind] - xmin) + 1);

    //------------- Model powerlaw -----------------------------------------

		double worstdif = -1;
		int worstx = -1;
    
		for (int j=ind+1; j<n; j++) {
			double aux;
			aux = abs((double)y[j]/y[ind] - powlawc((int)x[j],xmin,alpha));
			if (aux >= bestdifa) {
				worstdif = aux;
				worstx = (int)x[j]; 
				j = n;  //Finish search of worst diff
			} else if (aux >= worstdif) {
				worstdif = aux;
				worstx = (int)x[j];
			}
		}
		for (int j=ind; j<n; j++) {
			if (x[j] + 1 < x[j+1]) {
				double aux;
				aux = abs((double)y[j+1]/y[ind] - powlawc((int)x[j]+1,xmin,alpha));
				if (aux >= bestdifa) {
					worstdif = aux;
					worstx = (int)x[j]+1; 
					j = n;  //Finish search of worst diff
				} else if (aux >= worstdif) {
					worstdif = aux;
					worstx = (int)x[j]+1;
				}
			}
		}
		if(worstdif < bestdifa) { 
			bestalpha = alpha; 
			bestxmina = xmin;
			bestdifa = worstdif;
			bestinda = ind;
			wherea = worstx;
		}	
		
		//------------- Model exponential -----------------------------------------
		worstdif = -1;
		worstx = -1;

		for (int j=ind+1; j<n; j++) {
			double aux;
			aux = abs((double)y[j]/y[ind] - exponc(x[j],xmin,beta));
			if (aux >= bestdifb) {
				worstdif = aux;
				worstx = x[j]; 
				j = n;  //Finish search of worst diff
			} else if (aux >= worstdif) {
				worstdif = aux;
				worstx = x[j];
			}
		}
		for (int j=ind; j<n; j++) {
			if (x[j] + 1 < x[j+1]) {
				double aux;
				aux = abs((double)y[j+1]/y[ind] - exponc(x[j]+1,xmin,beta));
				if (aux >= bestdifb) {
					worstdif = aux;
					worstx = x[j]+1; 
					j = n;  //Finish search of worst diff
				} else if (aux >= worstdif) {
					worstdif = aux;
					worstx = x[j]+1;
				}
			}
		}
		if(worstdif < bestdifb) { 
			bestbeta = beta;
			bestxminb = xmin;
			bestdifb = worstdif;
			bestindb = ind;
			whereb = worstx;
		}
	}
	cout << ", " << -bestalpha;
	cout << ", " << bestbeta;

return -bestalpha;
}

//-----------------------------------------------------------------------------
pair <double,double> regresion(vector <pair <double,double> > &v) {
//-----------------------------------------------------------------------------
//Given a vector of points, computes the alpha and beta of a regression
//-----------------------------------------------------------------------------
	double Sx = 0, Sy = 0, Sxx = 0, Syy = 0, Sxy = 0;
	for (vector<pair <double,double> >::iterator it=v.begin(); it != v.end(); it++) {
		double x = it->first;
		double y = it->second;
		Sx += x;
		Sy += y;
		Sxx += x * x;
		Syy += y * y;
		Sxy += x * y;
	}
	
	double alpha = (Sx * Sy - v.size() * Sxy)/( Sx * Sx - v.size() * Sxx);
	double beta = Sy / v.size() - alpha * Sx / v.size();
	return pair <double,double>(alpha,beta);
}

#endif
