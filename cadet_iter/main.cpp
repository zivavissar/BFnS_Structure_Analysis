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
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <vector>
#include "graph_vector.h"
#include "tools.h"
#include "dimension.h"
#include "community.h"
#include <iostream>
#include <fstream>
#include <sstream>
#include <string>
#include <algorithm>

int abs(int x){
	if(x<0)
		return -x;
	else
		return x;
}

#ifndef MAIN_H
#define MAIN_H

#define ARGC (3)
using namespace std;

char *fin = NULL;

bool modeAll = true;
bool modeAlphaVar = false;
bool modeAlphaClause = false;
bool modeDimVIG = false;
bool modeDimCVIG = false;
bool modeModularityVIG = false;
bool modeModularityCVIG = false;

int minx = 0;
int maxx = 15;
int maxx2 = 6;
int maxxmin = 10;
double precision = 0.000001;

void printUsage(char * name){
	cout << "USAGE: " << name << " <instance.qdimacs> <instance_cadet_log.txt>" << endl;
	exit(-1);
}

pair <vector<int>, vector<int> > get_new_clause_from_log(FILE *log_in, int num_vars, vector<int> in_vars){
	int curr_var = 0;
	int aux = -1;
	vector<int> clause, in_clause;

	while ('\n' != (aux = getc(log_in))){
		ungetc(aux,log_in);
		if(fscanf(log_in, "%i", &curr_var)==1){
			clause.push_back(abs(curr_var) - 1);
			if (binary_search_find_index (in_vars, abs(curr_var))){
				in_clause.push_back(curr_var);
			}
		} else {
			break;
		}
	}
	return make_pair(clause, in_clause);
}

int main(int argc, char *argv[]){
	Graph* vig = NULL;
	Graph* cvig = NULL;
	Graph* concensus = NULL;
	double alphavarexp=-1;
	double alphaclauexp=-1;
	double modularity=-1;
	double modularity_bip=-1;
	vector<int> needed;
	vector <pair <double,double> > v1;
	vector <pair <double,double> > v2;
	pair <double,double> polreg = make_pair(-1,-1);
	pair <double,double> expreg = make_pair(-1,-1);
	pair <double,double> polregB = make_pair(-1,-1);
	pair <double,double> expregB = make_pair(-1,-1);
	FILE *source;
	int nclauses=0;
	int ninclauses=0;
	vector<pair <int,int> > arityVar;
	vector<pair <int,int> > arityClause;
	int var = -1;
	int prev = 0;
	int addition = 1;
	int iter_counter = 0;
	vector<int> nOccurs_clause(100,0);
	pair <vector<int>, vector<int> > new_clauses;
	int totVars=0, totClauses=0;
	int curr_var = 0;
	int aux=-1;
	vector<vector<int> > in_clauses;
	vector<int> clause;
	vector<int> in_clause;
	vector<int> in_vars;
	int saw_in = 0;
	int saw_out = 0;
	int agree = 0;

	if (ARGC != argc){
		printUsage(argv[0]);
		exit(-1);
	}
	source = fopen(argv[1], "r");
	if(!source){
		cerr << "Unable to read CNF file " << argv[1] << endl;
		exit(-1);
	}

	// Skip comments
	while((aux=getc(source))=='c'){
		while (getc(source)!='\n');
	}
	ungetc(aux,source);

	// File Head
	if( !fscanf(source, "p cnf %i %i\n", &totVars, &totClauses)) {
		cerr << "Invalid CNF file\n";
		exit(-1);
	}
	
	vector<int> nOccurs_vars(totVars,0);

	switch(aux=getc(source)){
		case 'a':
			if(saw_in){
				cerr << "More than one Forall line or Exists line!\n";
				break;
			}
			saw_in = 1;
			while(fscanf(source, "%d", &curr_var)==1) {
				if (curr_var==0) {
					getc(source);
					if (in_vars.size()>1) {
						sort (in_vars.begin(), in_vars.end());
					} else {
						cerr << "No Forall variables!\n";
						break;
					}
				} else {
					if (abs(curr_var) > totVars) {
						cerr << "Unvalid variable number " << abs(curr_var) << endl;
						exit(-1);
					}
					in_vars.push_back(abs(curr_var));
				}
			}
			break;
		case 'e':
			if(saw_out){
				cerr << "More than one Forall line or Exists line!\n";
				break;
			}
			saw_out = 1;
			while (getc(source)!='\n');
			break;
		default:
			ungetc(aux,source);
			cerr << aux << "\n";
			cerr << "No Forall line or no Exists line!\n";
			break;
	}
	switch(aux=getc(source)){
		case 'a':
			if(saw_in){
				cerr << "More than one Forall line or Exists line!\n";
				break;
			}
			saw_in = 1;
			while(fscanf(source, "%d", &curr_var)==1) {
				if (curr_var==0) {
					getc(source);
					if (in_vars.size()>1) {
						sort (in_vars.begin(), in_vars.end());
					} else {
						cerr << "No Forall variables!\n";
						break;
					}
				} else {
					if (abs(curr_var) > totVars) {
						cerr << "Unvalid variable number " << abs(curr_var) << endl;
						exit(-1);
					}
					in_vars.push_back(abs(curr_var));
				}
			}
			break;
		case 'e':
			if(saw_out){
				cerr << "More than one Forall line or Exists line!\n";
				break;
			}
			saw_out = 1;
			while (getc(source)!='\n');
			break;
		default:
			ungetc(aux,source);
			// cerr << aux << "\n";
			cerr << "No Forall line or no Exists line!\n";
			break;
	}

	if(!saw_out || !saw_in){
		cerr << "No Forall line or no Exists line!\n";
	}

	vig = new Graph(totVars, 0);
	cvig = new Graph(totVars,totClauses);
	
	// Read the clauses
	while(fscanf(source, "%i", &var)==1) {
		if (var==0) {
			if (clause.size()>0) {
				if(clause.size()>=nOccurs_clause.size())
					nOccurs_clause.resize(clause.size()+1);
				nOccurs_clause[clause.size()]++;
				double weight_vig = 0;
				double weight_cvig = 1.0/clause.size();
				if(clause.size()>1){
					weight_vig = 2.0 / (clause.size() * (clause.size()-1) );
					for (int i=0; i<clause.size()-1; i++){
						cvig->add_edge(clause[i], totVars+nclauses, weight_cvig);
						for (int j=i+1; j<clause.size(); j++){
							vig->add_edge(clause[i], clause[j], weight_vig);
						}
					}
					cvig->add_edge(clause[clause.size()-1], totVars+nclauses, weight_cvig);
				}else if(clause.size()==1){
					cvig->add_edge(clause[0], totVars+nclauses, weight_cvig);	
				}
				if (in_clause.size()>0) {
					ninclauses++;
					sort(in_clause.begin(), in_clause.end());
					in_clauses.push_back(in_clause);
				}
			}
			nclauses++;
			clause.clear();
			in_clause.clear();
		} else {
			if (abs(var) > totVars) {
				cerr << "Unvalid variable number " << abs(var) << endl;
				exit(-1);
			}
			nOccurs_vars[abs(var)-1]++;
			clause.push_back(abs(var)-1);
			if (binary_search_find_index (in_vars, abs(var), &curr_var)){
				in_clause.push_back(var);
			}
		}
	}

	sort(nOccurs_vars.begin(), nOccurs_vars.end());	
	prev = nOccurs_vars[0];
	for (int i=1; i<nOccurs_vars.size(); i++) {
		if (nOccurs_vars[i] == prev)
			addition++;
		else {
			arityVar.push_back(make_pair(prev,addition));
			prev = nOccurs_vars[i];
			addition = 1;
		}
	}
	arityVar.push_back(make_pair(prev,addition));
	
	for(int i=1; i<nOccurs_clause.size(); i++){
		if(nOccurs_clause[i]>0){
			arityClause.push_back(make_pair(i,nOccurs_clause[i]));
		}
	}

	concensus = new Graph(ninclauses, 0);
	for (vector<vector<int> >::iterator c_oit = in_clauses.begin(); c_oit != in_clauses.end(); ++c_oit){
		for (vector<vector<int> >::iterator c_iit = c_oit+1; c_iit != in_clauses.end(); ++c_iit){
			agree = 1;
			for (vector<int>::iterator v_it = (*c_oit).begin(); v_it != (*c_oit).end(); ++v_it){
				if (binary_search_find_index (*c_iit, -1*(*v_it), &curr_var)){
					agree = 0;
					break;
				}
			}
			if (agree){
				concensus->add_edge(distance(in_clauses.begin(), c_oit), distance(in_clauses.begin(), c_iit), 1.0);
			}
		}
	}
	//end readformula and powerlaw
	fclose(source);
	source = fopen(argv[2], "r");
	if(!source){
		cerr << "Unable to read log file " << argv[2] << endl;
		exit(-1);
	}
	clause.clear();
	in_clause.clear();
	cout << "ITERATION, VIG_SCALEFREE_ALPHA, VIG_SCALEFREE_BETA, CVIG_SCALEFREE_ALPHA, CVIG_SCALEFREE_BETA, VIG_SELF_SIMILAR_DIM, VIG_SELF_SIMILAR_DECAY, CVIG_SELF_SIMILAR_DIM, CVIG_SELF_SIMILAR_DECAY, CONSENSUS_SELF_SIMILAR_DIM, CONSENSUS_SELF_SIMILAR_DECAY, VIG_MODULARITY, VIG_COMMUNITIES, CVIG_MODULARITY, CVIG_COMMUNITIES, CONSENSUS_MODULARITY, CONSENSUS_COMMUNITIES" << endl;
	
	do {
		cout << iter_counter;
		if (clause.size()>0) {
			if(clause.size()>=nOccurs_clause.size())
				nOccurs_clause.resize(clause.size()+1);
			nOccurs_clause[clause.size()]++;
			double weight_vig = 0;
			double weight_cvig = 1.0/clause.size();
			cvig->add_node();
			if(clause.size()>1){
				weight_vig = 2.0 / (clause.size() * (clause.size()-1) );
				for (int i=0; i<clause.size()-1; i++){
					cvig->add_edge(clause[i], totVars+nclauses-1, weight_cvig);
					for (int j=i+1; j<clause.size(); j++){
						vig->add_edge(clause[i], clause[j], weight_vig);
					}
				}
				cvig->add_edge(clause[clause.size()-1], totVars+nclauses-1, weight_cvig);
			}else if(clause.size()==1){
				cvig->add_edge(clause[0], totVars+nclauses-1, weight_cvig);
			}
			if (in_clause.size()>0) {
				ninclauses++;
				sort(in_clause.begin(), in_clause.end());
				in_clauses.push_back(in_clause);
				concensus->add_node(false);
				//henceforth consensus handling
				for (vector<vector<int> >::iterator c_oit = in_clauses.begin(); c_oit != in_clauses.end(); ++c_oit){
					agree = 1;
					for (vector<int>::iterator v_it = (*c_oit).begin(); v_it != (*c_oit).end(); ++v_it){
						if (binary_search_find_index (in_clause, -1*(*v_it), &curr_var)){
							agree = 0;
							break;
						}
					}
					if (agree){
						concensus->add_edge(distance(in_clauses.begin(), c_oit), ninclauses-1, 1.0);
					}
				}
			}
			nclauses++;

			clause.clear();
			in_clause.clear();
			arityVar.clear();
			arityClause.clear();

			sort(nOccurs_vars.begin(), nOccurs_vars.end());	
			prev = nOccurs_vars[0];
			for (int i=1; i<nOccurs_vars.size(); i++) {
				if (nOccurs_vars[i] == prev)
					addition++;
				else {
					arityVar.push_back(make_pair(prev,addition));
					prev = nOccurs_vars[i];
					addition = 1;
				}
			}
			arityVar.push_back(make_pair(prev,addition));			
			for(int i=1; i<nOccurs_clause.size(); i++){
				if(nOccurs_clause[i]>0){
					arityClause.push_back(make_pair(i,nOccurs_clause[i]));
				}
			}
		}
		Community c(vig);
		Community con(concensus);
		Community c_bip(cvig);
		alphavarexp = mostlikely(arityVar, maxxmin, true);
		alphaclauexp = mostlikely(arityClause, maxxmin, false);
		v1.clear(); v2.clear();
		needed = computeNeeded(vig);
		for(int i=1; i<needed.size(); i++){
			if(i>=minx && i<=maxx2){
				v1.push_back(pair<double,double>(log(i), log(needed[i])));
				v2.push_back(pair<double,double>((double)i, log(needed[i])));	
			}
		}
		polreg = regresion(v1);
		expreg = regresion(v2);
		cout << ", " << -polreg.first;
		cout << ", " << -expreg.first;
		v1.clear(); v2.clear();
		needed = computeNeeded(cvig);
		for(int i=1; i<needed.size(); i++){
			if(i>=minx && i<=maxx2){
				v1.push_back(pair<double,double>(log(i), log(needed[i])));
				v2.push_back(pair<double,double>((double)i, log(needed[i])));	
			}
		}
		polregB = regresion(v1);
		expregB = regresion(v2);
		cout << ", " << -polregB.first;
		cout << ", " << -expregB.first;
		v1.clear(); v2.clear();
		needed = computeNeeded(concensus);
		for(int i=1; i<needed.size(); i++){
			if(i>=minx && i<=maxx2){
				v1.push_back(pair<double,double>(log(i), log(needed[i])));
				v2.push_back(pair<double,double>((double)i, log(needed[i])));	
			}
		}
		polreg = regresion(v1);
		expreg = regresion(v2);
		cout << ", " << -polreg.first;
		cout << ", " << -expreg.first;
		modularity = c.compute_modularity_GFA(precision);
		c.compute_communities();
		cout << ", " << modularity;
		cout << ", " << (int)c.ncomm;
		modularity_bip = c_bip.compute_modularity_GFA(precision);
		c_bip.compute_communities();
		cout << ", " << modularity_bip;
		cout << ", " << (int)c_bip.ncomm;
		modularity = con.compute_modularity_GFA(precision);
		con.compute_communities();
		cout << ", " << modularity;
		cout << ", " << (int)con.ncomm << endl;
		iter_counter++;
		new_clauses = get_new_clause_from_log(source, totVars, in_vars);
		clause = new_clauses.first;
		in_clause = new_clauses.second;
	} while (clause.size() != 0);
	fclose(source);
}

#endif
