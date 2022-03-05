/*
Manthan Iteration Analyzer
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
#define SYNTACTIC_UNATES_LINE ("c unates --")
#define SEMANTIC_UNATES_LINE ("unates ")
#define CANDIDATE_LINE ("c candidate skf for ")
#define CANDIDATE_LINE_WORDS (4)
#define OR_LINE ("c or of all the paths")
#define PATH_LINE ("c path: and of varibles listed below:")
#define REFINE_LINE ("c refine for ")
#define REFINE_LINE_WORDS (3)
using namespace std;

char *fin = NULL;

int minx = 0;
int maxx = 15;
int maxx2 = 6;
int maxxmin = 10;
double precision = 0.000001;

bool found_candidate = false, found_repr = false, need_repr = false, found_unate = false, need_unate = false;

void printUsage(char * name){
	cout << "USAGE: " << name << " <instance.qdimacs> <instance_manthan_log.txt>" << endl;
	exit(-1);
}

void create_graphs(vector<vector<int> > in_clauses, vector<vector<int> > clauses, Graph &concensus, Graph &vig, Graph &cvig, int totVars){
	bool agree = false;
	int curr_var = 0;

	vig = Graph(totVars, 0);
	cvig = Graph(totVars,clauses.size());
	concensus = Graph(in_clauses.size(), 0);

	for (vector<vector<int> >::iterator cl = clauses.begin(); cl != clauses.end(); ++cl){
		double weight_vig = 0;
		double weight_cvig = 1.0/cl->size();
		if(cl->size()>1){
			weight_vig = 2.0 / (cl->size() * (cl->size()-1) );
			for (int i=0; i<cl->size()-1; i++){
				cvig.add_edge((*cl)[i], totVars+distance(clauses.begin(), cl), weight_cvig);
				for (int j=i+1; j<cl->size(); j++){
					vig.add_edge((*cl)[i], (*cl)[j], weight_vig);
				}
			}
			cvig.add_edge((*cl)[cl->size()-1], totVars+distance(clauses.begin(), cl), weight_cvig);
		}else if(cl->size()==1){
			cvig.add_edge((*cl)[0], totVars+distance(clauses.begin(), cl), weight_cvig);	
		}
	}
	for (vector<vector<int> >::iterator c_oit = in_clauses.begin(); c_oit != in_clauses.end(); ++c_oit){
		for (vector<vector<int> >::iterator c_iit = c_oit+1; c_iit != in_clauses.end(); ++c_iit){
			agree = true;
			for (vector<int>::iterator v_it = (*c_oit).begin(); v_it != (*c_oit).end(); ++v_it){
				if (binary_search_find_index (*c_iit, -1*(*v_it), &curr_var)){
					agree = false;
					break;
				}
			}
			if (agree){
				concensus.add_edge(distance(in_clauses.begin(), c_oit), distance(in_clauses.begin(), c_iit), 1.0);
			}
		}
	}
}

bool get_iter_from_log(ifstream& log_in, vector<vector<int> >& init_clauses, vector<vector<vector<int> > >& var_representations, vector<int> in_vars, Graph &concensus, Graph &vig, Graph &cvig, int totVars){
	bool agree = false, found_change = false, new_in_clause_now = false, new_in_clause_at_all = false, new_clause_tautology = false;
	char aux = 0;
	string line, word;
	int curr_var = 0, new_info_var = 0, i = 0, num_curr_clauses = 0, num_curr_in_clauses = 0, num_del_clauses = 0, num_del_in_clauses = 0;
	vector<int> clause, in_clause, temp_clause, temp_in_clause;
	vector<vector<int> > built_clauses, built_clauses_temp, built_in_clauses, built_in_clauses_temp;

	/* get new info */
	if (log_in.peek()==EOF){
		return false;
	}
	while (getline(log_in, line)) {
		istringstream in (line);
		if (line.size() == 0){
			found_candidate = false; need_repr = false; need_unate = false;
			if (found_repr || found_unate){
				found_repr = false; found_unate = false; found_change = true;
				break;
			} else {
				found_change = false;
				continue;
			}
		} //else {
			// cout << line << endl;
		//}
		if (line.find(SYNTACTIC_UNATES_LINE) == 0){
			need_unate = true;
			continue;
		} else if (line.find(SEMANTIC_UNATES_LINE) == 0){
			continue;
		} else if (line.find(CANDIDATE_LINE) == 0){
			found_candidate = true;
			for (i = 0; i < CANDIDATE_LINE_WORDS; ++i) { in >> word;}
			in >> new_info_var;
			continue;
		} else if ((line.find(OR_LINE) == 0) && found_candidate){
			need_repr = true;
			continue;
		} else if ((line.find(PATH_LINE) == 0) && need_repr){
			need_repr = true;
			continue;
		} else if (line.find(REFINE_LINE) == 0){
			need_repr = true;
			for (i = 0; i < REFINE_LINE_WORDS; ++i) { in >> word;}
			in >> new_info_var;
			continue;
		} else if (need_unate){
			found_unate = true;
			in >> new_info_var;
			found_change = true;
			break;
		} else if (need_repr){
			found_repr = true;
			found_change = true;
			clause.clear();
			while (in >> curr_var){
				clause.push_back(curr_var);
			}
			var_representations[abs(new_info_var)-1].push_back(clause);
			if (!found_candidate){
				break;
			} else {
				continue;
			}
		} else {
			continue;
		}
	}

	/* do something with new info, if there is need to */
	if (found_unate){
		found_change = true; found_unate = false; need_unate = false;
		for (vector<vector<int> >::iterator c_it = init_clauses.begin(); c_it != init_clauses.end(); ++c_it){
			for(vector<int>::iterator v_it = (*c_it).begin(); v_it != (*c_it).end(); ++v_it){
				if (*v_it == new_info_var){
					init_clauses.erase(c_it--);
					break;
				} else if (*v_it == 0 - new_info_var) {
					(*c_it).erase(v_it--);
					break;
				}
			}
		}
	}

	/* build clauses from new info */
	clause.clear(); in_clause.clear();
	for (vector<vector<int> >::iterator c_it = init_clauses.begin(); c_it != init_clauses.end(); ++c_it){
		/* every initial clause */
		for(vector<int>::iterator v_it = (*c_it).begin(); v_it != (*c_it).end(); ++v_it){
			/* every var of initial clause */
			clause.clear(); in_clause.clear(); i = 0;
			num_curr_clauses = built_clauses_temp.size();
			num_curr_in_clauses = built_in_clauses_temp.size();
			num_del_in_clauses = num_del_clauses = 0;
			if (num_curr_clauses == 0 && num_curr_in_clauses == 0){
				/* first var of initial clause */
				if (var_representations[abs(*v_it)-1].size() == 0){
					clause.push_back(abs(*v_it)-1);
					if (binary_search_find_index (in_vars, abs(*v_it))){
						in_clause.push_back(*v_it);
					}
					built_clauses_temp.push_back(clause);
					built_in_clauses_temp.push_back(in_clause);
				} else {
					for (vector<vector<int> >::iterator r_it = var_representations[abs(*v_it)-1].begin(); r_it != var_representations[abs(*v_it)-1].end(); ++r_it){
						for(vector<int>::iterator rv_it = (*r_it).begin(); rv_it != (*r_it).end(); ++rv_it){
							clause.push_back(abs(*rv_it)-1);
							if (binary_search_find_index(in_vars, abs(*rv_it))){
								in_clause.push_back(*rv_it);
							}
						}
						built_clauses_temp.push_back(clause);
						built_in_clauses_temp.push_back(in_clause);
					}
				}
			} else {
				/* second var etc... */
				for (vector<vector<int> >::iterator b_it = built_clauses_temp.begin(); i < num_curr_clauses; ++i, ++b_it){
					/* every thus far built clause */
					if (var_representations[abs(*v_it)-1].size() == 0){
						(*b_it).push_back(abs(*v_it)-1);
					} else {
						temp_clause.clear();
						for(vector<int>::iterator bv_it = (*b_it).begin(); bv_it != (*b_it).end(); ++bv_it){
							temp_clause.push_back(*bv_it);
						}
						sort(temp_clause.begin(), temp_clause.end());
						for (vector<vector<int> >::iterator r_it = var_representations[abs(*v_it)-1].begin(); r_it != var_representations[abs(*v_it)-1].end(); ++r_it){
							new_clause_tautology = false;
							for(vector<int>::iterator tc_it = temp_clause.begin(); tc_it != temp_clause.end(); ++tc_it){
								clause.push_back(*tc_it);
							}
							for(vector<int>::iterator rv_it = (*r_it).begin(); rv_it != (*r_it).end(); ++rv_it){
								if (binary_search_find_index(temp_clause, -1*(*rv_it))){
									new_clause_tautology = true;
									break;
								} else if (binary_search_find_index(temp_clause, (*rv_it))){
									continue;
								}
								clause.push_back(abs(*rv_it)-1);
							}
							if (!new_clause_tautology){
								built_clauses_temp.push_back(clause);
							}
							clause.clear();
						}
						num_del_clauses++;
					}
				}
				i = 0;  in_clause.clear();
				for (vector<vector<int> >::iterator bi_it = built_in_clauses_temp.begin(); i < num_curr_in_clauses; ++i, ++bi_it){
					/* every thus far built in clause */
					new_in_clause_at_all = false;
					if (var_representations[abs(*v_it)-1].size() == 0 && binary_search_find_index (in_vars, abs(*v_it))){
						(*bi_it).push_back(*v_it);
					} else if (var_representations[abs(*v_it)-1].size() != 0) {
						for(vector<int>::iterator bvi_it = (*bi_it).begin(); bvi_it != (*bi_it).end(); ++bvi_it){
							temp_in_clause.push_back(*bvi_it);
						}
						sort(temp_in_clause.begin(), temp_in_clause.end());
						for (vector<vector<int> >::iterator r_it = var_representations[abs(*v_it)-1].begin(); r_it != var_representations[abs(*v_it)-1].end(); ++r_it){
							new_clause_tautology = false; new_in_clause_now = false; in_clause.clear();
							for(vector<int>::iterator tc_it = temp_in_clause.begin(); tc_it != temp_in_clause.end(); ++tc_it){
								in_clause.push_back(*tc_it);
							}
							for(vector<int>::iterator rv_it = (*r_it).begin(); rv_it != (*r_it).end(); ++rv_it){
								if (binary_search_find_index(in_vars, abs(*rv_it))){
									new_in_clause_now = true; new_in_clause_at_all = true;
									if (binary_search_find_index(temp_in_clause, -1*(*rv_it))){
										new_clause_tautology = true;
										break;
									} else if (binary_search_find_index(temp_in_clause, (*rv_it))){
										continue;
									}
									in_clause.push_back((*v_it > 0 ? *rv_it : -1*(*rv_it)));
								}
							}
							if (new_in_clause_now && !new_clause_tautology){
								built_in_clauses_temp.push_back(in_clause);
							}
						}
						if (new_in_clause_at_all){
							num_del_in_clauses++;
						}
					}
				}
			}
		}
		for (vector<vector<int> >::iterator b_it = built_clauses_temp.begin() + num_del_clauses; b_it != built_clauses_temp.end(); ++b_it){
			built_clauses.push_back(std::move(*b_it));
		}
		for (vector<vector<int> >::iterator bi_it = built_in_clauses_temp.begin() + num_del_in_clauses; bi_it != built_in_clauses_temp.end(); ++bi_it){
			built_in_clauses.push_back(std::move(*bi_it));
		}
		built_clauses_temp.clear(); built_in_clauses_temp.clear();
	}
	create_graphs(built_in_clauses, built_clauses, concensus, vig, cvig, totVars);
	
l_cleanup:
	built_clauses.clear();
	built_in_clauses.clear();
	return found_change;
}

int main(int argc, char *argv[]){
	std::ifstream log_in;
	FILE *source;
	double modularity=-1, modularity_bip=-1;
	pair <double,double> polreg = make_pair(-1,-1), polregB = make_pair(-1,-1);
	vector <pair <double,double> > v1;
	int nclauses=0, ninclauses=0, var = -1, iter_counter = 0, totVars=0, totClauses=0, curr_var = 0, aux=-1;
	vector<int> clause, clause_init, in_clause, in_vars, needed;
	vector<vector<int> > in_clauses, all_clauses, all_clauses_initial;
	vector<vector<vector<int> > > variable_representations;
	bool have_more_iters = false, saw_in = false, saw_out = false;
	Graph vig, cvig, concensus;

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
	variable_representations.resize(totVars);

	switch(aux=getc(source)){
		case 'a':
			if(saw_in){
				cerr << "More than one Forall line or Exists line!\n";
				break;
			}
			saw_in = true;
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
			saw_out = true;
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
			saw_in = true;
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
			saw_out = true;
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
	
	// Read the clauses
	while(fscanf(source, "%i", &var)==1) {
		if (var==0) {
			if (clause.size()>0) {
				if (in_clause.size()>0) {
					ninclauses++;
					sort(in_clause.begin(), in_clause.end());
					in_clauses.push_back(in_clause);
				}
				nclauses++;
				sort(clause.begin(), clause.end());
				sort(clause_init.begin(), clause_init.end());
				all_clauses.push_back(clause);
				all_clauses_initial.push_back(clause_init);
			}
			clause.clear();
			clause_init.clear();
			in_clause.clear();
		} else {
			if (abs(var) > totVars) {
				cerr << "Invalid variable number " << abs(var) << endl;
				exit(-1);
			}
			clause_init.push_back(var);
			clause.push_back(abs(var)-1);
			if (binary_search_find_index (in_vars, abs(var), &curr_var)){
				in_clause.push_back(var);
			}
		}
	}
	fclose(source);
	
	log_in.open(argv[2], std::ifstream::in);
	if (!log_in){
		cerr << "Unable to read log file " << argv[2] << endl;
		exit(-1);
	}
	clause.clear(); in_clause.clear();
	cout << "ITERATION, VIG_SELF_SIMILAR_DIM, CVIG_SELF_SIMILAR_DIM, CONSENSUS_SELF_SIMILAR_DIM, VIG_MODULARITY,CVIG_MODULARITY, CONSENSUS_MODULARITY" << endl;
	
	create_graphs(in_clauses, all_clauses, concensus, vig, cvig, totVars);
	all_clauses.clear();
	in_clauses.clear();
	do {
		cout << iter_counter;
		Community c(&vig);
		Community con(&concensus);
		Community c_bip(&cvig);
		v1.clear();
		needed = computeNeeded(&vig);
		for(int i=1; i<needed.size(); i++){
			if(i>=minx && i<=maxx2){
				v1.push_back(pair<double,double>(log(i), log(needed[i])));
			}
		}
		polreg = regresion(v1);
		cout << ", " << -polreg.first;
		v1.clear();
		needed = computeNeeded(&cvig);
		for(int i=1; i<needed.size(); i++){
			if(i>=minx && i<=maxx2){
				v1.push_back(pair<double,double>(log(i), log(needed[i])));	
			}
		}
		polregB = regresion(v1);
		cout << ", " << -polregB.first;
		v1.clear();
		needed = computeNeeded(&concensus);
		for(int i=1; i<needed.size(); i++){
			if(i>=minx && i<=maxx2){
				v1.push_back(pair<double,double>(log(i), log(needed[i])));
			}
		}
		polreg = regresion(v1);
		cout << ", " << -polreg.first;
		modularity = c.compute_modularity_GFA(precision);
		cout << ", " << modularity;
		modularity_bip = c_bip.compute_modularity_GFA(precision);
		cout << ", " << modularity_bip;
		modularity = con.compute_modularity_GFA(precision);
		cout << ", " << modularity << endl;
		iter_counter++;
		have_more_iters = get_iter_from_log(log_in, all_clauses_initial, variable_representations, in_vars, concensus, vig, cvig, totVars);
	} while (have_more_iters);
}

#endif
