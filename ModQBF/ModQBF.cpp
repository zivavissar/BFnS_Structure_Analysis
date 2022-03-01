/*
Modularity-based BFnS Generator.
Version 1.0
Authors:
	- Jesús Giráldez-Cru (IIIA-CSIC)
	- Jordi Levy (IIIA-CSIC)
	- Ziv Avissar (OpenU-Israel)

Contact: zavissar@openu.ac.il

    Copyright (C) 2015 J. Giráldez-Cru, J. Levy, 2022 Z. Avissar

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

#include <getopt.h>
#include <stdlib.h>
#include <iostream>
#include <math.h>
#include <vector>
#include <stdio.h>

using namespace std;

int k = 3;		// k-CNF
int n = 10000;	// number of variables
double percent_in = 0.25; // percantage of input variables
int m = 42500;	// number of clauses
double Q = 0.8;	// modularity
int c = 80;		// number of communities
bool requireInput = True;

double P;

char* output = NULL;

//assumes all input variables are given first
class Community{
private:
	vector<int> vars;
	int num_input_vars;
public:
	Community(){
		vars = vector<int>();
		num_input_vars = 0;
	}
	~Community(){
		vars.clear();
	}

	int get_num_input_vars(void){
		return num_input_vars;
	}
	int get_size(void){
		return vars.size();
	}
	void add_var(int var, bool is_input){
		vars.push_back(var);
		num_input_vars += is_input? 1: 0;
	}
	int get_rand_var(void){
		int index = rand() % vars.size();
		return vars[index];
	}
	int get_rand_input_var(void){
		int index = rand() % num_input_vars;
		return vars[index];
	}
	int get_rand_output_var(void){
		int index = rand() % (vars.size() - num_input_vars);
		return vars[num_input_vars + index];
	}
	void print(void){
		for (unsigned int i = 0; i<vars.size();++i){
			cout << " " << vars[i];
		}
		cout << endl;
	}
};


void printUsage_QBF(char* app){
	cerr << "  Usage: " << app << " [options]" << endl;
	cerr << "    -n <int>   :  number of variables (10000)" << endl;
	cerr << "    -p <float> :  percantage of input variables (0.25)" << endl;
	cerr << "    -m <int>   :  number of clauses (42500)" << endl;
	cerr << "    -c <int>   :  number of communities (80)" << endl;
	cerr << "    -Q <float> :  modularity: Q (0.8)" << endl;
	cerr << "    -k <int>   :  number of literals by clause: k-CNF (3)" << endl;
	cerr << "    -o <string>:  output file (stdout)" << endl;
	cerr << "    --reqInput	:  require each clause to contain at least one input variable (True)" << endl;
	cerr << "  Restrictions:" << endl;
	cerr << "    1. c must be greater than 1" << endl;
	cerr << "    2. p must be in the interval (0,1)" << endl;
	cerr << "    3. Q must be in the interval (0,1)" << endl;
	cerr << "	 4. k must be greater than 1" << endl;
	cerr << "    5. c must be greater or equal than k" << endl;
	cerr << "    6. (c*k) must be smaller or equal than n" << endl;
	cerr << "    7. (p*n) must be in range [c, n-c]" << endl;
	exit(-1);
}


void parseArgs_QBF(int argc, char **argv){
	int opt, opt_indx;
	static struct option long_options[] = {
          {"reqInput", no_argument, &requireInput, 1},
          {0, 0, 0, 0}
    };
	while((opt=getopt_long(argc, argv, "n:m:p:c:Q:k:?ho:", long_options, &opt_indx)) != -1){
		switch(opt){
			case 0:
				break;
			case 'n':
				n = atoi(optarg);
				if (n < 1){
					cerr << "n should be a positive integer (n = " << n << ")" << endl;
					cerr << "  Execution failed." << endl;
					exit(-1);
				}
				break;
			case 'm':
				m = atoi(optarg);
				if (m < 1){
					cerr << "m should be a positive integer (m = " << m << ")" << endl;
					cerr << "  Execution failed." << endl;
					exit(-1);
				}
				break;
			case 'p':
				percent_in = atof(optarg);
				if(percent_in <= 0 || percent_in >= 1){
					cerr << "WARNING: p must be in the interval (0,1)" << endl;
					cerr << "  p changed to 0.25 (default value)" << endl;
					percent_in = 0.25;
				}
				break;
			case 'c':
				c = atoi(optarg);
				if(c <= 1 /*|| c >= xxx*/){
					cerr << "WARNING: c must be greater than 1" << endl;
					cerr << "  c changed to 80 (default value)" << endl;
					c = 80;
				}
				break;
			case 'Q':
				Q = atof(optarg);
				if(Q <= 0 || Q >= 1){
					cerr << "WARNING: Q must be in the interval (0,1)" << endl;
					cerr << "  Q changed to 0.8 (default value)" << endl;
					Q = 0.8;
				}
				break;
			case 'k':
				k = atoi(optarg);
				if(k < 3){
					cerr << "WARNING: k must be greater than 2" << endl;
					cerr << "  k changed to 3 (default value)" << endl;
					k = 3;
				}
				break;
			case 'o':
				output = optarg;
				break;
			case 'h':
			case '?':
				printUsage_QBF(argv[0]);
				break;
			default:
				cerr << "ERROR: Incorrect argument: " << optarg << endl;
				printUsage_QBF(argv[0]);
		}
	}
	
	if(c < k){
		cerr << "ERROR: c (c=" << c << ") must be greater or equal than k (k=" << k << ")" << endl;
		cerr << "  Execution failed." << endl;
		exit(-1);
	}

	if (c > (int)(percent_in*n) || n-c < (int)(percent_in*n)){
		cerr << "ERROR: p*n (p=" << percent_in << ", n=" << n << ") must be in range [c, n-c] (c=" << c << ", n=" << n << ")" << endl;
		cerr << "  Execution failed." << endl;
		exit(-1);
	}
	
	if(c*k > n){
		cerr << "ERROR: c*k (c=" << c << ", k=" << k << ") must be less or equal than n (n=" << n << ")" << endl;
		cerr << "  Execution failed." << endl;
		exit(-1);
	}
}

void computeProbability(){
	P = Q + 1/(double)c;
		
}


void computeN2C_QBF(vector<int> &n2c){
	int rn;
	double rd;	
		
	rn = rand();
	rd = ((double)rn) / (RAND_MAX);
	if(rd <= P){ // All variables in the same community
		rn = rand();
		for(int i=0; i<k; ++i)
			n2c[i] = rn % c;
	}else{ // All variables in distict communitites
		for(int i=0; i<k; ++i){
			bool used=false;
			do{
				used=false;
				rn = rand();
				for(int j=0; j<i && !used; ++j){
					if(n2c[j] ==  rn%c)
						used=true;
				}
			}while(used);
			n2c[i] = rn%c;
		}
	}
}


void computeClause_QBF(vector<int> &n2c, vector<int> &clause, vector<Community> communities){
	int rn;
	for(int j=0; j<k; ++j){
		// Random variable in the community
		//   avoiding tautologies with previous literals
		int var;
		bool tautology = false;
		//output variable
		if (j == 0) {
			var = communities[n2c[j]].get_rand_output_var();
		//input variable
		} else if (j == 1 && requireInput) {
			var = communities[n2c[j]].get_rand_input_var();
		} else{
			do{
				var = communities[n2c[j]].get_rand_var();
				tautology = false;
				for(int l=0; l<j && !tautology; ++l){
					if(abs(clause[l]) == var){
						tautology = true;
					}
				}
			}while(tautology);
		}

		// Polarity of the variable
		rn = rand();
		if(rn > (RAND_MAX/2))
			var = -var;
		
		clause.push_back(var);
	}
}


void init_communities_QBF(vector<Community>& communities){
	int i, j;
	int num_in = percent_in*n;
	for (i = 0; i < c; ++i){
		for (j = (int)((((float)i)/c)*num_in); j < (int)((((float)(i + 1))/c)*num_in); ++j){
			communities[i].add_var(j + 1, true);
		}
		for (j = ((((float)i)/c)*(n-num_in)); j < (int)((((float)(i + 1))/c)*(n-num_in)); ++j){
			communities[i].add_var(j + num_in + 1, false);
		}
	}
}


int main(int argc, char **argv){
	FILE *fout;
	int i, j;
	unsigned int seed = time (NULL);
	srand (seed);
	vector<Community> communities(c, Community());
	vector<int> n2c(k,0);
	vector<int> clause;

	// Parse arguments
	parseArgs_QBF(argc, argv);
	
	if(output!=NULL){
		fout = fopen(output, "w");
	}
	
	// Compute the probability P, according to k, c and Q
	computeProbability();
	
	// Print header
	if(output!=NULL){
		fprintf(fout, "c Modularity-based k-CNF Generator (V2.0). J. Giraldez-Cru and J. Levy\n");
		fprintf(fout, "c   value n = %d\n", n);
		fprintf(fout, "c   value m = %d\n", m);
		fprintf(fout, "c   value k = %d\n", k);
		fprintf(fout, "c   value Q = %f\n", Q);
		fprintf(fout, "c   value c = %d\n", c);
		fprintf(fout, "c   value seed = %d\n", seed);
		fprintf(fout, "p cnf %d %d\n", n, m);		
		fprintf(fout, "a ");
		for (i = 0; i < percent_in*n; ++i){
			fprintf(fout, "%d ", (i + 1));
		}
		fprintf(fout, "0\n");
		fprintf(fout, "e ");
		for (i = percent_in*n; i < n; ++i){
			fprintf(fout, "%d ", (i + 1));
		}
		fprintf(fout, "0\n");
	}else{
		cout << "c Modularity-based k-CNF Generator (V2.0). J. Giraldez-Cru and J. Levy" << endl;
		cout << "c   value n = " << n << endl;
		cout << "c   value m = " << m << endl;
		cout << "c   value k = " << k << endl;
		cout << "c   value Q = " << Q << endl;
		cout << "c   value c = " << c << endl;
		cout << "c   value seed = " << seed << endl;
		cout << "p cnf " << n << " " << m << endl;
		cout << "a ";
		for (i = 0; i < percent_in*n; ++i){
			cout << i << " ";
		}
		cout << "0" << endl;
		cout << "e ";
		for (i = percent_in*n; i < n; ++i){
			cout << i << " ";
		}
		cout << "0" << endl;
	}

	init_communities_QBF(communities);
	for (i = 0; i<c;++i){
		if (communities[i].get_size() <= k){
			cerr << "ERROR: cannot create communities for given parameters, aborting!" << endl;
			exit(1);
		}
	}
	clause.clear();

	// Iterate for each clause
	for(i=0; i<m; ++i){
		
		// n2c is the community of each literal
		computeN2C_QBF(n2c);
		
		// Compute the clause
		computeClause_QBF(n2c, clause, communities);
		
		// Print the clause
		for(j=0; j<k; ++j){
			if(output!=NULL){
				fprintf(fout, "%d ", clause[j]);
			}else{
				cout << clause[j] << " ";
			}
		}
		
		if(output!=NULL){
			fprintf(fout, "0\n");
		}else{
			cout << "0" << endl;
		}
		
		clause.clear();
	}	
	
	if(output!=NULL){
		fclose(fout);
	}
}