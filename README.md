# BFnS Structure Analysis
Code accompanying the paper "Structure Analysis in Boolean Functional Synthesis"

All iteration analyzers are based on the tool GraphFeatSAT
ModQBF is based on the tool Community attachment
Both original tools may be found at https://www.ugr.es/~jgiraldez/

### How to Use the Various Tools

##### ModQBF

```
make
./modqbf -n <number of variables> -m <number of clauses> -c <number of communities> -Q <desired modularity> -k <number of variables in each clause> -p <portion of variables that are input variables> -o <your_qdimacs_ouptut_name>
```

##### BnF Iter
BFSS from commit [complete here] applied with the patches in diff_to_apply.diff should be run with arguments:
```
./bafsyn <input instance in qdimacs> > <log of BnF run> 2> [optional furthe log of BnF run]
```
followed by:
```
make
./baf_iter_c <input instance in qdimacs> <log of BnF run> > <csv file output redirects into>
```
##### BFSS Iter
BFSS from commit [complete here] applied with the patches in diff_to_apply.diff should be run with arguments:
```
./readCnf <input instance in qdimacs>
cp <basename of input instance in qdimacs>_dep.txt <bfss .dep file>
./genVarOrder ./<basename of input instance in qdimacs>.v ./<basename of input instance in qdimacs>_var.txt > <variable order file>
./bfss ./$(basename $in_file .qdimacs).v <variable order file> -fela --checkWDNNF > <log of bfss run>
```
followed by:
```
make
./bfss_iter <input instance in qdimacs> <log of bfss run> <bfss .dep file> > <csv file output redirects into>
```
##### CADET Iter
BFSS from commit [complete here] applied with the patches in diff_to_apply.diff should be run with arguments:
```
./cadet --no_colors <input instance in qdimacs> > <log of cadet run> 2> [optional further log of cadet]
```
followed by:
```
make
./bfss_iter <input instance in qdimacs> <log of cadet run> <bfss .dep file> > <csv file output redirects into>
```
##### Manthan Iter
Manthan from commit [complete here] applied with the patches in diff_to_apply.diff should be run with arguments:
```
./manthan.py --logtime 1 --qdimacs --dumpdata <log of manthan run> <input instance in qdimacs> > [optional further log of manthan]
```
followed by:
```
make
./manth_iter <input instance in qdimacs> <log of manthan run> > <csv file output redirects into>
```
