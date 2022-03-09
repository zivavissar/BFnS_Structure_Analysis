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
BnF from commit 3981be4426850bdef25bb168ecefe35dfb703149 applied with the patches in diff_to_apply.diff should be run with arguments:
```
./bafsyn <input instance in qdimacs> > <log of BnF run> 2> [optional furthe log of BnF run]
```
followed by:
```
make
./baf_iter_c <input instance in qdimacs> <log of BnF run> > <csv file output redirects into>
```
##### BFSS Iter
BFSS from commit 13c60df758bc58b652ffeab2be7e95a0b57f7853 applied with the patches in diff_to_apply.patch should be run with arguments:
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
CADET from commit 60dd426b8a2ba2574f5f663af5b9b8b1ce93c774 applied with the patches in diff_to_apply.diff should be run with arguments:
```
./cadet --no_colors <input instance in qdimacs> > <log of cadet run> 2> [optional further log of cadet]
```
followed by:
```
make
./cadet_iter <input instance in qdimacs> <log of cadet run> <bfss .dep file> > <csv file output redirects into>
```
##### Manthan Iter
Manthan from commit a92eb8fe003260d90a530d9e088b5e6fced0319d applied with the patches in diff_to_apply.diff should be run with arguments:
```
./manthan.py --logtime 1 --qdimacs --dumpdata <log of manthan run> <input instance in qdimacs> > [optional further log of manthan]
```
followed by:
```
make
./manth_iter <input instance in qdimacs> <log of manthan run> > <csv file output redirects into>
```
