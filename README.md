# BFnS Structure Analysis
Code accompanying the paper "Structure Analysis in Boolean Functional Synthesis"

All iteration analyzers are based on the tool GraphFeatSAT
ModQBF is based on the tool Community attachment
Both original tools may be found at https://www.ugr.es/~jgiraldez/

##How to Use the Various Tools

### ModQBF

```
make
./modqbf -n <number of variables> -m <number of clauses> -c <number of communities> -Q <desired modularity> -k <number of variables in each clause> -p <portion of variables that are input variables> -o <your_qdimacs_ouptut_name>
```

### BnF Iter

### BFSS Iter

### CADET Iter

### Manthan Iter
