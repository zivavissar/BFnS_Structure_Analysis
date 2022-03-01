#!/bin/bash
mkdir ./gen_modqbf
mkdir ./gen_modqbf/gen_logs
for i in {100..300..100}
  do
     echo n = $i
     for j in $(seq $((3*$i)) 50 $((5*$i)))
        do
           echo m = $j
           for q in $(seq 0.05 0.05 0.95)
              do
                 echo q = $q
                 for p in $(seq 0.2 0.1 0.8)
                    do
                       echo p = $p
                       for c in {5..20..1}
                          do
                             echo c = $c
                             for l in {1..10..1}
                                do
                                   echo i = $l
                                   ./modqbf_e -n $i -m $j -c $c -Q $q -k 5 -p $p -o "./gen_modqbf/n_($i)__m_($j)__c_($c)__Q_($q)__p_($p)__k_5__num_($l).qdimacs" >"./gen_modqbf/gen_logs/n_($i)__m_($j)__c_($c)__Q_($q)__p_($p)__k_5__num_($l).log"
                              done
                        done
                  done
            done
      done
 done

