# all:
# 	gcc -Wall -Wextra -std=c99 -pedantic -g3 -o modqbf modularityGen_v2.1.cpp
all:
	g++ -Wall -Wextra -pedantic -DNDEBUG -DQBF -O3 -o modqbf modularityGen_v2.1.cpp
	g++ -Wall -Wextra -pedantic -DNDEBUG -DQBF -O3 -o modqbf_e modularityGen_v2.1_edited.cpp
clean:
	rm *~ modqbf modqbf_e