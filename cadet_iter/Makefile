CPP = g++ -DNDEBUG -O3
CC = g++ -O3
LDLIBS += -lm
CFLAGS += -Wall -Wno-deprecated -DNDEBUG -bstatic

all : cadet_iter

clean :
	rm -f *.o cadet_iter *~

cadet_iter: main.cpp graph_vector.h tools.h community.h dimension.h
	$(CPP) --static -o $@ $^

%.o: %.cpp %.h
	$(CPP) -o $@ -c $<

%.cpp: %.lex
	lex -+ -o $@ $<
