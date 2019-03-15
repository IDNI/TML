#CXXFLAGS = -W -Wall -Wpedantic -otml -std=c++1y -O3 -flto
CXXFLAGS = -W -Wall -Wpedantic -otml -std=c++1y -ggdb3
CXX = g++
OBJ = input.o driver.o lp.o bdd.o
SRC = input.cpp input.h defs.h driver.cpp driver.h lp.cpp lp.h bdd.cpp bdd.h
all: input.o driver.o lp.o bdd.o
	$(CXX) $(CXXFLAGS) $(OBJ) -otml

input.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c input.cpp -o input.o
driver.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c driver.cpp -o driver.o
lp.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c lp.cpp -o lp.o
bdd.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c bdd.cpp -o bdd.o

test: bdd.test.cpp bdd.cpp bdd.h defs.h
	g++ bdd.test.cpp bdd.cpp -otest -g -W -Wall -Wpedantic

.PHONY: clean
clean:
	rm tml *.o
