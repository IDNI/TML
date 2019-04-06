#CXXFLAGS = -W -Wall -Wpedantic -otml -std=c++1y -O3 -flto
CXXFLAGS = -W -Wall -Wpedantic -otml -std=c++1y -ggdb3
CXX = g++
OBJ = query.o rule.o input.o driver.o lp.o bdd.o dict.o main.o output.o transform.o tree.o
SRC = input.cpp input.h defs.h driver.cpp driver.h lp.cpp lp.h bdd.cpp bdd.h rule.cpp rule.h main.cpp dict.cpp query.h query.cpp term.h Makefile output.cpp transform.cpp tree.cpp dict.h
all: $(OBJ)
	$(CXX) $(CXXFLAGS) $(OBJ) -otml

driver.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c driver.cpp -o driver.o
query.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c query.cpp -o query.o
rule.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c rule.cpp -o rule.o
transform.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c transform.cpp -o transform.o
lp.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c lp.cpp -o lp.o
tree.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c tree.cpp -o tree.o
bdd.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c bdd.cpp -o bdd.o
dict.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c dict.cpp -o dict.o
input.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c input.cpp -o input.o
output.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c output.cpp -o output.o
main.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c main.cpp -o main.o

test: bdd.test.cpp bdd.cpp bdd.h defs.h query.h query.cpp rule.h rule.cpp query.test.h query.test.cpp driver.cpp
	g++ query.cpp bdd.test.cpp query.test.cpp rule.cpp bdd.cpp driver.cpp lp.cpp -otest -g -W -Wall -Wpedantic dict.cpp input.cpp -ggdb3

dimacs: dimacs.cpp bdd.h bdd.cpp defs.h
	g++ dimacs.cpp bdd.cpp -O3 -flto

.PHONY: clean
clean:
	rm tml *.o
