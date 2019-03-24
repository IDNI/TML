CXXFLAGS = -W -Wall -Wpedantic -otml -std=c++1y -O3 -flto
#CXXFLAGS = -W -Wall -Wpedantic -otml -std=c++1y -ggdb3
CXX = g++
OBJ = input.o driver.o lp.o bdd.o rule.o dict.o main.o query.o
SRC = input.cpp input.h defs.h driver.cpp driver.h lp.cpp lp.h bdd.cpp bdd.h rule.cpp rule.h main.cpp dict.cpp query.h query.cpp
all: $(OBJ)
	$(CXX) $(CXXFLAGS) $(OBJ) -otml

input.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c input.cpp -o input.o
driver.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c driver.cpp -o driver.o
lp.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c lp.cpp -o lp.o
bdd.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c bdd.cpp -o bdd.o
dict.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c dict.cpp -o dict.o
rule.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c rule.cpp -o rule.o
query.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c query.cpp -o query.o
main.o: $(SRC)
	$(CXX) $(CXXFLAGS) -c main.cpp -o main.o

test: bdd.test.cpp bdd.cpp bdd.h defs.h query.h query.cpp rule.h rule.cpp query.test.h query.test.cpp
	g++ query.cpp bdd.test.cpp query.test.cpp rule.cpp bdd.cpp -otest -g -W -Wall -Wpedantic

.PHONY: clean
clean:
	rm tml *.o
