all:
	g++ hash.cpp clause.cpp literal.cpp parser.cpp formatter.cpp tml.cpp -g -otml -std=c++11 -W -Wall -Wpedantic -D_DEBUG
