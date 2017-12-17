all:
	g++ tml.cpp parser.cpp formatter.cpp -g -otml -std=c++11 -W -Wall -Wpedantic -D_DEBUG
