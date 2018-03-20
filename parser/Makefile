# c++11 also works with minor warnings
all:
	clang++ -D_DEBUG earley.cpp -W -Wall -Wpedantic -oearley -std=c++1z -g
small:
	g++ -D_DEBUG earley.cpp -W -Wall -Wpedantic -oearley -std=c++1z -Os
	strip earley
fast:
	clang++ -D_DEBUG earley.cpp -W -Wall -Wpedantic -oearley -std=c++1z -O3
	strip earley
