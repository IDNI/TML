all:
	clang++ -D_DEBUG earley.cpp -W -Wall -Wpedantic -oearley -flto -std=c++11 -g
small:
	g++ earley.cpp -W -Wall -Wpedantic -oearley -flto -std=c++11 -Os
	strip earley
fast:
	g++ earley.cpp -W -Wall -Wpedantic -oearley -flto -std=c++11 -O3
	strip earley
