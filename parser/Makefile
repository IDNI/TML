all:
	clang++ -D_DEBUG earley.cpp -W -Wall -Wpedantic -oearley -std=c++11 -g
small:
	clang++ -D_DEBUG earley.cpp -W -Wall -Wpedantic -oearley -std=c++11 -Oz
	strip earley
fast:
	clang++ -D_DEBUG earley.cpp -W -Wall -Wpedantic -oearley -std=c++11 -O3
	strip earley
