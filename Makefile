all:
	g++ -std=c++1y tml.cpp driver.cpp -W -Wall -Wpedantic -otml -ggdb3
	#g++ -std=c++1y tml.cpp -W -Wall -Wpedantic -otml -O3 -flto
	#clang++-6.0 -std=c++1y tml.cpp -W -Wall -Wpedantic -otml -g #-O3 -flto
