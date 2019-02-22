all:
	 #g++ -std=c++1y tml.cpp -W -Wall -Wpedantic -otml -ggdb3 # -O3 -flto
	 g++ -std=c++1y tml.cpp -W -Wall -Wpedantic -otml -O3 -flto
	 #clang++-7 -std=c++1y tml.cpp -W -Wall -Wpedantic -otml -g #-O3 -flto
