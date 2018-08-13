all:
	clang-6.0 ed.c io.c -W -Wall -Wpedantic -g
	#gcc ed.c io.c -W -Wall -Wpedantic -Os -flto
