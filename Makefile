
name=precolor_extend

$(name): $(name).cpp graph.h
	g++ -O5 -o $(name) $(name).cpp
