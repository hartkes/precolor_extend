
name=precolor_extend
CXX=g++
CXX=clang++

$(name): $(name).cpp graph.h
	$(CXX) -O5 -o $(name) $(name).cpp
