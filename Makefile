
name=precolor_extend
CXX=g++
#CXX=clang++

all: $(name) $(name)128

$(name): $(name).cpp graph.h
	$(CXX) -O5 -o $(name) $(name).cpp

# We use a macro to indicate whether we should use 128 bits for bit masks.
# Since this is simulated with two 64-bit words on 64-bit machines, it's slower than 64-bit masks.
# We compile the 128-bit version to a separate executable.
$(name)128: $(name).cpp graph.h
	$(CXX) -O5 -D USE128BITS=yes -o $(name)128 $(name).cpp

clean:
	rm $(name) $(name)128
