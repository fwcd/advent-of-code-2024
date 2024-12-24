.PHONY: all
all: out/day22

out:
	mkdir -p $@

out/day22: ./day22.cpp | out
	$(CXX) $< -Ofast -std=c++11 -o $@
