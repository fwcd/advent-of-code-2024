# We need Homebrew LLVM since Apple Clang doesn't support OpenMP
CXX=/opt/homebrew/opt/llvm/bin/clang++

.PHONY: all
all: out/day22

out:
	mkdir -p $@

out/day22: ./day22.cpp | out
	$(CXX) $< -ffast-math -fopenmp -O3 -std=c++11 -o $@
