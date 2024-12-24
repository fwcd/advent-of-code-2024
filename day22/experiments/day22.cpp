#include <cstdlib>
#include <iostream>
#include <fstream>
#include <vector>

const int LIMIT = 2000;

int next(int secret) {
  int mask = 16777215; // = 2^24 - 1
  secret ^= secret << 6;
  secret &= mask;
  secret ^= secret >> 5;
  secret &= mask;
  secret ^= secret << 11;
  secret &= mask;
  return secret;
}

int prng(int secret, int n) {
  for (int i = 0; i < n; i++) {
    secret = next(secret);
  }
  return secret;
}

int monkey(int secret, int x1, int x2, int x3, int x4) {
  int d1 = -1, d2 = -1, d3 = -1, d4 = -1;
  for (int i = 0; i < LIMIT; i++) {
    int lastPrice = secret % 10;
    secret = next(secret);
    int price = secret % 10;
    d1 = d2;
    d2 = d3;
    d3 = d4;
    d4 = price - lastPrice;
    if (d1 == x1 && d2 == x2 && d3 == x3 && d4 == x4) {
      return price;
    }
  }
  return -1;
}

int score(std::vector<int> input, int x1, int x2, int x3, int x4) {
  int sum = 0;
  for (int n : input) {
    int price = monkey(n, x1, x2, x3, x4);
    if (price > 0) {
      sum += price;
    }
  }
  return sum;
}

int findBestScore(std::vector<int> input) {
  int bestScore = 0;
  int bound = 9;
  for (int x1 = -bound; x1 <= bound; x1++) {
    for (int x2 = -bound; x2 <= bound; x2++) {
      std::cout << "Searching (" << x1 << ", " << x2 << ")" << std::endl;
      for (int x3 = -bound; x3 <= bound; x3++) {
        for (int x4 = -bound; x4 <= bound; x4++) {
          int n = score(input, x1, x2, x3, x4);
          if (n > bestScore) {
            bestScore = n;
          }
        }
      }
    }
  }
  return bestScore;
}

int main(int argc, char *argv[]) {
  if (argc == 1) {
    std::cerr << "Usage: " << argv[0] << " <path to input>" << std::endl;
    return 1;
  }

  std::vector<int> input;

  {
    std::ifstream file;
    file.open(argv[1]);
    for (std::string line; std::getline(file, line);) {
      input.push_back(std::atoi(line.c_str()));
    }
  }

  int part1 = 0;
  for (int n : input) {
    part1 += prng(n, LIMIT);
  }
  std::cout << "Part 1: " << part1 << std::endl;

  int part2 = findBestScore(input);
  std::cout << "Part 2: " << part2 << std::endl;

  return 0;
}
