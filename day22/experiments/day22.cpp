#include <cstdlib>
#include <cstdint>
#include <iostream>
#include <fstream>
#include <vector>

const uint64_t LIMIT = 2000;

uint64_t next(uint64_t secret) {
  uint64_t mask = 16777215; // = 2^24 - 1
  secret ^= secret << 6;
  secret &= mask;
  secret ^= secret >> 5;
  secret &= mask;
  secret ^= secret << 11;
  secret &= mask;
  return secret;
}

uint64_t prng(uint64_t secret, uint64_t n) {
  for (uint64_t i = 0; i < n; i++) {
    secret = next(secret);
  }
  return secret;
}

uint64_t monkey(uint64_t secret, uint64_t x1, uint64_t x2, uint64_t x3, uint64_t x4) {
  uint64_t d1 = -1, d2 = -1, d3 = -1, d4 = -1;
  for (uint64_t i = 0; i < LIMIT; i++) {
    uint64_t lastPrice = secret % 10;
    secret = next(secret);
    uint64_t price = secret % 10;
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

uint64_t score(std::vector<uint64_t> input, uint64_t x1, uint64_t x2, uint64_t x3, uint64_t x4) {
  uint64_t sum = 0;
  for (uint64_t n : input) {
    uint64_t price = monkey(n, x1, x2, x3, x4);
    if (price > 0) {
      sum += price;
    }
  }
  return sum;
}

uint64_t findBestScore(std::vector<uint64_t> input) {
  uint64_t bestScore = 0;
  uint64_t bound = 9;
  #pragma omp parallel for
  for (uint64_t x1 = -bound; x1 <= bound; x1++) {
    for (uint64_t x2 = -bound; x2 <= bound; x2++) {
      std::cout << "Searching (" << x1 << ", " << x2 << ")" << std::endl;
      for (uint64_t x3 = -bound; x3 <= bound; x3++) {
        for (uint64_t x4 = -bound; x4 <= bound; x4++) {
          uint64_t n = score(input, x1, x2, x3, x4);
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

  std::vector<uint64_t> input;

  {
    std::ifstream file;
    file.open(argv[1]);
    for (std::string line; std::getline(file, line);) {
      input.push_back(std::atoi(line.c_str()));
    }
  }

  uint64_t part1 = 0;
  for (uint64_t n : input) {
    part1 += prng(n, LIMIT);
  }
  std::cout << "Part 1: " << part1 << std::endl;

  uint64_t part2 = findBestScore(input);
  std::cout << "Part 2: " << part2 << std::endl;

  return 0;
}
