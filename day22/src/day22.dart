import 'dart:io';

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
  for (var i = 0; i < n; i++) {
    secret = next(secret);
  }
  return secret;
}

int monkey(int secret, int x1, int x2, int x3, int x4) {
  int? d1 = null, d2 = null, d3 = null, d4 = null;
  for (var i = 0; i < LIMIT; i++) {
    int lastPrice = secret % 10;
    secret = next(secret);
    int price = secret % 10;
    (d1, d2, d3, d4) = (d2, d3, d4, price - lastPrice);
    if (d1 == x1 && d2 == x2 && d3 == x3 && d4 == x4) {
      return price;
    }
  }
  return -1;
}

int score(List<int> input, int x1, int x2, int x3, int x4) {
  int sum = 0;
  for (int n in input) {
    int price = monkey(n, x1, x2, x3, x4);
    if (price > 0) {
      sum += price;
    }
  }
  return sum;
}

int findBestScore(List<int> input) {
  int bestScore = 0;
  int bound = 9;
  for (var x1 = -bound; x1 <= bound; x1++) {
    for (var x2 = -bound; x2 <= bound; x2++) {
      print("Searching ($x1, $x2, ...)");
      for (var x3 = -bound; x3 <= bound; x3++) {
        for (var x4 = -bound; x4 <= bound; x4++) {
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

Future<void> main(List<String> args) async {
  final raw = await File(args[0]).readAsString();
  final input = raw.split('\n').map((l) => l.trim()).where((l) => !l.isEmpty).map(int.parse).toList();

  final part1 = input.map((n) => prng(n, LIMIT)).reduce((a, b) => a + b);
  print("Part 1: $part1");

  final part2 = findBestScore(input);
  print("Part 2: $part2");
}
