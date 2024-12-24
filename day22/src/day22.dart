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
  int d1 = -1, d2 = -1, d3 = -1, d4 = -1;
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

Future<void> main(List<String> args) async {
  final raw = await File(args[0]).readAsString();
  final input = raw.split('\n').map((l) => l.trim()).where((l) => !l.isEmpty).map(int.parse).toList();

  final part1 = input.map((n) => prng(n, LIMIT)).reduce((a, b) => a + b);
  print("Part 1: $part1");

  final part2 = monkey(2024, -2, 1, -1, 3);
  print("Part 2: $part2");
}
