import 'dart:io';

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
  for (var x = 0; x < n; x++) {
    secret = next(secret);
  }
  return secret;
}

Future<void> main(List<String> args) async {
  final raw = await File(args[0]).readAsString();
  final input = raw.split('\n').map((l) => l.trim()).where((l) => !l.isEmpty).map(int.parse).toList();

  final part1 = input.map((n) => prng(n, 2000)).reduce((a, b) => a + b);
  print("Part 1: $part1");
}
