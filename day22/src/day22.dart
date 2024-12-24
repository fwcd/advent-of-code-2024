import 'dart:io';

Future<void> main(List<String> args) async {
  final input = await File(args[0]).readAsString();
  print("Input: $input");
}
