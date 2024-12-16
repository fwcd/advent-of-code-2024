using System;
using System.IO;

if (args.Length == 0)
{
  Console.WriteLine("usage: day17 <path to input>");
  return 1;
}

string input = File.ReadAllText(args[0]);
// TODO

Console.WriteLine($"Input: {input}");

return 0;
