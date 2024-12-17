using System;
using System.Collections.Generic;
using System.Linq;
using System.IO;

if (args.Length == 0)
{
  Console.WriteLine("usage: day17 <path to input>");
  return 1;
}

string[] rawChunks = File.ReadAllText(args[0]).Trim().Split("\n\n");
List<int> registers = rawChunks[0].Split("\n").Select(l => int.Parse(l.Split(": ")[1])).ToList();
List<int> program = rawChunks[1].Split(" ")[1].Split(",").Select(int.Parse).ToList();
// TODO

Console.WriteLine($"Program: {string.Join(",", program)}, registers: {string.Join(",", registers)}");

return 0;
