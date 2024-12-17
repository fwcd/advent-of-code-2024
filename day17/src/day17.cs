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

var machine = new Machine { Registers = registers, Program = program };
List<int> output = machine.Run();

Console.WriteLine($"{machine}");
Console.WriteLine($"Part 1: {string.Join(",", output)}");

return 0;

public class Machine
{
  public List<int> Registers;
  public List<int> Program;

  public List<int> Run()
  {
    var outputs = new List<int>();
    for (int i = 0; i < Program.Count;)
    {
      int opcode = Program[i];
      int operand = Program[i + 1];
      int combo = operand > 3 && operand < 6 ? Registers[operand - 3] : operand;
      bool jumped = false;
      Console.WriteLine($"{(new string[] {"adv", "bxl", "bst", "jnz", "bxc", "out", "bdv", "cdv"})[opcode]} {operand}: {string.Join("", Program.Take(i))}\x1B[4m{Program[i]}\x1B[0m{string.Join("", Program.Skip(i + 1))} - {string.Join(",", Registers)}");
      switch (opcode)
      {
        case 0: // adv (A divide)
          Registers[0] /= 1 << combo;
          break;
        case 1: // bxl (bitwise xor literal)
          Registers[1] ^= operand;
          break;
        case 2: // bst (bitwise store?)
          Registers[1] = combo % 8;
          break;
        case 3: // jnz (jump not zero)
          if (Registers[0] != 0 && i != operand)
          {
            i = operand;
            jumped = true;
          }
          break;
        case 4: // bxc (bitwise xor combo)
          Registers[1] = Registers[1] ^ Registers[2];
          break;
        case 5: // out (output)
          outputs.Add(combo % 8);
          break;
        case 6: // bdv (B divide)
          Registers[1] = Registers[0] / (1 << combo);
          break;
        case 7: // cdv (C divide)
          Registers[2] = Registers[0] / (1 << combo);
          break;
      }
      if (!jumped)
      {
        i += 2;
      }
    }
    return outputs;
  }

  public override string ToString() => $"Program: {string.Join(",", Program)}, Registers: {string.Join(",", Registers)}";
}
