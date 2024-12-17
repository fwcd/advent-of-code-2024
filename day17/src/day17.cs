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
Machine machine = new Machine(registers, program);

{
  List<int> output = machine.Copy().Run();
  Console.WriteLine($"Part 1: {string.Join(",", output)}");
}

for (int i = 0; ; i++)
{
  if (i % 10_000_000 == 0) {
    Console.WriteLine($"  (searching {i}...)");
  }
  machine.Registers[0] = i;
  List<int> output = machine.Copy().Run();
  if (output.SequenceEqual(machine.Program))
  {
    Console.WriteLine($"Part 2: {i}");
    break;
  }
}

return 0;

public class Machine
{
  public List<int> Registers;
  public List<int> Program;

  public Machine(List<int> registers, List<int> program)
  {
    Registers = registers;
    Program = program;
  }

  public List<int> Run()
  {
    var outputs = new List<int>();
    for (int i = 0; i < Program.Count;)
    {
      int opcode = Program[i];
      int operand = Program[i + 1];
      int combo = operand >= 4 && operand < 7 ? Registers[operand - 4] : operand;
      bool jumped = false;
      // Console.WriteLine($"{(new string[] {"adv", "bxl", "bst", "jnz", "bxc", "out", "bdv", "cdv"})[opcode]} {operand}: {string.Join("", Program.Take(i))}\x1B[4m{Program[i]}\x1B[0m{string.Join("", Program.Skip(i + 1))} - {string.Join(",", Registers)}");
      switch (opcode)
      {
        case 0: // adv (A divide)
          Registers[0] >>= combo;
          break;
        case 1: // bxl (B xor literal)
          Registers[1] ^= operand;
          break;
        case 2: // bst (B store?)
          Registers[1] = combo & 0b111;
          break;
        case 3: // jnz (jump not zero)
          if (Registers[0] != 0 && i != operand)
          {
            i = operand;
            jumped = true;
          }
          break;
        case 4: // bxc (B xor combo)
          Registers[1] ^= Registers[2];
          break;
        case 5: // out (output)
          outputs.Add(combo & 0b111);
          break;
        case 6: // bdv (B divide)
          Registers[1] = Registers[0] >> combo;
          break;
        case 7: // cdv (C divide)
          Registers[2] = Registers[0] >> combo;
          break;
      }
      if (!jumped)
      {
        i += 2;
      }
    }
    return outputs;
  }

  public List<int> RunOptimizedInputProgram()
  {
    var outputs = new List<int>();
    do
    {
      Registers[1] = (Registers[0] & 0b111) ^ 0b001;
      Registers[2] = Registers[0] >> Registers[1];
      Registers[1] ^= Registers[2] ^ 0b101;
      outputs.Add(Registers[1] & 0b111);
      Registers[0] >>= 3;
    } while (Registers[0] != 0);
    return outputs;
  }

  public Machine Copy() => new Machine(Registers.ToList(), Program.ToList());

  public override string ToString() => $"Registers: {string.Join(",", Registers)}, Program: {string.Join(",", Program)}";
}
