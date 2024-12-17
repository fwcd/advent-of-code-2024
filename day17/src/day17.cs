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

int i = 0;
int solved = 0;
int solvedBitCount = 0;
int solvedOutputValues = 0;

while (true)
{
  if (i % 10_000_000 == 0) {
    Console.WriteLine($"  (searching {i}...)");
  }

  int part2 = (i << solvedBitCount) | solved;
  machine.Registers[0] = part2;
  machine.Registers[1] = 0;
  machine.Registers[2] = 0;

  List<int> output = machine.Run();
  if (output.SequenceEqual(machine.Program))
  {
    Console.WriteLine($"Part 2: {part2}");
    break;
  }

  int n = 9;
  if (output.Skip(solvedOutputValues).Take(n).SequenceEqual(machine.Program.Skip(solvedOutputValues).Take(n)))
  {
    int newBitCount = 1;
    int newBitMask = (1 << newBitCount) - 1;
    solved |= (i & newBitMask) << solvedBitCount;
    solvedBitCount += newBitCount;
    solvedOutputValues++;
    i = 0;
    Console.WriteLine($"{Convert.ToString(part2, 2)} {solvedBitCount} ({Convert.ToString(solved, 2)}) " + string.Join(",", output));
  }
  else
  {
    i++;
  }
}

return 0;

public class Machine
{
  public List<int> Registers;
  public List<int> Program;
  private bool optimized;

  public Machine(List<int> registers, List<int> program)
  {
    Registers = registers;
    Program = program;
    optimized = program.SequenceEqual(new List<int> { 2,4,1,1,7,5,1,5,4,0,5,5,0,3,3,0 });
  }

  public List<int> Run()
  {
    if (optimized)
    {
      return RunOptimizedInputProgram();
    }
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

  private List<int> RunOptimizedInputProgram()
  {
    var outputs = new List<int>();
    do
    {
      int l = Registers[0] & 0b111;
      outputs.Add((l ^ 0b100 ^ (Registers[0] >> (l ^ 0b001))) & 0b111);
      Registers[0] >>= 3;
    } while (Registers[0] != 0);
    return outputs;
  }

  public Machine Copy() => new Machine(Registers.ToList(), Program.ToList());

  public override string ToString() => $"Registers: {string.Join(",", Registers)}, Program: {string.Join(",", Program)}";
}
