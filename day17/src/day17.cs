using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Linq;
using System.IO;
using System.Text.RegularExpressions;

if (args.Length == 0)
{
  Console.WriteLine("usage: day17 <path to input>");
  return 1;
}

string[] rawChunks = File.ReadAllText(args[0]).Trim().Split("\n\n");
List<long> registers = rawChunks[0].Split("\n").Select(l => long.Parse(l.Split(": ")[1])).ToList();
List<int> program = rawChunks[1].Split(" ")[1].Split(",").Select(int.Parse).ToList();
Machine machine = new Machine(registers, program);

{
  List<long> output = machine.Copy().Run();
  Console.WriteLine($"Part 1: {string.Join(",", output)}");
}

{
  long? solution = null;
  long minSolution = -1;
  
  while ((solution = machine.SolveQuine(solution)) != null) {
    Console.WriteLine($"Found solution: {solution.Value}");
    minSolution = solution.Value;
  }

  Console.WriteLine($"Part 2: {minSolution}");

  machine.Registers[0] = minSolution;
  List<long> output = machine.Run();
  Console.WriteLine($"(outputs {string.Join(",", output)})");
}

return 0;

public class Machine
{
  public List<long> Registers;
  public List<int> Program;
  private bool optimized;

  public Machine(List<long> registers, List<int> program)
  {
    Registers = registers;
    Program = program;
    optimized = program.SequenceEqual(new List<int> { 2,4,1,1,7,5,1,5,4,0,5,5,0,3,3,0 });
  }

  public List<long> Run()
  {
    if (optimized)
    {
      return RunOptimizedInputProgram();
    }
    var outputs = new List<long>();
    for (int i = 0; i < Program.Count;)
    {
      int opcode = Program[i];
      int operand = Program[i + 1];
      long combo = operand >= 4 && operand < 7 ? Registers[operand - 4] : operand;
      bool jumped = false;

      // Uncomment to debug-log the executed instructions
      // Console.WriteLine($"{(new string[] {"adv", "bxl", "bst", "jnz", "bxc", "out", "bdv", "cdv"})[opcode]} {operand}: {string.Join("", Program.Take(i))}\x1B[4m{Program[i]}\x1B[0m{string.Join("", Program.Skip(i + 1))} - {string.Join(",", Registers)}");

      switch (opcode)
      {
        case 0: // adv (A divide)
          Registers[0] >>= (int) combo;
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
        case 4: // bxc (B xor C)
          Registers[1] ^= Registers[2];
          break;
        case 5: // out (output)
          outputs.Add(combo & 0b111);
          break;
        case 6: // bdv (B divide)
          Registers[1] = Registers[0] >> (int) combo;
          break;
        case 7: // cdv (C divide)
          Registers[2] = Registers[0] >> (int) combo;
          break;
      }
      if (!jumped)
      {
        i += 2;
      }
    }
    return outputs;
  }

  private List<long> RunOptimizedInputProgram()
  {
    var outputs = new List<long>();
    do
    {
      long l = Registers[0] & 0b111;
      outputs.Add((l ^ 0b100 ^ (Registers[0] >> (int) (l ^ 0b001))) & 0b111);
      Registers[0] >>= 3;
    } while (Registers[0] != 0);
    return outputs;
  }

  public long? SolveQuine(long? upperBound = null)
  {
    // For part 2 we use an approach inspired by a Reddit post by deferring the
    // heavy-lifting to the Z3 SMT solver:
    // https://www.reddit.com/r/adventofcode/comments/1hgk9nt/2024_day_17_part_2_this_feels_like_cheating/
    //
    // The approach is to encode the instructions as assertions/equations in an
    // SSA-like form (creating a new variable for every assignment), unroll the
    // loop/jump for enough iterations and then simply solve for a0.
    //
    // We use bitvector arithmetic as documented here:
    // https://microsoft.github.io/z3guide/docs/theories/Bitvectors/

    int unrolledIterations = Program.Count - 1;
    int bits = 64;

    var registerVars = new List<string> { "a", "b", "c" };
    var registerCounts = registerVars.Select(_ => 0).ToList();
    var smtAssertions = new List<string>();
    int outputs = 0;
    int iterations = 0;

    string Long2Bv(long value) => $"((_ int2bv {bits}) {value})";
    string Register(int i, int offset = 0) => $"{registerVars[i]}{registerCounts[i] + offset}";

    for (int i = 0; i < Program.Count;)
    {
      int opcode = Program[i];
      int operand = Program[i + 1];
      string literal = Long2Bv(operand);
      string combo = operand >= 4 && operand < 7 ? Register(operand - 4) : literal;
      bool jumped = false;
      switch (opcode)
      {
        case 0: // adv (A divide)
          smtAssertions.Add($"(assert (= {Register(0, 1)} (bvlshr {Register(0)} {combo})))");
          registerCounts[0]++;
          break;
        case 1: // bxl (B xor literal)
          smtAssertions.Add($"(assert (= {Register(1, 1)} (bvxor {Register(1)} {literal})))");
          registerCounts[1]++;
          break;
        case 2: // bst (B store?)
          smtAssertions.Add($"(assert (= {Register(1, 1)} (bvand {combo} {Long2Bv(0b111)})))");
          registerCounts[1]++;
          break;
        case 3: // jnz (jump not zero)
          if (iterations < unrolledIterations && i != operand)
          {
            i = operand;
            jumped = true;
            iterations++;
          }
          else
          {
            // After the unrolled iterations we want the jump to fail so the loop exits
            smtAssertions.Add($"(assert (= {Long2Bv(0)} {Register(0)}))");
          }
          break;
        case 4: // bxc (B xor C)
          smtAssertions.Add($"(assert (= {Register(1, 1)} (bvxor {Register(1)} {Register(2)})))");
          registerCounts[1]++;
          break;
        case 5: // out (output)
          smtAssertions.Add($"(assert (= (bvand {combo} {Long2Bv(0b111)}) {Long2Bv(Program[outputs])}))");
          outputs++;
          break;
        case 6: // bdv (B divide)
          smtAssertions.Add($"(assert (= {Register(1, 1)} (bvlshr {Register(0)} {combo})))");
          registerCounts[1]++;
          break;
        case 7: // cdv (C divide)
          smtAssertions.Add($"(assert (= {Register(2, 1)} (bvlshr {Register(0)} {combo})))");
          registerCounts[2]++;
          break;
      }
      if (!jumped)
      {
        i += 2;
      }
    }

    if (upperBound != null)
    {
      smtAssertions.Add($"(assert (bvult a0 {Long2Bv(upperBound.Value)}))");
    }

    var smtDeclarations = registerCounts.Zip(registerVars).SelectMany(p => Enumerable.Range(0, p.First + 1).Select(i => $"(declare-const {p.Second}{i} (_ BitVec {bits}))")).ToList();
    var smtTrailer = new List<string> { "(check-sat)", "(get-model)" };
    var smtProgram = smtDeclarations.Concat(smtAssertions).Concat(smtTrailer).ToList();

    // Uncomment to debug-log the generated SMT-LIB program
    // Console.WriteLine(string.Join("\n", smtProgram));

    using (var process = new Process())
    {
      var startInfo = new ProcessStartInfo();
      startInfo.FileName = "z3";
      startInfo.Arguments = "-smt2 -in";
      startInfo.RedirectStandardInput = true;
      startInfo.RedirectStandardOutput = true;

      process.StartInfo = startInfo;
      process.Start();

      using (var z3Input = process.StandardInput)
      {
        foreach (string line in smtProgram)
        {
          z3Input.WriteLine(line);
        }
      }

      process.WaitForExit();

      using (var z3Output = process.StandardOutput)
      {
        string output = z3Output.ReadToEnd().Replace("\n", " ");
        foreach (Match match in Regex.Matches(output, @$"\(define-fun\s+(?<name>\w+)\s+\(\)\s+\(_\s+BitVec\s+{bits}\)\s+#x(?<hex>[0-9a-f]+)\)"))
        {
          // Uncomment to debug-log the Z3-solved variables
          // Console.WriteLine(match);

          if (match.Groups["name"].Value == "a0")
          {
            return Convert.ToInt64(match.Groups["hex"].Value, 16);
          }
        }
      }
      return null;
    }
  }

  public Machine Copy() => new Machine(Registers.ToList(), Program.ToList());

  public override string ToString() => $"Registers: {string.Join(",", Registers)}, Program: {string.Join(",", Program)}";
}
