BITS = 1

alias Vars = Array(Tuple(String, Int64))
alias Circuit = Array(Tuple(Array(String), String))

def parse_input(raw : String) : Tuple(Vars, Circuit)
  raw_vars, raw_circuit = raw.split("\n\n").map { |r| r.lines }
  vars = raw_vars.map do |r|
    var, raw_value = r.split(": ")
    value = raw_value.to_i64
    {var, value}
  end
  circuit = raw_circuit.map do |r|
    raw_expr, res = r.split(" -> ")
    expr = raw_expr.split(' ')
    {expr, res}
  end
  {vars, circuit}
end

def translate_to_z3(vars : Vars, circuit : Circuit) : String
  [
    *vars.map { |v| "(declare-const #{v[0]} (_ BitVec #{BITS}))" },
    *circuit.map { |c| "(declare-const #{c[1]} (_ BitVec #{BITS}))" },
    *vars.map { |v| "(assert (= #{v[0]} ((_ int2bv #{BITS}) #{v[1]})))" },
    *circuit.map { |c| "(assert (= #{c[1]} (bv#{c[0][1].downcase} #{c[0][0]} #{c[0][2]})))" },
    "(check-sat)",
    "(get-model)",
  ].join("\n")
end

def translate_to_dot(vars : Vars, circuit : Circuit) : String
  [
    "digraph {",
    *circuit.flat_map do |c|
      [
        "  #{c[0][0]} -> #{c[1]};",
        "  #{c[0][2]} -> #{c[1]};",
      ]
    end,
    "}",
  ].join("\n")
end

def solve(z3_src : String) : Array(Tuple(String, Int64))
  z3_proc = Process.new("z3", ["-smt2", "-in"], input: :pipe, output: :pipe)
  z3_proc.input.puts(z3_src)
  z3_proc.input.close

  z3_output = z3_proc.output.gets_to_end.gsub("\n", "")
  output_vars = [] of Tuple(String, Int64)
  z3_output.scan(/\(define-fun\s+(\w+)\s+\(\)\s+\(_\s+BitVec\s+\d+\)\s+#[xb](\d+)\)/).each do |match|
    output_vars << {match[1], match[2].to_i64}
  end
  output_vars.sort!

  output_vars
end

def swap(i : Int, j : Int, circuit : Circuit) : Circuit
  new_circuit = [*circuit]
  new_circuit[i] = {circuit[i][0], circuit[j][1]}
  new_circuit[j] = {circuit[j][0], circuit[i][1]}
  new_circuit
end

def flip!(i : Int, vars : Vars)
  vars[i] = {vars[i][0], 1_i64 - vars[i][1]}
end

RNG = Random.new

def randomize!(vars : Vars)
  (0...vars.size).each do |i|
    if RNG.next_bool
      flip!(i, vars)
    end
  end
end

def find_best_swap(vars : Vars, circuit : Circuit, visited : Set(String)) : Tuple(Int32, Int32)
  output_vars = solve(translate_to_z3(vars, circuit))
  x = extract_int("x", output_vars)
  y = extract_int("y", output_vars)

  smallest = 1000000
  smallest_i = -1
  smallest_j = -1
  (0...circuit.size)
    .flat_map do |i|
      # Baed on manual analysis of the GraphViz plot, the swaps seem to be relatively local
      ({i + 1, circuit.size - 1}.min..{i + 5, circuit.size - 1}.min)
        .select { |j| i != j && !visited.includes?(circuit[i][1]) && !visited.includes?(circuit[j][1]) }
        .map { |j| {i, j} }
    end
    .each do |pair|
      i, j = pair
      max_d = 0
      max_d_z = 0
      vars = [*vars]
      4.times do
        randomize!(vars)
        output_vars = solve(translate_to_z3(vars, swap(i, j, circuit)))
        x = extract_int("x", output_vars)
        y = extract_int("y", output_vars)
        z = extract_int("z", output_vars)
        d = hamming_dist(x + y, z)
        if d > max_d
          max_d = d
          max_d_z = z
        end
      end
      if max_d < smallest
        puts "#{i}, #{j} -> #{max_d}"
        smallest = max_d
        smallest_i = i
        smallest_j = j
      end
    end
  {smallest_i, smallest_j}
end

def hamming_dist(n : Int64, m : Int64) : Int64
  (n ^ m).popcount
end

def extract_int(prefix : String, values : Array(Tuple(String, Int64))) : Int
  values
    .select { |v| v[0].starts_with?(prefix) }
    .map { |v| v[1] }
    .reverse
    .reduce(0_i64) { |acc, b| (acc << 1) | b }
end

if ARGV.size == 0
  puts "Usage: day24 [--dump-dot] [--dump-z3] <path to input>"
  exit 1
end

flags = ARGV.select { |a| a.starts_with?("--") }.to_s
positionals = ARGV.select { |a| !flags.includes?(a) }

path = positionals[0]
raw = File.read(path)
vars, circuit = parse_input(raw)

if flags.includes?("--dump-dot")
  puts translate_to_dot(vars, circuit)
elsif flags.includes?("--dump-z3")
  puts translate_to_z3(vars, circuit)
else
  part1 = extract_int("z", solve(translate_to_z3(vars, circuit)))
  puts "Part 1: #{part1}"

  # For part 2 we use a probabilistic algorithm that tries to find the best
  # swaps for randomized inputs.

  swapped = [] of String
  visited = Set(String).new

  4.times do |n|
    i, j = find_best_swap(vars, circuit, visited)

    [circuit[i][1], circuit[j][1]].each do |v|
      swapped << v
      visited << v
    end

    circuit = swap(i, j, circuit)

    puts "#{i}, #{j}"
  end
  swapped.sort!
  puts "Part 2: #{swapped.join(",")}"
end
