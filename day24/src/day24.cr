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

def extract_int(prefix : String, values : Array(Tuple(String, Int64))) : Int
  values
    .select { |v| v[0].starts_with?(prefix) }
    .map { |v| v[1] }
    .reverse
    .reduce(0_i64) { |acc, b| (acc << 1) | b }
end

def is_x(s : String) : Bool
  s.starts_with?("x")
end

def is_y(s : String) : Bool
  s.starts_with?("y")
end

def is_z(s : String) : Bool
  s.starts_with?("z")
end

def is_coord(s : String) : Bool
  is_x(s) || is_y(s) || is_z(s)
end

def is_wrong(expr : Array(String), res : String) : Bool
  lhs, op, rhs = expr
  xor_gate = op == "XOR"
  or_gate = op == "OR"
  and_gate = op == "AND"
  
  [
    xor_gate && !is_coord(lhs) && !is_coord(rhs) && !is_coord(res),
    !xor_gate && is_z(res) && res != "z45",
  ].any?
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

  part2 = circuit
    .select { |c| is_wrong(c[0], c[1]) }
    .map { |c| c[1] }
    .join(",")
  puts "Part 2: #{part2}"
end
