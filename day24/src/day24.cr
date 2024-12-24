BITS = 1

def translate_to_z3(vars, circuit) : String
  [
    *vars.map { |v| "(declare-const #{v[0]} (_ BitVec #{BITS}))" },
    *circuit.map { |c| "(declare-const #{c[1]} (_ BitVec #{BITS}))" },
    *vars.map { |v| "(assert (= #{v[0]} ((_ int2bv #{BITS}) #{v[1]})))" },
    *circuit.map { |c| "(assert (= #{c[1]} (bv#{c[0][1].downcase} #{c[0][0]} #{c[0][2]})))" },
    "(check-sat)",
    "(get-model)",
  ].join("\n")
end

def translate_to_dot(vars, circuit) : String
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

if ARGV.size == 0
  puts "Usage: day24 [--dot] <path to input>"
  exit 1
end

flags = ARGV.select { |a| a.starts_with?("--") }.to_s
positionals = ARGV.select { |a| !flags.includes?(a) }

path = positionals[0]
raw = File.read(path)

raw_vars, raw_circuit = raw.split("\n\n").map { |r| r.lines }
vars = raw_vars.map { |r| r.split(": ") }
circuit = raw_circuit.map do |r|
  raw_expr, res = r.split(" -> ")
  expr = raw_expr.split(' ')
  [expr, res]
end

if flags.includes?("--dot")
  puts translate_to_dot(vars, circuit)
else
  puts translate_to_z3(vars, circuit)
end
