if ARGV.size == 0
  puts "Usage: day24 <path to input>"
  exit 1
end

path = ARGV[0]
raw = File.read(path)

raw_vars, raw_circuit = raw.split("\n\n").map { |r| r.lines }
vars = raw_vars.map { |r| r.split(": ") }
circuit = raw_circuit.map do |r|
  raw_expr, res = r.split(" -> ")
  expr = raw_expr.split(' ')
  [expr, res]
end

puts "Vars: #{vars}, circuit: #{circuit}"
