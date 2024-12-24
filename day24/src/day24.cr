if ARGV.size == 0
  puts "Usage: day24 <path to input>"
  exit 1
end

path = ARGV[0]
lines = File.read_lines(path)

puts "Lines: #{lines}"
