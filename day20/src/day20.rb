#!/usr/bin/env ruby

if ARGV.empty?
  puts "usage: day20 <path to input>"
  exit 1
end

matrix = File.readlines(ARGV[0])

puts "#{matrix}"
