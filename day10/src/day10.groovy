#!/usr/bin/env groovy

if (args.length == 0) {
  println "Usage: day10 <path to input>"
  System.exit(1)
}

List<List<Integer>> input = new File(args[0]).text
  .lines()
  .map { it.chars().map { it - (int) '0' }.toList() }
  .toList()

println "Input: $input"
