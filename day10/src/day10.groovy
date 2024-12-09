#!/usr/bin/env groovy

if (args.length == 0) {
  println "Usage: day10 <path to input>"
  System.exit(1)
}

String input = new File(args[0]).text

println "Input: $input"
