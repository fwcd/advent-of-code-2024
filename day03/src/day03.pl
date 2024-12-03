#!/usr/bin/env perl
use warnings;
use strict;

my ($inputFile) = @ARGV;

if (not defined $inputFile) {
  die "Usage: day03 <path to input> \n";
}

open(FH, '<', "$inputFile") or die $!;

while (<FH>) {
  while ($_ =~ /mul\((\d+),(\d+)\)/g) {
    print "mul($1, $2)\n";
  }
  print "\n";
}

print "Hello World\n";
