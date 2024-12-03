#!/usr/bin/env perl
use warnings;
use strict;

my ($inputFile) = @ARGV;

if (not defined $inputFile) {
  die "Usage: day03 <path to input> \n";
}

open(FH, '<', "$inputFile") or die $!;

my $part1 = 0;

while (<FH>) {
  while ($_ =~ /mul\((\d+),(\d+)\)/g) {
    $part1 += $1 * $2;
  }
}

print "Part 1: $part1\n";
