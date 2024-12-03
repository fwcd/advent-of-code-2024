#!/usr/bin/env perl
use warnings;
use strict;

my ($inputFile) = @ARGV;

if (not defined $inputFile) {
  die "Usage: day03 <path to input> \n";
}

open(FH, '<', "$inputFile") or die $!;

my $part1 = 0;
my $part2 = 0;
my $enabled = 1;

while (<FH>) {
  while ($_ =~ /(do(n't)?)\(\)|mul\((\d+),(\d+)\)/g) {
    if (defined $1) {
      $enabled = not defined $2;
    } else {
      my $product = $3 * $4;
      $part1 += $product;
      if ($enabled) {
        $part2 += $product;
      }
    }
  }
}

print "Part 1: $part1\n";
print "Part 2: $part2\n";
