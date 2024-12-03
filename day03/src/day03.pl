#!/usr/bin/env perl
use warnings;
use strict;

my ($inputFile) = @ARGV;

if (not defined $inputFile) {
  die "Usage: day03 <path to input> \n";
}

open(FH, '<', "$inputFile") or die $!;

while (<FH>) {
  my $line = $_;
  print "$line";
}

print "Hello World\n";
