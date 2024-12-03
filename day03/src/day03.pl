#!/usr/bin/env perl
use warnings;
use strict;

my ($inputFile) = @ARGV;
open(FH, '<', "$inputFile") or die $!;

while (<FH>) {
  my $line = $_;
  print "$line";
}

print "Hello World\n";
