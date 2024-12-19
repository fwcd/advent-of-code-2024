#!/nix/store/10d7wwch6lly2jvpx2pi471vv5ny54y1-python3-3.12.7-env/bin/pygyat

import fileinput
import re

lines = [line.strip() for line in fileinput.input()]
towels = sorted(lines[0].split(', '))
designs = lines[2:]

def towel_combinations(design: str) -> int:
  if not design:
    return 1
  # TODO: Binary search
  candidates = [towel for towel in towels if design.startswith(towel)]
  return sum(towel_combinations(design[len(candidate):]) for candidate in candidates)

part1 = len([design for design in designs if towel_combinations(design) > 0])
print(f'Part 1: {part1}')

