<!-- Automatically generated from README.md.gyb, do not edit directly! -->

# Advent of Code 2024

[![Run](https://github.com/fwcd/advent-of-code-2024/actions/workflows/run.yml/badge.svg)](https://github.com/fwcd/advent-of-code-2024/actions/workflows/run.yml)

My solutions to the [Advent of Code 2024](https://adventofcode.com/2024), written in 25 different programming languages.

- [x] [**Day 01**](day01): [PowerShell](day01/src/day01.ps1)
- [x] [**Day 02**](day02): [Nix](day02/src/day02.nix)
- [x] [**Day 03**](day03): [Perl](day03/src/day03.pl)
- [x] [**Day 04**](day04): [C](day04/src/day04.c)
- [x] [**Day 05**](day05): [Prolog](day05/src/day05.pl)
- [x] [**Day 06**](day06): [Zig](day06/src/day06.zig)
- [x] [**Day 07**](day07): [Curry](day07/src/Day07.curry)
- [x] [**Day 08**](day08): [PHP](day08/src/day08.php)
- [x] [**Day 09**](day09): [JavaScript](day09/src/day09.js)
- [x] [**Day 10**](day10): [Groovy](day10/src/day10.groovy)
- [x] [**Day 11**](day11): [Lua](day11/src/day11.lua)
- [x] [**Day 12**](day12): [Objective-C](day12/src/day12.m)
- [x] [**Day 13**](day13): [Python](day13/src/day13.py)
- [x] [**Day 14**](day14): [Haskell](day14/src/Day14.hs)
- [x] [**Day 15**](day15): [C++](day15/src/day15.cpp)
- [x] [**Day 16**](day16): [Kotlin](day16/src/day16.kts)
- [x] [**Day 17**](day17): [C#](day17/src/day17.cs) (using Z3 to solve part 2)
- [x] [**Day 18**](day18): [Java](day18/src/Day18.java)
- [x] [**Day 19**](day19): [PyGyat](day19/src/day19.gyat)
- [x] [**Day 20**](day20): [Rust](day20/src/day20.rs)
- [x] [**Day 21**](day21): [Scala](day21/src/day21.scala)
- [x] [**Day 22**](day22): [Dart](day22/src/day22.dart)
- [x] [**Day 23**](day23): [Go](day23/src/day23.go)
- [x] [**Day 24**](day24): [Crystal](day24/src/day24.cr)
- [ ] [**Day 25**](day25): [Swift](day25/src/day25.swift)

## Development

The programs are packaged with [Nix](https://nixos.org/), a functional package manager for Linux and macOS that focuses on reproducible builds. This makes it easy to build the programs, both locally and CI, without relying on system packages.

To build one of the days, `cd` into the corresponding directory and build and/or run the Nix flake. For example, to run day 1, use the following commands:

```sh
cd day01
nix run . resources/input.txt
```

Every day is packaged up to take exactly one command-line argument, the input file, and usually includes the demo input from the exercise too.

> [!TIP]
> The build environment can be added to the current `PATH` using `nix develop`. This is useful to manually run the compiler.

## Lessons Learned

- Dijkstra, Dijkstra, Dijkstra (day [16](day16), [18](day18), [20](day20))
- The [Lanternfish](https://adventofcode.com/2021/day/6)-style counting trick seems to be useful (day [11](day11), [21](day21))
  - See e.g. also [this Reddit post](https://www.reddit.com/r/adventofcode/comments/1hbn15t/2024_day_11_is_this_a/) or [this one](https://www.reddit.com/r/adventofcode/comments/1hk3wwd/2024_day_21_history_repeats_itself/)
- Plot graph-like inputs with GraphViz (day [23](day23), [24](day24))
  - In some cases, the solution is visually apparent in the plot (23.2)
- Use bigger ints, ideally at least 64-bits (day [17](day17), [21](day21), [24](day24))

## Previous Years

My solutions to the previous challenges can be found here:

- [Advent of Code 2023](https://github.com/fwcd/advent-of-code-2023)
- [Advent of Code 2022](https://github.com/fwcd/advent-of-code-2022)
- [Advent of Code 2021](https://github.com/fwcd/advent-of-code-2021)
- [Advent of Code 2020](https://github.com/fwcd/advent-of-code-2020)
- [Advent of Code 2019](https://github.com/fwcd/advent-of-code-2019)
- [Advent of Code 2015](https://github.com/fwcd/advent-of-code-2015)
