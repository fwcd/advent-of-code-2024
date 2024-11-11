<!-- Automatically generated from README.md.gyb, do not edit directly! -->

# Advent of Code 2024

[![Run](https://github.com/fwcd/advent-of-code-2024/actions/workflows/run.yml/badge.svg)](https://github.com/fwcd/advent-of-code-2024/actions/workflows/run.yml)

My solutions to the [Advent of Code 2024](https://adventofcode.com/2024), written in 25 different programming languages.

- [ ] [**Day 01**](day01): [PowerShell](day01/src/day01.ps1)

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

- Visualize the input with GraphViz (day [8](day08), [20](day20), [23](day23), [25](day25))
- Some puzzles are actually reverse-engineering exercises and rely on undocumented input constraints to be solved efficiently or even feasibly at all (day [8](day08), [20](day20), [23](day23))
- Take the [LCM](https://en.wikipedia.org/wiki/Least_common_multiple) to solve cycle alignment problems (day [8](day08), [20](day20))
  - If there are offsets, use the [CRT](https://en.wikipedia.org/wiki/Chinese_remainder_theorem) ([like in previous years](https://github.com/fwcd/advent-of-code-2020/blob/18c3ba9820cb52627366a632ccaab233a6d9f563/day13/src/day13.c#L39-L59))
- Binary counters can elegantly be modeled as chains of flip flop (day [20](day20))
- Cross products can be surprisingly useful to turn the most nonlinear-looking problems into linear equations (day [24](day24))

## Previous Years

My solutions to the previous challenges can be found here:

- [Advent of Code 2023](https://github.com/fwcd/advent-of-code-2023)
- [Advent of Code 2022](https://github.com/fwcd/advent-of-code-2022)
- [Advent of Code 2021](https://github.com/fwcd/advent-of-code-2021)
- [Advent of Code 2020](https://github.com/fwcd/advent-of-code-2020)
- [Advent of Code 2019](https://github.com/fwcd/advent-of-code-2019)
- [Advent of Code 2015](https://github.com/fwcd/advent-of-code-2015)
