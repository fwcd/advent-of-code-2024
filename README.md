<!-- Automatically generated from README.md.gyb, do not edit directly! -->

# Advent of Code 2024

[![Run](https://github.com/fwcd/advent-of-code-2024/actions/workflows/run.yml/badge.svg)](https://github.com/fwcd/advent-of-code-2024/actions/workflows/run.yml)

My solutions to the [Advent of Code 2024](https://adventofcode.com/2024), written in 25 different programming languages.

- [x] [**Day 01**](day01): [PowerShell](day01/src/day01.ps1)

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

## Previous Years

My solutions to the previous challenges can be found here:

- [Advent of Code 2023](https://github.com/fwcd/advent-of-code-2023)
- [Advent of Code 2022](https://github.com/fwcd/advent-of-code-2022)
- [Advent of Code 2021](https://github.com/fwcd/advent-of-code-2021)
- [Advent of Code 2020](https://github.com/fwcd/advent-of-code-2020)
- [Advent of Code 2019](https://github.com/fwcd/advent-of-code-2019)
- [Advent of Code 2015](https://github.com/fwcd/advent-of-code-2015)
