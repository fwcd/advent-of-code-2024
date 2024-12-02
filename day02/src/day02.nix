{ inputPath, lib ? import <nixpkgs/lib> }:
  let inherit (builtins) readFile;
      inherit (lib.strings) splitString;
  in
  let input = readFile inputPath;
      lines = splitString "\n" input;
  in "Lines: " + toString lines
