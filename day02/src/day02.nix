{ inputPath, lib ? import <nixpkgs/lib> }:
  let inherit (builtins) length readFile;
      inherit (lib.lists) all count filter head tail zipListsWith;
      inherit (lib.strings) splitString toInt stringLength;
  in
  let abs        = x: if x >= 0 then x else -x;
      compose    = f: g: x: f (g x);
      input      = readFile inputPath;
      isNonEmpty = s: stringLength s > 0;
      lines      = filter isNonEmpty (splitString "\n" input);
      reports    = map (compose (map toInt) (splitString " ")) lines;
      isSafe     = r: let diffs = zipListsWith (x: y: x - y) r (tail r);
                      in (all (x: x > 0) diffs || all (x: x < 0) diffs)
                         && all (x: x >= 1 && x <= 3) (map abs diffs);
      part1      = count isSafe reports;
  in "Part 1: " + toString part1
