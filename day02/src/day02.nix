{ inputPath, lib ? import <nixpkgs/lib> }:
  let inherit (builtins) head tail length readFile;
      inherit (lib.lists) all any count filter range zipListsWith;
      inherit (lib.strings) splitString toInt stringLength;
      inherit (lib.trivial) flip;
  in
  let abs        = x: if x >= 0 then x else -x;
      compose    = f: g: x: f (g x);
      dropNth    = n: xs: if n == 0 then tail xs else [(head xs)] ++ dropNth (n - 1) (tail xs);
      removeOne  = r: map (flip dropNth r) (range 0 (length r - 1));
      input      = readFile inputPath;
      isNonEmpty = s: stringLength s > 0;
      lines      = filter isNonEmpty (splitString "\n" input);
      reports    = map (compose (map toInt) (splitString " ")) lines;
      isSafe1    = r: let diffs = zipListsWith (x: y: x - y) r (tail r);
                      in (all (x: x > 0) diffs || all (x: x < 0) diffs)
                         && all (x: x >= 1 && x <= 3) (map abs diffs);
      isSafe2    = compose (any isSafe1) removeOne;
      part1      = count isSafe1 reports;
      part2      = count isSafe2 reports;
  in "Part 1: " + toString part1 + ", Part 2: " + toString part2
