{ stdenv }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day04";
    src = ./src;

    buildPhase = ''
      mkdir -p out
      $CC -o out/day04 day04.c
    '';

    installPhase = ''
      mkdir -p $out/bin
      cp out/day04 $out/bin
    '';
  }
