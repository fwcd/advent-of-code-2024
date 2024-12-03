{ stdenv, perl }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day03";
    src = ./src;

    installPhase = ''
      mkdir -p $out/bin
      cp day03.pl $out/bin/day03
    '';
  }
