{ stdenv, ghc }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day14";
    src = ./src;

    nativeBuildInputs = [
      ghc
    ];

    buildPhase = ''
      mkdir out
      ghc -o out/day14 Day14.hs
    '';

    installPhase = ''
      mkdir -p $out/bin
      cp out/day14 $out/bin
    '';
  }
