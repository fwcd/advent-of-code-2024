{ stdenv, rustc }:
  stdenv.mkDerivation {
    name = "advent-of-code-2023-day20";
    src = ./src;

    nativeBuildInputs = [
      rustc
    ];

    buildPhase = ''
      mkdir -p out
      rustc -o out/day20 -C opt-level=3 day20.rs
    '';

    installPhase = ''
      mkdir -p $out/bin
      cp out/day20 $out/bin/day20
    '';
  }
