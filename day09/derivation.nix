{ stdenv, nodejs }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day09";
    src = ./src;

    buildInputs = [
      nodejs
    ];

    installPhase = ''
      mkdir -p $out/bin
      cp day09.js $out/bin/day09
    '';
  }
