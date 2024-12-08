{ stdenv, pakcs }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day07";
    src = ./src;

    buildInputs = [
      pakcs
    ];

    buildPhase = ''
      pakcs :load Day07 :save main :quit
    '';

    installPhase = ''
      mkdir -p $out/bin
      cp Day07 $out/bin/day07
    '';
  }
