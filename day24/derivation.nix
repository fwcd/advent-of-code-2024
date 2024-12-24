{ stdenv, crystal }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day24";
    src = ./src;

    buildInputs = [
      crystal
    ];

    buildPhase = ''
      crystal build day24.cr
    '';

    installPhase = ''
      mkdir -p $out/bin
      cp day24 $out/bin
    '';
  }
