{ stdenv }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day15";
    src = ./src;

    buildPhase = ''
      mkdir -p out
      $CXX -o out/day15 day15.cpp
    '';

    installPhase = ''
      mkdir -p $out/bin
      cp out/day15 $out/bin
    '';
  }
