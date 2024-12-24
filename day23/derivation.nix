{ stdenv, go }:
  stdenv.mkDerivation {
    name = "advent-of-code-2023-day23";
    src = ./src;
    sourceRoot = ".";

    nativeBuildInputs = [
      go
    ];

    buildPhase = ''
      mkdir out cache

      GOCACHE=$PWD/cache go build -o out/day23 src/day23.go
    '';

    installPhase = ''
      mkdir -p $out/bin
      cp out/day23 $out/bin
    '';
  }
