{ stdenv, zig }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day06";
    src = ./src;
    sourceRoot = ".";

    nativeBuildInputs = [
      zig
    ];

    buildPhase = ''
      mkdir out cache

      zig build-exe --global-cache-dir cache -femit-bin=out/day06 -O ReleaseSafe src/day06.zig
    '';

    installPhase = ''
      mkdir -p $out/bin
      cp out/day06 $out/bin
    '';
  }
