{ stdenv, darwin, clang, gnustep }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day12";
    src = ./src;

    buildInputs = if stdenv.isDarwin then [
      darwin.apple_sdk.frameworks.Foundation
    ] else [
      clang
      gnustep.base # TODO: Investigate how to make this work on Linux
    ];

    buildPhase = ''
      mkdir -p out
      clang -fobjc-arc -Ofast -framework Foundation -o out/day12 day12.m
    '';

    installPhase = ''
      mkdir -p $out/bin
      cp out/day12 $out/bin
    '';
  }
