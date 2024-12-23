{ swift, swiftPackages }:
  swiftPackages.stdenv.mkDerivation {
    name = "advent-of-code-2024-day25";
    src = ./src;

    nativeBuildInputs = [
      swift
      swiftPackages.Foundation
    ];

    buildPhase = ''
      mkdir -p out

      # Explicitly set the target since swiftc seems to otherwise use an older
      # macOS version that doesn't support all of the regex stuff.
      target="$(swiftc --version 2>/dev/null | grep Target | sed 's/Target: //g' | sed "s/-pc-linux-/-unknown-linux-/g")"
      swiftc -target "$target" -o out/day25 day25.swift
    '';

    installPhase = ''
      mkdir -p $out/bin
      cp out/day25 $out/bin
    '';
  }
