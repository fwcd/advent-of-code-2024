{ stdenv, cargo }:
  stdenv.mkDerivation {
    name = "advent-of-code-2023-day20";
    src = ./.;

    nativeBuildInputs = [
      cargo
    ];

    buildPhase = ''
      mkdir -p target
      CARGO_TARGET_DIR=target cargo build --release
    '';

    installPhase = ''
      mkdir -p $out/bin
      cp target/release/day20 $out/bin
    '';
  }
