{ stdenv, python3 }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day13";
    src = ./src;

    buildInputs = [
      (python3.withPackages (ps: [ ps.numpy ]))
    ];

    installPhase = ''
      mkdir -p $out/bin
      cp day13.py $out/bin/day13
    '';
  }
