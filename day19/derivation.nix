{ stdenv, python3, pygyat }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day19";
    src = ./src;

    buildInputs = [
      (python3.withPackages (ps: [ ps.numpy pygyat ]))
    ];

    installPhase = ''
      mkdir -p $out/bin
      cp day19.gyat $out/bin/day19
    '';
  }
