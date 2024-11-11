{ stdenv, powershell }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day01";
    src = ./src;

    buildInputs = [
      powershell
    ];

    installPhase = ''
      mkdir -p $out/bin
      cp day01.ps1 $out/bin/day01
    '';
  }
