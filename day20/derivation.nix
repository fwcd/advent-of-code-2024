{ stdenv, ruby }:
  stdenv.mkDerivation {
    name = "advent-of-code-2023-day20";
    src = ./src;

    buildInputs = [
      ruby
    ];

    installPhase = ''
      mkdir -p $out/bin
      cp day20.rb $out/bin/day20
      chmod +x $out/bin/day20
    '';
  }
