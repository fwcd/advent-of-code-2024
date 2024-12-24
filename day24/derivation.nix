{ stdenv, crystal, z3 }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day24";
    src = ./src;

    buildInputs = [
      crystal
      z3
    ];

    buildPhase = ''
      crystal build day24.cr
    '';

    installPhase = ''
      mkdir -p $out/bin
      cp day24 $out/bin/day24-impl

      cat <<EOF > $out/bin/day24
      #!/bin/bash
      PATH="${z3.outPath}/bin:\$PATH" "\$(dirname "\$0")/day24-impl" "\$@"
      EOF
      chmod +x $out/bin/day24
    '';
  }
