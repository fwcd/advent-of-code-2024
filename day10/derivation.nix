{ stdenv, groovy }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day10";
    src = ./src;

    buildInputs = [
      groovy
    ];

    installPhase = ''
      mkdir -p $out/{bin,share}
      cp day10.groovy $out/share

      cat <<EOF > $out/bin/day10
      #!/bin/bash
      exec "${groovy.outPath}/bin/groovy" "\$(dirname "\$0")/../share/day10.groovy" "\$@"
      EOF

      chmod +x $out/bin/day10
    '';
  }
