{ stdenv, swi-prolog }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day05";
    src = ./src;

    buildInputs = [
      swi-prolog
    ];

    installPhase = ''
      mkdir -p $out/{bin,share}
      cp day05.pl $out/share

      cat <<EOF > $out/bin/day05
      #!/bin/bash
      exec "${swi-prolog.outPath}/bin/swipl" -s "\$(dirname "\$0")/../share/day05.pl" -t main --quiet -- "\$0" "\$@"
      EOF

      chmod +x $out/bin/day05
    '';
  }
