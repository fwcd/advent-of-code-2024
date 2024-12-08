{ stdenv, php }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day08";
    src = ./src;

    buildInputs = [
      php
    ];

    installPhase = ''
      mkdir -p $out/{bin,share}
      cp day08.php $out/share

      cat <<EOF > $out/bin/day08
      #!/bin/bash
      exec "${php.outPath}/bin/php" -d memory_limit=1G "\$(dirname "\$0")/../share/day08.php" "\$@"
      EOF

      chmod +x $out/bin/day08
    '';
  }
