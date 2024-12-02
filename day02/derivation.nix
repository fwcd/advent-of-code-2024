{ stdenv, coreutils }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day02";
    src = ./src;

    buildInputs = [
      coreutils # for realpath
    ];

    installPhase = ''
      mkdir -p $out/{bin,share}
      cp day02.nix $out/share
      
      cat <<EOF > $out/bin/day02
      #!/bin/bash
      set -e
      if [ -z "\$1" ]; then
        echo "Usage: \$0 <path to input>"
        exit 1
      fi
      exec nix-instantiate --eval --show-trace --strict --arg inputPath "\"\$(${coreutils.outPath}/bin/realpath \$1)\"" "\$(dirname "\$0")/../share/day02.nix"
      EOF

      chmod +x $out/bin/day02
    '';
  }
