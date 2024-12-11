{ stdenv, lua }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day11";
    src = ./src;

    buildInputs = [
      lua
    ];

    installPhase = ''
      mkdir -p $out/{bin,share}
      cp day11.lua $out/share

      cat <<EOF > $out/bin/day11
      #!/bin/bash
      exec "${lua.outPath}/bin/lua" "\$(dirname "\$0")/../share/day11.lua" "\$@"
      EOF

      chmod +x $out/bin/day11
    '';
  }
