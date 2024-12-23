{ stdenv, scala }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day21";
    src = ./src;

    buildInputs = [
      scala
    ];

    installPhase = ''
      mkdir -p $out/{bin,share}
      cp day21.scala $out/share

      cat <<EOF > $out/bin/day21
      exec "${scala.outPath}/bin/scala" "\$(dirname "\$0")/../share/day21.scala" "\$@"
      EOF
      chmod +x $out/bin/day21
    '';
  }
