{ stdenv, kotlin }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day16";
    src = ./src;

    buildInputs = [
      kotlin
    ];

    installPhase = ''
      mkdir -p $out/{bin,share}
      cp day16.kts $out/share

      cat <<EOF > $out/bin/day16
      exec "${kotlin.outPath}/bin/kotlin" "\$(dirname "\$0")/../share/day16.kts" "\$@"
      EOF
      chmod +x $out/bin/day16
    '';
  }
