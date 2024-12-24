{ stdenv, dart }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day22";
    src = ./src;

    buildInputs = [
      dart
    ];

    installPhase = ''
      mkdir -p $out/{bin,share}
      cp day22.dart $out/share

      cat <<EOF > $out/bin/day22
      exec "${dart.outPath}/bin/dart" run "\$(dirname "\$0")/../share/day22.dart" "\$@"
      EOF
      chmod +x $out/bin/day22
    '';
  }
