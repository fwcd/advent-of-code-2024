{ stdenv, powershell }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day01";
    src = ./src;

    buildInputs = [
      powershell
    ];

    installPhase = ''
      mkdir -p $out/{bin,share}
      cp day01.ps1 $out/share

      cat <<EOF > $out/bin/day01
      exec pwsh "\$(dirname "\$0")/../share/day01.ps1" "$@"
      EOF
      chmod +x $out/bin/day01
    '';
  }
