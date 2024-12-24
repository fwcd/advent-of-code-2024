{ stdenv, dart }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day22";
    src = ./src;

    nativeBuildInputs = [
      dart
    ];

    buildPhase = ''
      mkdir -p {tmpbin,out}

      # Ad-hoc signing is required on arm64 macOS, this fixes it (not sure why
      # the dart derivation doesn't provide it)
      ${if stdenv.isDarwin then ''
        ln -s /usr/bin/codesign tmpbin/codesign
      '' else ""}

      PATH="./tmpbin:$PATH" dart compile exe day22.dart -o out/day22
    '';

    installPhase = ''
      mkdir -p $out/bin
      cp out/day22 $out/bin
    '';
  }
