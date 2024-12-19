{ stdenv, jdk21 }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day18";
    src = ./src;

    buildInputs = [
      jdk21
    ];

    buildPhase = ''
      javac Day18.java
    '';

    installPhase = ''
      mkdir -p $out/{bin,share}
      cp *.class $out/share

      cat <<EOF > $out/bin/day18
      #!/bin/sh
      "${jdk21.outPath}/bin/java" -classpath "\$(dirname "\$0")/../share" Day18 "\$@"
      EOF

      chmod +x $out/bin/day18
    '';
  }
