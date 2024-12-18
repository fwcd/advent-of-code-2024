{ stdenv, dotnet-runtime, dotnet-sdk, z3 }:
  stdenv.mkDerivation {
    name = "advent-of-code-2024-day17";
    src = ./src;

    nativeBuildInputs = [
      dotnet-sdk
    ];

    buildInputs = [
      dotnet-runtime
      z3
    ];

    # https://stackoverflow.com/questions/46065777/is-it-possible-to-compile-a-single-c-sharp-code-file-with-the-net-core-roslyn-c

    buildPhase = ''
      sdk="$(echo "${dotnet-sdk.outPath}"/sdk/*)"
      shared="$(echo "${dotnet-runtime.outPath}"/shared/Microsoft.NETCore.App/*)"
      dotnet "$sdk/Roslyn/bincore/csc.dll" \
        -r:"$shared/System.Private.CoreLib.dll" \
        -r:"$shared/System.Runtime.dll" \
        -r:"$shared/System.Runtime.InteropServices.dll" \
        -r:"$shared/System.Collections.dll" \
        -r:"$shared/System.ComponentModel.Primitives.dll" \
        -r:"$shared/System.Diagnostics.Process.dll" \
        -r:"$shared/System.Console.dll" \
        -r:"$shared/System.IO.dll" \
        -r:"$shared/System.Linq.dll" \
        day17.cs
    '';

    installPhase = ''
      mkdir -p $out/{bin,lib}
      cp day17.exe $out/lib

      cat <<EOF > $out/lib/day17.runtimeconfig.json
      {
        "runtimeOptions": {
          "framework": {
            "name": "Microsoft.NETCore.App",
            "version": "$(ls ${dotnet-runtime.outPath}/shared/Microsoft.NETCore.App)"
          }
        }
      }
      EOF

      cat <<EOF > $out/bin/day17
      #!/bin/bash
      exec "${dotnet-runtime.outPath}/bin/dotnet" "\$(dirname "\$0")/../lib/day17.exe" "\$@"
      EOF

      chmod +x $out/bin/day17
    '';
  }
