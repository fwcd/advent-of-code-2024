{ lib, pkgs, stdenv }:
  with pkgs.python3Packages;

  let
    pname = "pygyat";
    version = "1.0.7";
  in
    buildPythonPackage {
      inherit pname version;
      src = pkgs.fetchPypi {
        inherit pname version;
        sha256 = "v82QZXsgr1DUQmnetvFsfPs+yCIyoWSg8qkocCwGJ3E=";
      };
    }
