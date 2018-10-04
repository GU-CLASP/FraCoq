{ nixpkgs ? import <nixpkgs> {} }:
with nixpkgs.pkgs;
stdenv.mkDerivation {
  name = "fracoq-env-0";
  buildInputs = [ coq haskellPackages.gf ];
}

