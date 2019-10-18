# { nixpkgs ? import <nixpkgs> {} }:
let distro = fetchTarball "https://github.com/NixOS/nixpkgs/archive/4a2340ff6bd0474d9a3e933f28b8568c59019b82.tar.gz";
             # fetchTarball https://github.com/NixOS/nixpkgs-channels/archive/nixos-18.09.tar.gz  # CGI broken here (and GF strangely depends on it)
             # fetchTarball https://github.com/NixOS/nixpkgs-channels/archive/nixos-19.09.tar.gz  # GF still broken (in its Setup.hs)
in with import distro {};
let myGHC = haskellPackages.ghcWithPackages
                     (haskellPackages: with haskellPackages; [
                       # libraries
                       parsek
                       # tools
                       cabal-install
                       mtl
                       split
                       logict
                       monadplus
                       scalpel pretty-show  # to scrape answers from fracas.xml
                       
                     ]);

in stdenv.mkDerivation {
  name = "fracoq-env-0";
  buildInputs = [
    coq haskellPackages.gf myGHC
  ];
  shellHook = ''
    export LANG=en_US.UTF-8
  '';
}


