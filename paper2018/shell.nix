# Non-reproducible "current" version:
# with (import <nixpkgs> {});
with import (fetchTarball https://github.com/NixOS/nixpkgs-channels/archive/nixos-18.03.tar.gz) {};


let orgEmacs = emacsWithPackages (with emacsPackagesNg; [org]);
    ghc = haskellPackages.ghcWithPackages (hp: with hp; [mtl split]);
in stdenv.mkDerivation {
  name = "docsEnv";
  shellHook = ''
        export LANG=en_US.UTF-8
        eval $(egrep ^export ${ghc}/bin/ghc)
       '';
  buildInputs = [ # orgEmacs
                  haskellPackages.lhs2tex
                  # ghc
                  biber
                  zip
                  (texlive.combine {
                       inherit (texlive)
                       biblatex
                       boondox
                       cmll
                       collection-fontsrecommended
                       comment
                       enumitem
                       environ
                       fontaxes
                       inconsolata
                       kastrup
                       latexmk
                       libertine
                       listings
                       lm
                       logreq
                       mweights
                       ncclatex
                       ncctools
                       newtx
                       newtxsf
                       newtxtt
                       newunicodechar
                       prftree
                       relsize
                       scheme-small wrapfig marvosym wasysym
                       stmaryrd lazylist polytable
                       todonotes
                       totpages
                       trimspaces
                       ucs
                       wasy cm-super unicode-math filehook lm-math capt-of
                       xargs
                       xstring ucharcat;
                     })
                ];
}
