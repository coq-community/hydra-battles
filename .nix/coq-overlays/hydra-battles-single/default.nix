{ lib, mkCoqDerivation, coq, version ? null
, coqprime, equations, gaia, LibHyps, mathcomp-ssreflect, mathcomp-algebra, mathcomp-zify, coq-elpi, zorns-lemma
, python3Packages, serapi, texlive, withMovies ? true, withTex ? true }:

with lib; mkCoqDerivation rec {
  pname = "hydra-battles-single";
  repo = "hydra-battles";
  inherit version;

  extraBuildInputs =
    (if withMovies
    then [ serapi python3Packages.alectryon ]
    else [])
    ++
    (if withTex then
      [ (texlive.combine {
        inherit (texlive)
          # With lualatex
          scheme-small
          # Extra packages
          caption
          doublestroke
          draftwatermark
          environ
          fancyvrb
          float
          fontspec
          lkproof
          mathdots
          mathtools
          mdframed
          needspace
          newunicodechar
          placeins
          synttree
          tcolorbox
          texments
          threeparttable
          tikzsymbols
          xcolor
          zref;
      }) ]
     else []);

  propagatedBuildInputs = [
    coqprime
    equations
    gaia
    LibHyps
    mathcomp-ssreflect
    mathcomp-algebra
    mathcomp-zify
    coq-elpi
    zorns-lemma
  ];

  meta = {
    description = "Hydra Battles monorepo";
    license = licenses.mit;
  };
}
