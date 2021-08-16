{ lib, mkCoqDerivation, coq, version ? null
, equations, gaia, mathcomp-ssreflect, mathcomp-algebra, mathcomp-zify, paramcoq }:

with lib; mkCoqDerivation rec {
  pname = "hydra-battles-single";
  repo = "hydra-battles";
  inherit version;

  propagatedBuildInputs = [
    equations
    gaia
    mathcomp-ssreflect
    mathcomp-algebra
    mathcomp-zify
    paramcoq
  ];

  meta = {
    description = "Hydra Battles monorepo";
    license = licenses.mit;
  };
}
