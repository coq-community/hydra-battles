{ lib, mkCoqDerivation, coq, hydra-battles, gaia, mathcomp-zify }:

with lib; mkCoqDerivation rec {
  pname = "gaia-hydras";
  inherit (hydra-battles) version src;

  propagatedBuildInputs = [
    hydra-battles
    gaia
    mathcomp-zify
  ];

  useDune2 = true;

  meta = {
    description = "Comparison between ordinals in Gaia and Hydra battles";
    license = licenses.mit;
  };
}
