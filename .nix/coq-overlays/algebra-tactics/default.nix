{ lib, mkCoqDerivation, coq, mathcomp-algebra,
  coq-elpi, mathcomp-zify, version ? null }:

with lib; mkCoqDerivation rec {
  pname = "algebra-tactics";
  owner = "math-comp";
  inherit version;
  defaultVersion = "1.0.0";
  release."1.0.0".sha256 = "sha256-kszARPBizWbxSQ/Iqpf2vLbxYc6AjpUCLnSNlPcNfls=";

  propagatedBuildInputs = [ mathcomp-algebra coq-elpi mathcomp-zify ];

  meta = {
    description = "A Library for algebra tactics";
    maintainers = with maintainers; [ cohencyril ];
  };
}
