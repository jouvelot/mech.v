{
  pkgs ? import (fetchTarball "https://github.com/NixOS/nixpkgs/archive/5c7a370a208d93d458193fc05ed84ced0ba7f387.tar.gz") {}
}:
pkgs.stdenv.mkDerivation rec {

  name = "coq-vcg";
  version = "0.0.1";

  # EJGA: There is a way to make the install from the binary cache,
  # but I don't know enough nix to make this work.
  buildInputs = [
    pkgs.dune_2
    # This seems very heavy too.
    # pkgs.ocaml-ng.ocamlPackages_4_11.ocaml
    pkgs.coqPackages_8_13.coq
    # This will recompile math-comp :S, see above note
    pkgs.coqPackages_8_13.mathcomp
  ];

  src =
    with builtins; filterSource
      (path: _:
        !elem (baseNameOf path) [".git" "_build" "nix"]) ./.;

  # This call make all
  buildFlags = "all";

  # Not working needs a bit more work
  # installTargets = "install";
}
