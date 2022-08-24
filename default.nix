args@{
  rev    ? "963d27a0767422be9b8686a8493dcade6acee992"
, sha256 ? "0mvq8wxdns802b1gvjvalbvdsp3xjgm370bimdd93mwpspz0250p"

, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

let category-theory = coqPackages:
  with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
    name = "coq${coq.coq-version}-category-theory-${version}";
    version = "1.0";

    src = if pkgs ? coqFilterSource
          then pkgs.coqFilterSource [] ./.
          else ./.;

    buildInputs = [
      coq coq.ocaml coq.camlp5 coq.findlib equations
      dpdgraph
    ];
    enableParallelBuilding = true;

    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

    env = pkgs.buildEnv { inherit name; paths = buildInputs; };
    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.14" "8.15" "8.16" ];
    };
  };

in {
  inherit category-theory;
  category-theory_8_14 = category-theory "coqPackages_8_14";
  category-theory_8_15 = category-theory "coqPackages_8_15";
  category-theory_8_16 = category-theory "coqPackages_8_16";
}
