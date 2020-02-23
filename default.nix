{ packages ? "coqPackages_8_11"

, rev      ? "cc1ae9f21b9e0ce998e706a3de1bad0b5259f22d"
, sha256   ? "0zjafww05h50ncapw51b5qxgbv9prjyag0j22jnfc3kcs5xr4ap0"

, pkgs     ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
    overlays = [
      (self: super:
       let
         nixpkgs = { rev, sha256 }:
           import (super.fetchFromGitHub {
             owner = "NixOS";
             repo  = "nixpkgs";
             inherit rev sha256;
           }) { config.allowUnfree = true; };

         known-good-20191113_070954 = nixpkgs {
           rev    = "620124b130c9e678b9fe9dd4a98750968b1f749a";
           sha256 = "0xgy2rn2pxii3axa0d9y4s25lsq7d9ykq30gvg2nzgmdkmy375rr";
         };
       in
       {
         inherit (known-good-20191113_070954) shared-mime-info;
       })
    ];
  }
}:

with pkgs.${packages};

let equations =
pkgs.stdenv.mkDerivation rec {

  name = "coq${coq.coq-version}-equations-${version}";
  version = "1.2.2pre";

  src = pkgs.fetchFromGitHub {
    owner = "mattam82";
    repo = "Coq-Equations";
    rev = "d277d668aeceb780ca4cc97c06fcb1539e255f30"; # refs/heads/8.11
    sha256 = "1jywfhnxrjwzdsm52ys7db080cci98wjyv74kd78nc4i7d7niqgv";
  };

  buildInputs = with coq.ocamlPackages; [ ocaml camlp5 findlib coq ];

  configurePhase = "./configure.sh";

  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  meta = with pkgs.stdenv.lib; {
    homepage = https://mattam82.github.io/Coq-Equations/;
    description = "A plugin for Coq to add dependent pattern-matching";
    maintainers = with maintainers; [ jwiegley ];
    platforms = coq.meta.platforms;
  };

  passthru = {
    compatibleCoqVersions = v: builtins.hasAttr v params;
  };

}; in

pkgs.stdenv.mkDerivation rec {
  name = "coq${coq.coq-version}-category-theory-${version}";
  version = "1.0";

  src =
    if pkgs ? coqFilterSource
    then pkgs.coqFilterSource [] ./.
    else ./.;

  buildInputs = [
    coq coq.ocaml coq.camlp5 coq.findlib equations
  ];
  enableParallelBuilding = true;

  buildPhase = "make JOBS=$NIX_BUILD_CORES";
  preBuild = "coq_makefile -f _CoqProject -o Makefile";
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
  passthru = {
    compatibleCoqVersions = v: builtins.elem v [ "8.6" "8.7" "8.8" "8.9" "8.10" "8.11" ];
 };
}
