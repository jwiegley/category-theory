{ packages ? "coqPackages_8_8"
, rev      ? "89b618771ad4b0cfdb874dee3d51eb267c4257dd"
, sha256   ? "0jlyggy7pvqj2a6iyn44r7pscz9ixjb6fn6s4ssvahfywsncza6y"
, pkgs     ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

with pkgs.${packages};

let
  metalib = pkgs.${packages}.metalib.overrideAttrs (attrs: rec {
    name = "metalib-${coq.coq-version}-${version}";
    version = "20180911";

    src = pkgs.fetchgit {
      url = https://github.com/plclub/metalib.git;
      rev = "7cc5702462d952327304500165bf19478f156a17";
      sha256 = "1w67r400g07v4fpvw69vdkhibxi5ikv09qjxly41d0w7csr00r5a";
      # date = 2018-09-11T08:47:41-04:00;
    };
  });

in pkgs.stdenv.mkDerivation rec {
  name = "category-theory";
  version = "1.0";

  src =
    if pkgs.lib.inNixShell
    then null
    else
    if pkgs ? coqFilterSource
    then pkgs.coqFilterSource [] ./.
    else ./.;

  buildInputs = [
    coq coq.ocaml coq.camlp5 coq.findlib equations metalib
  ];
  enableParallelBuilding = true;

  buildPhase = "make JOBS=$NIX_BUILD_CORES";
  preBuild = "coq_makefile -f _CoqProject -o Makefile";
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  env = pkgs.buildEnv { name = name; paths = buildInputs; };
  passthru = {
    compatibleCoqVersions = v: builtins.elem v [ "8.6" "8.7" "8.8" ];
 };
}
