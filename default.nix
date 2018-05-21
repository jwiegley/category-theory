{ packages ? "coqPackages_8_7"
, rev      ? "95b1827682dc30ff1ccffb4f46c197289cea3e1c"
, sha256   ? "0v5s2918a04h6h1m18pzp36l5f41rhkipwqgysamsz7h0q4zwhwz"
, pkgs     ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

with pkgs.${packages}; pkgs.stdenv.mkDerivation rec {
  name = "category-theory";
  version = "1.0";
  src =
    if pkgs.lib.inNixShell
    then null
    else
      builtins.filterSource (path: type:
        let baseName = baseNameOf path; in
        !( type == "directory"
           && builtins.elem baseName [".git"])
        &&
        !( type == "unknown"
           || baseName == ".coq-version"
           || baseName == "CoqMakefile.conf"
           || baseName == "Makefile.coq"
           || baseName == "Makefile.coq-old.conf"
           || baseName == "result"
           || pkgs.stdenv.lib.hasSuffix ".a" path
           || pkgs.stdenv.lib.hasSuffix ".o" path
           || pkgs.stdenv.lib.hasSuffix ".cmi" path
           || pkgs.stdenv.lib.hasSuffix ".cmo" path
           || pkgs.stdenv.lib.hasSuffix ".cmx" path
           || pkgs.stdenv.lib.hasSuffix ".cmxa" path
           || pkgs.stdenv.lib.hasSuffix ".cmxs" path
           || pkgs.stdenv.lib.hasSuffix ".ml" path
           || pkgs.stdenv.lib.hasSuffix ".mli" path
           || pkgs.stdenv.lib.hasSuffix ".ml.d" path
           || pkgs.stdenv.lib.hasSuffix ".ml4" path
           || pkgs.stdenv.lib.hasSuffix ".ml4.d" path
           || pkgs.stdenv.lib.hasSuffix ".mllib.d" path
           || pkgs.stdenv.lib.hasSuffix ".aux" path
           || pkgs.stdenv.lib.hasSuffix ".glob" path
           || pkgs.stdenv.lib.hasSuffix ".v.d" path
           || pkgs.stdenv.lib.hasSuffix ".vo" path))
      ./.;
  buildInputs = [ coq coq.ocaml coq.camlp5 coq.findlib equations ];
  enableParallelBuilding = true;
  buildPhase = "make -j$NIX_BUILD_CORES";
  preBuild = "coq_makefile -f _CoqProject -o Makefile";
  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
  env = pkgs.buildEnv { name = name; paths = buildInputs; };
  passthru = {
    compatibleCoqVersions = v: builtins.elem v [ "8.6" "8.7" "8.8" ];
 };
}
