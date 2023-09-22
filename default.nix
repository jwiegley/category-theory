args@{
  rev    ? "8b5ab8341e33322e5b66fb46ce23d724050f6606"
, sha256 ? "05ynih3wc7shg324p7icz21qx71ckivzdhkgf5xcvdz6a407v53h"

, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

let

category-theory = coqPackages:
  with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
    name = "coq${coq.coq-version}-category-theory-${version}";
    version = "1.0";

    src = if pkgs ? coqFilterSource
          then pkgs.coqFilterSource [] ./.
          else ./.;

    buildInputs = [
      coq coq.ocaml coq.findlib pkgs.${coqPackages}.equations
    ] ++ pkgs.lib.optionals (coqPackages != "coqPackages_8_16" &&
                             coqPackages != "coqPackages_8_17" &&
                             coqPackages != "coqPackages_8_18") [
      dpdgraph
    ];
    enableParallelBuilding = true;

    configurePhase = "coq_makefile -f _CoqProject -o Makefile.coq";

    installFlags = [
      "COQLIB=$(out)/lib/coq/${coq.coq-version}/"
      "COQLIBINSTALL=$(out)/lib/coq/${coq.coq-version}/user-contrib"
      "COQPLUGININSTALL=$(OCAMLFIND_DESTDIR)"
      "DOCDIR=$(out)/share/coq/${coq.coq-version}/"
      "COQDOCINSTALL=$(out)/share/coq/${coq.coq-version}/user-contrib"
    ];

    env = pkgs.buildEnv { inherit name; paths = buildInputs; };
    passthru = {
      compatibleCoqVersions = v:
        builtins.elem v [ "8.14" "8.15" "8.16" "8.17" "8.18" ];
    };
  };

in rec {
  inherit category-theory;
  category-theory_8_14 = category-theory "coqPackages_8_14";
  category-theory_8_15 = category-theory "coqPackages_8_15";
  category-theory_8_16 = category-theory "coqPackages_8_16";
  category-theory_8_17 = category-theory "coqPackages_8_17";
  category-theory_8_18 = category-theory "coqPackages_8_18";
  category-theory_cur  = category-theory_8_18;
}
