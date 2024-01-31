args@{
  rev    ? "90f456026d284c22b3e3497be980b2e47d0b28ac"
, sha256 ? "164lsq7xjjvpga6l6lfi9wfsnshgfxnpa8lvb2imscdwgmajakrc"

, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

let

equations = coqPackages:
  with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
    name = "coq${coq.coq-version}-equations-${version}";
    version = "1.3";

    src = pkgs.fetchFromGitHub ({
      owner = "mattam82";
      repo = "Coq-Equations";
    } //
    (if coqPackages == "coqPackages_8_14"
     then {
       rev = "v1.3-8.14";
       sha256 = "19bj9nncd1r9g4273h5qx35gs3i4bw5z9bhjni24b413hyj55hkv";
     } else {}) //
    (if coqPackages == "coqPackages_8_15"
     then {
       rev = "v1.3-8.15";
       sha256 = "1vfcfpsp9zyj0sw0cwibk76nj6n0r6gwh8m1aa3lbvc0b1kbm32k";
     } else {}) //
    (if coqPackages == "coqPackages_8_16"
     then {
       rev = "v1.3-8.16";
       sha256 = "sha256-zyMGeRObtSGWh7n3WCqesBZL5EgLvKwmnTy09rYpxyE=";
     } else {}) //
    (if coqPackages == "coqPackages_8_17"
     then {
       rev = "v1.3-8.17";
       sha256 = "sha256-yNotSIxFkhTg3reZIchGQ7cV9WmTJ7p7hPfKGBiByDw=";
     } else {}) //
    (if coqPackages == "coqPackages_8_18"
     then {
       rev = "v1.3-8.18";
       sha256 = "sha256-8MZO9vWdr8wlAov0lBTYMnde0RuMyhaiM99zp7Zwfao=";
     } else {}) //
    (if coqPackages == "coqPackages_8_19"
     then {
       rev = "v1.3-8.19";
       sha256 = "sha256-roBCWfAHDww2Z2JbV5yMI3+EOfIsv3WvxEcUbBiZBsk=";
     } else {}));

    phases = [
      "unpackPhase" "configurePhase" "buildPhase" "checkPhase" "installPhase"
    ];

    buildInputs = [
      coq coq.ocaml coq.findlib
    ];
    enableParallelBuilding = true;

    configurePhase = "coq_makefile -f _CoqProject -o Makefile.coq";
    checkPhase = "make examples test-suite";

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
        builtins.elem v [ "8.14" "8.15" "8.16" "8.17" "8.18" "8.19" ];
    };
  };

category-theory = coqPackages:
  with pkgs.${coqPackages}; pkgs.stdenv.mkDerivation rec {
    name = "coq${coq.coq-version}-category-theory-${version}";
    version = "1.0";

    src = if pkgs ? coqFilterSource
          then pkgs.coqFilterSource [] ./.
          else ./.;

    buildInputs = [
      coq coq.ocaml coq.findlib (equations coqPackages)
    ] ++ pkgs.lib.optionals (coqPackages != "coqPackages_8_16" &&
                             coqPackages != "coqPackages_8_17" &&
                             coqPackages != "coqPackages_8_18" &&
                             coqPackages != "coqPackages_8_19") [
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
        builtins.elem v [ "8.14" "8.15" "8.16" "8.17" "8.18" "8.19" ];
    };
  };

in rec {
  inherit category-theory;
  category-theory_8_14 = category-theory "coqPackages_8_14";
  category-theory_8_15 = category-theory "coqPackages_8_15";
  category-theory_8_16 = category-theory "coqPackages_8_16";
  category-theory_8_17 = category-theory "coqPackages_8_17";
  category-theory_8_18 = category-theory "coqPackages_8_18";
  category-theory_8_19 = category-theory "coqPackages_8_19";
  category-theory_cur  = category-theory_8_19;
}
