{ compiler ? "coq_8_7"
, rev      ? "255a833e841628c0b834575664eae373e28cdc27"
, sha256   ? "022xm1pf4fpjjy69g7qz6rpqnwpjcy1l0vj49m8xmgn553cs42ch"
, nixpkgs  ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

let inherit (nixpkgs) pkgs;

  coqPackages = let cpkgs = pkgs.mkCoqPackages pkgs.${compiler}; in cpkgs // {
    equations =
      if compiler == "coq_8_8"
      then with pkgs; with cpkgs; stdenv.mkDerivation rec {
        name = "coq${coq.coq-version}-equations-${version}";
        version = "1.0";

        src = fetchFromGitHub {
          owner = "mattam82";
          repo = "Coq-Equations";
          rev = "v1.0-8.8";
          sha256 = "0dd7zd5j2sv5cw3mfwg33ss2vcj634q3qykakc41sv7f3rfgqfnn";
        };

        buildInputs = [ coq.ocaml coq.camlp5 coq.findlib coq ];

        preBuild = "coq_makefile -f _CoqProject -o Makefile";

        installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

        meta = with stdenv.lib; {
          homepage = https://mattam82.github.io/Coq-Equations/;
          description = "A plugin for Coq to add dependent pattern-matching";
          maintainers = with maintainers; [ jwiegley ];
          platforms = coq.meta.platforms;
        };

        passthru = {
          compatibleCoqVersions = v: builtins.elem v [ "8.8" ];
        };
      }
      else cpkgs.equations;
  };

in
  with coqPackages; pkgs.stdenv.mkDerivation rec {
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
    env = pkgs.buildEnv { name = name;  paths = buildInputs; };
    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.6" "8.7" "8.8" ];
   };
  }
