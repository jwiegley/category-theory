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

  # QuickChick_8_8 = cpkgs:
  #   self.callPackage ./coq/QuickChick.nix { inherit (cpkgs) coq; };

  # equations_8_8 = cpkgs:
  #   self.callPackage ./coq/equations.nix { inherit (cpkgs) coq; };

  coqPackages = let cpkgs = pkgs.mkCoqPackages pkgs.${compiler}; in cpkgs // {
    # QuickChick = QuickChick_8_8 cpkgs;
    # equations = equations_8_8 cpkgs;
  };

in
  with coqPackages; pkgs.stdenv.mkDerivation rec {
    name = "category-theory";
    version = "1.0";
    src = if pkgs.lib.inNixShell then null else ./.;
    buildInputs = [ coq coq.ocaml coq.camlp5 coq.findlib equations ];
    preBuild = "coq_makefile -f _CoqProject -o Makefile";
    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
    env = pkgs.buildEnv { name = name;  paths = buildInputs; };
    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.5" "8.6" "8.7" "8.8" ];
   };
  }
