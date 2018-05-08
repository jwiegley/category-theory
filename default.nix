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
    src = if pkgs.lib.inNixShell then null else ./.;
    buildInputs = [ coq coq.ocaml coq.camlp5 coq.findlib equations ];
    preBuild = "coq_makefile -f _CoqProject -o Makefile";
    installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";
    env = pkgs.buildEnv { name = name;  paths = buildInputs; };
    passthru = {
      compatibleCoqVersions = v: builtins.elem v [ "8.5" "8.6" "8.7" "8.8" ];
   };
  }
