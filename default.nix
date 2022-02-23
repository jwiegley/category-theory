args@{ coqPackages ? "coqPackages_8_15"

, rev    ? "74b10859829153d5c5d50f7c77b86763759e8654"
, sha256 ? "0g9gak16a0mx6kwjzpz8fx4rwl9p1jj8f4f4frl12vjhnrssf6zp"
, pkgs   ? import (builtins.fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256; }) {
    config.allowUnfree = true;
    config.allowBroken = false;
  }
}:

with pkgs.${coqPackages};

pkgs.stdenv.mkDerivation rec {
  name = "coq${coq.coq-version}-category-theory-${version}";
  version = "1.0";

  src = if pkgs ? coqFilterSource
        then pkgs.coqFilterSource [] ./.
        else ./.;

  buildInputs = [ coq coq.ocaml coq.camlp5 coq.findlib equations ];
  enableParallelBuilding = true;

  buildFlags = [
    "JOBS=$(NIX_BUILD_CORES)"
  ];

  installFlags = "COQLIB=$(out)/lib/coq/${coq.coq-version}/";

  env = pkgs.buildEnv { inherit name; paths = buildInputs; };
  passthru = {
    compatibleCoqVersions = v: builtins.elem v [ "8.10" "8.11" "8.12" "8.13" "8.14" "8.15" ];
  };
}
