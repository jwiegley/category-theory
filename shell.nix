args@{ version ? "category-theory_cur", pkgs ? null }:
(import ./default.nix (if pkgs == null then {} else { inherit pkgs; })).${version}
