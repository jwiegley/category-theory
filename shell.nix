args@{ version ? "category-theory_8_15", pkgs ? null }:
(import ./default.nix (if pkgs == null then {} else { inherit pkgs; })).${version}
