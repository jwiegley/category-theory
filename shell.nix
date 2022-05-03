args@{ version ? "category-theory_8_15", pkgs ? null }:
(import ./default.nix args).${version}
