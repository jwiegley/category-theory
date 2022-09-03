args@{ version ? "category-theory_8_16", pkgs ? null }:
(import ./default.nix { inherit pkgs; }).${version}
