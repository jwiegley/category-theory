{
  description = "An axiom-free formalization of category theory in Coq for personal study and practical work";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        equations = coqPackages: with pkgs.${coqPackages};
          let
            useDune = coqPackages == "coqPackages_9_0" || coqPackages == "coqPackages_9_1";
            rocqPackages = if coqPackages == "coqPackages_9_0" then "rocqPackages_9_0"
                           else if coqPackages == "coqPackages_9_1" then "rocqPackages_9_1"
                           else null;
            stdlib = if rocqPackages != null then pkgs.${rocqPackages}.stdlib else null;
          in pkgs.stdenv.mkDerivation rec {
          name = "coq${coq.coq-version}-equations-${version}";
          version = "1.3";

          src = pkgs.fetchFromGitHub ({
            owner = "mattam82";
            repo = "Coq-Equations";
          } //
          (if coqPackages == "coqPackages_8_19"
          then {
            rev = "v1.3-8.19";
            sha256 = "sha256-roBCWfAHDww2Z2JbV5yMI3+EOfIsv3WvxEcUbBiZBsk=";
          } else {}) //
          (if coqPackages == "coqPackages_8_20"
          then {
            rev = "v1.3.1-8.20";
            sha256 = "sha256-u8LB1KiACM5zVaoL7dSdHYvZgX7pf30VuqtjLLGuTzc=";
          } else {}) //
          (if coqPackages == "coqPackages_9_0"
          then {
            rev = "v1.3.1-9.0";
            sha256 = "sha256-186Z0/wCuGAjIvG1LoYBMPooaC6HmnKWowYXuR0y6bA=";
          } else {}) //
          (if coqPackages == "coqPackages_9_1"
          then {
            rev = "v1.3.1-9.1";
            sha256 = "sha256-LtYbAR3jt+JbYcqP+m1n3AZhAWSMIeOZtmdSJwg7L1A=";
          } else {}));

          nativeBuildInputs = pkgs.lib.optionals useDune [ pkgs.dune_3 ];
          buildInputs = [
            coq coq.ocaml coq.findlib
          ] ++ pkgs.lib.optionals useDune [
            coq.ocamlPackages.ppx_optcomp
          ] ++ pkgs.lib.optionals (stdlib != null) [
            stdlib
          ];
          enableParallelBuilding = true;

          buildPhase = if useDune
            then "dune build -p rocq-equations @install"
            else "make";

          configurePhase = if useDune
            then ""
            else "coq_makefile -f _CoqProject -o Makefile.coq";

          checkPhase = if useDune
            then ""
            else "make examples test-suite";

          # For Dune-based builds (Rocq 9.0/9.1), install to standard locations
          installPhase = if useDune
            then ''
              # Install using Dune's standard layout
              # Dune installs Coq theories to $libdir/coq/user-contrib/
              dune install rocq-equations --prefix=$out --libdir=$out/lib/ocaml

              # Create symlink for standard Coq layout compatibility
              # Dune puts files in lib/ocaml/coq/user-contrib/
              # We symlink to lib/coq/VERSION/user-contrib/ for coq_makefile
              mkdir -p $out/lib/coq/${coq.coq-version}
              ln -sf $out/lib/ocaml/coq/user-contrib $out/lib/coq/${coq.coq-version}/user-contrib
            ''
            else null;

          installFlags = if useDune then [] else [
            "COQLIB=$(out)/lib/coq/${coq.coq-version}/"
            "COQLIBINSTALL=$(out)/lib/coq/${coq.coq-version}/user-contrib"
            "COQPLUGININSTALL=$(OCAMLFIND_DESTDIR)"
            "DOCDIR=$(out)/share/coq/${coq.coq-version}/"
            "COQDOCINSTALL=$(out)/share/coq/${coq.coq-version}/user-contrib"
          ];

          env.env = pkgs.buildEnv { inherit name; paths = buildInputs; };
          passthru = {
            compatibleCoqVersions = v:
            builtins.elem v [ "8.19" "8.20" "9.0" "9.1" ];
          };
        };

        category-theory = coqPackages: with pkgs.${coqPackages};
          let
            isRocq = coqPackages == "coqPackages_9_0" || coqPackages == "coqPackages_9_1";
            rocqPackages = if coqPackages == "coqPackages_9_0" then "rocqPackages_9_0"
                           else if coqPackages == "coqPackages_9_1" then "rocqPackages_9_1"
                           else null;
            stdlib = if rocqPackages != null then pkgs.${rocqPackages}.stdlib else null;
            eqns = equations coqPackages;
          in pkgs.stdenv.mkDerivation rec {
          name = "coq${coq.coq-version}-category-theory-${version}";
          version = "1.0";

          src = if pkgs ? coqFilterSource
          then pkgs.coqFilterSource [] ./.
          else ./.;

          buildInputs = [
            coq coq.ocaml coq.findlib eqns
          ] ++ pkgs.lib.optionals (coqPackages == "coqPackages_8_14" ||
                                   coqPackages == "coqPackages_8_15") [
            dpdgraph
          ] ++ pkgs.lib.optionals (stdlib != null) [
            stdlib
          ];
          enableParallelBuilding = true;

          # Set path variables for finding Equations theories and plugins
          # For Rocq 9.x, use ROCQPATH; for older Coq, use COQPATH
          # OCAMLPATH allows findlib to locate the rocq-equations.plugin package (for Rocq 9.x)
          ROCQPATH = if isRocq then "${eqns}/lib/coq/${coq.coq-version}/user-contrib" else null;
          COQPATH = if isRocq then null else "${eqns}/lib/coq/${coq.coq-version}/user-contrib";
          OCAMLPATH = if isRocq then "${eqns}/lib/ocaml" else null;

          configurePhase = "coq_makefile -f _CoqProject -o Makefile.coq";

          installFlags = [
            "COQLIB=$(out)/lib/coq/${coq.coq-version}/"
            "COQLIBINSTALL=$(out)/lib/coq/${coq.coq-version}/user-contrib"
            "COQPLUGININSTALL=$(OCAMLFIND_DESTDIR)"
            "DOCDIR=$(out)/share/coq/${coq.coq-version}/"
            "COQDOCINSTALL=$(out)/share/coq/${coq.coq-version}/user-contrib"
          ];

          env.env = pkgs.buildEnv { inherit name; paths = buildInputs; };
          passthru = {
            compatibleCoqVersions = v:
            builtins.elem v [ "8.19" "8.20" "9.0" "9.1" ];
          };
        };

      in rec {
        packages = rec {
          category-theory_8_19 = category-theory "coqPackages_8_19";
          category-theory_8_20 = category-theory "coqPackages_8_20";
          category-theory_9_0 = category-theory "coqPackages_9_0";
          category-theory_9_1 = category-theory "coqPackages_9_1";

          default = category-theory_9_1;
        };

        devShells = {
          default = let
            coqPkg = pkgs.coqPackages_9_1.coq;
            rocqStdlib = pkgs.rocqPackages_9_1.stdlib;
            eqns = equations "coqPackages_9_1";
          in pkgs.mkShell {
            packages = [
              coqPkg
              coqPkg.ocaml
              coqPkg.findlib
              rocqStdlib
              eqns
              pkgs.gnumake
              pkgs.lefthook
            ];

            ROCQPATH = "${eqns}/lib/coq/${coqPkg.coq-version}/user-contrib";
            OCAMLPATH = "${eqns}/lib/ocaml";

            shellHook = ''
              echo "Category Theory development shell (Rocq ${coqPkg.coq-version})"
              echo "Run 'make' to build, 'lefthook install' to set up git hooks"
            '';
          };
        };

        checks = {
          build = packages.default;

          format-check = pkgs.runCommand "format-check" {
            nativeBuildInputs = [ pkgs.gnugrep pkgs.findutils ];
          } ''
            cd ${self}
            echo "Checking for trailing whitespace in .v files..."
            found=$(find . -name '*.v' -exec grep -ln '[[:blank:]]$' {} + 2>/dev/null || true)
            if [ -n "$found" ]; then
              echo "ERROR: Trailing whitespace found in:"
              echo "$found" | head -20
              exit 1
            fi
            echo "Format check passed."
            touch $out
          '';

          admitted-check = pkgs.runCommand "admitted-check" {
            nativeBuildInputs = [ pkgs.gnugrep pkgs.findutils pkgs.gawk ];
          } ''
            cd ${self}
            echo "Checking admitted proof count..."
            current=$(find . -name '*.v' -print0 \
              | xargs -0 grep -ciE '(Admitted\.|[^_]admit|Abort\.)' 2>/dev/null \
              | awk -F: '{s+=$2} END {print s+0}')
            baseline=$(cat .admitted-baseline 2>/dev/null || echo 0)
            echo "Current: $current, Baseline: $baseline"
            if [ "$current" -gt "$baseline" ]; then
              echo "ERROR: Admitted proof count increased ($current > $baseline)"
              exit 1
            fi
            echo "Admitted proof count within baseline."
            touch $out
          '';
        };
      });
}
