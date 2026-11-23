{
  description = "An axiom-free formalization of category theory in Coq for personal study and practical work";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        release = assert pkgs.rocqPackages_9_3.coq.version == "9.3.0"; pkgs.rocqPackages_9_3;
        inherit (release) coq equations stdlib;
        category-theory = pkgs.stdenv.mkDerivation rec {
          name = "coq${coq.coq-version}-category-theory-${version}";
          version = "1.0";

          src = if pkgs ? coqFilterSource
          then pkgs.coqFilterSource [] ./.
          else ./.;

          buildInputs = [ coq coq.ocaml coq.findlib equations stdlib ];
          enableParallelBuilding = true;


          configurePhase = "coq_makefile -f _CoqProject -o Makefile.coq";

          # Enforce the axiom audit on the default toolchain, inside the
          # build environment that already compiles the library.  This wires
          # the Makefile `print-assumptions` gate into `nix flake check` (the
          # default package is `checks.build`), so an audited flagship that
          # acquires an unexpected axiom fails the build rather than merely
          # printing. Enable these checks on the default toolchain.
          doCheck = true;
          nativeCheckInputs = [ pkgs.python3 ];
          checkPhase = ''
            runHook preCheck
            make -s print-assumptions
            # Use allocated cores for the fresh rebuild, within the guard's 16-job cap.
            probe_jobs=$NIX_BUILD_CORES
            if (( probe_jobs > 16 )); then probe_jobs=16; fi
            make PROBE_ARITY_JOBS="$probe_jobs" probe-arity-check probe-arity-coq-selftest
            runHook postCheck
          '';

          installFlags = [
            "COQLIB=$(out)/lib/coq/${coq.coq-version}/"
            "COQLIBINSTALL=$(out)/lib/coq/${coq.coq-version}/user-contrib"
            "COQPLUGININSTALL=$(OCAMLFIND_DESTDIR)"
            "DOCDIR=$(out)/share/coq/${coq.coq-version}/"
            "COQDOCINSTALL=$(out)/share/coq/${coq.coq-version}/user-contrib"
          ];

        };

      in rec {
        packages = rec {
          category-theory_9_3 = category-theory;

          default = category-theory_9_3;
        };

        devShells = {
          default = pkgs.mkShell {
            packages = [
              coq coq.ocaml coq.findlib stdlib equations
              pkgs.gnumake
              pkgs.python3
              pkgs.lefthook
            ];

            CATEGORY_ROCQ_BIN = "${coq}/bin";
            shellHook = ''
              echo "Category Theory development shell (Rocq ${coq.version})"
              echo "Run 'make' to build, 'lefthook install' to set up git hooks"
            '';
          };
        };

        checks = {
          build = packages.default;

          # The semantic guard needs the declared compiler, Stdlib and
          # Equations environment. The default package's checkPhase runs it;
          # this alias and checks.build share one derivation, not a cycle.
          probe-arity-check = packages.default;

          probe-arity-unit = pkgs.runCommand "probe-arity-unit" {
            nativeBuildInputs = [ pkgs.gnumake pkgs.python3 ];
          } ''
            cd ${self}
            make probe-arity-unit
            touch $out
          '';

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
            echo "Checking for live Admitted. proof holes..."
            holes=$(find . -name '*.v' -print0 \
              | xargs -0 grep -lE '^[[:space:]]*Admitted\.' 2>/dev/null || true)
            if [ -n "$holes" ]; then
              echo "ERROR: live Admitted. proof hole(s):"
              printf '%s\n' "$holes"
              exit 1
            fi
            echo "No Admitted. proof holes."
            current=$(find . -name '*.v' -print0 \
              | xargs -0 grep -ciE '(Admitted\.|[^_]admit|Abort\.)' 2>/dev/null \
              | awk -F: '{s+=$2} END {print s+0}')
            baseline=$(cat .admitted-baseline 2>/dev/null || echo 0)
            echo "Aborted-sketch count: $current, Baseline: $baseline"
            if [ "$current" -gt "$baseline" ]; then
              echo "ERROR: aborted-sketch count rose ($current > $baseline)"
              exit 1
            fi
            echo "Aborted-sketch count within baseline."
            touch $out
          '';
        };
      });
}
