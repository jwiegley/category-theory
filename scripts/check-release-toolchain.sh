#!/usr/bin/env bash
# Run in the locked development shell or in the pinned opam switch.
set -eu -o pipefail
umask 077
# The upstream banner for 9.2.0 may print only 9.2. Bind PATH to the
# exact package checked by the flake assertion or the opam caller first.
expected_bin=${1:-${CATEGORY_ROCQ_BIN:?expected compiler bin directory required}}
for program in rocq coqc coqtop coq_makefile; do
  actual=$(command -v "$program")
  if ! [[ "$actual" -ef "$expected_bin/$program" ]]; then
    printf 'Wrong %s: expected %s, found %s\n' "$program" "$expected_bin/$program" "$actual" >&2
    exit 1
  fi
  printf '%s\n' "$actual"
done
version=$(rocq c -print-version)
printf 'Rocq and OCaml versions: %s\n' "$version"
case ${version%% *} in 9.2|9.2.0) ;; *) exit 1 ;; esac
ocamlfind query rocq-equations.plugin
work=$(mktemp -d)
cd "$work"
cat > ReleaseSmoke.v <<'ROCQ'
From Corelib Require Import Init.Prelude.
From Stdlib Require Import Lists.List.
From Equations Require Import Equations.
Locate Library Corelib.Init.Prelude.
Locate Library Stdlib.Lists.List.
Locate Library Equations.Prop.Equations.
Equations smoke (n : nat) : nat :=
smoke O := O;
smoke (S n) := n.
Example smoke_check : smoke 1 = 0 := eq_refl.
ROCQ
rocq c -q ReleaseSmoke.v
test -s ReleaseSmoke.vo
