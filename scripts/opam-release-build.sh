#!/usr/bin/env bash
# Run inside the release image, in a writable copy of the checked-out sources.
set -eu -o pipefail
umask 077
export OPAMYES=1 OPAMJOBS=4
# Keep the image's repository snapshots: do not update to a moving dev set.
opam install --deps-only .
for spec in rocq-core:9.3.0 rocq-runtime:9.3.0 coq:9.3.0 rocq-stdlib:9.2.0 rocq-equations:1.3.2+9.3; do
  pkg=${spec%:*}
  version=$(opam list --installed --short --columns=version "$pkg")
  printf '%s: %s\n' "$pkg" "$version"
  test "$version" = "${spec#*:}"
done
opam exec -- bash scripts/check-release-toolchain.sh "$(opam var bin)"
opam install --verbose .
# Import from outside the checkout: compilation alone does not test install.
work=$(mktemp -d)
cd "$work"
printf 'From Category Require Import Lib.\nLocate Library Category.Lib.\n' > Installed.v
opam exec -- rocq c -q Installed.v
test -s Installed.vo
