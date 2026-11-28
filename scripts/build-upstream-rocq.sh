#!/usr/bin/env bash
# Build an unreleased Rocq, with Stdlib and Equations, from the sources named
# in .github/rocq-upstream.conf, and install them under one prefix.
#
#   scripts/build-upstream-rocq.sh resolve
#       print three NAME=ID lines; each selected ID must name a commit
#   scripts/build-upstream-rocq.sh check-manifest MANIFEST
#       check the exact three-line format, without resolving or building
#   scripts/build-upstream-rocq.sh build PREFIX [MANIFEST]
#       build and install into PREFIX, which must not exist or be empty.
#       With MANIFEST (a file holding the output of `resolve`) build exactly
#       those commits; without it, resolve first.
#
# Run it in `nix develop .#upstream`, which supplies OCaml, dune and zarith.
# PREFIX/SOURCES records the three commits built; `. PREFIX/env.sh` puts the
# result on PATH. See doc/UPSTREAM.md.
set -eu -o pipefail
unset CDPATH

die() { printf '%s\n' "$*" >&2; exit 1; }
usage() { printf 'Usage: %s resolve | check-manifest MANIFEST | build PREFIX [MANIFEST]\n' "$0" >&2; exit 2; }

case ${1:-} in
  resolve) [ $# -eq 1 ] || usage ;;
  check-manifest) [ $# -eq 2 ] || usage ;;
  build) [ $# -eq 2 ] || [ $# -eq 3 ] || usage ;;
  *) usage ;;
esac

is_commit() { [[ $1 =~ ^[0-9a-f]{40}$ ]]; }

emit_manifest() { printf 'rocq=%s\nstdlib=%s\nequations=%s\n' "$rocq" "$stdlib" "$equations"; }

load_manifest() {
  local file key row value
  case $1 in /*) file=$1 ;; *) file=$PWD/$1 ;; esac
  [ -f "$file" ] || die "$file: no such file"
  {
    for key in rocq stdlib equations; do
      IFS= read -r row || die "$file: expected a newline-terminated $key entry"
      [[ $row == "$key="* ]] || die "$file: expected $key in resolve order"
      value=${row#*=}
      is_commit "$value" || die "$file: $key is not a full lowercase commit ID"
      case $key in rocq) rocq=$value ;; stdlib) stdlib=$value ;; equations) equations=$value ;; esac
    done
  } < "$file"
  # Reject extra records (even without a final newline) and any other bytes
  # that would not be reproduced in SOURCES by the build.
  emit_manifest | cmp -s - "$file" || die "$file: expected each entry exactly once in canonical format"
}

if [ "$1" = check-manifest ]; then
  load_manifest "$2"
  exit 0
fi

check_empty_dir() {
  local contents
  [ -d "$1" ] || die "$1 is not a directory"
  # Keep the terminator: command substitution strips trailing newlines.
  contents=$(ls -A -- "$1" && printf '.') || die "cannot list $1"
  [ "$contents" = . ] || die "$1 is not empty; build into a fresh prefix"
}

# Check the prefix and optional manifest before any remote operation.
if [ "$1" = build ]; then
  [ -n "$2" ] || die 'build requires a nonempty prefix'
  case $2 in /*) prefix=$2 ;; *) prefix=$PWD/$2 ;; esac
  [[ $prefix =~ ^[A-Za-z0-9_./+@-]+$ ]] || die "$prefix: use a prefix made of letters, digits and _ . / + @ - only"
  case "$prefix/" in */../*) die "$prefix: a prefix may not contain a .. component" ;; esac
  if [ -e "$prefix" ] || [ -L "$prefix" ]; then check_empty_dir "$prefix"; fi
  if [ $# -eq 3 ]; then load_manifest "$3"; fi
  jobs=${JOBS:-$(getconf _NPROCESSORS_ONLN)} || die 'cannot determine processor count; set JOBS'
  [[ $jobs =~ ^[1-9][0-9]*$ ]] || die "invalid job count '$jobs': expected a positive decimal integer"
  # The build changes directory, but its children and cleanup all need the
  # same temporary root. Resolve a relative TMPDIR here, not after the cd.
  TMPDIR=${TMPDIR:-/tmp}
  case $TMPDIR in /*) ;; *) TMPDIR=$PWD/$TMPDIR ;; esac
  export TMPDIR
fi

conf=$(cd -- "$(dirname -- "$0")/.." && pwd)/.github/rocq-upstream.conf
[ -f "$conf" ] || die "$conf: no such file"
setting() { # KEY -> its value in the configuration file, read as data
  local count value
  count=$(grep -c "^$1=" "$conf" || true)
  [ "$count" = 1 ] || die "$conf: $1 must be set exactly once (found $count)"
  value=$(sed -n "s/^$1=//p" "$conf")
  [ -n "$value" ] || die "$conf: $1 is empty"
  printf '%s\n' "$value"
}

resolve() { # REPO REF -> full object ID; build verifies the checkout
  local repo=$1 ref=$2 listing commit
  if is_commit "$ref"; then printf '%s\n' "$ref"; return; fi
  case $ref in refs/*) ;; *) ref=refs/heads/$ref ;; esac
  listing=$(git ls-remote "$repo" "$ref" "$ref^{}") || die "cannot list $repo"
  # Match exact names and peel annotated tags. ls-remote does not report object types.
  commit=$(printf '%s\n' "$listing" | awk -v ref="$ref" '
    $2 == ref "^{}" { peeled = $1 }
    $2 == ref       { plain = $1 }
    END { if (length(peeled)) print peeled; else if (length(plain)) print plain }')
  [ -n "$commit" ] || die "no ref $ref in $repo (give a commit as its full 40-character lowercase ID)"
  is_commit "$commit" || die "$repo: found $ref, but its object ID is not 40 lowercase hex digits"
  printf '%s\n' "$commit"
}

fetch() { # REPO COMMIT DIR
  mkdir -p -- "$3"
  git -C "$3" init -q
  git -C "$3" fetch -q --depth 1 "$1" "$2"
  git -C "$3" checkout -q FETCH_HEAD
  [ "$(git -C "$3" rev-parse HEAD)" = "$2" ] || die "$1: fetched something other than $2"
}

repository() {
  local repo
  repo=$(setting "$1") || return 1
  # fetch runs in a temporary checkout. A relative path would name a
  # different repository there than it does during ls-remote.
  case $repo in
    /*|https://*|ssh://*|file:///*) printf '%s\n' "$repo" ;;
    *) die "$conf: $1 must use https://, ssh://, file:/// or an absolute local path" ;;
  esac
}
rocq_repo=$(repository ROCQ_REPO)
stdlib_repo=$(repository STDLIB_REPO)
equations_repo=$(repository EQUATIONS_REPO)

if [ "$1" = resolve ] || [ $# -eq 2 ]; then
  rocq_ref=$(setting ROCQ_REF)
  stdlib_ref=$(setting STDLIB_REF)
  equations_ref=$(setting EQUATIONS_REF)
  rocq=$(resolve "$rocq_repo" "$rocq_ref")
  stdlib=$(resolve "$stdlib_repo" "$stdlib_ref")
  equations=$(resolve "$equations_repo" "$equations_ref")
fi

if [ "$1" = resolve ]; then
  emit_manifest
  exit 0
fi

mkdir -p -- "$prefix"
check_empty_dir "$prefix"
work=$(mktemp -d "$TMPDIR/rocq-upstream.XXXXXX")
trap 'rm -rf -- "$work"' EXIT

fetch "$rocq_repo" "$rocq" "$work/rocq"
fetch "$stdlib_repo" "$stdlib" "$work/stdlib"
fetch "$equations_repo" "$equations" "$work/equations"

cd -- "$work/rocq"
./configure -prefix "$prefix" -native-compiler no
make -j"$jobs" dunestrap
dune build -j"$jobs" -p rocq-runtime,rocq-core,coq-core,rocq-devtools
dune install --prefix="$prefix" rocq-runtime rocq-core coq-core rocq-devtools

export PATH="$prefix/bin:$PATH"
export OCAMLPATH="$prefix/lib${OCAMLPATH:+:$OCAMLPATH}"
export ROCQLIB="$prefix/lib/coq"

cd -- "$work/stdlib"
dune build -j"$jobs" -p rocq-stdlib @install
dune install --prefix="$prefix" rocq-stdlib

cd -- "$work/equations"
./configure.sh rocq
dune build -j"$jobs" -p rocq-equations @install
dune install --prefix="$prefix" rocq-equations

emit_manifest > "$prefix/SOURCES"
{
  printf "ROCQ_UPSTREAM_PREFIX='%s'\n" "$prefix"
  cat <<'ENV'
export PATH="$ROCQ_UPSTREAM_PREFIX/bin:$PATH"
export OCAMLPATH="$ROCQ_UPSTREAM_PREFIX/lib${OCAMLPATH:+:$OCAMLPATH}"
export ROCQLIB="$ROCQ_UPSTREAM_PREFIX/lib/coq"
export COQEXTRAFLAGS="${COQEXTRAFLAGS:+$COQEXTRAFLAGS }-native-compiler no"
ENV
} > "$prefix/env.sh"
"$prefix/bin/rocq" --version
