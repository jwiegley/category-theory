# Building against an unreleased Rocq

`master` targets one released Rocq (see "Versioning" in CLAUDE.md). This
document describes how the library is also built against Rocq before it is
released. The two compatibility branches serve different purposes:

| Branch | Intended contents | Built against |
| --- | --- | --- |
| `rocq-master` | the same commits as `master` | Rocq's `master` branch |
| `rocq-22721` | `master` plus the changes [rocq-prover/rocq#22721](https://github.com/rocq-prover/rocq/pull/22721) needs | that pull request's head |

`rocq-master` is meant to show when a change merged into Rocq breaks the
library as it stands. `rocq-22721` is meant to carry source the released
compiler rejects: the overlay for that pull request writes `max(...)` in
universe constraints, which Rocq 9.3.0 refuses as a syntax error. Such a
branch cannot be merged into `master` until a release contains the pull
request. Nothing enforces that `rocq-master` equals `master`; it is kept so
by hand (below).

## What a branch is built against

A branch names its compiler in `.github/rocq-upstream.conf`: a repository
and a ref for Rocq, for Stdlib and for Equations. The file is read as
`KEY=VALUE` data. Use an `https://`, `ssh://` or `file:///` URL, or an
absolute local path: resolution and fetching run in different directories.
A ref is a branch name, a full ref (`refs/heads/...`,
`refs/tags/...`, `refs/pull/N/head`) or a full lowercase 40-hex commit ID.
A bare name other than such an ID is looked up as a branch, not expanded as
an abbreviated commit. Use `refs/heads/...` for a branch named like a pin.
A tag must ultimately point to a commit. `resolve` uses the advertised ID,
peeled for an annotated tag; it does not check the object's type. `build`
checks out the object and verifies that `HEAD` equals the requested ID.
The copy on `master` names the three default branches. A branch that tracks a pull request names
that pull request's head and the library branches of its overlay, and keeps
that copy to itself: when such a branch is merged into `master`, `master`'s
copy of the file is the one to keep.

`scripts/build-upstream-rocq.sh` builds the three from source and installs
them under one prefix:

```bash
nix develop --no-update-lock-file .#upstream            # OCaml 4.14, dune, zarith
scripts/build-upstream-rocq.sh resolve > sources.txt    # record the chosen revisions
scripts/build-upstream-rocq.sh build ~/rocq-22721 sources.txt
. ~/rocq-22721/env.sh                                   # activate that installation
make                                                    # build the library with it
```

Give `build` a new or empty directory reserved for this installation. Its
absolute path may contain only letters, digits and `_ . / + @ -`, with no
`..` component. An unsuccessful install can leave the prefix partly filled:
temporary source trees are removed, but installed files are not. Retry in a
fresh prefix or empty the partial installation yourself.

To build the same commits again, keep `sources.txt` and pass it to `build`
with a fresh prefix. `check-manifest FILE` and `build` accept the
same format: three newline-terminated `name=commit` records in the order
`rocq`, `stdlib`, `equations`, with lowercase 40-hex IDs and no other data.
`~/rocq-22721/SOURCES` records the three commits installed.
Sourcing `env.sh` appends `-native-compiler no` to `COQEXTRAFLAGS` without
removing existing flags; use a clean shell if those flags belonged to a
different compiler. Rocq's `dev/ci/scripts/ci-category_theory.sh` also
disables native compilation. Compiled files from another
compiler cannot safely be reused. Use a clean checkout, or run `make
fullclean` with the old toolchain before switching; `make clean` leaves the
generated makefile and its configuration behind.

## Continuous integration

`.github/workflows/rocq-upstream.yml` does the above on GitHub. What it
builds depends on what started it:

| Started by | Builds |
| --- | --- |
| the daily schedule, or a manual dispatch | each of the two branches that exists, at its current head |
| a push to `rocq-master` or `rocq-22721` | the pushed commit; branch deletions are skipped |
| a pull request into `master` that changes the workflow, the configuration file, the build script, `flake.nix` or `flake.lock` | the pull request's head, against what its own configuration file names |
| opening, reopening, updating the head of a PR into `rocq-22721`, or changing a PR's base to `rocq-22721` | the PR's head, with no path filter, via `.github/workflows/rocq-22721-pr.yml`; editing only the title or body does not run the build |

For a PR into `rocq-22721`, the event's base commit supplies the flake,
build script and compiler configuration. The library comes from the PR's
head commit, not the base or GitHub's test merge. Retargeting a head that
still names Rocq `master` therefore tests that source with #22721. This job
does not test a proposed change to the compiler recipe itself: the local
staged check uses the proposed recipe, and a branch push uses the pushed one.

It never runs on a push to `master`. It is meant as an early warning and
should not be made a required check: Rocq's default branch can break the
build for reasons that have nothing to do with a change here. A failure on
a pull request does show as a failed check on that pull request.

The refs are resolved to commits once per job; the toolchain is built from
exactly those commits and cached under them, together with the build
script and the two flake files. A job that finds a cached toolchain checks
that its `SOURCES` names the commits it resolved before using it. A fresh
build must pass the same comparison before it can enter the cache. GitHub
may evict a cached toolchain.

GitHub starts scheduled workflows from the default branch only, so the
schedule lives on `master` and checks each branch out. The released-Rocq
opam build in `.github/workflows/coq-ci.yml` skips pushes to `rocq-22721`
and PR builds whose base is exactly `rocq-22721`. Its independent
configuration checks still run on the usual push and PR events; retargeting
triggers the separate PR-compiler workflow without requiring a new head.
Tags, other branch pushes and PRs into other bases keep their release policy.

## Keeping the branches current

- `rocq-master`: fast-forward it to `master`. It carries no commit of its
  own.
- `rocq-22721`: merge `master` into it and repair what the merge breaks.
  Explicit universe instances are the usual cause: the same constant can
  have a different number of universes under the two compilers.
- When a Rocq release contains the pull request: move `master` to that
  release, merge the branch into `master` keeping `master`'s
  `.github/rocq-upstream.conf`, and delete the branch.

On `master` and `rocq-master` the pre-commit hooks check the released
compiler. On `rocq-22721`, source the intended installation's `env.sh`
(as above), then run `export ROCQ_UPSTREAM_PREFIX` before committing.
This exports the path set by that installation; it does not select a
second one. The hook and the following command check the same staged tree:

```bash
bash -euo pipefail -c 'tree=$(git write-tree); git cat-file blob "$tree:scripts/check_rocq_22721.py" | python3 -IB - "$tree"'
```

The launcher captures the index once. It reads the driver from that tree,
not the working copy; the driver exports that same tree, resolves its refs
and compares the manifest with `$ROCQ_UPSTREAM_PREFIX/SOURCES`. If a ref
has moved, build into a fresh prefix, source its `env.sh` and export
`ROCQ_UPSTREAM_PREFIX` again.

The hook builds a clean export of the Git index in the locked `upstream`
shell, installs into a temporary directory, and runs `make check`, including
the assumptions audit, a separate fresh probe-arity build and its compiler
self-tests. It checks each installed object against the copy it built.
When retiring this branch, keep `master`'s released checks as well as its
upstream configuration.

Rocq's own CI builds this library from the branch named for
`category_theory` in its `dev/ci/ci-basic-overlay.sh` (`master`, when this
was written), and a pull request to Rocq can redirect that with an overlay
file. Which branch those name is decided in the Rocq repository.

## What has been run

On 2026-11-25 the original source-build script built Rocq `9bb782bb`, Stdlib
`b4e230d3` and Equations `2538ee88` on macOS and Linux (both aarch64).
The library at `a210bcd4` with the proposed CI changes built all 1,180
registered files on each machine. These runs preceded the manifest check.

On 2026-11-28 a fresh Linux/aarch64 container ran the build job's shell
steps on the library from `7ddc3a7d` with the manifest reader tested that
day. It resolved Rocq `5428c28e`, Stdlib `9657c750` and Equations
`ad825260`, built those commits, compared `SOURCES` with the original
manifest using a standalone `cmp`, and built all 1,180 `.vo` files. The
container exited zero. This tested the build for a cache miss, not GitHub's
restore and save actions. On macOS/arm64 the
revised script also installed those three commits using a relative prefix
and `TMPDIR`; `cmp` passed, and no source-build directory remained.

Not done at that point: a hosted workflow run, an x86_64 build of the new
workflow, a cache restore or save on GitHub, or a run triggered by a push
to either compatibility branch. A pull request changing the workflow itself
is eligible for a hosted test before either branch is created.
