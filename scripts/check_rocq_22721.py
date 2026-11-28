#!/usr/bin/env python3
"""Check the staged library using the source-built toolchain for this branch."""
import filecmp
import os
from pathlib import Path
import subprocess
import sys
import tempfile


# Resolve from the staged configuration, once. Do not let a released Rocq or
# an ambient make/compiler setting stand in for the tools from that prefix.
CHECK = r'''
scripts/build-upstream-rocq.sh resolve > "$2/requested"
scripts/build-upstream-rocq.sh check-manifest "$2/requested"
cmp "$2/requested" "$1/SOURCES"
cat "$2/requested"
. "$1/env.sh"
for tool in rocq coqc coqtop coq_makefile; do
    expected="$1/bin/$tool"
    if ! selected=$(command -v "$tool") ||
       [[ $(type -t "$tool") != file || ! -x "$expected" || ! "$selected" -ef "$expected" ]]; then
        echo "Expected $expected after activating the toolchain" >&2
        exit 1
    fi
done
rocq --version
rocq makefile -f _CoqProject -o Makefile.coq
make -j"$3"
make install DESTDIR="$2/install"
make check PROBE_ARITY_JOBS="$3" PROBE_ARITY_WORK_DIR="$2/probe-arity"
'''


def main():
    # The launcher loads this very script from the captured tree. Do not
    # resample the index here: the recipe and all inputs must share one tree.
    if len(sys.argv) != 2 or sys.argv[0] != "-":
        raise SystemExit("Use the staged check command in doc/UPSTREAM.md")
    tree = sys.argv[1]
    setting = os.environ.get("ROCQ_UPSTREAM_PREFIX")
    if not setting:
        raise SystemExit("Set ROCQ_UPSTREAM_PREFIX to the PR toolchain prefix; see doc/UPSTREAM.md")
    prefix = Path(setting).resolve(strict=True)
    jobs = str(min(8, os.cpu_count() or 1))
    with tempfile.TemporaryDirectory(prefix="check-rocq-22721-") as tmp:
        work = Path(tmp).resolve()
        source = work / "source"
        source.mkdir()
        archive = work / "staged.tar"
        subprocess.run(["git", "archive", "--format=tar", "-o", archive, tree], check=True)
        subprocess.run(["tar", "-xf", archive, "-C", source], check=True)
        if next(source.rglob("*.vo"), None) is not None:
            raise SystemExit("The staged tree contains compiled .vo files; expected a clean build")
        print(f"Checking staged tree {tree}", flush=True)
        subprocess.run([
            "nix", "develop", "--no-update-lock-file", "--ignore-environment", "path:.#upstream",
            "--command", "bash", "-euo", "pipefail", "-c", CHECK,
            "check-rocq-22721", prefix, work, jobs,
        ], cwd=source, check=True)

        # A successful install must actually include the built library. DESTDIR
        # keeps these files out of the compiler prefix used by the fresh probe build.
        roots = list((work / "install").rglob("user-contrib/Category/Lib.vo"))
        if len(roots) != 1:
            raise SystemExit("Expected one installed Category/Lib.vo")
        installed = roots[0].parent
        inputs = [Path(f) for f in (source / "_CoqProject").read_text().split() if f.endswith(".v")]
        if not inputs:
            raise SystemExit("No registered library sources")
        for f in inputs:
            vo = f.with_suffix(".vo")
            if not (installed / vo).is_file() or not filecmp.cmp(source / vo, installed / vo, shallow=False):
                raise SystemExit(f"Installed object missing or different: {vo}")
        print(f"Verified {len(inputs)} installed objects from staged tree {tree}.")


if __name__ == "__main__":
    main()
