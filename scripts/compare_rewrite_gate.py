#!/usr/bin/env python3
"""Compare every gated About block in two built trees (see doc/REWRITE_UNIVERSES.md)."""
import argparse
import difflib
from pathlib import Path
import re
import subprocess


def instrument(source):
    commands = ["Set Printing All. Set Printing Universes. "
                "Set Printing Primitive Projection Parameters. Set Printing Depth 1000000."]
    names = []

    def mark():
        return f'Goal True. idtac "Q1371_{len(names)}". Abort.'

    for line in source.splitlines():
        match = re.fullmatch(r"Print Assumptions ([\w.']+)\.", line)
        if match:
            commands.extend([mark(), f"About {match[1]}."])
            names.append(match[1])
        elif "Print Assumptions" in line:
            raise ValueError(f"unrecognized audit command: {line}")
        else:
            commands.append(line)
    if not names or len(names) != len(set(names)):
        raise ValueError("empty or duplicate audit name list")
    commands.append(mark())
    return names, "\n".join(commands) + "\n"


def query(root, directory, source, names):
    directory.mkdir()
    (directory / "Query.v").write_text(source)
    stdout = directory / "stdout"
    with stdout.open("wb") as out, (directory / "stderr").open("wb") as err:
        subprocess.run(["coqc", "-q", "-R", str(root.resolve()), "Category", "Query.v"],
                       cwd=directory, stdout=out, stderr=err, check=True)
    text = stdout.read_text()
    marks = list(re.finditer(r"^Q1371_(\d+)\n", text, re.M))
    if [int(m[1]) for m in marks] != list(range(len(names) + 1)):
        raise ValueError(f"incomplete query: {directory}")
    frames = [text[m.end():n.start()] for m, n in zip(marks, marks[1:])]
    for name, frame in zip(names, frames):
        if "not a defined object" in frame or not frame.strip():
            raise ValueError(f"unresolved {name} in {directory}")
    return frames


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for arg in ("audit_query", "before_tree", "after_tree", "new_output_dir"):
        parser.add_argument(arg, type=Path)
    args = parser.parse_args()
    dest = args.new_output_dir
    dest.mkdir()
    names, source = instrument(args.audit_query.read_text())
    before = query(args.before_tree, dest / "base", source, names)
    after = query(args.after_tree, dest / "preferred", source, names)
    changed = 0
    with (dest / "gate.diff").open("w") as out:
        for name, a, b in zip(names, before, after):
            if a != b:
                changed += 1
                out.writelines(difflib.unified_diff(a.splitlines(True), b.splitlines(True),
                                                    name + " (base)", name + " (preferred)"))
    print(f"{changed} of {len(names)} About blocks changed; see {dest / 'gate.diff'}")


if __name__ == "__main__":
    main()
