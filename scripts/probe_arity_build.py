"""Fresh compiler evidence for probe_arity; never consumes checkout products.

No cache/reuse mode: copy registered sources, rebuild every dependency, then
replay relevant whole files with read-only About queries. Exact-span .glob
references reject notation capture; About resolves canonical names that short
.glob paths can omit. All evidence belongs to this one compiler invocation.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

import probe_arity as guard


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_project(root):
    words = guard.shlex.split((root / "_CoqProject").read_text(), comments=True)
    if words[:3] != ["-R", ".", "Category"]:
        raise guard.ScanError("compiled guard requires project load path '-R . Category'")
    files = words[3:]
    if (not files or len(files) != len(set(files)) or any(
            not f.endswith(".v") or Path(f).is_absolute() or ".." in Path(f).parts
            for f in files)):
        raise guard.ScanError("unsupported, empty or duplicate project source inventory")
    return files


def load_unreached(path, files):
    entries = json.loads(path.read_text())
    if not isinstance(entries, list):
        raise guard.ScanError("unreached-reference configuration must be an array")
    result = {}
    fields = {"file", "declaration", "constant", "arity", "reason"}
    for entry in entries:
        if not isinstance(entry, dict) or set(entry) != fields:
            raise guard.ScanError("invalid unreached-reference fields")
        if any(not isinstance(entry[k], str) or not entry[k].strip()
               for k in fields - {"arity"}):
            raise guard.ScanError("unreached-reference string fields must be nonempty strings")
        if (entry["file"] not in files or type(entry["arity"]) is not int or entry["arity"] < 0
                or not guard.QUALID.fullmatch(entry["constant"]) or "." not in entry["constant"]
                or not guard.QUALID.fullmatch(entry["declaration"]) or "." in entry["declaration"]):
            raise guard.ScanError("invalid unreached-reference target")
        key = tuple(entry[k] for k in ("file", "declaration", "constant", "arity"))
        if key in result:
            raise guard.ScanError("duplicate unreached-reference entry")
        result[key] = entry
    return result


def logical_name(file):
    return "Category." + ".".join(Path(file).with_suffix("").parts)


def run(command, cwd, env, log, timeout=900, success=True):
    with log.open("w") as output:
        output.write("command: " + repr(command) + "\n")
        output.flush()
        try:
            result = subprocess.run(command, cwd=cwd, env=env, stdout=output,
                                    stderr=subprocess.STDOUT, timeout=timeout)
        except (OSError, subprocess.TimeoutExpired) as error:
            raise guard.ScanError(f"compiler command unavailable/timed out: {error}; log: {log}") from error
        output.write(f"\nexit status: {result.returncode}\n")
    if success and result.returncode:
        raise guard.ScanError(f"compiler command failed ({result.returncode}); log: {log}")
    return result.returncode


def canonical_about(path):
    if not path.is_file():
        raise guard.ScanError(f"missing About output: {path}")
    matches = re.findall(r"^Expands to: (Constant|Inductive|Constructor)\s+(\S+)\s*$",
                         path.read_text(), re.MULTILINE)
    if len(matches) != 1:
        raise guard.ScanError(f"missing/ambiguous global identity: {path}")
    return matches[0]


def collect_evidence(root, work, files, unreached, env, coqc, coqtop):
    references, identities = {}, {}
    used, extractions = set(), []
    queries = work / "queries"
    queries.mkdir()
    for index, file in enumerate(files):
        raw = (root / file).read_bytes()
        source = raw.decode()
        glob = root / Path(file).with_suffix(".glob")
        if not glob.is_file():
            raise guard.ScanError(f"missing freshly compiled artifact: {glob}")
        refs = guard.glob_references(raw, glob.read_text(), logical_name(file))
        references[file], identities[file] = refs, {}
        commands = list(guard.commands(source))
        tasks, insertions, gaps = [], [], []
        for command in commands:
            words = [t.text for t in command]
            uses = guard.instances(command)
            negative = "Fail" in words
            if not negative and not guard.bare_check(command, uses):
                continue
            declaration = words[2] if words[:2] == ["Fail", "Definition"] else None
            prefixes = []
            for use in uses:
                key = (file, declaration, use.name, use.arity)
                if key in unreached:
                    position = next(i for i, t in enumerate(command) if t.start == use.start)
                    if position == 0 or words[position - 1] != "@" or "." not in use.name:
                        raise guard.ScanError(f"unreached reference is not protected canonical @ syntax: {key}")
                    used.add(key)
                    if guard.reference_at(source, use, refs) is None:
                        gaps.append((command, use))
                if guard.reference_at(source, use, refs) is None and key not in unreached:
                    # Missing or notation-only evidence is a violation, never
                    # licensed by an unrelated successful name lookup.
                    continue
                output = queries / f"About{index}_{len(tasks)}"
                quoted = str(output).replace('"', '""')
                prefixes.append(f'Redirect "{quoted}" About {use.name}.\n')
                tasks.append((use, output.with_suffix(".out")))
            if prefixes:
                insertions.append((command[0].start, "".join(prefixes)))
        if tasks:
            replay = source
            for offset, text in reversed(insertions):
                replay = replay[:offset] + text + replay[offset:]
            replay_file = queries / f"Replay{index}.v"
            replay_file.write_text(replay)
            run([coqtop, "-q", "-batch", "-R", str(root), "Category", "-top", logical_name(file),
                 "-l", str(replay_file)], root, env, queries / f"Replay{index}.log")
            for use, output in tasks:
                identities[file][use.start] = canonical_about(output)
        if gaps:
            verify_unreached(root, queries, index, file, source, gaps, refs,
                             identities[file], env, coqc, extractions)
    if used != set(unreached):
        raise guard.ScanError(f"stale unreached-reference entries: {sorted(set(unreached) - used)}")
    (work / "canonical-identities.json").write_text(json.dumps(identities, indent=2) + "\n")
    return references, identities, extractions


def verify_unreached(root, queries, index, file, source, gaps, refs, identities,
                     env, coqc, extractions):
    """Only the enumerated protected references can use fresh extraction.

    First verify that stripping their enclosing Fail stops at an earlier
    universe refusal, not at syntax/lookup/arity. Then compile extracted
    explicit canonical references and compare their identities to the fresh
    whole-file About replay. Source universe-instance tokens are untouched;
    fresh slots in extraction check arity without imposing those constraints.
    """
    groups = {}
    for command, use in gaps:
        groups.setdefault(command[0].start, (command, []))[1].append(use)
    for ordinal, (command, uses) in enumerate(groups.values()):
        fail = command[0]
        assert fail.text == "Fail"
        stripped = source[:fail.start] + source[fail.start + 5:]
        probe = queries / f"Unreached{index}_{ordinal}.v"
        probe.write_text(stripped)
        log = probe.with_suffix(".log")
        status = run([coqc, "-q", "-R", str(root), "Category", str(probe)], root, env,
                     log, success=False)
        output = log.read_text()
        error = output[output.rfind("Error:"):]
        locations = re.findall(r'File "' + re.escape(str(probe)) + r'", line (\d+), characters (\d+)-', output)
        if (status == 0 or not locations or
                not any(s in error for s in ("Universe inconsistency", "universe inconsistency", "Cannot enforce"))
                or "Universe instance length" in error):
            raise guard.ScanError(f"unreached premise is not an earlier universe refusal: {log}")
        line, column = map(int, locations[-1])
        offset = sum(len(s.encode()) for s in stripped.splitlines(keepends=True)[:line - 1]) + column
        begin = len(stripped[:fail.start].encode())
        first_use = min(len(stripped[:u.start - 5].encode()) for u in uses)
        if not begin <= offset < first_use:
            raise guard.ScanError(f"unreached refusal does not precede target: {log}")
        text = f"Require Import {logical_name(file)}.\n"
        for use in uses:
            text += f"Check @{use.name}@{{{' '.join(['_'] * use.arity)}}}.\n"
        extracted = root / f"ProbeArityExtract{index}_{ordinal}.v"
        if extracted.exists():
            raise guard.ScanError(f"generated extraction path collides with input: {extracted}")
        extracted.write_text(text)
        run([coqc, "-q", "-R", ".", "Category", str(extracted)], root, env,
            queries / f"Extract{index}_{ordinal}.log")
        evidence = guard.glob_references(extracted.read_bytes(), extracted.with_suffix(".glob").read_text(),
                                         logical_name(extracted.name))
        checks = [c for c in guard.commands(text) if c[0].text == "Check"]
        for original, check in zip(uses, checks):
            actual = guard.instances(check)[0]
            ref = guard.reference_at(text, actual, evidence)
            canonical = ".".join(x for x in ref[:3] if x != "<>") if ref else None
            if canonical != original.name or identities[original.start][1] != original.name:
                raise guard.ScanError("extracted reference did not resolve to its canonical global")
            start = len(source[:original.start].encode())
            refs[start, start + len(original.name.encode()) - 1] = ref
            extractions.append({"file": file, "constant": original.name, "arity": original.arity,
                                "source_offset": original.start, "earlier_refusal_log": str(log),
                                "extracted_source": str(extracted)})


def build(root, jobs, unreached_path, work_dir=None):
    root = root.resolve()
    files = read_project(root)
    unreached = load_unreached(root / unreached_path, files)
    if not 1 <= jobs <= 16:
        raise guard.ScanError("jobs must be between 1 and 16")
    work = Path(work_dir) if work_dir else Path(tempfile.mkdtemp(prefix="probe-arity-"))
    if work_dir:
        work.mkdir(parents=True, exist_ok=False, mode=0o700)
    work = work.resolve()
    snapshot = work / "source"
    snapshot.mkdir()
    inputs = ["_CoqProject"] + files
    originals = {f: (root / f).read_bytes() for f in inputs}
    originals[unreached_path] = (root / unreached_path).read_bytes()
    policy = {str(p.resolve()): p.read_bytes() for p in (Path(__file__), Path(guard.__file__))}
    for name in inputs:
        target = snapshot / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(originals[name])
    tools = {name: shutil.which(name) for name in ("coqc", "coqtop", "coq_makefile", "make")}
    if not all(tools.values()):
        raise guard.ScanError("required declared compiler/build tool unavailable")
    env = os.environ.copy()
    # Keep declared library selection (including the saved stand-in), not
    # ambient make/compiler overrides or a parent's jobserver/quick mode.
    selection = {"COQLIB", "COQRUNTIMELIB", "ROCQLIB", "ROCQRUNTIMELIB", "COQPATH", "ROCQPATH"}
    for name in list(env):
        if name in {"MAKEFLAGS", "MFLAGS", "GNUMAKEFLAGS", "MAKEOVERRIDES", "MAKEFILES",
                    "MAKELEVEL", "VOS", "VOK"} or (
                name.startswith(("COQ", "ROCQ")) and name not in selection):
            env.pop(name)
    for option, name in (("--version", "compiler-version"), ("-config", "compiler-config")):
        run([tools["coqc"], option], snapshot, env, work / f"{name}.log")
    run([tools["coq_makefile"], "-f", "_CoqProject", "-o", "Makefile.coq"], snapshot, env,
        work / "configure.log")
    run([tools["make"], "-f", "Makefile.coq", f"-j{jobs}",
         "COQBIN=" + str(Path(tools["coqc"]).parent) + os.sep, "COQFLAGS=-q", "all"],
        snapshot, env, work / "build.log", timeout=3000)
    for file in files:
        if not (snapshot / Path(file).with_suffix(".vo")).is_file():
            raise guard.ScanError(f"missing full .vo product: {file}")
    references, identities, extractions = collect_evidence(
        snapshot, work, files, unreached, env, tools["coqc"], tools["coqtop"])
    for name, data in originals.items():
        if (root / name).read_bytes() != data:
            raise guard.ScanError(f"source changed during compiler validation: {name}")
    for name, data in policy.items():
        if Path(name).read_bytes() != data:
            raise guard.ScanError(f"guard policy changed during compiler validation: {name}")
    manifest = {"mode": "fresh full .vo build (-q) plus whole-file About replay; no reuse",
                "policy": {f: digest(b) for f, b in policy.items()},
                "tools": tools, "sources": {f: digest(b) for f, b in originals.items()},
                "environment": {k: env.get(k, "") for k in (
                    "COQLIB", "ROCQLIB", "ROCQRUNTIMELIB", "COQPATH", "ROCQPATH", "OCAMLPATH")},
                "compiler_version": (work / "compiler-version.log").read_text(),
                "compiler_config": (work / "compiler-config.log").read_text(),
                "products": {f: digest((snapshot / Path(f).with_suffix(".vo")).read_bytes()) for f in files},
                "extractions": extractions}
    (work / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"probe-arity compiler evidence: {len(files)} freshly built files; {len(extractions)} protected extractions; {work}")
    return snapshot, files, references, identities, work
