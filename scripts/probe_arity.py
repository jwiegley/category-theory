#!/usr/bin/env python3
"""Compiler-backed arity hygiene for Coq Fail commands (#1380).

Only an explicit-@ bare Check supplies an eager positive control. Fresh
compiler references and whole-file canonical-name queries reject notation
capture and generated-name shadowing. Source scanning alone is a weaker
syntax preflight, never the semantic gate. See doc/PROBE_ARITY.md.
"""

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import shlex
import sys


class ScanError(ValueError):
    pass


@dataclass(frozen=True)
class Token:
    text: str
    start: int


@dataclass(frozen=True)
class Instance:
    name: str
    arity: int
    start: int


IDENT = r"[^\W\d][\w']*|_[\w']*"
QUALID = re.compile(rf"(?:{IDENT})(?:\.(?:{IDENT}))*", re.UNICODE)
DECL = set("Definition Example Lemma Theorem Fact Corollary Remark Proposition "
           "Let Instance Fixpoint CoFixpoint Inductive CoInductive Record "
           "Structure Class Axiom Axioms Parameter Parameters Variable "
           "Variables Hypothesis Hypotheses".split())
PREFIX = set("Fail Time Succeed Local Global Export Polymorphic Monomorphic "
             "Program Cumulative NonCumulative".split())
# Namespace or grammar changes invalidate textual name identity. Unknown
# vernacular commands are barriers too; proof tactics are handled separately.
# Declarations and Context are handled separately in scan().
NEUTRAL = set("Universe Universes Constraint Constraints Set Unset "
              "Generalizable Arguments About Print".split())


def string_end(source, start):
    """Coq strings, also inside comments, escape quotes by doubling them."""
    i = start + 1
    while i < len(source):
        if source[i] != '"':
            i += 1
        elif source.startswith('""', i):
            i += 2
        else:
            return i + 1
    raise ScanError(f"unterminated string at offset {start}")


def lex(source):
    """Comments nest; Coq strings escape quotes by doubling them."""
    i = 0
    while i < len(source):
        if source[i].isspace():
            i += 1
        elif source.startswith("(*", i):
            start, depth = i, 1
            i += 2
            while i < len(source) and depth:
                if source[i] == '"':
                    i = string_end(source, i)
                elif source.startswith("(*", i):
                    depth += 1
                    i += 2
                elif source.startswith("*)", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ScanError(f"unterminated comment at offset {start}")
        elif source[i] == '"':
            start = i
            i = string_end(source, start)
            # Keep an opaque token: dropping it could manufacture a bare Check.
            yield Token('"string"', start)
        else:
            match = QUALID.match(source, i) or re.compile(r"\d+").match(source, i)
            if match:
                yield Token(match[0], i)
                i = match.end()
            else:
                yield Token(source[i], i)
                i += 1


def commands(source):
    command = []
    for token in lex(source):
        command.append(token)
        # Qualid dots are consumed by lex. Coq's sentence dot must be followed
        # by whitespace, a comment, or EOF; projection/notation dots aren't it.
        end = token.start + 1
        if token.text == "." and (end == len(source) or
                                  source[end].isspace() or
                                  source.startswith("(*", end)):
            yield command
            command = []
    if command:
        raise ScanError(f"unterminated command at offset {command[0].start}")


def head(tokens):
    """Skip attributes and vernacular control/modifier prefixes."""
    i = 0
    while i < len(tokens):
        if tokens[i] == "#" and tokens[i + 1:i + 2] == ["["]:
            depth = 1
            i += 2
            while i < len(tokens) and depth:
                depth += (tokens[i] == "[") - (tokens[i] == "]")
                i += 1
        elif tokens[i] in PREFIX:
            i += 1
        elif tokens[i] in {"Timeout", "Redirect"}:
            i += 2
        else:
            break
    return i


def instances(command):
    words = [t.text for t in command]
    h = head(words)
    binders = set()
    if h < len(words) and words[h] in DECL:
        binders.add(h + 1)
        # Mutual declarations' heads also bind, rather than instantiate.
        if words[h] in {"Fixpoint", "CoFixpoint", "Inductive", "CoInductive"}:
            depth = matches = 0
            for i, word in enumerate(words):
                depth += (word in {"(", "{", "["}) - (word in {")", "}", "]"})
                matches += (word == "match") - (word == "end")
                if word == "with" and depth == 0 and matches == 0:
                    binders.add(i + 1)
    result = []
    for i, token in enumerate(command):
        if words[i + 1:i + 3] != ["@", "{"]:
            continue
        if not QUALID.fullmatch(token.text):
            raise ScanError(f"unrecognized universe target at offset {token.start}")
        try:
            close = words.index("}", i + 3)
        except ValueError as error:
            raise ScanError(f"unclosed universe instance at offset {token.start}") from error
        # Sort expressions also admit max/successor syntax, not arity slots.
        if i in binders or token.text == "Type":
            continue
        levels = words[i + 3:close]
        if any(not QUALID.fullmatch(u) for u in levels):
            raise ScanError(f"unsupported universe instance at offset {token.start}")
        result.append(Instance(token.text, len(levels), token.start))
    return result


def bare_check(command, uses):
    words = [t.text for t in command]
    if not words or words[0] != "Check" or len(uses) != 1:
        return None
    term = words[1:-1]
    while term[:1] == ["("] and term[-1:] == [")"]:
        term = term[1:-1]
    if term[:1] != ["@"]:
        return None
    term = term[1:]
    use = uses[0]
    if (term[:3] == [use.name, "@", "{"] and term[-1:] == ["}"]
            and len(term) == use.arity + 4):
        return use
    return None


def tactic_regions(command):
    """Offsets in balanced ltac:/ltac2: quotations, including nested terms."""
    words = [t.text for t in command]
    regions = []
    for i, word in enumerate(words):
        if word not in {"ltac", "ltac2"} or words[i + 1:i + 3] != [":", "("]:
            continue
        depth, j = 1, i + 3
        while j < len(words) and depth:
            depth += (words[j] == "(") - (words[j] == ")")
            j += 1
        if depth:
            raise ScanError(f"unclosed tactic quotation at offset {command[i].start}")
        regions.append((command[i].start, command[j - 1].start))
    return regions


def glob_references(source, data, logical_name):
    """Validate a freshly compiled .glob and index direct global references.

    This is not a cache validator: only the fresh-build driver may supply
    semantic evidence. Digest/header checks additionally reject missing,
    stale or swapped files; different references at one span are ambiguous.
    """
    lines = data.splitlines()
    if lines[:2] != ["DIGEST " + hashlib.md5(source).hexdigest(), "F" + logical_name]:
        raise ScanError("stale or swapped .glob (source digest/logical module mismatch)")
    spans = {}
    for line in lines[2:]:
        if not line.startswith("R"):
            continue
        match = re.fullmatch(r"R(\d+):(\d+) (\S+) (\S+) (\S+) (\S+)", line)
        if not match:
            raise ScanError("malformed .glob reference")
        start, end = map(int, match.groups()[:2])
        if not 0 <= start <= end < len(source):
            raise ScanError(".glob reference outside source")
        spans.setdefault((start, end), set()).add(match.groups()[2:])
    # A notation or local variable is not a direct constant reference.
    kinds = {"def", "inst", "rec", "class", "constr", "thm", "ind", "scheme", "proj", "ax"}
    return {span: next(iter(refs)) for span, refs in spans.items()
            if len(refs) == 1 and next(iter(refs))[-1] in kinds}


def reference_at(source, use, references):
    start = len(source[:use.start].encode())
    return references.get((start, start + len(use.name.encode()) - 1))


def scan(source, references=None, identities=None):
    """Match explicit-@ Checks in conservative resolution epochs.

    Without compiler evidence this is ONLY a syntax preflight. The real gate
    combines direct .glob references with About identities from a fresh
    whole-file replay. Short .glob paths alone do not identify nested modules.
    """
    if (references is None) != (identities is None):
        raise ScanError("partial compiler evidence")
    controls, negatives, bad_controls = set(), [], []
    epoch = 0
    for command in commands(source):
        words = [t.text for t in command]
        uses = instances(command)
        h = head(words)
        kind = words[h] if h < len(words) else ""
        def key(use):
            evidence = ()
            if references is not None:
                ref = reference_at(source, use, references)
                identity = identities.get(use.start)
                evidence = (ref, identity) if ref is not None and identity is not None else None
            return (epoch, use.name, use.arity, evidence)
        if "Fail" in words:
            # Even user-defined binding notation must write its binder name.
            # Do not guess which bare occurrences bind: require qualification
            # whenever the same short name also occurs without an instance.
            sites = {u.start for u in uses}
            other = {t.text for t in command if t.start not in sites}
            regions = tactic_regions(command)
            for use in uses:
                dynamic = (kind not in DECL | {"Check"} or
                           any(a <= use.start <= b for a, b in regions))
                ambiguous = "." not in use.name and (use.name in other or dynamic)
                identity = key(use)
                negatives.append((use, identity, ambiguous or identity[-1] is None))
            continue
        control = bare_check(command, uses)
        if control:
            identity = key(control)
            if identity[-1] is None:
                bad_controls.append(control)
            else:
                controls.add(identity)
        elif (references is not None and kind in {
                "Definition", "Example", "Lemma", "Theorem", "Fact", "Corollary",
                "Remark", "Proposition", "Let", "Instance"} and "Program" not in words[:h]
              and "using" not in words):
            # Even imported Program Mode can generate names here. Reuse is
            # licensed by the fresh canonical identities, not literal tokens.
            pass
        elif kind not in NEUTRAL:
            # Includes records, inductives, Program, proof/obligation steps,
            # imports, scopes, resets and every unknown extension.
            epoch += 1
    return bad_controls + [u for u, identity, shadowed in negatives
                           if shadowed or identity not in controls]


def load_exceptions(path):
    entries = json.loads(path.read_text())
    if not isinstance(entries, list):
        raise ScanError("exceptions must be a JSON array")
    exceptions = {}
    for entry in entries:
        if (not isinstance(entry, dict) or
                set(entry) != {"file", "constant", "arity", "reason", "evidence"}):
            raise ScanError("exception must have file, constant, arity, reason, evidence")
        if any(not isinstance(entry[field], str) or not entry[field].strip()
               for field in ("file", "constant", "reason", "evidence")):
            raise ScanError("exception file, constant, reason and evidence must be nonempty strings")
        if type(entry["arity"]) is not int or entry["arity"] < 0:
            raise ScanError("exception arity must be a nonnegative integer")
        key = (entry["file"], entry["constant"], entry["arity"])
        if key in exceptions or not QUALID.fullmatch(key[1]):
            raise ScanError(f"invalid/duplicate exception: {key}")
        exceptions[key] = entry
    return exceptions


def check(root, files, exceptions, references=None, identities=None):
    errors, used, count = [], set(), 0
    for name in files:
        source = (root / name).read_bytes().decode()
        count += 1
        try:
            evidence = references[name] if references is not None else None
            names = identities[name] if identities is not None else None
            for use in scan(source, evidence, names):
                key = (name, use.name, use.arity)
                missing = evidence is not None and (reference_at(source, use, evidence) is None
                                                     or use.start not in names)
                if key in exceptions and not missing:
                    used.add(key)
                else:
                    line = source.count("\n", 0, use.start) + 1
                    reason = ("lacks direct compiler reference evidence" if missing else
                              "lacks an unambiguous explicit-@ Check twin in this resolution epoch")
                    errors.append(f"{name}:{line}: {use.name}@{{{use.arity} entries}} {reason}")
        except ScanError as error:
            errors.append(f"{name}: {error}")
    for key in exceptions.keys() - used:
        if key[0] in files:
            errors.append(f"stale exception: {key}")
    return errors, count, len(used)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path("."))
    parser.add_argument("--exceptions", default="scripts/probe_arity_exceptions.json")
    parser.add_argument("--unreached", default="scripts/probe_arity_unreached.json")
    parser.add_argument("--jobs", type=int, default=2, help="fresh build parallelism (1-16)")
    parser.add_argument("--work-dir", type=Path, help="new evidence directory; must not exist")
    parser.add_argument("--syntax-only", action="store_true", help="weaker preflight, NOT semantic validation")
    parser.add_argument("files", nargs="*", help="default: every .v in _CoqProject; semantic mode still rebuilds the project")
    args = parser.parse_args()
    try:
        exceptions_path = args.root / args.exceptions
        exceptions_bytes = exceptions_path.read_bytes()
        exceptions = load_exceptions(exceptions_path)
        if args.syntax_only:
            print("probe-arity: SYNTAX PREFLIGHT ONLY; no compiler identity evidence")
            files = args.files or [word for word in shlex.split(
                (args.root / "_CoqProject").read_text(), comments=True) if word.endswith(".v")]
            root, references, identities = args.root, None, None
        else:
            import probe_arity_build
            root, registered, references, identities, work = probe_arity_build.build(
                args.root, args.jobs, args.unreached, args.work_dir)
            files = args.files or registered
            if not set(files) <= set(registered):
                raise ScanError("selected files outside registered project")
            print(f"probe-arity: semantic evidence manifest: {work / 'manifest.json'}")
        if not files or len(files) != len(set(files)):
            raise ScanError("empty or duplicate source inventory")
        if exceptions_path.read_bytes() != exceptions_bytes:
            raise ScanError("exceptions changed during validation")
        unknown = {key[0] for key in exceptions} - set(files)
        if unknown and not args.files:
            raise ScanError(f"exceptions outside source inventory: {sorted(unknown)}")
        errors, count, used = check(root, files, exceptions, references, identities)
        if not args.syntax_only:
            manifest_path = work / "manifest.json"
            manifest = json.loads(manifest_path.read_text())
            manifest["verification"] = {"files": files, "errors": errors,
                "exceptions_sha256": hashlib.sha256(exceptions_bytes).hexdigest(),
                "exceptions_used": used}
            manifest_path.write_text(json.dumps(manifest, indent=2) + "\n")
    except (OSError, ValueError, TypeError) as error:
        print(f"probe-arity: {error}", file=sys.stderr)
        return 1
    for error in errors:
        print(error, file=sys.stderr)
    print(f"probe-arity: {count} files, {len(errors)} violations, {used} exceptions")
    return bool(errors)


if __name__ == "__main__":
    sys.exit(main())
