#!/usr/bin/env python3
"""Verify the four invariants the issue dependency graph must satisfy before the
catalog can be implemented issue-by-issue with parallel agents.

    1 ACYCLIC       a valid total order exists at all
    2 CONSISTENT    body "Depends on:" lines == native blockedBy relations
                    (the campaign contract makes the BODY the source of truth,
                    so a native-only edge is as much a defect as a missing one)
    3 RESOLVED      no dependency is left as a bare item-id; an implementing
                    agent cannot follow "maclane:VIII.2:construction2"
    4 CONFLICT-FREE two issues with NO dependency path between them must not
                    both CREATE the same new module file -- otherwise a
                    scheduler calls them independent and two agents collide

Property 4 is not expressible in the dependency graph, which is exactly why it
needs its own check: the graph can be perfect and the schedule still unsafe.

Usage:  check_graph.py [--json]
Exit:   0 = all invariants hold; 1 = at least one violation.
"""
import json
import os
import re
import subprocess
import sys
from collections import Counter, defaultdict

REPO = "jwiegley/category-theory"
# This file lives at <repo>/doc/plan/books/tools/check_graph.py, so the repo root
# is FIVE dirname()s up: tools -> books -> plan -> doc -> <repo>. Getting this
# off by one silently breaks the "file already exists" filter in creates(),
# which then treats every EXISTING module as newly-proposed and reports
# hundreds of phantom conflicts (Theory/Universal/Arrow.v alone produced ~30).
ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                    "..", "..", "..", ".."))
BOOKS = os.path.join(ROOT, "doc/plan/books")
if not os.path.isdir(os.path.join(ROOT, "Theory")):
    sys.exit("ROOT misresolved to %r (expected the repo root containing Theory/)"
             % ROOT)

# --- dependency extraction -------------------------------------------------
# Two innocent constructions must NOT be read as dependencies. Getting this
# wrong reported 190 phantom unresolved deps and 3 phantom cycles:
#   (a) an item-id as the LABEL of an already-resolved dep:
#         "Depends on: #530 (`maclane:VIII.1:remark2`) (equalizers ...)"
#   (b) trailing DOWNSTREAM prose on the same line, which points the other way:
#         "... Required by the member calculus (`maclane:VIII.4:def-member`)"
#         "The pullbacks obtained here feed ... (`maclane:VIII.4:prop2`)"
# Reading (b) as a dependency INVERTS the arrow, which is how the phantom
# cycles appeared.
DEP_LINE = re.compile(r"^\s*[-*]?\s*Depends on:")
# Cues after which an item-id on a "Depends on:" line is NOT a dependency.
# Two families, both load-bearing:
#   DOWNSTREAM ("Required by", "feeds", "Provides") -- points the other way, so
#     reading it as a dep INVERTS the arrow and manufactures phantom cycles;
#   SOFT ("Benefits from", "is the same obligation as", "Related (NOT
#     blocking)") -- a real relation but NOT a prerequisite. Treating a soft
#     mention as a blocker over-constrains the schedule: #541 says only
#     "Benefits from the finite-biproduct matrix calculus", and promoting that
#     to a hard edge needlessly serialized it behind #536.
REVERSE_CUE = re.compile(
    r"\b(Required by|Provides?|feeds?|used by|Downstream|is recorded on"
    r"|tracked by|consumed by|Related \(NOT blocking\)|Benefits? from"
    r"|same obligation as|Benefits)\b", re.I)
# A resolved dep labels its item-id after the issue number. The paren often
# carries explanatory prose too -- "#731 (`awodey:9.7:remark21` — structure on
# slice categories)" -- so do NOT require the paren to hold the id alone, or
# every well-annotated dependency is reported as unresolved.
RESOLVED_LABEL = re.compile(r"#\d+\s*\(\s*`[^`]*`[^)]*\)")
ITEM_ID = re.compile(r"\b((?:maclane|awodey|7sketches|riehl):[^\s`,\)\];]+)")
TRAILER = re.compile(r"<!-- catalog: (\{.*?\}) -->\s*$")

# --- module-creation extraction (property 4) -------------------------------
# A path may be named because the issue CREATES it or merely IMPORTS it. Only
# creation collides. Imports follow a donor marker; some issues put a proposal
# AND its donors on one line ("Suggested path: `A.v`. Donors: `B.v`"), so
# truncate at the marker rather than dropping the line.
SECTIONS = re.compile(
    r"^##\s*(Work to be done|Definition of Done|Verification)\s*$", re.M)
VPATH = re.compile(r"`?([A-Z][A-Za-z0-9_]*(?:/[A-Za-z0-9_]+)*\.v)`?")
DONOR = re.compile(
    r"(In-tree donors|Donors?\s*:|Require\s+Import|Downstream consumers?)", re.I)


def sh(cmd):
    p = subprocess.run(cmd, capture_output=True, text=True)
    if p.returncode:
        sys.exit("command failed: " + " ".join(cmd) + "\n" + p.stderr)
    return p.stdout


def body_deps(body):
    out = set()
    for line in (body or "").splitlines():
        if not DEP_LINE.match(line):
            continue
        m = REVERSE_CUE.search(line)
        if m:
            line = line[:m.start()]
        out |= {int(x) for x in re.findall(r"#(\d+)", line)}
    return out


def unresolved_deps(body):
    out = set()
    for line in (body or "").splitlines():
        if not DEP_LINE.match(line):
            continue
        m = REVERSE_CUE.search(line)
        if m:
            line = line[:m.start()]
        out |= set(ITEM_ID.findall(RESOLVED_LABEL.sub("", line)))
    return out


def creates(body):
    if not body:
        return set()
    out = set()
    for i in [m.start() for m in SECTIONS.finditer(body)]:
        nxt = body.find("\n## ", i + 4)
        for line in body[i: nxt if nxt != -1 else len(body)].splitlines():
            d = DONOR.search(line)
            if d:
                line = line[:d.start()]
            out |= set(VPATH.findall(line))
    return {p for p in out if not os.path.exists(os.path.join(ROOT, p))}


def fetch():
    issues = json.loads(sh(["gh", "issue", "list", "-R", REPO, "--limit", "900",
                            "--state", "all", "--json", "number,title,body,labels"]))
    book = {i["number"]: i for i in issues
            if any(l["name"].startswith("book:") for l in i["labels"])}
    nums, native = sorted(book), {}
    for k in range(0, len(nums), 40):
        q = 'query{repository(owner:"jwiegley",name:"category-theory"){'
        for n in nums[k:k + 40]:
            q += ('i%d:issue(number:%d){number blockedBy(first:50){nodes{number}}} '
                  % (n, n))
        q += "}}"
        for _, v in json.loads(sh(["gh", "api", "graphql", "-f", "query=" + q]))[
                "data"]["repository"].items():
            if v:
                native[v["number"]] = {x["number"] for x in v["blockedBy"]["nodes"]}
    return book, native


def main():
    as_json = "--json" in sys.argv
    book, native = fetch()
    ids = set(book)
    maps = {}
    for bk in ("maclane", "awodey", "seven-sketches", "riehl"):
        p = os.path.join(BOOKS, bk, "issue-map.json")
        if os.path.exists(p):
            maps.update(json.load(open(p)))

    violations = []

    # 2 CONSISTENT
    for n in sorted(ids):
        b, nv = body_deps(book[n]["body"]), native.get(n, set()) & ids
        if b != nv:
            violations.append(
                "CONSISTENT #%d: body %s != native %s (missing native %s; "
                "native-only %s)" % (n, sorted(b), sorted(nv),
                                     sorted(b - nv), sorted(nv - b)))

    # 3 RESOLVED
    for n in sorted(ids):
        for x in sorted(unresolved_deps(book[n]["body"])):
            tgt = maps.get(x) or maps.get(x.split("@")[0])
            violations.append(
                "RESOLVED #%d: dependency left as bare item-id '%s'%s" %
                (n, x, " -> should cite #%d" % tgt if tgt else
                 " (no issue: item is PRESENT/unfiled -- reword, do not cite)"))

    # 1 ACYCLIC
    g = {n: native.get(n, set()) & ids for n in ids}
    color, cycles = {}, []
    def dfs(u, stack):
        color[u] = 1
        stack.append(u)
        for v in g[u]:
            if color.get(v, 0) == 0:
                dfs(v, stack)
            elif color.get(v) == 1:
                cycles.append(stack[stack.index(v):] + [v])
        color[u] = 2
        stack.pop()
    sys.setrecursionlimit(10000)
    for n in ids:
        if color.get(n, 0) == 0:
            dfs(n, [])
    for c in cycles:
        violations.append("ACYCLIC: cycle " + " <- ".join("#%d" % x for x in c))

    # 4 CONFLICT-FREE
    mod = defaultdict(set)
    for n in ids:
        for p in creates(book[n]["body"]):
            mod[p].add(n)
    RC = {}
    def reach(s):
        if s not in RC:
            seen, st = {s}, [s]
            while st:
                u = st.pop()
                for v in g[u]:
                    if v not in seen:
                        seen.add(v)
                        st.append(v)
            RC[s] = seen
        return RC[s]
    # A co-location conflict is DISCHARGED either by a dependency path (an
    # order exists) or by an explicit serialize-group declaring the pair as
    # peers that must not share a parallel wave. The second kind cannot be an
    # edge: asserting precedence that does not exist over-constrains the
    # schedule, and a fabricated edge is worse than a documented hazard because
    # it silently serializes work that could have run in parallel. So the group
    # file is the honest home for them -- but it must be READ here, or the gate
    # can never reach clean and stops being a gate.
    ser_path = os.path.join(BOOKS, "graph/serialize-groups.json")
    acknowledged = set()
    groups = json.load(open(ser_path)) if os.path.exists(ser_path) else []
    for grp in groups:
        ns = sorted(grp.get("issues") or [])
        for i, a in enumerate(ns):
            for b in ns[i + 1:]:
                acknowledged.add((a, b))

    hazards, ack_pairs = [], []
    for p, ns in sorted(mod.items()):
        ns = sorted(ns)
        for i, a in enumerate(ns):
            for b in ns[i + 1:]:
                if b in reach(a) or a in reach(b):
                    continue
                if (a, b) in acknowledged:
                    ack_pairs.append((p, a, b))
                    continue
                hazards.append((p, a, b))
                violations.append(
                    "CONFLICT-FREE %s: #%d and #%d both create it with no "
                    "dependency path and no serialize-group -- a scheduler "
                    "would call them independent and they would collide" % (p, a, b))

    # layering (report only)
    layer = {}
    def lay(u, seen=frozenset()):
        if u in layer:
            return layer[u]
        if u in seen:
            return 0
        layer[u] = 1 + max([lay(v, seen | {u}) for v in g[u]], default=-1)
        return layer[u]
    for n in ids:
        lay(n)
    dist = Counter(layer.values())

    if as_json:
        print(json.dumps({
            "issues": len(ids),
            "edges": sum(len(v) for v in g.values()),
            "acyclic": not cycles,
            "violations": violations,
            "layers": {str(k): dist[k] for k in sorted(dist)},
            "hazards": [[p, a, b] for p, a, b in hazards],
            "acknowledged_serialize_pairs": [[p, a, b] for p, a, b in ack_pairs],
        }, indent=1))
    else:
        print("issues %d | native edges %d | layers %d"
              % (len(ids), sum(len(v) for v in g.values()),
                 max(layer.values()) + 1 if layer else 0))
        for L in sorted(dist):
            print("   layer %d: %4d%s" % (L, dist[L],
                  "  <- no prerequisites, fully parallel" if L == 0 else ""))
        print()
        if ack_pairs:
            print("serialize-groups (acknowledged, NOT violations -- these pairs")
            print("share a new file with no logical precedence; a scheduler must")
            print("not put them in the same parallel wave): %d pairs" % len(ack_pairs))
            for p_, a, b in ack_pairs:
                print("   %s: #%d + #%d" % (p_, a, b))
            print()
        if violations:
            print("VIOLATIONS: %d" % len(violations))
            for v in violations:
                print("  " + v)
        else:
            print("ALL FOUR INVARIANTS HOLD "
                  "(acyclic, consistent, resolved, conflict-free)")
    return 1 if violations else 0


if __name__ == "__main__":
    sys.exit(main())
