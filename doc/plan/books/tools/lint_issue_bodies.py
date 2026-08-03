#!/usr/bin/env python3
"""Corpus-wide linter for the issue-body defects THIS CAMPAIGN KEEPS CREATING.

check_graph.py validates the dependency GRAPH. This validates the issue BODY
TEXT that the graph is derived from, catching the failure modes that a scripted
edit introduces and that check_graph can only see indirectly (or not at all):

  L1 duplicate `<!-- catalog: -->` trailer            (a re-append that did not de-dupe)
  L2 trailer is not the last thing in the body        (silently breaks file_chapter.py's
                                                       id-append path -- it匹 anchors on end-of-body)
  L3 trailer is not parseable JSON                    (a trailing comma from a scripted removal)
  L4 a `Depends on:` line carrying MORE THAN ONE #N   (the six-times-committed defect: a hedge or a
                                                       second clause glued onto a dependency line)
  L5 a `Depends on:` line containing a hedge word     (coordinate / not a prerequisite / same module /
                                                       do not duplicate / NOT blocking)
  L6 a heading or bullet glued to the end of a line   (`...needs.### SHARED` -- a missing newline in a
                                                       scripted insert; this is what produced L4 four
                                                       separate times)
  L7 `Depends on:` appearing OUTSIDE `## Dependencies` (a dependency declared where no reviewer looks)
  L8 a `Depends on: #N (`item-id`)` label whose item-id the TARGET DOES NOT OWN, or which
     belongs to a different book than the target issue. Three separate scripted repairs
     picked an arbitrary id out of a reverse map and cited, e.g., a Riehl item as the reason
     one issue depends on a Mac Lane delooping issue. Truthful (the target does cover that
     item) but misleading, and invisible to check_graph, which only requires SOME label.

Usage: lint_issue_bodies.py [--fix-whitespace]   (read-only by default)
"""
import json, re, subprocess, sys, collections

REPO = "jwiegley/category-theory"
HEDGE = re.compile(r"\b(coordinate|not a prerequisite|same module|do not duplicate"
                   r"|NOT blocking|ordering constraint|does not supply)\b", re.I)
DEP = re.compile(r"^\s*[-*]?\s*Depends on:")

def bodies(nums):
    out = {}
    for i in range(0, len(nums), 60):
        ch = nums[i:i + 60]
        q = ('query{repository(owner:"jwiegley",name:"category-theory"){'
             + " ".join("i%d: issue(number:%d){body}" % (n, n) for n in ch) + "}}")
        r = subprocess.run(["gh", "api", "graphql", "-f", "query=" + q],
                           capture_output=True, text=True)
        try:
            d = json.loads(r.stdout)["data"]["repository"]
        except Exception:
            continue
        for n in ch:
            v = d.get("i%d" % n)
            if v:
                out[n] = v["body"]
    return out

def lint(n, b):
    bad = []
    tr = re.findall(r"<!-- catalog: (\{.*?\}) -->", b)
    if len(tr) > 1:
        bad.append(("L1", "duplicate trailer x%d" % len(tr)))
    if tr:
        if not b.rstrip().endswith("-->"):
            bad.append(("L2", "trailer is not last"))
        for t in tr:
            try:
                json.loads(t)
            except Exception as e:
                bad.append(("L3", "trailer not valid JSON: %s" % str(e)[:40]))
    dep_sec = re.search(r"(?ms)^## Dependencies\b(.*?)(?=^## |\n<!-- catalog|\Z)", b)
    sec = dep_sec.group(1) if dep_sec else ""
    for line in b.splitlines():
        if not DEP.match(line):
            continue
        if len(re.findall(r"#\d+", line)) > 1:
            bad.append(("L4", "multiple #N on one Depends-on line: " + line[:70]))
        if HEDGE.search(line):
            bad.append(("L5", "hedge inside a Depends-on line: " + line[:70]))
        if dep_sec and line not in sec:
            bad.append(("L7", "Depends-on outside ## Dependencies: " + line[:60]))
    # L6: a markdown heading or a task bullet that is NOT at column 0 of its own
    # line -- i.e. a scripted insert that forgot its newline. Checked by an
    # explicit line scan; a lookbehind here silently over-matched 998 times.
    for ln in b.splitlines():
        stripped = ln.lstrip()
        for tok in ("###", "- [ ] ", "- Related (NOT"):
            # a line that legitimately BEGINS with the token is fine; we are
            # looking for one embedded mid-line, which means a missing newline.
            if stripped.startswith(tok):
                continue
            i = ln.find(tok)
            if i > 0:
                bad.append(("L6", "%r embedded mid-line: %s" % (tok.strip(), ln[max(0, i - 45):i + 25])))
                break
    for m in LABEL.finditer(b):
        tgt, lab = int(m.group(1)), m.group(2)
        owned = OWNS.get(tgt)
        if owned and lab not in owned:
            bad.append(("L8", "#%d's label `%s` is not an item id that issue owns" % (tgt, lab)))
    return bad

# L8 needs the item-id registers
import glob as _glob
OWNS = {}
for _p in _glob.glob("doc/plan/books/*/issue-map.json"):
    for _k, _v in json.load(open(_p)).items():
        OWNS.setdefault(int(_v), set()).add(_k.split("@")[0])
LABEL = re.compile(r"Depends on:\s*#(\d+)\s*\(`([^`]+)`\)")

nums = json.load(open("/tmp/all-issue-nums.json"))
bs = bodies(nums)
counts = collections.Counter()
problems = []
for n in sorted(bs):
    for code, msg in lint(n, bs[n]):
        counts[code] += 1
        problems.append((n, code, msg))
print("issues linted: %d" % len(bs))
print("by rule: %s" % dict(counts))
for p in problems[:40]:
    print("  #%-5d %s  %s" % p)
if len(problems) > 40:
    print("  ... and %d more" % (len(problems) - 40))
sys.exit(1 if problems else 0)
