#!/usr/bin/env python3
"""Pre-filing check: does a draft propose a NEW module file that an
already-filed issue also proposes?

Two issues that independently propose the same new .v file, with no
cross-link between them, is this campaign's most persistent defect: it
recurred in Ch6, Ch7, Ch8 and Ch9. The drafter dedups on TITLES, and two
issues can have entirely unrelated titles while targeting the same file --
the module path is the better signal.

WHY THIS SCRIPT EXISTS (the Ch9 lesson): the ad-hoc version of this check
indexed only lines containing the word "Suggested", and MISSED 3 of the 4
real collisions in Ch9 -- #658 and #320 phrase their proposals differently
("The bifunctor should live in ...", a bare path in a Work-to-be-done
bullet). Recall matters far more than precision here: a false positive
costs one glance, a false negative ships a duplicated obligation.

KNOWN BLIND SPOT (Riehl Ch6): this script matches PROPOSED MODULE PATHS. Two issues
that build the SAME CONSTRUCTION under DIFFERENT paths are structurally
invisible to it, and to check_graph.py's conflict-free invariant as well.
Two such pairs shipped and were found only by reading:
  * #972 `Construction/Fractions.v` vs #1028 `Construction/Localization/Fractions.v`
    -- the same zig-zag localization; C[C^-1] is the W=all case of C[W^-1].
  * #1011 `Instance/Module/Complex.v` vs #557 `Structure/Abelian/Homology.v`
    -- the same chain complexes and the same graded tensor product.
Both are now recorded in graph/serialize-groups.json with a disclosure on the
issues. There is no mechanical fix here short of comparing the CONTENT of Work
items; the mitigation is that a same-concept-different-path pair must be caught
by the drafter's backlog search or by review, and this note exists so a future
reader does not mistake a clean collision report for an absence of overlap.

So: index every .v path appearing in the *Work to be done* / *Definition of
Done* / *Verification* sections of every filed issue, then intersect with
the same extraction over the new drafts. Paths that already EXIST in the
repo are dropped -- those are references to real files, not proposals.

Usage: check_collisions.py <ROMAN> <SCRATCH_DIR> <BOOK>
Exit status is always 0; this is an advisory report, read it.
"""
import json, os, re, subprocess, sys

R, SCRATCH, BOOK = sys.argv[1], sys.argv[2], sys.argv[3]
REPO = "jwiegley/category-theory"
ROOT = "/Users/johnw/src/category-theory/master"

SECTIONS = re.compile(
    r"^##\s*(Work to be done|Definition of Done|Verification)\s*$", re.M)
VPATH = re.compile(r"`?([A-Z][A-Za-z0-9_]*(?:/[A-Za-z0-9_]+)*\.v)`?")


# A path can be named because the issue CREATES it or merely IMPORTS it. Only
# creation collides. Issues declare imports after a donor marker -- "In-tree
# donors: `A.v`, `B.v` (new)" -- and sometimes put a proposal and its donors on
# ONE line ("Suggested path: `A.v`. Donors: `B.v`"), so truncate at the marker
# rather than dropping the whole line.
DONOR = re.compile(r"(In-tree donors|Donors?\s*:|Require\s+Import|Downstream consumers?)", re.I)


def proposed(body):
    """.v paths this issue would CREATE, minus files that already exist.

    Excludes imports. Getting this wrong is not academic: counting donor
    mentions as proposals inflated the hazard report badly -- for
    Adjunction/Conjugate.v it reported 6 conflicting pairs when only ONE issue
    (#394) creates the file and the other four just list it as
    "`Adjunction/Conjugate.v` (new)" under In-tree donors. 20 of 27 edges then
    "proposed" by the resolver already existed, because the real relationship
    was creator/consumer and had been recorded correctly all along.
    """
    if not body:
        return set()
    out = set()
    for i in [m.start() for m in SECTIONS.finditer(body)]:
        nxt = body.find("\n## ", i + 4)
        chunk = body[i: nxt if nxt != -1 else len(body)]
        for line in chunk.splitlines():
            d = DONOR.search(line)
            if d:
                line = line[: d.start()]
            out |= set(VPATH.findall(line))
    return {p for p in out if not os.path.exists(os.path.join(ROOT, p))}


filed = json.loads(subprocess.run(
    ["gh", "issue", "list", "-R", REPO, "--limit", "900", "--state", "all",
     "--json", "number,title,body"], capture_output=True, text=True).stdout)
index, titles = {}, {}
for i in filed:
    titles[i["number"]] = i["title"]
    for p in proposed(i.get("body")):
        index.setdefault(p, set()).add(i["number"])

raw = open(os.path.join(SCRATCH, f"drafts-{R}.md")).read()
hits = 0
for d in raw.split("\n---8<---\n"):
    t = re.search(r'^title:\s*"(.*)"', d, re.M)
    if not t:
        continue
    for p in sorted(proposed(d)):
        # Drop the draft's OWN issue: normally this runs pre-filing so it
        # cannot match itself, but re-running after filing (to confirm a
        # repair) otherwise reports every draft as colliding with itself.
        others = sorted(h for h in index.get(p, ()) if titles[h] != t.group(1))
        if others:
            hits += 1
            print(f"\n  DRAFT: {t.group(1)[:78]}")
            print(f"   proposes NEW module {p}, also proposed by:")
            for h in others:
                linked = f"#{h}" in d
                print(f"     #{h} {'[cross-linked]' if linked else '[NO CROSS-LINK]'}"
                      f"  {titles[h][:66]}")

print(f"\ncollision candidates: {hits}")
print("Each needs a judgement: same obligation -> dedup instead of filing;")
print("different obligations in one file -> file, but CROSS-LINK both ways")
print("(a Depends-on on the consumer, a 'Downstream consumer' note on the")
print("producer), so neither is built twice.")
