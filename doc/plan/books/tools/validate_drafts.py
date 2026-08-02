#!/usr/bin/env python3
"""Structural validation of a chapter's drafts + duplicates against the
frozen issue contract. Usage: validate_drafts.py <ROMAN> <SCRATCH_DIR>"""
import re, json, sys, os

import glob
R, SCRATCH = sys.argv[1], sys.argv[2]
BOOK = sys.argv[3] if len(sys.argv) > 3 else "maclane"
PROJECT = {"maclane": "4", "awodey": "5", "seven-sketches": "6", "riehl": "10"}[BOOK]
BOOKSDIR = "/Users/johnw/src/category-theory/master/doc/plan/books"
FILED = f"{BOOKSDIR}/{BOOK}/filed-issues.tsv"


def split_draft(d):
    """Return (yaml_header, body) tolerating both ```yaml fences and bare
    YAML headers (fields until the first blank line, then the body)."""
    d = d.strip()
    m = re.match(r"^```yaml\n(.*?)\n```\n(.*)$", d, re.S)
    if m:
        return m.group(1), m.group(2)
    parts = d.split("\n\n", 1)
    if len(parts) == 2 and re.search(r"^title:", parts[0], re.M):
        return parts[0], parts[1]
    return None, None

raw = open(os.path.join(SCRATCH, f"drafts-{R}.md")).read()
drafts = [d.strip() for d in raw.split("\n---8<---\n") if d.strip()]
print(f"drafts: {len(drafts)}")
ids_covered, dep_items, dep_filed, problems = set(), set(), set(), []
for i, d in enumerate(drafts, 1):
    y, body = split_draft(d)
    if y is None:
        problems.append(f"draft {i}: no parseable yaml header"); continue
    title = re.search(r'^title:\s*"(.*)"', y, re.M)
    labels = re.search(r"^labels:\s*\[(.*)\]", y, re.M)
    projects = re.search(r"^projects:\s*\[(.*)\]", y, re.M)
    covers = re.search(r"^covers:\s*\[(.*)\]", y, re.M)
    if not (title and labels and projects and covers):
        problems.append(f"draft {i}: missing yaml field(s)"); continue
    if projects.group(1).strip() != PROJECT:
        problems.append(f"draft {i}: projects={projects.group(1)} (expected {PROJECT})")
    labs = [l.strip() for l in labels.group(1).split(",")]
    if f"book:{BOOK}" not in labs or "coverage-gap" not in labs or not any(l.startswith("kind:") for l in labs):
        problems.append(f"draft {i}: labels {labs}")
    cov = [c.strip() for c in covers.group(1).split(",") if c.strip()]
    for c in cov:
        if c in ids_covered:
            problems.append(f"draft {i}: {c} covered twice")
        ids_covered.add(c)
    tr = re.search(r"<!-- catalog: (\{.*?\}) -->\s*$", body)
    if not tr:
        problems.append(f"draft {i}: no catalog trailer")
    else:
        t = json.loads(tr.group(1))
        if sorted(t.get("ids", [])) != sorted(cov):
            problems.append(f"draft {i}: trailer ids != covers")
    # tolerate an optional list-bullet prefix ("- Depends on: ...")
    # authoritative dep set = trailer `deps` (robust to prose drift:
    # backticks, multiple-per-line, parenthetical forward-refs)
    tj = re.search(r"<!-- catalog: (\{.*?\}) -->", body)
    for dep in (json.loads(tj.group(1)).get("deps", []) if tj else []):
        dep = str(dep).strip().strip("`")
        (dep_filed if dep.startswith("#") else dep_items).add(dep.rstrip(")`,."))
    for sec in ["## Source", "## Background", "## Current state in the library",
                "## Work to be done", "## Definition of Done", "## Verification", "## Dependencies"]:
        if sec not in body:
            problems.append(f"draft {i}: missing section {sec}")
    if not re.search(r"ncatlab\.org|wikipedia\.org", body):
        problems.append(f"draft {i}: no nLab/Wikipedia link")

dup_path = os.path.join(SCRATCH, f"duplicates-{R}.json")
dups = json.load(open(dup_path)) if os.path.exists(dup_path) else []
for du in dups:
    if not (du.get("item_id") and du.get("issue") and du.get("append_block")):
        problems.append(f"duplicate entry malformed: {du}")
print(f"items covered by drafts: {len(ids_covered)}; duplicates: {len(dups)}")
dangling = dep_items - ids_covered
print(f"same-chapter dep ids not covered: {sorted(dangling) if dangling else 'none'}")
# cross-book deps reference prior books' issues, so check ALL books' filed lists
fmap = set()
for tsv in glob.glob(f"{BOOKSDIR}/*/filed-issues.tsv"):
    for l in open(tsv):
        if l.strip():
            fmap.add(int(l.split("\t")[0]))
bad = [x for x in dep_filed if int(x.lstrip("#")) not in fmap]
print(f"filed deps referenced: {len(dep_filed)}; unknown: {bad if bad else 'none'}")
print("PROBLEMS:" if problems else "STRUCTURALLY CLEAN")
for p in problems:
    print(" -", p)
sys.exit(1 if problems else 0)
