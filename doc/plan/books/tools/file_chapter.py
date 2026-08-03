#!/usr/bin/env python3
"""Phase F for a MacLane chapter: file issues from drafts-<R>.md, handle
same-book duplicates (append source blocks to existing issues), keep the
ledger + durable issue map current. Idempotent: skips drafts whose first
covered item already has an issue row in the ledger, and duplicate items
already in the ledger.

Usage: file_chapter.py <ROMAN> <SCRATCH_DIR>
"""
import json, re, subprocess, sys, time, tempfile, os, glob

R, SCRATCH = sys.argv[1], sys.argv[2]
BOOK = sys.argv[3] if len(sys.argv) > 3 else "maclane"
PROJECT = {"maclane": "4", "awodey": "5", "seven-sketches": "6", "riehl": "10"}[BOOK]
REPO = "jwiegley/category-theory"
BOOKS = "/Users/johnw/src/category-theory/master/doc/plan/books"
LEDGER = f"{BOOKS}/ledger.tsv"
ISSUEMAP = f"{BOOKS}/{BOOK}/issue-map.json"
OWNER = "jwiegley"

def split_draft(d):
    """(yaml, body) tolerating ```yaml fences and bare YAML headers."""
    d = d.strip()
    m = re.match(r"^```yaml\n(.*?)\n```\n(.*)$", d, re.S)
    if m:
        return m.group(1), m.group(2)
    parts = d.split("\n\n", 1)
    if len(parts) == 2 and re.search(r"^title:", parts[0], re.M):
        return parts[0], parts[1]
    return None, None


def run(cmd, retries=3):
    for attempt in range(1, retries + 1):
        p = subprocess.run(cmd, capture_output=True, text=True)
        if p.returncode == 0:
            return p.stdout.strip()
        sys.stderr.write(f"FAIL (attempt {attempt}): {' '.join(cmd[:5])}...\n{p.stderr}\n")
        time.sleep(10 * attempt)
    raise RuntimeError(f"command failed after {retries} attempts: {' '.join(cmd)}")

# final classification + first-evidence pointer per item
cls, ev = {}, {}
for vf in sorted(glob.glob(os.path.join(SCRATCH, f"verified-{R}-*.json"))):
    for rec in json.load(open(vf)):
        c = rec["classification"]
        v = (rec.get("verifier") or {}).get("verdict", "")
        if v.startswith("OVERTURNED:"):
            c = v.split(":", 1)[1]
        cls[rec["id"]] = c
        e = rec.get("evidence") or []
        if e:
            # Record UP TO 3 evidence entries, not just the first. The Ch5
            # PRESENT re-verification found the ledger's single-entry rule was
            # systematically transcribing the DEFINITIONAL/NAMING artifact
            # (evidence #1) while the actual theorem sat at #2/#3 — six rows
            # pointed a reader at something asserting nothing about the claim
            # (a bare predicate record, `Equalizer F := Limit F` aliases, a
            # comment line). Keeping several entries makes the ledger
            # self-sufficient without needing a "strongest" heuristic.
            ev[rec["id"]] = "; ".join(
                f"{x['file']}:{x['line']} {x.get('symbol','')}".strip()
                for x in e[:3]
            )
        elif rec.get("out_of_scope_reason"):
            ev[rec["id"]] = "OOS: " + rec["out_of_scope_reason"][:80]

raw = open(os.path.join(SCRATCH, f"drafts-{R}.md")).read()
drafts = [d.strip() for d in raw.split("\n---8<---\n") if d.strip()]

ledger_rows = open(LEDGER).read().splitlines()
ledger_issued = {l.split("\t")[0] for l in ledger_rows[1:] if len(l.split("\t")) >= 3 and l.split("\t")[2].startswith("#")}
ledger_have = {l.split("\t")[0] for l in ledger_rows[1:]}

# (item_id, issue) pairs already in the ledger. The duplicate loop MUST key its
# idempotency skip on this pair, never on the item id alone.
#
# Riehl Ch5, the failure this exists to prevent: the filer aborted mid-run (the
# active gh account flipped and `gh project item-add` failed), leaving #992 and
# #993 created but with no ledger row. Repairing those two rows BY HAND put
# their item ids into `ledger_have`, and the resumed run then skipped all FIVE
# of their duplicate legs -- three appends for riehl:5.2:example6 and two for
# riehl:5.5:example7 were silently never posted, while the drafts kept asserting
# distribution maps naming targets that did not hold the clauses. A skip keyed
# on the item id cannot distinguish "this item's DRAFT leg is filed" from "this
# item's APPEND onto #465 is filed"; a multi-part item legitimately needs both.
ledger_pairs = set()
for _l in ledger_rows[1:]:
    _f = _l.split("\t")
    if len(_f) >= 3 and _f[2].startswith("#"):
        try:
            ledger_pairs.add((_f[0].split("@")[0], int(_f[2][1:])))
        except ValueError:
            pass
issue_map = json.load(open(ISSUEMAP)) if os.path.exists(ISSUEMAP) else {}

# Which items land on MORE THAN ONE issue? Computed up front from BOTH sources
# (drafts' covers + the duplicates file) so the draft loop below can flag them.
# Without this the draft loop writes the issue TITLE as every ledger note, so a
# multi-part item's new-issue leg silently loses its part name while its
# dedup-append leg keeps one -- an asymmetry that produced exactly two bad rows
# across 2010 ledger ids before it was noticed, in Ch3 and Ch6.
_dup_path = os.path.join(SCRATCH, f"duplicates-{R}.json")
_dups_pre = json.load(open(_dup_path)) if os.path.exists(_dup_path) else []
_targets = {}
for _d in _dups_pre:
    _targets.setdefault(_d["item_id"], set()).add(int(str(_d["issue"]).lstrip("#")))
for _d in drafts:
    _y, _ = split_draft(_d)
    if not _y:
        continue
    _m = re.search(r"^covers:\s*\[(.*)\]", _y, re.M)
    _t = re.search(r'^title:\s*"(.*)"', _y, re.M)
    if not _m:
        continue
    for _c in [c.strip() for c in _m.group(1).split(",") if c.strip()]:
        _targets.setdefault(_c, set()).add(_t.group(1) if _t else "draft")
multi_pre = {k for k, v in _targets.items() if len(v) > 1}

# Part names for a DRAFT leg of a multi-part item, keyed "<title>|<item-id>".
# The duplicates file carries a structured `part` per row; drafts had no
# equivalent, so every new-issue leg of a split item landed in the ledger as
# "NEEDS NAMING" and had to be filled in by hand afterwards (8 rows in Riehl
# Ch1, 15 in Ch2). schemas.md forbids recovering the part by parsing the draft
# prose -- that regex has failed four times on four different phrasings -- so
# the part is EXTRACTED ONCE into this side-file, eyeballed, and read here as a
# structured field. Absent file or absent key falls back to the loud flag.
_parts_path = os.path.join(SCRATCH, f"draft-parts-{R}.json")
draft_parts = json.load(open(_parts_path)) if os.path.exists(_parts_path) else {}

for i, d in enumerate(drafts, 1):
    y, body = split_draft(d)
    if y is None:
        print(f"draft {i}: MALFORMED (no parseable yaml header) — skipped, fix manually"); continue
    title = re.search(r'^title:\s*"(.*)"', y, re.M).group(1)
    labels = [l.strip() for l in re.search(r"^labels:\s*\[(.*)\]", y, re.M).group(1).split(",")]
    covers = [c.strip() for c in re.search(r"^covers:\s*\[(.*)\]", y, re.M).group(1).split(",") if c.strip()]
    if covers[0] in ledger_issued:
        print(f"draft {i}: already filed, skipping ({covers[0]})"); continue
    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as tf:
        tf.write(body.strip() + "\n"); bodyfile = tf.name
    cmd = ["gh", "issue", "create", "-R", REPO, "--title", title, "--body-file", bodyfile]
    for l in labels:
        cmd += ["--label", l]
    url = run(cmd); os.unlink(bodyfile)
    num = int(url.rstrip("/").rsplit("/", 1)[1])
    run(["gh", "project", "item-add", PROJECT, "--owner", OWNER, "--url", url])
    with open(LEDGER, "a") as lf:
        for c in covers:
            # A multi-part item's rows must each NAME the part (schemas.md). The
            # title is not a part name, so flag it loudly rather than writing a
            # note that merely looks filled in.
            if c not in multi_pre:
                note = title
            elif draft_parts.get(f"{title}|{c}"):
                note = f"part: {draft_parts[f'{title}|{c}']}"
            else:
                note = (f"part: NEEDS NAMING -- multi-part, also on {sorted(_targets[c] - {title})} "
                        f"-- name this leg's part by hand")
            lf.write(f"{c}\t{cls.get(c,'?')}\t#{num}\t{PROJECT}\t{note}\n")
            ledger_pairs.add((c.split("@")[0], num))
    for c in covers:
        # Same no-clobber rule as the duplicate pass below. A multi-part item
        # can be split across TWO NEW DRAFTS (Ch10: `awodey:10:ex7` -- draft 1
        # takes the general comonad-from-adjunction construction, draft 3 takes
        # part (c)), not only across a draft and an append. Without this the
        # second draft silently rewrote the first's mapping, which is exactly
        # the Ch9 corruption one loop earlier.
        if c in issue_map and issue_map[c] != num:
            issue_map[f"{c}@{num}"] = num
        else:
            issue_map[c] = num
    json.dump(issue_map, open(ISSUEMAP, "w"), indent=1)
    print(f"draft {i}: #{num}  {title}")
    time.sleep(3)

# duplicates: append source blocks to existing issues, extend trailers, ledger
# own_issues = issues THIS book owns (for cross-book project association)
# associated = cross-book targets already added to this project this run
# (GitHub dedups project cards by URL, but skip the redundant API calls)
own_issues = set(issue_map.values())
associated = set()
dup_path = os.path.join(SCRATCH, f"duplicates-{R}.json")
dups = json.load(open(dup_path)) if os.path.exists(dup_path) else []

# How many distinct issues does each item land in? (drafts already filed above
# contribute their entry in issue_map; dups contribute one per row.) Used only
# to decide whether a ledger note should name a part.
multi_target = {}
for dup in dups:
    n = int(str(dup["issue"]).lstrip("#"))
    multi_target.setdefault(dup["item_id"], set()).add(n)
for iid_, n_ in issue_map.items():
    multi_target.setdefault(iid_.split("@")[0], set()).add(n_)
multi_target = {k: len(v) for k, v in multi_target.items()}

for dup in dups:
    iid, num, block = dup["item_id"], int(str(dup["issue"]).lstrip("#")), dup["append_block"]
    if (iid, num) in ledger_pairs:
        print(f"dup {iid} -> #{num}: pair already in ledger, skipping"); continue
    if num not in own_issues and num not in associated:  # cross-book: associate with THIS book's project once
        associated.add(num)
        # The dedup contract has THREE steps: (a) add the later book's `book:`
        # label, (b) add to its project, (c) append the source block. Only (b)
        # and (c) were automated here, so (a) was silently skipped on EVERY
        # cross-book append and had to be swept by hand three separate times
        # (Awodey campaign-wide, Awodey Ch10, Seven Sketches Ch1). It matters:
        # the resume pre-flight in schemas.md is `gh issue list --label
        # book:<book>`, so an unlabelled target is invisible to the idempotency
        # check and a resumed run can re-file duplicates against it.
        try:
            run(["gh", "issue", "edit", str(num), "-R", REPO,
                 "--add-label", f"book:{BOOK}"], retries=1)
            print(f"dup {iid}: cross-book, labelled #{num} book:{BOOK}")
        except Exception as e:
            print(f"dup {iid}: LABEL book:{BOOK} on #{num} FAILED ({e}); add manually")
        try:
            run(["gh", "project", "item-add", PROJECT, "--owner", OWNER,
                 "--url", f"https://github.com/jwiegley/category-theory/issues/{num}"], retries=1)
            print(f"dup {iid}: cross-book, added #{num} to project {PROJECT}")
        except Exception as e:
            print(f"dup {iid}: cross-book project-add for #{num} FAILED ({e}); associate manually")
    body = json.loads(run(["gh", "issue", "view", str(num), "-R", REPO, "--json", "body"]))["body"]
    tm = re.search(r"<!-- catalog: (\{.*?\}) -->\s*$", body)
    if tm:
        tr = json.loads(tm.group(1))
        if iid not in tr.get("ids", []):
            tr.setdefault("ids", []).append(iid)
        newbody = body[:tm.start()].rstrip() + "\n\n" + block.strip() + "\n\n" + f"<!-- catalog: {json.dumps(tr)} -->\n"
    else:
        newbody = body.rstrip() + "\n\n" + block.strip() + "\n"
    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as tf:
        tf.write(newbody); bf = tf.name
    run(["gh", "issue", "edit", str(num), "-R", REPO, "--body-file", bf]); os.unlink(bf)
    # A MULTI-PART item legitimately lands in more than one issue (schemas.md),
    # and each of its rows must NAME the part. The drafter already writes the
    # part as a parenthetical just before the page citation ("... Example 9.12
    # (first leg) — printed pp. 228-229"), so lift that rather than writing the
    # useless generic note on every leg. Two guards, both needed:
    #   * only for items that really do land in >1 issue -- for a single-target
    #     item the same slot holds the item's NAME ("(natural numbers object)"),
    #     which is not a part;
    #   * require a part-word, and anchor on "— printed" so we never match the
    #     later "(item `...`; multi-part -- the dual-image leg is recorded
    #     against ...)" paren, which names the OTHER leg and would invert the
    #     label.
    # Prefer the drafter's STRUCTURED `part` field. Parsing the part out of the
    # append prose has now failed four separate times because every chapter
    # phrases the citation differently; the fallbacks below are kept only for
    # duplicates files written before the schema carried `part`.
    note = "also covered by existing issue"
    structured = (dup.get("part") or "").strip()
    if structured and multi_target.get(iid, 0) > 1:
        note = f"part: {structured}"
    elif multi_target.get(iid, 0) > 1:
        flat = re.sub(r"\s+", " ", block)
        # Drafters phrase the citation two ways, both seen in this campaign:
        #   "... Example 9.12 (first leg) — printed pp. 228-229 ..."   (Ch9)
        #   "... Exercise 10.6.1(a)-(b), printed page 290 (PDF page 299)
        #    — item `awodey:10:ex1` (parts (a) and (b); part (c) is on #252)"
        # so try the pre-"printed" slot first, then a "(part...)" parenthetical
        # anywhere. Never match the trailing "recorded against/is on #N" clause:
        # it names the OTHER leg and would invert the label.
        part = re.search(r"\(([^()]{1,70}\b(?:leg|clause|half|direction)\b[^()]{0,70})\)"
                         r"\s*(?:—|--)\s*printed", flat)
        if part:
            note = f"part: {part.group(1).strip()}"
        else:
            # Second phrasing: "(parts (a) and (b); part (c) is recorded on #252)".
            # Regex is the wrong tool -- the group NESTS parens and names THIS
            # leg before the other. Scan for balance, then keep only the text
            # before the first ';' (everything after it describes the OTHER leg,
            # and including it would invert the label).
            m2 = re.search(r"\(parts?\b", flat)
            if m2:
                depth, end = 0, None
                for j in range(m2.start(), len(flat)):
                    if flat[j] == "(":
                        depth += 1
                    elif flat[j] == ")":
                        depth -= 1
                        if depth == 0:
                            end = j
                            break
                if end:
                    inner = flat[m2.start() + 1:end].split(";")[0].strip()
                    if 0 < len(inner) <= 70:
                        note = f"part: {inner}"
        if note == "also covered by existing issue":
            # Third phrasing, seen in Seven Sketches: the part is stated as prose
            # right after the item id -- "item `7sketches:1.2.2:remark35` -- the
            # second half of the remark: ...". Take the clause up to the first
            # sentence break. Chasing a fourth phrasing with regexes is a losing
            # game; if this misses, the note stays generic and the reviewer names
            # the part by hand (as was done for Ch1's eight rows).
            m3 = re.search(r"item\s+`[^`]+`\s*(?:—|--|-)\s*([^.;:]{8,70})", flat)
            if m3:
                note = "part: " + m3.group(1).strip()
    with open(LEDGER, "a") as lf:
        lf.write(f"{iid}\t{cls.get(iid,'?')}\t#{num}\t{PROJECT}\t{note}\n")
        ledger_pairs.add((iid.split("@")[0], num))
    # Do NOT clobber an existing mapping. The Ch9 filing found the overwrite is
    # actively harmful: `awodey:9.7:prop18` was covered by a NEW issue (#730) and
    # also appended to an existing one (#387), so the dup pass rewrote its
    # primary 730 -> 387. Phase G then resolved #730's OWN identity (it looks the
    # draft up by its first covered item) to #387 and emitted a self-cycle
    # #387 <- #387, silently dropping #730's two real edges and planting one
    # undeclared edge on a MacLane issue. Keep the primary; record further legs
    # under the schema's `<item-id>@<issue>` key.
    if iid in issue_map and issue_map[iid] != num:
        issue_map[f"{iid}@{num}"] = num
    else:
        issue_map[iid] = num
    json.dump(issue_map, open(ISSUEMAP, "w"), indent=1)
    print(f"dup {iid}: appended to #{num}")
    time.sleep(2)

# PRESENT / OUT_OF_SCOPE ledger rows with evidence pointers
ledger_have = {l.split("\t")[0] for l in open(LEDGER).read().splitlines()[1:]}
with open(LEDGER, "a") as lf:
    for iid, c in sorted(cls.items()):
        if iid not in ledger_have and c in ("PRESENT", "OUT_OF_SCOPE"):
            lf.write(f"{iid}\t{c}\t-\t-\t{ev.get(iid, 'see coverage matrix')}\n")
print("DONE. total mapped:", len(issue_map))
