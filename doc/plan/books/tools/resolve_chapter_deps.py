#!/usr/bin/env python3
"""Phase G for a MacLane chapter: rewrite same-chapter item-ID Depends-on
lines to issue numbers (cross-chapter deps arrive pre-resolved as #N), mirror
ALL dependency edges of the new issues as native blocked-by relations, and
validate the graph. Idempotent.

Usage: resolve_chapter_deps.py <ROMAN> <SCRATCH_DIR>
"""
import json, re, subprocess, sys, time, tempfile, os

R, SCRATCH = sys.argv[1], sys.argv[2]
BOOK = sys.argv[3] if len(sys.argv) > 3 else "maclane"
REPO = "jwiegley/category-theory"
BOOKS = "/Users/johnw/src/category-theory/master/doc/plan/books"
issue_map = json.load(open(f"{BOOKS}/{BOOK}/issue-map.json"))

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
    raise RuntimeError(f"command failed: {' '.join(cmd)}")

raw = open(os.path.join(SCRATCH, f"drafts-{R}.md")).read()
drafts = [d.strip() for d in raw.split("\n---8<---\n") if d.strip()]

# Draft -> its own issue number, resolved by EXACT TITLE.
#
# It used to be issue_map[covers[0]], which is WRONG for a multi-part item.
# file_chapter.py stores the first leg of a split item under the plain key and
# every later leg under "<item-id>@<issue>" (the Ch9 no-clobber fix), so for
# each later draft issue_map[covers[0]] returns the FIRST draft's issue. Riehl
# Ch2 had five such drafts: #929/#933/#934/#943 all resolved to #927 and #935
# to #934, so four drafts' dependencies were written onto one issue as native
# blocked-by edges while the drafts themselves got none -- 7 graph violations.
# Titles are unique per issue and are what `gh issue create` echoed back, so
# they identify the draft's own issue exactly. issue_map stays the fallback.
_titles, _dup_titles = {}, set()
for _r in json.loads(run(["gh", "issue", "list", "-R", REPO, "--label", f"book:{BOOK}",
                          "--state", "all", "--limit", "800", "--json", "number,title"])):
    if _r["title"] in _titles:          # title uniqueness is load-bearing here
        _dup_titles.add(_r["title"])
    _titles[_r["title"]] = _r["number"]


def draft_issue(y, covers, problems):
    """The issue number this draft was filed as, or None.

    A title MISS must be loud. Falling back to issue_map[covers[0]] would
    silently reinstate the very mis-resolution this function exists to prevent
    (a multi-part covers[0] resolves to the FIRST leg's issue), so the fallback
    is reported as a problem and the draft is skipped rather than mis-edited.
    A DUPLICATE title is equally fatal: it would pick whichever issue happened
    to come last out of `gh issue list`.
    """
    t = re.search(r'^title:\s*"(.*)"', y, re.M)
    title = t.group(1) if t else None
    if title in _dup_titles:
        problems.append(f"AMBIGUOUS title, refusing to guess: {title!r}")
        return None
    if title in _titles:
        return _titles[title]
    problems.append(
        f"title not found among book:{BOOK} issues, refusing the covers[0] "
        f"fallback (it mis-resolves multi-part items): {title!r}")
    return None

edges, problems = [], []
for i, d in enumerate(drafts, 1):
    y, body = split_draft(d)
    if y is None:
        continue
    body = body.strip()
    covers = [c.strip() for c in re.search(r"^covers:\s*\[(.*)\]", y, re.M).group(1).split(",") if c.strip()]
    num = draft_issue(y, covers, problems)
    if num is None:
        problems.append(f"draft {i}: unresolved, skipping deps"); continue
    # AUTHORITATIVE dep source = the catalog trailer's `deps` array
    # (structured JSON; robust against prose-line format drift — backticks,
    # multiple deps per line, parenthetical forward-refs). The prose
    # "Depends on:" line is only rewritten for human readability, using
    # the trailer deps as a whitelist so forward-references are left alone.
    tm = re.search(r"<!-- catalog: (\{.*?\}) -->", d)
    deps = json.loads(tm.group(1)).get("deps", []) if tm else []
    if not deps:
        continue
    # fetch the LIVE body (it is authoritative post-filing)
    live = json.loads(run(["gh", "issue", "view", str(num), "-R", REPO, "--json", "body"]))["body"]
    # Isolate the "## Dependencies" section so the prose rewrite touches only
    # declared deps there (never Current-state / Work forward-references).
    dm = re.search(r"(?ms)^## Dependencies\b.*?(?=^## |\n<!-- catalog|\Z)", live)
    depsec = dm.group(0) if dm else ""
    newdepsec, changed = depsec, False
    for dep in deps:
        dep = str(dep).strip().strip("`")
        if dep.startswith("#"):  # pre-resolved cross-chapter dep
            edges.append((num, int(dep.lstrip("#").rstrip(")`,.")))); continue
        if dep not in issue_map:
            problems.append(f"#{num}: dangling dep {dep}"); continue
        dn = issue_map[dep]
        if dn == num:
            problems.append(f"#{num}: self-dep via {dep}"); continue
        edges.append((num, dn))
        if f"#{dn} (`{dep}`)" in newdepsec:
            continue  # already resolved (idempotent re-run)
        bt = re.compile(rf"(?<!\()`{re.escape(dep)}`")
        if bt.search(newdepsec):  # backtick-wrapped item id -> resolve all in-section
            newdepsec = bt.sub(f"#{dn} (`{dep}`)", newdepsec); changed = True
        else:  # bare item id on a Depends-on line — replace ONLY the token,
               # preserving any trailing descriptive prose (which may wrap
               # across physical lines). Replacing to end-of-line strands the
               # tail clause (App #638 garble, 2026-07-23).
            pat = re.compile(rf"(?<!`)Depends on: {re.escape(dep)}\b")
            if pat.search(newdepsec):
                newdepsec = pat.sub(f"Depends on: #{dn} (`{dep}`)", newdepsec, count=1)
                changed = True
    newbody = live.replace(depsec, newdepsec) if changed else live
    if changed:
        with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False) as tf:
            tf.write(newbody + ("\n" if not newbody.endswith("\n") else "")); bf = tf.name
        run(["gh", "issue", "edit", str(num), "-R", REPO, "--body-file", bf]); os.unlink(bf)
        print(f"#{num}: rewrote {len([x for x in deps])} trailer dep(s) into prose")
        time.sleep(1)

# cycle check over this chapter's new edges (cross-chapter edges cannot form
# cycles: old issues never gain deps on new ones)
adj = {}
for a, b in edges:
    adj.setdefault(a, set()).add(b)
state = {}
def dfs(u, stack):
    state[u] = 1
    for v in adj.get(u, ()):
        if state.get(v) == 1:
            problems.append(f"cycle: {stack + [v]}")
        elif state.get(v, 0) == 0:
            dfs(v, stack + [v])
    state[u] = 2
for a in list(adj):
    if state.get(a, 0) == 0:
        dfs(a, [a])

# node ids incl. dep targets from earlier chapters
nums = sorted({n for e in edges for n in e})
node = {}
for i in range(0, len(nums), 20):
    chunk = nums[i:i+20]
    q = '{ repository(owner:"jwiegley", name:"category-theory") { ' + " ".join(
        f"i{n}: issue(number:{n}) {{ id }}" for n in chunk) + " } }"
    data = json.loads(run(["gh", "api", "graphql", "-f", f"query={q}"]))
    for n in chunk:
        r = data["data"]["repository"].get(f"i{n}")
        if r is None:
            problems.append(f"dep target #{n} does not exist")
        else:
            node[n] = r["id"]

# existing native relations for idempotency
existing = set()
for n in sorted({a for a, _ in edges}):
    q = f'{{ repository(owner:"jwiegley", name:"category-theory") {{ issue(number:{n}) {{ blockedBy(first:50) {{ nodes {{ number }} }} }} }} }}'
    try:
        data = json.loads(run(["gh", "api", "graphql", "-f", f"query={q}"], retries=2))
        for nd in data["data"]["repository"]["issue"]["blockedBy"]["nodes"]:
            existing.add((n, nd["number"]))
    except RuntimeError:
        pass

added = 0
for num, dn in edges:
    if (num, dn) in existing or num not in node or dn not in node:
        continue
    q = f'mutation {{ addBlockedBy(input:{{issueId:"{node[num]}", blockingIssueId:"{node[dn]}"}}) {{ clientMutationId }} }}'
    try:
        run(["gh", "api", "graphql", "-f", f"query={q}"], retries=2)
        added += 1
        print(f"blocked-by: #{num} blocked by #{dn}")
    except RuntimeError:
        problems.append(f"native relation failed: #{num} <- #{dn} (body text remains source of truth)")
    time.sleep(1)

print(f"\nedges: {len(edges)} (native added: {added}, pre-existing: {len(existing & set(edges))})")
print("PROBLEMS:" if problems else "GRAPH CLEAN")
for p in problems:
    print(" -", p)
