# Library defects surfaced during the Riehl catalog campaign

Same convention as the other three ledgers: in-tree defects (dangling pointers,
comment-vs-code mismatches) found while classifying — NOT missing-theory gaps.
Recorded so they are not lost; filing as GitHub issues is a maintainer call.
`R` prefix for book 4.

## Chapter 1 haul (2026-07-31)

| # | File:line | Defect | Disposition |
|---|-----------|--------|-------------|
| **R1** | Theory/Metacategory.v:25-27 **↔** :184-190 | The header asserts "The three axioms (matchability, associativity, and existence of identities) **then capture exactly a category**". The same file's `jww (TODO)` note at `:184-190` says the third axiom uses `->` where `/\` was meant, is therefore "**vacuously true** (any non-identity `[u]` makes the implication trivially hold), so this axiom **imposes no real constraint**". Verified both verbatim. So the header's "capture exactly a category" is contradicted by the file's own disclosure. | Recorded (MEDIUM). Distinct site from **S10** (Seven Sketches ledger), which recorded the vacuous `identity_law` itself; this is the HEADER claim built on it. The honest fix is to scope the header sentence, as the note already scopes the axiom. |
| — | Instance/Poset.v:21, Instance/Proset.v:19 | **A1/A2 recur for the fifth consecutive book-chapter**, with a sharper observation from this verifier: the two dangling pointers are **mutually reinforcing** — a reader checking `[Pos]` is sent to `[Ord]` and vice versa, and neither exists. | Duplicates of A1/A2. |

## A CLAUDE.md index gap — real, but MY CAUSAL DIAGNOSIS WAS WRONG

**The facts hold.** `Instance/Comp.v` is registered at `_CoqProject:177` and
contains the **only in-tree single-sorted universal-algebra development** —
`OpSignature`/`OpAlgebra`/`AlgHom`, the category `Algs : Category` (`:151`) with
Terminal (`:160`), Cartesian (`:169`), Closed (`:190`), Initial (`:209`) and
Cocartesian (`:224`) instances, `EqSignature` (`:240`), varieties
`Record Algebra S E` (`:268`), `Group := Algebra GroupOp GroupEq` (`:382`) and
`Bool : Group` (`:405`). It appears **zero times** in CLAUDE.md. All verified.

**⚠ MY CAUSAL CLAIM WAS FALSE AND fess-r1 REFUTED IT WITH COUNTS.** I wrote that
Phase C "missed it for exactly that reason … the classifier was searching an
index that does not mention the file". That is not supported: **228 of the 486
`_CoqProject`-registered files are unnamed in CLAUDE.md**, and this very
chapter's coverage pass cites **33 of those unindexed files across 111 of its
277 citations (40%)** — including `Theory/Isomorphism.v`, `Theory/Morphisms.v`,
`Functor/Hom.v`, `Construction/Groupoid.v`, `Theory/Equivalence/Bundled.v` and
`Construction/Free/Quiver.v`. **The classifier demonstrably searches the TREE,
not the index.** Being absent from CLAUDE.md therefore does not explain the miss,
and the audit found exactly **one** other record in the same class
(`riehl:1.1:example4`, which missed `Instance/One.v:25`) — also unindexed, also
minor. Two misses out of 158 items is not an index-driven pattern.

**What stands:** adding `Instance/Comp.v` to CLAUDE.md's index is still a
reasonable improvement, and any future batch touching algebraic theories,
varieties or Lawvere models should be pointed at it explicitly. **Not done** —
CLAUDE.md is a TRACKED file and this campaign has touched only untracked
`doc/plan/`; it is John's call.

**Lesson recorded:** I inferred a cause from a correlation (file missing from
index + classifier missed file) without checking the base rate. The base rate
refuted it in one query.

## Chapter 1 catalog defects (fess-r1) — all fixed

| Finding | Fix |
|---|---|
| **#915 declared the WRONG prerequisite for `cHaus`** — `Depends on: #489`, which CONSUMES `cHaus` to prove it monadic, rather than **#413**, which BUILDS it in `Instance/CompHaus.v`. #915's own prose named #413. Consequence: the Riesz issue was parked behind Beck's monadicity (#484), absolute coequalizers (#477) and Stone-Cech (#455), none of which it needs. | Retargeted to #413 in body, trailer and native edge; #489 edge removed. |
| **The `riehl:1.4:example11` append dropped half its obligation.** Riehl (printed p.29) asserts naturality for FOUR isomorphisms; #284 commits to two, and the append's checkbox covered only the cardinality half — leaving naturality of `Structure/BiCCC.v:90` and `:134` homeless. | Two checkboxes added to #284. |
| **The `riehl:1.4:example4(i)` append silently narrowed the hypothesis** — Riehl says "for vector spaces of **any dimension**"; #237 is FdVect-scoped throughout and no unrestricted `Vect_k` exists anywhere in the campaign. | Scope checkbox added to #237. |
| **#921 said "#225 … not a build prerequisite" INSIDE a `Depends on:` line**, so the resolver made it a hard blocker — the graph asserting what the prose denied. Same error I made on #871. | Demoted to a related-note; native edge removed. |
| **#913's work item said "reuse the Riehl §1.1 issue" without ever naming #907**, which was in neither its Depends-on list nor its `blockedBy` — the only intra-campaign edge in the batch, dropped. | Declared and edged. |
| **Riehl referred to as "he"/"his" in THREE live issue bodies** (#231, #288, #250). | All corrected to she/her. **The clean-sweep certification originally written here was FALSE and has been retracted** — see the Chapter 2 section: the Ch1 sweep was scoped to that chapter's new issue numbers, so it could not see the *append* blocks, and Ch2 shipped three more misgenderings into pre-existing issues. Both chapters are now clean under a correctly scoped sweep. |
| LOW, recorded not fixed: `riehl:1.1:example4`'s gap says "the only one-object category in the tree is the ad-hoc `ListMon`" — `Instance/One.v:25` is also one. The substantive claim (no general delooping) is correct and independently confirmed. Also `riehl:1.6:def3`→#500 leaves topological monoids homeless, `riehl:1.3:example2` clauses (iii)-(iv) get no checkbox, and the PDF-63 page note contradicts its own (correct) items list. | Recorded. |

**A gap in MY audit brief, for the record:** my numbering-gap list omitted
**(1.4.12)**, a trailing display closing §1.4. The inventory DID disclose it in
its PDF-49 note, so the artifact was right and the brief was wrong.

## Chapter 2 library defects — every claim re-verified from source by hand

The Phase-D verifiers reported 14 defect claims. **The `problems[]` array is not
persisted into `verified-2-*.json`** (the Phase-D agents return it in their
structured result but the schema's array is not written to the coverage file),
so the text survives only here and in the workflow task output. Persisting these
into this file is the mitigation; a future chapter should either add `problems`
to the written record or accept that this ledger is its only home.

All claims below were checked against the tree with the command shown. **None
was accepted on the verifier's word** — one earlier campaign defect (A46) was
flatly false, so the default is verify-then-record.

| # | File | Claim | Verified? |
|---|---|---|---|
| 1 | `Functor/Representable.v:22-25` | Header says the universal-element and uniqueness facts "are developed in `Structure/UniversalProperty.v`". They are not developed **for this class**: `representability_by_yoneda` (`:72`) is stated for a **contravariant** `F : C^op ⟶ Sets` while `Class Representable` is covariant (`[Hom repr_obj,─] ≅ F`), and `univ_property_unique_up_to_unique_iso` (`:175`) is scoped to the separate `Class IsUniversalProperty` (`:41`). No lemma connects the two packagings. | **CONFIRMED.** Read both lemma statements. NOTE: the verifier also wrote that `UniversalProperty.v` "never mentions Representable" — **that phrasing is wrong**, `:18` carries a `Representable_functor` Wikipedia URL. The substance stands; the phrasing does not. |
| 2 | `Functor/Representable.v` (class inertness) | `Class Representable` has zero instances and zero consumers tree-wide. | **CONFIRMED**, but only after filtering: `rg Representable` hits 7 other files, all of which are URLs, comment file-paths, or the unrelated compounds `Representable profunctors` / `RepresentableMulticategory` / `RepresentableKit`. The only in-file use is the coercion at `:51`. A bare grep would have refuted this claim; the filtered one confirms it. |
| 3 | `Structure/Topos.v:71-73` | Glosses `classifier_classifies` as making "subobjecthood representable", but that lemma is a **per-object** setoid iso `SubObj x ≅ (x ~> Ω)`; the natural iso `Sub ≅ [Hom ─,Ω]` the word names is nowhere stated, though `Sub : C^op ⟶ Sets` exists (`Theory/Subobject/Functor.v:180`). | **CONFIRMED.** Overstated gloss, not a false theorem — the appositive that follows it *is* proved. Low severity. |
| 4 | `Functor/Hom/Yoneda.v:22` | Header displays the lemma as "`Nat([Hom ─,A], F) ≅ F A`, **natural in both A and F**", but neither `Yoneda_Lemma` (`:133`) nor `Covariant_Yoneda_Lemma` (`:182`) states or proves naturality — each is a pointwise family with `F` a fixed section parameter. | **CONFIRMED.** `rg 'natural in' Functor/ Theory/ Structure/` returns this comment and nine unrelated hits (Traversable, Premonoidal, …); no Yoneda naturality statement exists in the tree. |
| 5 | `Functor/Hom/Yoneda.v:86-88` | Claims `Construction/Cayley.v` "builds the Cayley representation … on `[Covariant_Yoneda_Embedding]`", overstating the dependency: Cayley builds `Cayley`/`To_Cayley`/`From_Cayley` directly and says so at its own `:24`; the embedding is consumed only in `Cayley_Cartesian`. | **CONFIRMED.** |
| 6 | `Construction/Cayley.v:38-39` | Header says `To_Cayley`/`From_Cayley` "witness that this embedding is (split) faithful: `From_Cayley (To_Cayley f) ≈ f`", but that round trip is stated nowhere and there is no `Faithful To_Cayley` instance. | **CONFIRMED**, but my cited command was wrong: `rg` is case-sensitive and `:39` reads lowercase "faithful", so `rg Faithful Construction/Cayley.v` returns only `:75`. Use `rg -i faithful`. The substance was re-verified independently across all ten `From_Cayley` sites (`:38,:39,:89,:105,:168,:169,:181,:193,:326,:327`): no round-trip lemma, no `Faithful To_Cayley` instance. True and near-definitional, but not built. |
| 7 | `Structure/Cartesian/Closed.v:47-50` | Comment on `exp_iso` calls it a natural isomorphism; naturality is not part of the field. | Recorded, **not independently re-verified** — same class as #4 and consistent with the in-tree `curry_comp_l`/`curry_comp` naturality lemmas being separate. Flagged as lower confidence than the rest of this table. |
| 8 | `Construction/Grothendieck.v:107-109` | Header states that restricting fibres to sets "recovers the category of elements `el(F)`, whose projection is a discrete opfibration", phrased as though the construction delivers it. It does not: `Grothendieck` consumes an `IndexedCat B`, and the restriction is not even free because `DiscreteCat` has strict-equality homs whereas a `Sets` fibre is a setoid. | **CONFIRMED.** `rg -c Sets Construction/Grothendieck.v` → **0 occurrences**; `Instance/Discrete.v:37` shows `hom := fun x y => x = y` with a strict-eq setoid. Neither `el(F)` nor "discrete opfibration" is defined in the library. |
| 9 | `Instance/Proset.v:19` | Header says "See also `[Ord]`, for the category of preordered sets", but no `Ord` exists. | **CONFIRMED.** `rg '\bOrd\b'` over all `.v` returns **exactly this one comment line**; no `Instance/Ord.v`. Dangling cross-reference to a category never written. |
| 10 | `Instance/Fact.v:10` | The file's two pointers are nLab *factorization category* and Wikipedia *Twisted arrow category*, but `Fact f` (`:43`) is the category of factorizations of **one fixed** morphism, which is not `Tw(C)` and not a fibre of it. Misdirects a reader looking for `Tw(C)` — which Riehl Exercise 2.4.vii needs and which is genuinely ABSENT. | **CONFIRMED.** `rg -i twisted` over all `.v` hits only `Instance/Fact.v` and `Construction/Grothendieck.v`, both comments. |

**Pattern across all ten:** every one is a **header/comment claim that overstates
what the file proves** — a promised API, a naturality qualifier, a cross-reference
to something unwritten. None is an unsound proof. This is a documentation-accuracy
class, and it is dense enough in this chapter's neighbourhood (Yoneda, Cayley,
Representable, Grothendieck) to be worth a dedicated sweep rather than
issue-by-issue patching. **Not filed as issues** — these are defects in prose the
campaign did not author, and the campaign's remit is cataloguing theory gaps; they
are recorded here for John to triage.

## Chapter 2 catalog defects (fess-r2)

Verdict: sound on every structural claim tested; **one HIGH I missed**, one MEDIUM,
three LOW. All folded.

| Finding | Fix |
|---|---|
| **HIGH — three live Riehl misgenderings, authored by this unit** (#306, #716, #809), all in **append blocks** rather than the 24 new issues. My sweep was scoped to the new issue numbers, so it had a **permanent blind spot on exactly the surface where the drafter paraphrases the author**. Two are sentence-initial "He", which a case-sensitive grep also misses. | Fixed in `duplicates-2.json` (both copies) and all three live bodies. Sweep re-run **case-insensitively over `gh issue list --label book:riehl`** — 108 issues, zero Riehl misgenderings (the one hit, #253's "he closes by pointing to", is Saunders Mac Lane and correct). The false certification from Ch1 is retracted above. |
| **MEDIUM — `riehl:2.2:cor8` was PRESENT with an explicitly uncovered clause and no home.** Its own record disclosed that the corollary's trailing consequence (C is isomorphic to the full subcategory of presheaves spanned by the representables) is unformalized. Disclosure is not a home, and `schemas.md` makes an item with a not-covered clause PARTIAL-with-`gap`. | Reclassified PARTIAL, `gap` written, ledger row and `issue-map` retargeted to **#918** (Riehl 1.5, `EssentialImage`), and a checkbox added there naming the one-step instantiation at `Yoneda_Full`/`Yoneda_Faithful`. |
| **LOW — the resolver fix kept the original bug as a silent fallback.** On a title miss `draft_issue` returned `issue_map[covers[0]]` with no problem recorded — a title edited between Phase F and a Phase G re-run would silently reproduce the corruption. | Fallback removed. A title miss and an AMBIGUOUS (duplicate) title now both append to `problems[]` and skip the draft. Re-run is idempotent: 48 edges, 0 added. |
| **LOW — title uniqueness was load-bearing but unenforced** (verified true today: 0 duplicate titles across 755 issues). | Duplicate-title detection added alongside the above. |
| **LOW — a miscited command in this ledger** (`rg Faithful` vs. the lowercase text). | Corrected in row 6 above; substance independently re-verified. |

### The argument I got wrong

I claimed no earlier chapter suffered the multi-part resolver corruption, on the
grounds that `check_graph.py` validates body-vs-native corpus-wide and exits 0.
**That argument is insufficient, and the auditor was right to reject it**: a
corruption later "repaired" by editing the BODY to match a wrong native edge — my
own documented failure mode of repairing the mirror instead of the source — is
invisible to CONSISTENT, because both sides then agree.

The **conclusion** survives two stronger tests that do not share that blind spot:

1. **Fingerprint replay.** Recomputing the buggy resolver's identity function
   `issue_map[trailer.ids[0]]` for every book-labelled issue with a trailer finds
   exactly **six** mismatches corpus-wide: the five Riehl Ch2 ones and **#742**
   (`awodey:10:ex7` → #740), which was inert because its trailer `deps` is empty and
   #740 has zero native edges, so the resolver's `if not deps: continue` fired and
   nothing was written. The premise `trailer.ids[0] == covers[0]` holds in 226/226
   drafts on disk.
2. **Third-source check.** For all 734 book issues, resolved trailer deps ⊆ body deps
   AND ⊆ native edges: **0 violations**. The trailer is the drafter's original
   declaration and is never rewritten by the resolver, so this catches precisely the
   "body and native both wrong the same way" case that defeats CONSISTENT.

**Lesson:** when a check and the bug share a blind spot, passing the check is not
evidence. Find a source the buggy process never wrote to — here, the catalog trailer.

### Disclosed verification gaps (auditor's, carried forward)

- Mac Lane drafts and Awodey Ch1–8 drafts are **not on disk**, so the fingerprint
  replay's premise is untested for those chapters; the trailer-vs-body-vs-native test
  does not depend on it, which is why both were run.
- `doc/plan/` is **untracked**, so no artifact has git history — only current state can
  be audited, never when a value changed. This will keep forcing forensic checks.
- Clause partitions were verified against issue bodies and the inventory's paraphrases,
  **not against the PDF**; page/clause fidelity rests on the inventory.

## Chapter 3 library defects (22 distinct sites)

Volume note, stated plainly: the Ch3 verifiers reported **22 distinct defect sites**,
too many to re-verify individually at the rate the campaign is running. I verified
**three** from source directly (below) and am recording the remaining nineteen as
**REPORTED, NOT INDEPENDENTLY VERIFIED**. That labelling is the point — the Ch2 audit
checked whether I marked an unverified claim honestly, and the answer must keep being
yes. Do not cite an unverified row as established.

### Verified directly

| Site | Claim | Verification |
|---|---|---|
| `Structure/Limit.v:70-72` | Header: "Whatever is proved once about `[Limit]` — **uniqueness up to unique isomorphism**, preservation, **construction from products and equalizers** — thereby specializes to each of these at no further cost." Only *preservation* is actually proved about `Limit`. | **CONFIRMED.** Read `:68-73`. `Structure/Complete.v` contains exactly two declarations, `Complete` (`:115`) and `Cocomplete` (`:119`) — both bare definitions, no products+equalizers existence theorem. No limit-uniqueness lemma exists; the only uniqueness in the neighbourhood is `UniversalProperty/Limit.v`'s mediating-map uniqueness, which is a different statement (two maps agreeing on every leg are equal). |
| `Structure/Pullback.v:79, :178-179` | Both comments say pullbacks are unique up to a unique isomorphism **respecting the projections**. | **CONFIRMED.** The lemma at `:182` concludes only `Pull f g P ≅ Pull f g Q` — no uniqueness clause, no commutation with `pullback_fst`/`pullback_snd`. Note the parallel `equalizer_unique` (`Structure/Equalizer/Fork.v:106`) has the same bare-`≅` shape but its comments correctly claim only "up to isomorphism", so that one is accurate — the defect is the comment, not the lemma. |
| `Structure/Cone.v:37-39` | `AConeEquiv` is declared with `(F : C ⟶ J)` while `ACone` (`:24-25`), `Cone` (`:51`), `Cocone`, `ConePresheaf` and the file header all use `F : J ⟶ C`. | **CONFIRMED.** Read all four declarations. The variance is genuinely flipped. It typechecks because the setoid never inspects the functor's direction, so this is a latent readability/maintenance trap rather than a soundness bug — but a reader matching the header's convention against this instance will be misled. |

### Reported, not independently verified

`Instance/Cones/Limit.v:37` · `Instance/Cones/Comma.v:64` ·
`Functor/Structure/Terminal.v:53-61` · `Structure/Complete.v:54, :74-76` ·
`Structure/Cartesian.v:449` · `Instance/Fun/Cartesian.v:36` ·
`Structure/Limit/Preservation.v:19-24, :35-36` ·
`Construction/Comma/Limit.v:17,32,121` · `Structure/Regular.v:61` ·
`Structure/Pullback.v:96-97` · `Construction/Slice/Pullback.v:24` ·
`Construction/Free/Quiver.v:48-51` · `Construction/Free.v:294-300`

**Pattern, same as Ch2:** these are overwhelmingly **header/comment claims that
overstate what the file proves**. Across two chapters the library's prose is
measurably ahead of its theorems in the limits/Yoneda neighbourhood. Still **not filed
as issues** — the campaign catalogues theory gaps, not documentation drift in prose it
did not author. Recorded for John to triage; a single dedicated documentation-accuracy
sweep would be a better instrument than per-issue patching.

## Chapter 3 catalog defects (fess-r3)

Verdict: structurally sound and mechanically clean — accounting reconciles exactly, both
overturns homed with content matching the NEW classification, pronoun sweep clean across
all three surfaces (19 drafts + 82 append blocks + all 172 live `book:riehl` bodies), and
every known-failure-mode regression check passed. Of 82 appends audited, **three fail**.

| Finding | Fix |
|---|---|
| **MEDIUM — `riehl:3.1:remark27` clause (iii) → #336: non-dischargeable append.** Riehl states the matrix determination for **arbitrary** index sets; #336 is *finite* throughout (title, background, Work, DoD, and `Depends on: #335`). No checkbox filed for the difference. Worse: `rg -i 'icoprod\|IsIndexedCoproduct\|HasIndexedCoproducts'` → **0 hits** tree-wide, so the domain `∐_{i∈I} A_i` is not writable at all; the issue that builds it is **#320**, which hosts clauses (i)–(ii) of this same partition. The partition put the MORE GENERAL clause on the NARROWER host. | Checkbox added to #336 for the arbitrary-`(I × J)` determination **as a bijection, not merely joint monicity** (the finite Work item proves only the uniqueness half), with the 0-hits evidence and a `Related (NOT blocking): #320`. |
| **MEDIUM — `riehl:3.1:def-direct-sums` → #336: the load-bearing clause unpinned.** Riehl's definition turns on the identity-matrix comparison **being an isomorphism**; #336 only *defines* the n-ary comparison and never asks it be inverted, so no n-ary direct-sum object is in scope. In tree the invertibility is **binary only** (`Structure/Biproduct.v:42`, `Structure/Semiadditive.v:227`). | Checkbox added to #336 for the invertibility and the `⊕_{i∈I} A_i` object. |
| **MEDIUM — `riehl:3.8:example8` → #559: a dropped clause.** Riehl lists **six** worked examples; the checkbox names five. The one-object-with-idempotent witness was disclosed in prose only, and the "any non-empty ordinal category" generalization was narrowed to `Omega`. The prose also pointed at #220 while **#957 Work item 3 builds exactly that shape** — stale against a sibling draft in the same batch. | Both clauses given checkboxes; pointer retargeted from #220 to #957 with a `Related (NOT blocking)`. |
| **MEDIUM-LOW — #416: suppliers unnamed.** Its general products+equalizers theorem is strictly more general than Riehl's `Set` case, so instantiation suffices — but ticking every box still does not yield the `Set` statement and neither supplier is named. | `Related (NOT blocking): #254, #407` added, with the reason stated. |
| **LOW — `riehl:3.5:example4` → #321: third clause unhomed.** The gap has three parts; the append covers (1) and (2) and disclosed (3) — the `Set` identification of `A^I` with the function set and `ev_i` with evaluation — in prose only. **I re-verified this at source** (the auditor had not): #321's Work items scope `power` and the hom bijection but nothing instantiates at `Sets`, and `HasIndexedProducts` is uninhabited. | Checkbox added to #321 with `Related: #254`. |
| **LOW — misquoted in-tree statement, live on #336.** The append quoted `fork_merge` as `≈ (f ▽ h) △ (g △ i)`; `Structure/Bicartesian.v:41` reads `≈ (f ▽ h) △ (g ▽ i)`. Presented as verbatim. | Corrected in the live body. |

### An auditor claim I checked and REFUTED

The audit flagged that #345's append ("there is no category of pointed sets `Set_*`")
contradicts #529's append calling `Instance/Coq/Par.v` "equivalent to pointed sets". It
does not. `Par` is the Kleisli category of the option monad, which **is** equivalent to
`Set_*`; and `Set_*` as a named in-tree category is genuinely absent. Both statements are
true simultaneously, and #345's append is careful enough to enumerate the `pointed` hits
and identify Par's as prose. **No fix needed** — but I added an implementer pointer to
#345, since whoever builds the pullback leg should start from `Par` rather than nothing.
The auditor explicitly marked this one not-re-verified, and the label was doing real work.

### A claim of MINE the auditor REFUTED

I flagged `riehl:3.2:example14` as a possible dropped clause — Riehl says the limit of an
idempotent in `Set` **is** the fixed-point set, and I believed the covering draft never
said so. **It does.** #957 Work item 5 reads "Example 3.2.14 in `Sets`. Show
`sets_split_obj e` is the equalizer of `(id, e)` and the limit of the walking-idempotent
diagram", and `sets_split_obj` (`Instance/Sets/Karoubi.v:41`) has carrier
`∃ a : X, e a ≈ a` — literally `{a | ea = a}`. I under-described my own work. Raising it
was still right: the cost of asking was one check, and Ch2 dropped a clause in exactly
this shape.

### Record-lossiness (open, not fixed)

`problems` is **still not a persisted key** in `verified-3-*.json`, yet six verifier notes
say "logged in `problems[]`". My Ch2 entry said "persisting these into this file is the
mitigation" — in Ch3 I persisted only `file:line` pointers, so **17 of 19 unverified
defect claims have no recoverable claim text**. The auditor reconstructed two from verifier
prose and both were true. The labelling was vindicated; the record was not. For Ch4 onward
the defect text must be copied out of the workflow result at fold time, not left as a
pointer.

### Correction to my own reporting

I told the user "82 append rows onto **76 existing issues**". Actual: 82 rows over **76
distinct items** landing on **48 distinct issues**. No artifact asserts 76 issues — the
error was confined to my prose.

## Chapter 4 library defects — claim text QUOTED, per the Ch3 lesson

Ch3 persisted bare `file:line` pointers and 17 of 19 claims became unrecoverable. The Ch4
brief required quoting the offending text verbatim; that is what follows.

| Site | Offending text (verbatim) | What is actually there | Verified? |
|---|---|---|---|
| `Structure/Pullback.v:129-130` | "The base-change functor between slices, **with its left adjoint**, is built in Construction/Slice/Pullback.v as `[Bang_Functor] ⊣ [Star_Functor]`" | Only the two FUNCTORS are built (`Construction/Slice/Pullback.v:50` `Bang_Functor`, `:67` `Star_Functor`). The adjunction is **entirely commented out** at `:121-127`. Since `⊣` is the library's `Adjunction` notation, the sentence reads as an in-tree adjunction. | **CONFIRMED**, both halves read at source. Note `Construction/Slice/Pullback.v` is itself HONEST — its `:38` says "The adjunction is sketched in the commented `Base_Functor_Adjunction` stub below". The defect is `Pullback.v`'s header overclaiming about another file. |
| `Construction/Slice/Pullback.v:122` (bonus, found while verifying the above) | the commented stub declares `Star_Functor f ⊣ Bang_Functor f` | **Backwards.** The same file's header at `:39-40` explicitly corrects it: "the live statement should read `Bang_Functor f ⊣ Star_Functor f`, since dependent sum is the LEFT adjoint." Anyone uncommenting the stub inherits the wrong orientation. | **CONFIRMED.** The file documents its own bug in prose but leaves the wrong code in place. |
| `Construction/Localization/Universal.v:64` | `reflection_counit_is_iso` is "**reproved transparently** so its inverse is available to later coherence proofs" | The lemma at `:110` ends in **`Qed`** (verified: `Qed.` at `:121`), so it is opaque, not transparent. | **CONFIRMED, but weaker than reported.** The file is more self-aware than the claim suggests: its own comment at `:108-109` says the inverse is named "by destructing this record, **which an opaque `Qed` proof still permits**". So the word "transparently" is wrong while the *consequence* the reader cares about is correctly disclosed. LOW. |
| `Construction/Comma.v:100` and `Construction/Comma/Limit.v:33` | "the projection `[comma_proj2]` **creates** the limits" / "`comma_proj2 : =(d) ↓ U ⟶ C` **creates them**" | Both comment texts confirmed verbatim at source. Whether only *existence* (rather than creation) is proved I did **not** verify end-to-end — that requires reading the whole limit construction. | **Comment text CONFIRMED; the "existence only" half REPORTED, NOT VERIFIED.** Already carried as a LIBRARY-DEFECT in filed issue **#438**'s Definition of Done, and cited in the appends for `riehl:4.7:lem2` and `riehl:4.7:exi`, so it is homed either way. |

**Same pattern as Ch2 and Ch3**: every one is a header/comment claim outrunning what the
file proves. Three chapters running, this is a stable property of the library's prose in
the limits/adjunctions neighbourhood. Still **not filed as issues** — the campaign
catalogues theory gaps, not documentation drift in prose it did not author.

## Chapter 4 catalog defects (fess-r4)

Verdict: structurally sound. The pipeline failure left **no correctness residue** — accounting
exact, no artifact absorbed a stale Phase-C classification, **no seam** between the two Phase-E
runs, no gap-fill leakage, pronoun sweep clean over 244 live bodies. All 23 filed bodies are
byte-identical to `drafts-4.md`; all 89 append blocks verbatim in their targets. Four defects.

| Finding | Fix |
|---|---|
| **MEDIUM-HIGH (F1) — `riehl:4.6:prop14`(i) → #373 with no checkbox.** The append states Riehl's sharpening in prose — the inclusion **CREATES** limits — while #373 is *inheritance* in title, Work and DoD. Creation is strictly stronger, and the tree has **no general creation predicate**: `rg -n Creates` returns only `CreatesUSplitCoequalizers` (`Monad/Monadicity/Beck.v:164`) and `equivalence_creates_limits` (`Theory/Equivalence/Limit.v:486`). **This is the Ch3 #1 defect repeated.** | Checkbox added to #373 naming the creation statement and the reusable `CreatesLimits` class it needs. |
| **MEDIUM (F2) — `riehl:4.6:example13`(ii) is TWO reflectors; the second is homed nowhere.** Riehl: abelianization for `Ab ↪ Group` **and** "a similar construction gives a left adjoint to `CRing → Ring`". The append recites the second parenthetically with no checkbox; #370's Work item 1 is the group case only. Corpus-wide the `Ring → CRing` reflector appears **exactly once — inside that append's own prose**. | Checkbox added to #370 for the commutator-ideal reflector; `rg -i 'commutator ideal\|CRing'` → **0 tree hits** recorded as evidence. |
| **MEDIUM (F3) — MY OWN ERROR, and the THIRD instance of a failure mode I have now committed three times.** I wrote "Whichever lands first creates the file and the other extends it" **inside a `Depends on:` line** on #972, so the resolver made #707 a hard native blocker while the prose denied precedence. #972's own Work item 1 defines `Grpd` independently, and #707's only blocker (#248) is one #972 already declares — so the edge was **fabricated**, parking a flagship issue behind a cartesian-closure result it explicitly does not need. Identical in shape to #921 and #871. | Native edge removed (`972 ← 707`), trailer dep dropped, line rewritten as `Related (NOT blocking)`, `Instance/Grpd.v` recorded as a serialize-group, reciprocal note added to #707. |
| **LOW-MEDIUM (F4) — the fourteen-clause judgement on `riehl:4.1:example10` is legitimate but its owner roster is wrong on six counts.** No clause is dropped — all twelve are genuinely owned — but the append credits #309 where **#473** owns the free commutative ring, omits **#400** (which owns three clauses), omits **#360** and **#987**, credits **#529** for a smash–hom adjunction it does not own, and credits **#362**, which owns none of the fourteen. | Correction table added to #312. No checkbox changes — the exception stands. |

### The lesson I keep not learning

F3 is the same mistake as #921 and #871: **a `Depends on:` line must contain ONLY
dependencies.** I have now made it three times, and this time I made it *in the same session
in which I wrote that exact rule into the Chapter 4 drafter brief*. Writing the rule for
someone else is not the same as applying it. The mechanical guard already exists and works —
`check_graph.py` compares body to native and the resolver harvests only the structured
trailer — but neither catches this, because I put the number in the trailer myself. **The only
reliable check is the one the auditor ran: read the native blocked_by list and ask, for each
edge, whether the issue's own Work items can proceed without it.**

### Three of the auditor's own provisional findings, REFUTED by it before reporting

Worth recording because it shows the pass working: it initially believed twelve clauses were
dropped (refuted — #400/#473/#360/#987 own them), that Stone–Čech had been scope-narrowed
(refuted — #455 covers Riehl's generality and explicitly notes the completely-regular
restriction is unnecessary), and that #657's late edit was unlogged (refuted by
`serialize-groups.json`). It also **strengthened** the one row I had honestly marked
unverified: the tree has no general limit-creation predicate at all, so `Comma/Limit.v:33`
cannot be *stating* creation — its deliverable is `Comma_Complete` at `:245`.

### Open loose end (disclosed, not resolved)

`verified-4-0.json` was written at **10:19:50**, 38 minutes into Phase E and before the
coverage rewrites — my account of the aborted resume ("began re-running the COVERAGE phase")
does not explain a `verified-*` write. **Exposure is bounded**: batch 0's Phase-C twin was not
overwritten and agrees with the verified record on all 12 items, and only one of the 12 is
covered by a carried-forward draft. No classification is in doubt, but the forensic story is
incomplete and I am not claiming otherwise.

## Chapter 5 library defects — all verified from source, claim text quoted

| Site | Offending text (verbatim) | What is actually there | Verified? |
|---|---|---|---|
| **`Monad/Eilenberg/Moore/Adjunction.v:48-50`, `Monad/Eilenberg/Moore.v:33-35`, `Monad/Kleisli.v:28-30`** — one defect in three places, with **circular cross-references** | "the initial one is the Kleisli adjunction … **whose comparison into `C^T` lands in the free algebras**" · "the Kleisli category (see `Monad/Kleisli.v` …) is the initial one, **sitting inside `C^T` as the full subcategory of free algebras**" · "`C_T` is the full subcategory of free algebras inside the Eilenberg–Moore category **(see `Monad/Eilenberg/Moore.v`)**" | **No functor from `Kleisli` into `EilenbergMoore` exists anywhere in the tree** — `rg 'Kleisli.*EilenbergMoore\|EilenbergMoore.*Kleisli'` over all `.v` returns **zero hits**. Each of the three files points at one of the others for a result none of them contains. The ingredients do exist: `Monad/Comparison.v:186`'s `EM_Comparison` for a general resolution would yield the embedding when instantiated at the Kleisli adjunction (`:52` is the enclosing `Section EilenbergMooreComparison`, not the definition — corrected on audit) — but that instantiation is never made, and neither fullness nor essential-image-is-the-free-algebras is stated. | **CONFIRMED**, all three sites read plus the negative search. This is the sharpest defect of the chapter: a reader chasing the pointer lands in a cycle. |
| `Theory/Coq/Monad.v:29` | "the laws are NOT recorded as fields here; `[Monad]` carries only the operations, and **lawfulness is an obligation discharged for each concrete instance**" | No concrete instance discharges it. `IsMonad` appears **only** in `Theory/Coq/Monad/Proofs.v`, which proves it for `Identity` (`:57`), arrow/reader (`:63`) and `Compose` (`:90`). `list_Monad`, `Maybe_Monad`, `Either_Monad` and `Tuple_Monad` have **no lawfulness proof anywhere** — `rg -l IsMonad Theory/Coq/` returns that one file. | **CONFIRMED.** The same sentence appears verbatim at `Theory/Coq/Applicative.v:37` for `Applicative` and should be corrected with it. |
| `Instance/Sets/Par.v:16-19` | "Equivalently this is the Kleisli category of the maybe monad `[option]` on `[Sets]`; in Set (a Boolean topos) every Kleisli map of `[option]` is a partial function, **so PAR ≅ Kleisli(option)**" | `Part` is built **directly** at `:27` (`obj := Sets`), never as `Kleisli` of the maybe monad, and no such isomorphism is proved. The supporting argument is also stated about **Set** ("a Boolean topos") while the construction is over the **setoid** category `Sets`. | **CONFIRMED.** Compare `Instance/Coq/Par.v:34`, which makes the weaker and correctly-hedged "equivalent to pointed sets" claim. LOW severity (documentation). |

**Two candidates the verifier examined and CLEARED**, worth recording so they are not re-raised: `Structure/Limit.v:52` (p-adic integers as an inverse limit) and `Structure/Complete.v:57-59` ("monadic functors create limits, so algebras for a monad on a complete category are again complete") are **background-essay mathematics with citations**, not claims that the library contains those constants. `Monad/Monadicity/Beck.v:106-111` accurately discloses its own transport limitation. Clearing a candidate is as much a result as confirming one.

**A Phase-C search-log correction folded in** (classification unchanged): `riehl:5.1:exiii`'s gap asserted "the word `Monic` never appears in `Construction/Reflective/Idempotent.v`" — lowercase `monic` **does** appear at `:102` and `:137`, in comments observing that an invertible join is monic. The substance of the gap (characterization (ii), "μ is a monomorphism", is absent in both directions, and no lemma states that a monic join is invertible) is unaffected. This is the `rg`-case-sensitivity trap the Ch3 audit flagged, recurring in a search log rather than a defect claim.

## Chapter 5 catalog defects (fess-r5)

Verdict on substance: the strongest unit audited — accounting exact, the eight-clause
`riehl:5.1:example4` distribution map complete and reciprocally cross-referenced on all six
hosts, all three defect sites verbatim-true, pronoun sweep clean over 280 live bodies. **But
the filing failure left a correctness residue that my hand-repair did not miss — it CAUSED.**

| Finding | Fix |
|---|---|
| **HIGH (F1) — five appends were never posted, and my hand-repair caused it.** `file_chapter.py` keyed its duplicate-skip on the **item id alone**, from a snapshot taken before the run (`ledger_have`, `:73`/`:177`). Writing ledger rows for #992 and #993 by hand put their two item ids into that snapshot, so the resumed run skipped **all five** of their duplicate legs: `riehl:5.2:example6` → #465/#471/#463 and `riehl:5.5:example7` → #465/#474. Consequences: #992 and #993 asserted distribution maps naming targets that **did not hold the clauses**; a real checkbox (state R-Mod ⟶ Ab monadicity) was homeless; and **#474 had no `book:riehl` label and no project membership**, making it invisible to the campaign's own resume pre-flight. | All five appends landed with their trailers extended; #474 labelled and added to project 10; five ledger rows written with their `part:` values; five `@` keys added to `issue-map.json`; plus the sixth leg `riehl:5.5:example7@1006` (clause (iii)), which had no row either. Both items now show a complete four-clause distribution, and all five targets verified to contain their clause. **Tool fixed**: the skip now keys on the `(item_id, issue)` PAIR and the set is kept current at both write sites, so a hand-repair can never again suppress an append. |
| **MEDIUM-HIGH (F2) — `#993 ← #979` was a coordination note turned hard blocker. FOURTH instance.** The line read `Depends on: #979 (… coordinate the layout, do not duplicate it)`. #993's own Work names the real builder — **#906** — which it already depends on; #979 is itself blocked by four issues and needs quivers-as-presheaves, `Π_δ` and Beck–Chevalley, none of which #993 touches. | Edge removed, line demoted to `Related (NOT blocking)`, trailer dep dropped, `Instance/RQuiver.v` recorded as a serialize-group (#979 + #993, with #906 as the actual builder). |
| **MEDIUM-HIGH (F3) — `#1005 ← #466` and `← #704` contradicted a serialize-group I extended in the same session.** The group's own rationale records that #871 once carried these exact edges from a peer note inside a `Depends on:` line, and that they were removed as fabricated — and then I authored the sixth claimant carrying the same bug. #1005's Work item 1 **builds** the contravariant functor, and Paré's theorem does not use #466's covariant monad. | Both edges removed and demoted to `Related (NOT blocking)`. |
| **LOW (F5) — miscited line in this ledger.** `Monad/Comparison.v:52` is the enclosing `Section`; `EM_Comparison` is at `:186`. | Corrected above. |

### The `Depends on:` error, committed a FIFTH time — mechanically, while fixing the fourth

Repairing F2 and F3, my string surgery inserted the replacement text **without a leading
newline**, producing `Depends on: #906 (…)- Related (NOT blocking): **#979** …` as one
physical line. The parser harvests every number on a `Depends on:` line, so both issues
immediately failed the CONSISTENT invariant again — body asserting an edge that native no
longer had. **`check_graph.py` caught it within a minute** and I repaired the line breaks.

The lesson is narrower and more useful than "be careful": this class of error is not about
judgement at all any more — I understood the rule perfectly and still produced it, twice in
one session, once by reasoning and once by text-manipulation. What actually contains it is
the mechanical gate. The rule to internalise is **never hand-edit a `Dependencies` section
without re-running `check_graph.py` immediately afterwards.**

### Auditor claims I checked and adjusted

- The audit projected `riehl:5.5:example7` needing **five** ledger rows. The item has **four**
  clauses and all four are now homed; four is correct.
- It flagged `#750 ← #466/#704` as contradicting the Powerset serialize-group. Checked: #750 is
  *"the covariant powerset functor has no initial algebra"*, which **cannot be stated until that
  functor exists** — #466 builds it. That is a genuine consumer edge and I left it. What was
  wrong was the group's blanket phrase "no edge is asserted"; the rationale now records that a
  serialize-group asserts the absence of **precedence between peers**, not the absence of all
  edges, and that a claimant consuming another claimant's construction is a real dependency.

### What the audit confirmed that mattered most

**The zero-overturn result is genuine, not rubber-stamping.** The auditor ran an independent
agent with no access to `doc/plan/`, given only the book's paraphrases, over all 26 items in
§5.3 and §5.6 — the two sections I had flagged as anomalously low in PRESENT. It agreed on
**25 of 26**, and the single disagreement runs the *other* way (the campaign is more generous).
Under-crediting did not happen: the blind pass independently found the same root causes — no
general creates-limits predicate exists, `Complete`/`Cocomplete` have zero inhabitants tree-wide,
and `Instance/` has no Ab/Grp/Ring/Mod/Top/cHaus. My §5.3 and §5.6 flags were worth raising and
were both answered in the negative by evidence rather than by assertion.

## Chapter 6 library defects — verified from source, claim text quoted

| Site | Offending text (verbatim) | What is actually there | Verified? |
|---|---|---|---|
| `Theory/Kan/Extension.v:67-68` | "The header's specialization to **(co)limits** is realized in-tree by `[Kan_Limit]` in Structure/Limit/Kan/Extension.v" | Only the **limit** half is realized. `Structure/Limit/Kan/Extension.v` contains exactly one theorem, `Kan_Limit` (`:46`); there is no `Kan_Colimit` anywhere. The dual is prose only (`:23`, "Dually the colimit is the left Kan extension along that functor"). | **CONFIRMED.** `rg 'Kan_Limit\|Kan_Colimit'` finds only the limit theorem and its two header mentions; `rg 'LeftKan\|LocalLeftKan'` over `Structure/ Construction/ Instance/ Functor/ Adjunction/` returns **0 hits**, so no colimit-as-left-Kan statement can exist. The parenthesised "(co)" over-claims a built result. |
| `Theory/Kan/Extension.v:96-98` | "In-tree, `Construction/Day.v` **exhibits** Day convolution as the left Kan extension of the external tensor of two presheaves along the tensor of the base." | `Construction/Day.v` never mentions `LeftKan`, `LocalLeftKan` or any Kan universal property. Its only Kan reference is the **prose remark** at `:46` ("It is the left Kan extension of `[F ⊗ G]` along `[⨂]`"). What the file actually constructs is the coend formula plus unitors and associator. | **CONFIRMED.** "Exhibits" asserts a formalized identification that does not exist. |

**This is now the same pattern in five consecutive chapters** — a header claim outrunning what
the file proves, always in the same neighbourhood (limits, Yoneda, Kan, monad resolutions).
Across Ch2–Ch6 the campaign has recorded roughly forty such sites. None is an unsound proof;
every one is documentation that would mislead a reader about what is available. Still **not
filed as issues** — the campaign catalogues theory gaps, not prose it did not author — but at
this density a single dedicated documentation-accuracy sweep is clearly the right instrument,
and that recommendation is now backed by five chapters of evidence rather than one.

## Epilogue library defects and catalog defects (fess-rE)

### Library defects

Both Epilogue library-defect claims **duplicate sites already recorded from earlier chapters**,
verified at source with no contradiction between the entries:

- `Functor/Hom/Yoneda.v:22` — "natural in both `A` and `F`" with no naturality proved. Already
  Ch2 row 4 above. Homed as a LIBRARY-DEFECT checkbox on **#316**, whose title is literally
  *"Naturality of the Yoneda isomorphism in both variables"* — a better home than this ledger.
- `Structure/Limit.v:68-71` — the "uniqueness up to unique isomorphism, preservation,
  construction from products and equalizers" sentence. Already Ch3 above. Homed on **#416**.
  **Span correction**: both the Ch3 entry (`:70-72`) and the Epilogue append (`:69-72`) give the
  wrong line span; the sentence runs **68–71**. Also `limit_med_unique`/`limit_med_eq` are at
  `Structure/Limit/Preservation.v:82`/**`:91`**, not `:93` (`:93` is inside the proof body).
  Both corrected on #416.

Two further Epilogue defects survive **only as checkboxes on GitHub**, not here:
`Theory/Sheaf.v:181-190` (on #890) and `Structure/Topos.v:95-98` (referenced on #722).

**One defect claim is unrecoverable.** `riehl:E.2:def-symmetric-monoidal-category`'s verifier
note says the erroneous clause "traces to a library comment, logged on the defect channel" —
with no file, no line, no claim text anywhere on disk. `problems` is **still** not a persisted
key in `verified-E-*.json`. This is the Ch3 record-lossiness failure recurring **against this
ledger's own standing instruction** ("For Ch4 onward the defect text must be copied out of the
workflow result at fold time, not left as a pointer"). Writing the rule down did not make it
execute; only the chapters where I actually did the extraction have recoverable text.

### Catalog defects

| Finding | Fix |
|---|---|
| **MEDIUM-HIGH (F1) — `#1013 ← #417` was a FABRICATED edge, refuted by #1013's own body.** I justified it as "finite-limit preservation cannot be stated before that vocabulary exists". #1013's Work item 1 says the opposite: *"Do **not** invent a rival notion of finite shape category"*, assembling `PreservesFiniteLimits` from `TerminalFunctor`, `CartesianFunctor` and cospan-`PreservesLimit`, **all of which exist today**. My reasoning was the pre-correction Phase-C position that #1013's own Current-state section explicitly overturns — and I repeated it in the Dependencies section. Cost: transitive prerequisites `{326, 335, 416, 427}` at depth 2, inherited by #1014 and #1016, so **the entire Grothendieck/Giraud spine** sat behind a products-and-equalizers chain none of them consumes. Without the edge #1013 is layer-0. | Edge removed, line demoted to `Related (NOT blocking)`, `Structure/Limit/Finite.v` registered as a serialize-group (the shared file was the real relationship all along), gate re-run immediately per the Ch5 rule. |
| **MEDIUM (F2) — #1011 and #557 are the same graded-tensor obligation under two names.** #557 already carries a Riehl §4.4 checkbox for the tensor product of complexes; #1011 Work item 1 builds the same thing and described #557 as supplying only "chain complexes". #1011 also proposed `Instance/Module/Complex.v` while #557 defines complexes in `Structure/Abelian/Homology.v` — **different paths, so `check_collisions.py` and `check_graph.py` are both blind to it.** | Overlap disclosed on #1011 with two checkboxes (do not build a second complex category; build the graded tensor once). Not a full duplicate: the symmetric monoidal structure, hexagon, `braid_invol` and sign conventions are genuinely unowned and remain #1011's real content. |
| **MEDIUM (F3) — cocompleteness of a Grothendieck topos obliged on BOTH #1014 and #1016, with the actual builder named by neither.** **#434** (*"A full reflective subcategory of a cocomplete category is cocomplete"*) states exactly that theorem, and `Reflective` carries `reflective_full` so it applies on the nose. | Cross-references added both ways, #434 named as the builder on each. |
| **MEDIUM (F4) — clause (a) of the E.2 roster: prose, no checkbox.** The append correctly observes `Sets_Monoidal`/`Cat_Monoidal` are "one application away and none of them is one", then files nothing — while all four E.2 blocks assert "clause (a) is already in force". True of the generic `CC_SymmetricMonoidal`, false of the instances; `rg` → 0 hits and no corpus owner. The sibling leg #388 got a checkbox for exactly this shape. | Checkbox added to #490. |
| **LOW (F7) — #423 is product-only; Riehl states products **or coproducts**, complete **or cocomplete**.** The append called it "the same theorem and the same argument" with no checkbox. | Checkbox added; near-free via `C^op` since thinness is self-dual. |

### Corrections to my own reporting

I told the user the Epilogue was "36 append rows onto 30 existing issues". Actual: 36 rows over
**30 distinct items** landing on **29 distinct hosts**. This is the **same arithmetic slip as
Ch3** (recorded there as "82 rows over 76 items landing on 48 issues"), made again after being
written down. Both times it was confined to prose; no artifact asserts the wrong number.

### What the audit confirmed

Accounting exact (47 items, 54 ledger rows = 47 + 7 multi-part legs, 45 issue-map keys, zero
orphans either way). All 36 appends verbatim-live — **the Ch5 "five appends never posted"
failure did not recur**, which was the specific regression worth checking after that repair.
The edit-error residue check came back empty: #1014 contains zero occurrences of `#417`, all six
trailers parse, and all six live bodies are byte-identical to `drafts-E.md` apart from two
intended item-id resolutions. Pronoun sweep clean over **311** live bodies. Both clause
partitions correct, including `riehl:E.5:exi`, whose clause (i) needs no home because it is
PRESENT in a **stronger biconditional form** (`monic_iff_kernel_pzero`,
`epic_iff_cokernel_pzero`) — and both appends say so by name. The `#901`/`#1012` peer judgement
confirmed, with the rationale praised for separating coordination from precedence. Dedup on the
other three new issues confirmed clean.

## Chapter 6 catalog defects (fess-r6)

**The central question survived an independent blind reproduction.** The audit reclassified all
37 items of §6.2 and §6.5 with `doc/plan/` off-limits and found **zero PRESENT in either
section**. 28 of 37 matched exactly; of the 9 disagreements, **6 run the direction where the
campaign is MORE generous**, and the 3 where the blind pass was more generous are cases the
campaign's own records name and explicitly reject. **Under-crediting did not happen**, and
§6.5 append honesty — the surface I flagged as highest risk — came back clean across all 14
blocks, with every append lacking a checkbox covered by a host Work item verified verbatim.

| Finding | Fix |
|---|---|
| **MEDIUM (F1) — #972 and #1028 build the SAME zig-zag localization under two different paths.** `C[C⁻¹]` is literally the `W = all morphisms` case of `C[W⁻¹]`; both take the free category on a glued quiver and quotient by a hom-congruence, from the same two donors. I had *seen* the relation (#1028 carried a `Related: #972` note) and taken **no structural action**. Because the paths differ, `check_collisions.py` and `check_graph.py` are both blind to it. | Serialize-group added; build-once checkboxes and reciprocal `Related (NOT blocking)` notes on both issues. |
| **MEDIUM-LOW (F2) — the #345/#809 remedy was incomplete.** My serialize-not-dedupe conclusion was right (both must survive: #809 owns the pullback-in-`Cat` theorem and the `IsDiscreteOpfibration` correspondence that **#948 depends on it for**). But #809's Work item 1 still instructs a second `Elements` construction. I gave the correct "consume, do not re-create" instruction to the NEW issue #1021 and left the identical hazard on #809. **Serializing orders a duplicated instruction; it does not remove it.** | Consume-not-recreate checkbox added to #809. |
| **MEDIUM-LOW (F3) — `#1021 ← #716` is a relation, not a prerequisite.** Its only use is a Work-item sentence "relate it to #716's identification, of which this is the general form"; the corresponding DoD checkbox consumes #345 only. Sixth instance of the soft-note-as-hard-edge family, in its mildest form. | Edge removed, demoted to `Related (NOT blocking)`, gate re-run. |
| **LOW-MEDIUM (F4) — six appends cite a Ch6 sibling "filed as its own issue in the Riehl Chapter 6 batch" without the number**, while the same appends give numbers for pre-existing targets. This is the Ch1 #913/#907 defect recurring. Worst case #589, whose append says the reindexing functor "**which this issue's functoriality step needs**" is filed separately — with no edge either way and nothing on #589 naming #1021. | Reciprocal reference added to #589 naming #1021. |
| **LOW (F5) — the `Construction/Elements.v` rationale I wrote during Ch6 filing misdescribes the live graph.** It said "no precedence exists between #345 and #809"; `#809 ← #345` is live and correct, since #809 consumes the construction. | Rationale corrected to say the group records absence of precedence among the *remaining* pairs. |
| **LOW (F6) — #1028 used `Related:` rather than `Related (NOT blocking):`.** The full form exists because of the five times such a note became a hard blocker; #1021 used it correctly in the same batch. | Normalized. |
| **LOW (F7, tool) — `check_collisions.py` matches proposed PATHS**, so same-construction-different-path pairs are structurally invisible to it. Two shipped (F1, and Epilogue F2's #1011/#557). | Documented in the script's own header with both examples, so a clean collision report is not mistaken for an absence of overlap. |

### An artifact gap worth more than any single finding

The auditor observed that **the PARTIAL/ABSENT boundary rule was nowhere written down** — not
in `schemas.md`, only in one verifier's note on `riehl:6.2:cor7` — despite governing all 2920
classifications. It is now recorded in `schemas.md`: *PARTIAL requires a PROVED statement
covering part of the item; a never-instantiated class does not qualify.* That single sentence
is why a chapter sitting on a file named `Theory/Kan/Extension.v` scored 1 PRESENT in 85, and
why the blind pass agreed. Along with it, the near-miss corollary: record a near miss so the
implementer finds it, but never let it move the classification.
