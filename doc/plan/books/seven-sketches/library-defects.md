# Library defects surfaced during the Seven Sketches catalog campaign

Same convention as the MacLane and Awodey ledgers: in-tree defects (dangling
pointers, comment-vs-code mismatches) found by the coverage/verify agents while
classifying — NOT missing-theory gaps. Recorded so they are not lost; filing as
GitHub issues is a maintainer call.

Numbering continues the campaign's letter scheme with an `S` prefix for book 3.

## Chapter 1 haul (2026-07-29) — 4 new, 3 heavy recurrences

Every entry below was re-read from source by the main session before recording.

| # | File:line | Defect | Disposition |
|---|-----------|--------|-------------|
| **S1** | Instance/Two/Discrete.v:22-24 | Header asserts BOTH directions — "the limit of a diagram of shape `Two_Discrete` is a binary product, **and the colimit is a binary coproduct** (see [Structure/Limit/Cartesian.v])" — but the cited file contains **exactly one theorem**, `Cartesian_Limit` (:39), covering only the limit/product half. Verified: `Cocartesian_Colimit\|Colimit.*Cocartesian\|Cocartesian.*Colimit` = **0 hits tree-wide**, so the coproduct-as-colimit statement exists nowhere. The cross-reference is correct for products and overreaching for coproducts. | Recorded. The coproduct half is a genuine gap; it rides the Ch1 join/colimit issues. |
| **S2** | Instance/Sets.v:32-33 **↔** :99-104, :414-417 | Header says "This file builds … the characterizations of monos as injections **and epis as surjections**". The mono half is real (`injectivity_is_monic`, :369, an iff). The epi half is **not in the environment**: `surjectivity_is_epic` (:429) is *stated* as an iff but, as the file itself explains at :414-417, "the reverse direction is abandoned (this lemma ends in a non-completing tactic), so `[surjectivity_is_epic]` does **NOT** enter the environment and nothing downstream relies on it." So the file **contradicts its own header** — and the honest, well-argued disclosure at :99-104 (a predicativity/size obstruction, not sloppiness) makes the header the only wrong part. **SHARPENED (Ch7 verifier, re-verified by me at `:476`): the lemma ends in `Abort.`, so the WHOLE lemma never enters the environment — not even the PROVED forward direction (surjective → epic) is available.** My original wording ("the reverse direction is abandoned") understated it: nothing of the epi characterization is usable, in either direction. | Recorded (MEDIUM). Fix is a header word: "the characterization of monos as injections, and the forward half for epis". |
| **S3** | Instance/Rel.v:163-165 | The comment on `Relation_Functor` states it "is the identity on objects **and faithful**, exhibiting Coq (Set) as a wide subcategory of REL". Identity-on-objects is evident from `fobj := fun x => x` (:169), but **faithfulness is asserted and never proved**: `Relation_Functor` occurs exactly once in the tree (its own definition, :167) and there is no `Faithful` instance for it. | Recorded (LOW-MEDIUM). One-lemma fix; the claim is almost certainly true, just unproven. |
| S4 | Theory/Isomorphism.v:30-31 | Flagged by a verifier as a stale cross-reference: "An isomorphism in Cat is the same as an equivalence of categories." **I judge this NOT a defect and record it only so the next pass does not re-litigate it.** The sentence continues, in the same breath, "In order to get actual isomorphism between categories, the compositions `F ○ G` and `G ○ F` need to be **equal**, rather than equivalent, to identity. Since this is usually too strong a notion, it does not have its own abstraction here." Given the library's `Isomorphism` states its round trips up to `≈`, an iso in `Cat` really is an equivalence, and the passage says exactly that. | **Dismissed** (verifier's severity was already "lower confidence"). |

### Recurrences of already-recorded Awodey/MacLane defects
Recorded here only as evidence of independent re-discovery — the entries live in
`doc/plan/books/awodey/library-defects.md`.

| Recurs | Where | How often this chapter |
|---|---|---|
| **A1 / A2** (dangling `[Pos]` and `[Ord]` coqdoc pointers to categories that do not exist) | Instance/Poset.v:21-22, Instance/Proset.v:19 | Flagged **independently by 8 different agents** in Chapter 1 alone. Both files are foundational for this book's order-theoretic chapter, so every batch tripped over them. `Pos` is resolved by **#641**; `Ord` still has no home. This is now the campaign's most-rediscovered defect. |
| **A45** (Instance/Poset.v:46-54 "`[Poset]` installs the resulting dictionary" — it installs none of the four listed collapses) | Instance/Poset.v:45-54 | Flagged **5 times independently**. Re-confirmed with a sharper counter-search than A45 originally carried: `Cartesian\|Cocartesian` over BOTH `Instance/Poset.v` and `Instance/Proset.v` = **0 hits**, so neither file carries any Cartesian, Cocartesian, Monad or Adjunction instance. The dictionary is *described*, never *built*. |
| **A37** (Construction/Slice/Pullback.v:30-40 asserts an adjunction that is only a commented stub) | Construction/Slice/Pullback.v:30-40 | Flagged once, self-disclosed as before. |

### Useful provenance found while classifying (not a defect)
`Instance/Poset.v:96-100` **cites this very Seven Sketches chapter by name** and
states the generative-effect definition. Worth quoting in the Chapter 1
generative-effects issues as evidence the library already acknowledges the
concept without formalizing it.

**CORRECTION (fess-7s1 H2) — my earlier diagnosis here was wrong and too kind.**
I recorded that the coverage log's "generative effect → 0 hits" was true "only
because the phrase is line-broken in the source". It is not: line 97 reads
`"Generative Effects: Orders and Galois` **on one line**, so a plain
`grep -rni 'generative effect'` matches it. Verified directly. The log was a
straightforward **FALSE NEGATIVE**, and calling it a line-break artifact papered
over a real error. (A line-break blind spot IS real elsewhere — see the M3
entries below — but it is not the cause here.)

## Coverage-log defects found by fess-7s1 (Chapter 1) — evidence-trail, not classification

None of these changed a verdict, but the campaign's contract makes the
`negative_search_log` a reproducible evidence trail, and these break it.

| # | Record | Defect |
|---|---|---|
| **L-1** | `1.1.2:eq8` | "0 hits" for `generative effect` is a **FALSE NEGATIVE** — 1 hit at `Instance/Poset.v:97`, matched by the plain logged command. |
| **L-2** | `1.4.4:example123` | "0 hits for Lawvere–Tierney" — `Structure/Topos.v:88` says "Lawvere-Tierney topologies". |
| **L-3** | `1.4.3:thm115` | "'preserves meets' 0 hits; likewise 'meet-preserving'" — `Structure/Topos.v:87` says "finite-meet-preserving". |
| **L-4** | `1.3.1:example76` | "`transitive closure\|clos_trans\|clos_refl` 0 hits" — run properly, `transitive closure` hits `Instance/Lambda/Multi.v:14,16,32,44` and `clos_trans` hits `Lib/TList.v:55`. **Contradicted by two records in its own batch**: `remark39` cites `Instance/Lambda/Multi.v:74` as evidence and `construction-level-shift-rel-pos` says "`multi` is the in-tree version". |
| **L-5** | `1.3.1:prop91` | Output right, conclusion wrong: `cofinal\|final functor` really is 0 hits, but "final functor" DOES occur at `Structure/Factorization.v:96-97`, broken across the newline. A genuine line-break blind spot. |
| **L-6** | `1.4.4:construction-closure-from-galois-connection` | "4 hits, all prose in Instance/Poset.v" misses `Theory/Monad.v:66-67`, which is the most on-point in-tree prose for this exact item — "on a poset category a monad is precisely [a closure operator], the unit giving extensivity and [join] idempotency" — **in the very file that would host the formalization**. |

### ⚠⚠ SYSTEMIC: 28 logged greps CANNOT BE RE-RUN AS WRITTEN
They use `grep` with `|` alternation and **no `-E`**, e.g.
`grep -rn --include=*.v 'ZArith|Coq.Reals|QArith|Z_scope|BinInt' . -- 0 hits`.
Basic `grep` treats `|` **literally**, so such a command returns 0 hits
**unconditionally, regardless of tree contents** — the log records a command
that cannot fail. Most conclusions survive re-running each alternative
separately (there really is no `ZArith`, `Rle`, `Included`, `hasse`), but the
evidence trail does not, and **L-4 above is materially wrong** because of it.
FIX for later chapters: require `grep -E` (or `rg`) whenever a pattern contains
`|`, and require multi-word phrase searches to use a whitespace-tolerant pattern
(`rg -U 'final\s+functor'`) since the tree hard-wraps its prose at ~72 columns.

## Corrections to the fess-7s1 audit itself (verified by the main session)

The audit was strong and two of its findings corrected me. Verifying its
findings in the other direction turned up two that do not hold as stated.

- **L6 is WRONG.** It claimed "the exercise's headline deliverable (Hasse
  diagrams, 0 hits tree-wide) landed on neither target and got no issue".
  Hasse diagrams DID get an issue: **#768** ("The preorder presented by a
  graph — reachability closure, the edgeless case, and transitive
  redundancy") states the gap at its lines 59-60 ("no notion of a Hasse
  diagram, reduced graph or transitive reduction") and work item 5 is
  "define the covering relation (transitive reduction) for a finite preorder,
  so 'the Hasse diagram of a preorder' has an in-tree referent". Three more
  of the 17 new issues carry the same `rg -in 'hasse'` = 0 hits evidence.
  The auditor examined only `ex57`'s two APPEND targets (#273, #714) and did
  not check whether a NEW issue from the same pass covered the obligation.
  The 0-hits fact is correct; "got no issue" is not.
- **The `ex118` -> #382 finding is overstated.** Called "self-contradicting"
  for asking #382 for dual-image evaluations after the campaign assigned the
  dual image to #384. The append block in fact says, verbatim, "The general
  constructions are this issue's (and #384's) obligation; what this exercise
  adds is the concrete evaluation" — it names #384 as co-owner explicitly.
  The genuine (LOW) residue is only that the concrete dual-image evaluation
  checkbox lives on #382 while the dual-image construction is #384's, so an
  implementer of #384 might not know where the evaluation is tracked. FIXED
  by adding a pointer note to #384 rather than moving anything.

Both are recorded because the campaign's rule cuts both ways: verify a
finding before acting on it, whether it flatters the work or not.

## Chapter 2 haul (2026-07-30) — 3 new, all verified from source by the main session

| # | File:line | Defect | Disposition |
|---|-----------|--------|-------------|
| **S5** | Functor/Structure/Monoidal.v:110-124 **↔** :45-48 | **`LaxMonoidalFunctor` is not usable by a genuinely lax functor.** Its comparisons are correctly LAX — `lax_pure : I ~> F I` (:111) and `lax_ap : F x ⨂ F y ~> F (x ⨂ y)` (:118) are one-directional. But the class then REQUIRES three **isomorphism** fields with no defaults: `pure_left {x} : I ⨂ F x ≅ F (I ⨂ x)`, `pure_right`, and `ap_assoc {x y z} : (F x ⨂ F y) ⨂ F z ≅ F (x ⨂ (y ⨂ z))` (:120-124). An `≅` at `ap_assoc` cannot be supplied from a merely-lax `lax_ap`, so the class excludes lax-not-strong functors. And the header **says the opposite** at :45-48: these fields "record the derived isomorphisms used to phrase those coherence squares; **they are consequences of the comparisons, not extra structure**" — but a consequence would be a derived lemma, not a required field. Verified verbatim at both ends. This bites Seven Sketches §2.2.5 directly, whose monoidal monotones are the canonical lax-not-strong examples. **BLAST RADIUS (added by fess-7s2, which strengthened this entry):** the class has **no lax-not-strong inhabitant anywhere in the tree** — every instance is the identity (`Id.v:73`, which discharges `ap_assoc` by `apply tensor_assoc`, possible only because it is strong), a composite or product of such, or built from a genuinely strong `MonoidalFunctor`. Worse, roughly **eight developments take `LaxMonoidalFunctor` as a hypothesis and therefore silently require strongness**: the `DecoratedCospan` family (`.v:114`, `Category.v:88`, `Braided.v:78`, `Symmetric.v:80`, `Monoidal.v:83`, `Hypergraph.v:117`), `Cospan/BlackBox.v:81,171`, `Monad/Distributive.v:49`, `Monad/Compose.v:52`, and `Functor/Applicative.v:45`. Line-number corrections from the same audit: `lax_ap` is `:117` not `:118` and `pure_left` is `:119` not `:120`. | Recorded (HIGH — a class that cannot express its own advertised generality, with eight downstream consumers silently over-constrained). Folded by the drafter into **#782**'s Definition of Done, with **#783** (floor/inclusion) as the regression test. |
| **S6** | Construction/Enriched/Two.v:12 | Section heading claims "Categories enriched over 2 are **exactly** preorders". What is proved is `Enriched_Two_preorder : @Enriched _2 Two_Monoidal ↔ TwoPreorder` (:165), and `↔` is **`iffT`** (`Lib/Foundation.v:72`) — i.e. functions in both directions, NOT proven mutually inverse. "Exactly" asserts a bijection/equivalence; `iffT` gives mutual derivability. Verified both the heading and the notation definition. | Recorded (MEDIUM). Folded into **#785**, whose whole obligation is upgrading the two translations to a genuine bijection. |
| **S7** | Structure/Monoidal/Strict.v:42-43 | "Strict monoidal categories are precisely monoid objects in the cartesian monoidal category `[Cat]`" — stated with the library's in-tree `[Name]` bracket convention for a fact that is **not proven in-tree**. The tree has only the Funny-tensor cousin: `Instance/StrictCat/Premonoid.v:137` builds `StrictPremonoidal` from `@MonoidObject StrictCat Funny_Monoidal`, and that file's own header at :24 calls the Cat statement "the **classical fact**" — i.e. explicitly external. So the bracket misleads. | Recorded (LOW-MEDIUM). The honest fix is to mark it classical, as Premonoid.v already does. |

### Recurrences this chapter
**A1 / A2** again (dangling `[Pos]` at Instance/Poset.v:21-22 and `[Ord]` at
Instance/Proset.v:19-20). The Ch2 verifier added a sharper observation than the
original entries carried: chasing `[Pos]` lands a reader on the **stdlib**
`Pos` module (binary positives — `Pos.eqb_eq`/`Pos.eq_dec` in Lib/MapDecide.v),
which is *worse than a plain dead link* because it resolves to something real
and entirely unrelated.

## Coverage-log defects, Chapter 2 (fess-7s2) — the Ch1 rule is now MOSTLY honored

Ch1 had **28** log entries using `grep` with `|` alternation and no `-E` (a
command that returns 0 hits unconditionally, so the log cannot fail). Ch2 is
down to **10 of 373** — the launch-brief rule worked, but not completely. Four
of those ten narrate specific findings that a literal-match grep cannot return;
the auditor ran all three distinct commands verbatim and each exits 1 with zero
matches:

| Record | Logged command (bare `|`, no `-E`) | Claims |
|---|---|---|
| `def2`, `example4` | `grep -rn 'Monoidal' --include='*.v' Instance/ \| grep -i 'omega\|proset\|poset\|two'` | "only Instance/Two/Monoidal.v" |
| `remark3` | `grep -rn 'Lemma\|Theorem' Instance/Poset.v Instance/Proset.v` | "only eq_equiv and the Poset/Proset constructors" |
| `ex50` | `grep -n 'Theorem\|Lemma\|Definition\|Corollary\|Instance' Construction/Enriched/Sets.v` | "only EF, EG, EnrichedTransform_is_Transform" |

**The conclusions all survive** re-running the corrected forms (`grep -riE`
surfaces `Instance/Two/Monoidal.v:105-106` with tensor as meet and unit as top;
`Instance/Poset.v:111 Lemma eq_equiv`). These are transcription defects, not
fabricated classifications. But the standing rule holds: a log that cannot be
re-run is not evidence.

### Two Ch2 LOW items, recorded so they are not re-litigated
- `def41` cites `Functor/Structure/Monoidal/Id.v:83` for `Id_LaxMonoidalFunctor`;
  the instance is at **:73** and `:83` is inside its obligation block. The
  `intree_statement` shows the point IS about the obligations, so this is
  mislabelled rather than wrong — and `:85` (`Next Obligation. apply
  tensor_assoc. Qed.`) is strong corroboration of **S5**.
- `#795`'s parenthetical calls #308 "the metric-space structure" while #308's
  title is about metric-space *completion as a universal arrow*. Defensible —
  the `def51` append explicitly extended #308 to carry the definitional
  obligation — but the parenthetical names a prerequisite inside #308 rather
  than #308 itself.

### An unreconciled tension, disclosed rather than resolved
`def2` (PARTIAL, files #771) says "**NO** in-tree class asks for the object
equality `x ⨂ y = y ⨂ x` that Definition 2.2(d) demands", while `prop38`
(PRESENT, files nothing) says "a symmetric monoidal preorder **is the thin
case**" of a symmetric monoidal category. The auditor judged PRESENT defensible
on content — clause (d) never mentions the order and dualizes vacuously, and
`Monoidal_op`/`Symmetric_op` deliver the substance at greater generality — and
rated it LOW. But two sibling records make opposite claims about whether the
structure has an in-tree counterpart, and **the one that files nothing makes the
stronger claim**. Wording should be reconciled; no obligation is lost either way
because #771 creates the structure.

## Chapter 3 haul (2026-07-30) — S8 is the campaign's most serious TRUTH-CLAIM defect

| # | File:line | Defect | Disposition |
|---|-----------|--------|-------------|
| **S8** | Theory/Metacategory.v:148-159, 261-264, 413 | **`Three` is the EMPTY category, and the file presents it as the three-object one.** The chain, verified line by line: `arr := nat` (`:135`) is INFINITE; `pairs : M.t arr` (`:138`) is a FINITE map; `composite f g h := M.MapsTo (f,g) h pairs` (`:143`); and `identity (u) := (∀ f, composite f u f) ∧ (∀ g, composite u g g)` (`:158-159`) therefore demands a binding `(f,u) ↦ f` for **every** `f : nat` — infinitely many, in a finite map. So **no arrow satisfies `identity`**, `FromArrows`'s object type `obj := ∃ i, identity M i` (`:262`) is **uninhabited**, and `Three := FromArrows ThreeArrows` (`:413`) has zero objects. Every category law it "satisfies" — in particular the unit laws — holds **vacuously**. The file's own note at `:148-156` says dropping Mac Lane's definedness guard is "strictly stronger … but is **sound** for the finite, explicitly-enumerated metacategories built here". That is exactly backwards: over an infinite `arr` with a finite `pairs`, dropping the guard makes the predicate **unsatisfiable**, not merely stronger. | Recorded **HIGH as a truth claim** — the header at `:84-86` calls `FromArrows` a "**machine-checked witness** … to a `[Category]` whose objects are the identities", and in a library whose entire premise is machine-checked rigor, a vacuous witness is the worst kind of overclaim. **BLAST RADIUS: ZERO, verified.** Nothing in the tree imports `Theory/Metacategory.v` (its module functor is never instantiated outside itself), so no other development rests on it. **And the correct development already exists beside it**: `Theory/Metacategory/ArrowsOnly.v:70` keeps the guard, `(∀ f, defined f u → composite f u f)` — precisely what `:155` points at. The fix is to adopt the guarded form here, or to retract the soundness note and the witness language. |
| S9 | Theory/Metacategory.v:102-103 | "`[cardinality]` counts the identity arrows, the entries `[(i,i)]` mapping to `[i]`". `cardinality` (`:415`) counts finite-map entries whose key and value coincide — a purely SYNTACTIC proxy. It counts neither arrows satisfying `identity` (none do, per S8) nor objects of `Three` (there are none). `ThreeArrows_card_3` means "the table has three diagonal entries", nothing more. | Recorded (consequence of S8). |
| S10 | Theory/Metacategory.v:184-194 | **Self-disclosed but still live**: the third Mac Lane axiom is written `identity_law (g : arr) : exists u, identity u -> exists u', identity u' -> defined g u pairs /\ defined u' g pairs`, and the file's own `jww` note admits it is vacuously true and constrains nothing. Combined with S8, the ONLY real obligations discharged for ZeroArrows/OneArrow/TwoArrows/ThreeArrows are `composition_law` and `triple_composition`. | Recorded. |
| S11 | Construction/Free/Quiver.v:48-51 | Header states `FreeSyntax` "is equivalent to `[FreeOnQuiver]`", but the file constructs **no functor, isomorphism or equivalence** between them — only the round-trip lemmas `morDA_tlistDA` (`:582`) and `tlistDA_morDA` (`:592`). | Recorded (MEDIUM — same "iffT is not a bijection" family as S6). |

**S8 IS MACHINE-VERIFIED — and my earlier note here was WRONG.** I originally
recorded that "the probe cannot be written from outside" because `Metacategory` is a
module functor (`:122`) never instantiated elsewhere. **That is false, and it understated
the finding.** The auditor built the probe I said was impossible: the functor takes any
`WSfun PNN`, and `FMapWeakList.Make PNN` is one. I re-compiled it myself under Rocq 9.1
and it yields THREE axiom-free results (`Print Assumptions` = "Closed under the global
context" on each):
- `identity_unsatisfiable : ∀ (M : Metacategory) (u : arr M), identity M u -> False`
- `Three_is_empty : @obj Three -> False`
- `composition_law_live` — the surviving content IS non-vacuous: `composite ThreeArrows
  0 3 3`, `3 4 5` and `4 2 4` are inhabited, so `composition_law` fires on a genuine
  composable triple. This is what makes the related coverage verdict PARTIAL rather than
  ABSENT: the composition TABLE is real machine-checked data; only the CATEGORY
  realization is empty.
The contradiction is immediate once stated correctly: `WSfun` exposes `elements`/
`elements_1`, witnessing every binding in a FINITE list, so choosing `f` above every
first coordinate in `elements` refutes `∀ f, MapsTo (f,u) f pairs`. **`pairs` cannot be
infinite.**
Probe preserved at `doc/plan/books/probes/S8-metacategory-vacuity.v`.
Both severity claims independently re-verified by the auditor: the only in-tree importer
of the module is `Theory/Metacategory/DecideExample.v:5`, which imports the SIBLING
`ArrowsOnly` — so blast radius is genuinely zero — and `ArrowsOnly.v:70` does keep the
guard.

## Coverage-log greps, Chapter 3 — the defect got WORSE, and that is the signal

| Chapter | defective log lines | records affected |
|---|---|---|
| Ch1 | 28 | — |
| Ch2 | 10 of 373 | — |
| **Ch3** | **41** | **18** |

The launch brief for Ch3 carried an explicit, strongly-worded rule (use
`grep -E`/`rg` when a pattern contains `|`; every logged command must actually
produce the reported result, because the auditor re-runs them verbatim), and
the count went UP. **Prompt instruction alone is not fixing this.**

Proved on this box by the auditor:
```
grep -rln  --include='*.v' -i 'preorder|proset|poset' .   ->  0 files
grep -rlnE --include='*.v' -i 'preorder|proset|poset' .   -> 23 files
```
**It is mis-transcription, not fabrication** — decisive evidence: the
`3.2.3:ex3.21` log narrates *"23 files"*, exactly the `-E` answer, so a working
command was run and then written down wrong. Every re-run conclusion survives.
Two narrated HIT LISTS are nonetheless materially false:
- `Skeleton|skeletal` claimed "only Test/Poset.v"; **17** files match, incl.
  `Instance/FinSet.v:15`. (The attached clause "no `Skeleton` construction" is
  true.)
- `cardinal|Cardinal` claimed "only Theory/Metacategory.v and Instance/Shapes.v";
  also `Structure/Complete.v:69` and `Theory/Universal/Arrow.v:83`.
Both feed `3.2.5:def-cardinality`, whose `gap` is independently correct.
Credit where due: `3.2.3:construction-preorder-reflection` carries an explicit
in-place "CORRECTION to the Phase C log" and was overturned ABSENT->PARTIAL on
`Theory/Category.v:282` `hom_preorder`, which the auditor verified exists.

**RECOMMENDED STRUCTURAL FIX (not yet applied):** stop asking agents to
transcribe commands faithfully and instead have the coverage phase WRITE the
command and its output to a file it cannot edit afterwards, or have the
verifier mechanically re-run every logged command and diff. A rule that has now
been restated three times and is still violated needs a mechanism, not another
sentence.

## A blind spot in `check_collisions.py`, found by fess-7s3

The checker keys on **module paths** — its header calls that "the better
signal" than titles, which is true and was the fix for a real earlier failure.
But it is structurally blind to **the same concept proposed under two different
filenames**. Live instance: **#742** ("sets with an endomorphism", proposing
`Instance/Endo.v`) and **#807** ("discrete dynamical systems", proposing
`Instance/DDS.v`) are the same category. Zero path overlap, so zero collisions
reported. FIXED for this instance (#807 retargeted onto `Instance/Endo.v` with
a `Depends on: #742` and a reciprocal note), but the general gap stands: no
mechanical check catches synonymous concepts. Title/­concept similarity would
need a semantic pass, which is what the drafter's dedup step is for — so the
practical mitigation is that the DRAFTER, not the checker, must catch these.

## Chapter 4 haul (2026-07-30)

| # | File:line | Defect | Disposition |
|---|-----------|--------|-------------|
| **S12** | Construction/Enriched.v:79-81 | "Any closed monoidal base is moreover enriched in itself through its internal hom, **as Structure/Closed.v records**." It records no such thing. Verified: that file's ENTIRE set of declarations is `Curry` (:124), `Flip` (:144) and `Class Closed` (:166) — and CLAUDE.md itself describes `Structure/Closed.v` as "an incomplete Eilenberg–Kelly stub whose `Class Closed` is not yet in force". Its own :54-**58** merely repeats the same claim as prose attributed to the nLab **and then points BACK at `Construction/Enriched.v`** — so the pointer is **circular**, and following it in either direction yields another sentence (strengthened by fess-7s4; my original cited :54-56, the sentence runs to :58). Two further confirmations that `Class Closed` is unfinished rather than merely unused: it has a field literally named `hom_` whose type contains an unfilled `_` (`Structure/Closed.v:182-184`), and `Structure/Monoidal/StarAutonomous.v:60` independently declares "We do NOT use Structure/Closed.v, an Eilenberg-Kelly [stub]". No `Enriched` instance is built from `Closed` anywhere in the tree. | Recorded (MEDIUM). Bears directly on `7sketches:4.2.2:def4.8`, whose (correct) gap says the self-enrichment of the base V — one of the three ingredients Definition 4.8 needs — does not exist in-tree, while this header reads as if it did. |
| — | Instance/Poset.v:21, Instance/Proset.v:19 | **A1/A2 recur for the fourth consecutive chapter.** | Duplicates of A1/A2. |

### The negative-search-log defect in Ch4 — and a CORRECTION to how it has been counted

The Ch4 verifier self-reported **three** logs that misstate WHERE their hits are
(`ex4.17`, `ex4.50` (two sub-items), `ex4.62`), all confirmed. But the auditor
found a **separate and larger** family the ledger had not recorded: **nine**
entries using `grep` with a bare `|` and no `-E`, under `def4.21`,
`def-skeletal-quantale`, `thm4.23` (x2), `def4.24`, `def4.25`, `ex4.26`,
`lem4.27`, `lem4.31`. It proved the defect concretely — `def4.21`'s command run
verbatim returns 0 lines — then re-ran all nine with `-E`: **every conclusion
holds**, seven return 0 hits exactly as claimed, and the two that narrate
findings reproduce their narration precisely. So the agent ran the right
commands and dropped the `-E` when transcribing.

⚠ **COUNTING METHODOLOGY IS CONTESTED, AND EARLIER FIGURES ARE UNRELIABLE.**
The Ch4 auditor explicitly retracted its own first count, noting that 20 Ch4
logs use `\|` (VALID BRE alternation) and 35 use `-E`/`rg` (also correct), and
that lumping those with bare `|` "would have been the wrong number". That
casts doubt on the **41** figure reported for Ch3 and on the 28/10 for Ch1/Ch2,
which may have counted valid `\|` forms as defective. I attempted an
independent recount and got 2/4/34/0 for Ch1-4 — irreconcilable with the
auditors' 28/10/41/9, and demonstrably wrong for Ch4, where my regex reports 0
against a PROVEN instance. **I therefore do not publish a count.** The
qualitative finding is solid and unchanged: bare-`|`-without-`-E` logs exist in
every chapter, they are unreproducible as written, and in every case checked so
far the underlying conclusion survives re-running the corrected command — it is
transcription, not fabrication. The earlier claim that the defect "is getting
worse" rests on those disputed counts and should NOT be relied on.

## Chapter 5 haul (2026-07-30)

| # | File:line | Defect | Disposition |
|---|-----------|--------|-------------|
| S13 | Construction/Free/Quiver.v:4, :9 | **Two dead imports.** `Require Import Category.Construction.Groupoid.` (:9) and `Require Import Category.Theory.Isomorphism.` (:4) are both unused: verified that `Groupoid` occurs exactly ONCE in the file (its own import line) and that `Isomorphism\|iso_\|≅` likewise occurs exactly once (its own import line). Surfaced while verifying `example5.6`'s claim that `Groupoid` is applied only at `Fun C Sets` — the claim is true, but grepping for the module name alone would suggest a second consumer that does not exist. | **Removal CANDIDATE, not removed.** Per the standing no-wholesale-deletions rule this is surfaced for the owner to decide; the coverage agent correctly flagged rather than acted, and so have I. |

### Ch5 process notes (both positive, recorded because they show fixes landing)
- **Flag normalization: 0 added, 0 removed** — all 6 multi-page items already
  carried `spans-page-break` in BOTH ranges and no single-page item carried it
  spuriously. The merge said so explicitly rather than passing silently, which
  is the behaviour the Ch1 fix was written to produce.
- **The `Print Assumptions` instruction was honoured honestly**: the merge
  reported it "not applicable at this phase (no PRESENT verdicts are asserted
  here) and were not run" — a correct scope judgement rather than a hollow
  compliance claim.
- A conservative choice worth a reviewer's eye, disclosed rather than silently
  made: six numbered displays state definitional content in running prose
  (5.52, 5.75, 5.76, 5.78, 5.81) and were minted as `number:null` items flagged
  `number-N-is-a-display` instead of being promoted to kind `equation` with the
  book's number. The merge preserved the source agents' conservative choice and
  said so, rather than silently re-kinding.

### BOOK ERRATUM (Seven Sketches, not a library defect) — Def 5.11 vs Prop 5.54

Found by fess-7s5 and recorded here because the campaign records comparable
errata elsewhere (the `Sq_conjoint_iso` and `tperm`/`Permutation` entries) and
because **a literal formalization of Definition 5.11 will not support
Proposition 5.54's proof**.

Definition 5.11 (printed 151, PDF 163) requires only that a prop functor be
(a) identity-on-objects and (b) monoidal on morphisms, `F(f) + F(g) = F(f + g)`.
But the proof of Proposition 5.54 (printed 166, PDF 178) asserts that "S is a
prop functor by Theorem 5.53, which **by Definition 5.11** must preserve
identities, compositions, monoidal products, **and symmetries**." Symmetry
preservation is NOT in Definition 5.11 as printed.

Affects **#832** (which formalizes Def 5.11) and **#845** (which needs Prop
5.54). Whoever implements #832 must decide whether to formalize the definition
as printed and then strengthen it for #845, or to include symmetry preservation
from the start and note the divergence from the book's text. Recorded in
neither issue at filing time; noted here.

### Ch5 log-line corrections (fess-7s5)
- `7sketches:5.2.1:ex5.9` logs "grep -i 'quantale' . — 0 hits". There is **one**
  hit, a comment at `Construction/Enriched.v:78`. The SAME chapter's
  `example5.39` log reports that identical search correctly ("1 hit, a comment"),
  and ex5.9's own verifier note discloses it — only the log line was never
  fixed. Immaterial to the ABSENT verdict.
- The bare-`|`-without-`-E` defect recurred twice (`ex5.69` part 2,
  `example5.73` line 2) after being documented. Per the standing instruction the
  auditor re-ran the SEMANTIC queries rather than counting: **both conclusions
  are true** and each is independently supported by an adjacent well-formed log
  line, so no classification is affected.

### An adjudication worth keeping: how ABSENT is drawn in this campaign
fess-7s5 tested the `ex5.9` ABSENT call EMPIRICALLY rather than by argument, and
the result is a usable rule: **35 of the 38 ABSENT records name a concrete
in-tree `file:line` near-miss in their negative log.** So ABSENT consistently
means "the item's own named object has no in-tree counterpart, though
ingredients exist and are cited" — it does NOT mean "nothing relevant exists".
`example5.3` is PARTIAL because the book's `FinSet` IS in-tree under that name
with that data and only extra structure is missing; `ex5.9`'s "posetal prop" has
no counterpart at all. The line is defensible and consistently drawn, and it
costs nothing: #831 already cites `Instance/Poset.v:120`, `Instance/Omega.v:72`
and `Instance/Two/Monoidal.v:105` in Current-state and as donors.

## Chapter 6 haul (2026-07-31)

| # | File:line | Defect | Disposition |
|---|-----------|--------|-------------|
| **S14** | Structure/Pullback.v:178-183 **AND :79-80** | Comment heading `pullback_unique` reads "Pullbacks are unique up to **a unique isomorphism respecting the projections**", but the lemma at `:182-183` states only `Pull f g P ≅ Pull f g Q`. **Neither the uniqueness of the isomorphism nor its compatibility with the projections is in the statement.** Verified verbatim. Note the same overstatement does NOT affect `Structure/Equalizer/Fork.v:101` or `Structure/Coequalizer.v:101`, whose headings correctly say only "unique up to isomorphism" — so this is a local slip, not a house style. **UNDER-SCOPED IN MY ORIGINAL RECORD (fess-7s6 L1): the same overstatement appears a second time at `Structure/Pullback.v:79-80`, and that site is arguably worse — it is a "proven below as `[pullback_unique]`" cross-reference inserted INSIDE a Wikipedia quotation, so the false claim reads as part of the cited source.** Both sites need the fix. | Recorded (MEDIUM, two sites). |
| — | Theory/Isomorphism.v:82-83 | **A3 RECURS** (Awodey ledger), and this chapter sharpens it: the essay says the uniqueness statement has "**Structure/Terminal.v the simplest instance**". Verified: `Structure/Terminal.v` is 129 lines, Requires only `Category.Lib` and `Category.Theory.Category`, and contains **zero** occurrences of `IsUniversalProperty`, `Isomorphism` or `≅`. A tree-wide search finds exactly three `IsUniversalProperty` instances (`Structure/UniversalProperty/Limit.v:141`, `.../Cartesian.v:60`, `Structure/UniversalProperty/Universal/Arrow.v:61` — my original record cited `Theory/Universal/Arrow.v:61` for the third, which is PROSE; corrected on fess-7s6 L2, substance unaffected) and **none is for Terminal or Initial**. | Duplicate of **A3**, now with the sharper counter-evidence. Directly relevant: this missing bridge is exactly what would formalize Seven Sketches Remark 6.9 / Exercise 6.10 (two initial objects are uniquely isomorphic). |

### A Phase-C record defect the verifier caught and corrected itself
`7sketches:6.2.1:ex6.6`'s negative log asserted the free category on the
one-vertex-one-loop graph "is not built as a category anywhere". **False:**
`Test/Issue138.v:87` defines `B138_loop` as exactly that quiver, `:90` checks
`FreeOnQuiver B138_loop : Category`, and `:95` proves
`obj[FreeOnQuiver B138_loop] = Datatypes.unit` by `eq_refl` — and
`Test/Issue138.v` is registered in `_CoqProject`. ABSENT still holds (none of
the exercise's four initial-object verdicts is stated), but the stated REASON
was wrong and the verifier rewrote the log line rather than leaving it.

### A calibration split the verifier flagged for downstream consumers
`example6.5` is PARTIAL and `ex6.6` ABSENT although both are "carrier in tree,
claim absent". The verifier endorsed the split — `example6.5` additionally has
one half of the book's argument as a NAMED lemma (`Instance/Parallel.v:61`
`ParHom_Y_X_absurd`, the emptiness of `hom ParY ParX`), whereas `ex6.6` has no
argument content at all — but flagged that two records share a shape and differ
in verdict. Consistent with the Ch5 rule (ABSENT = the item's own named object
has no counterpart, though ingredients exist and are cited).

## Ch6 ownership-coordination defects (fess-7s6) — filed issues, not library code

These are catalog defects: two issues owning one deliverable with no edge
between them. None loses an obligation; each risks the work being done twice.

| Where | Overlap | Status |
|---|---|---|
| **#865 ↔ #320** | **A TRUE DUPLICATE.** Both specify `IsIndexedCoproduct`, `icoprod`, `colimit_is_indexed_coproduct` and `HasIndexedCoproducts` over `Instance/Discrete.v`'s `DiscreteCat`. | **FIXED**: #865 scoped to cede clause 3, `Depends on: #320` added in body, trailer and native edge. |
| #869 | Work item 3 says the Frobenius generators are "already available … checking the nine equations there", but `Construction/Cospan/SCFA.v:1271` `cospan_scfa` already PROVES them, generic in `C`, and `Construction/Cospan/HypergraphInstance.v:703` packages it as `Cospan_Hypergraph`. Neither appears in its donors. **Phase-E regression, not a coverage error** — the coverage record DID cite `Cospan_Hypergraph`; the draft kept `Cospan_SymmetricMonoidal` and dropped the other half. | OPEN — donor list should be corrected. |
| #863 ↔ #417 | Both schedule `FinitelyCocomplete` over the same finiteness predicate with covariant accessors, both produced by this chapter. | OPEN |
| #869 ↔ #879 | Both own creating `CospanCat FinSet` in their DoD; #879's Dependencies reads `None.` and asserts "nothing in the tree does this today". | OPEN |
| #860 ↔ #357 | Same in-tree promise at `Structure/Discrete.v:23` scheduled under two different words — *codiscrete* vs *indiscrete*. | OPEN |
| #862 ↔ #863 ↔ #326 | All target the same TODO region of `Structure/Pullback.v`; #862 cites `:255-274` but the terminal/product block is `:254-265` and `:267-274` is the pullback-as-equalizer block #326 owns. | OPEN |

### ⚠ THE CONTRACT GAP BEHIND THE DUPLICATE — now closed in the drafter
#865 and #320 each justified novelty with a grep of the **TREE** returning 0
hits. **Both greps were correct.** Neither searched the **BACKLOG**, and the two
proposed different module paths (`Structure/Limit/Coproduct.v` vs
`Structure/Colimit/Shapes.v`) so the path-keyed collision check could not see it
either. The search protocol mandated a tree search and nothing mandated a
backlog search. `draftPrompt` now requires, for each principal SYMBOL NAME to be
introduced, a grep of `filed-issues.tsv` and the ledger — with the rule stated
plainly: **a tree grep proves the LIBRARY lacks it; only a backlog grep proves
the CATALOG lacks it.**

## Chapter 7 haul (2026-07-31) — both findings are RECURRENCES, re-verified

| Recurs | Where | Evidence this chapter |
|---|---|---|
| **A30** (Awodey ledger — the two-file self-contradiction on the fundamental theorem of topos theory) | `Structure/Topos.v:95-98` **↔** `Construction/Slice.v:113-115` | Confirmed verbatim on both sides. Topos.v, under the heading "**The library exercises both readings**", says "Construction/Slice.v **records** the fundamental theorem of topos theory — every slice of a topos is again a topos — and names `[ElementaryTopos]` as its target", listing it beside two claims that ARE in-tree. Slice.v says the opposite in its own words: "Relative to Structure/Topos.v's `[ElementaryTopos]`, it remains the headline theorem about this construction **not yet formalized here**." `rg ElementaryTopos` returns only Topos.v (3), Slice.v:114 (prose) and Instance/FinSet/Topos.v:38 — **there is no `ElementaryTopos (Slice C c)` instance.** Suggested fix from the verifier: reword to "names the theorem as future work", so the sentence cannot be read as an inventory of proven results. |
| **S2** (this ledger — the epi characterization) | `Instance/Sets.v:32-33` | Recurred AND sharpened; see the S2 row above, now corrected. |

### Ch7 inventory notes
- **The `7sketches` / `seven-sketches` footgun bit an agent, as predicted.** The two
  range reports disagreed on the top-level `book` value (A: `seven-sketches`,
  B: `7sketches`). The merge normalized to `seven-sketches` (the directory and
  `file_chapter.py` spelling) and — correctly — left the item-ID prefixes as
  `7sketches:` per the schema's explicit two-spelling rule. **No id was
  rewritten**, which is the right call; this is exactly why the footgun is
  documented in schemas.md rather than "fixed" in one place.
- Flag vocabulary for unnumbered items was inconsistent (A: bare `unnumbered`;
  B: `unnumbered-definition`/`-construction`/`-remark`). The merge recomputed
  from `number == null` and collapsed to one flag, 20 edits — and then
  **disclosed that non-derivable editorial flags remain asymmetric across the
  A/B boundary**, warning that their absence in PDF 233-254 is not evidence.
  That is the right honesty: normalize what is derivable, disclose what is not.
- Two SOURCE-TEXT issues carried forward, not resolved: an apparent authorial
  slip in Example 7.74 (PDF 263-264, quantifier order and the roles of S and T
  do not line up with formula (7.73)), and an apparent typo in Exercise 7.80
  (PDF 266). Both are book errata, not inventory defects.

## ⚠ AN UNVERIFIABLE PROBE CLAIM (fess-7s7 verification gap) — Ch7 `def7.35`

The Ch7 verifier's strongest library finding states: *"I proved this against the
built library (Rocq 9.1) in `scratchpad/7s-ch7/ProbeSiteVacuous.v`:
`coverage_condition_is_vacuous`, `Site_from_any_choice`, `Empty_Site` and
`every_presheaf_is_a_sheaf` all compile."* **No such file exists on disk.**
`doc/plan/books/probes/` contains only `S8-metacategory-vacuity.v`.

The auditor confirmed the MATHEMATICAL claim independently by reading
`Theory/Sheaf.v:170-178`: the witness `hs` is existentially quantified over an
arbitrary `covering_family v`, which by the definition at `:161` carries no
covering requirement at all, so `(0; nil)` discharges the condition via
`ForallT_nil` for **any** category. So the claim is TRUE. What is unverified is
that it COMPILES.

**Rule going forward (the S8 precedent shows the campaign already knows how):**
a record that claims a probe compiles must leave the probe on disk, and it
should be copied into `doc/plan/books/probes/` at fold time. A compile claim
whose artifact is gone is an assertion, not evidence — and this campaign's whole
premise is that the difference matters.
