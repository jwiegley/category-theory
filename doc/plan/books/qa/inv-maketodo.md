# INV — Decision 5.6 re-verification: the `make todo` DoD-box sweep over #566–#584

**Auditor:** read-only QA subagent. No GitHub mutation, no repo file touched except this one.
**Date of audit:** 2026-08-01. **Tree:** `/Users/johnw/src/category-theory/master`, branch `johnw/rocq-dev-ci`, HEAD `8e199145`.

## Verdict up front

| Question | Answer |
|---|---|
| Is the justification true (`make todo` prints pre-existing hits, so "clean" is unachievable)? | **Yes.** 89 hits across 33 files on a pristine tree. |
| Were all 19 issues #566–#584 actually edited, and do they read correctly now? | **Yes, all 19.** |
| Did the sweep over-reach into #585–#600? | **No.** Those 16 never carried the defective phrasing; their `make todo` lines are byte-identical across every revision. |
| Did the sweep under-reach? | **YES — six issues were missed: #560, #561, #562, #563, #564, #565.** They still carry the identical defective box. |

The sweep is correct in what it did and incomplete in its extent. Nothing needs reverting;
six issues need the same fix.

---

## 1. `make todo` on a pristine tree

`make todo` was run in `/Users/johnw/src/category-theory/master` with no arguments (no
`nix develop` needed — the target is pure `find`/`egrep`, no Coq toolchain involved).

The target itself (`Makefile:1-7,17-18`) is, verbatim:

```make
MISSING	 =									\
	find . \( \( -name foo \) -prune \)					\
	    -o \( -name '*.v'							\
	       \) -print						|	\
		xargs egrep -i -Hn '(Fail|abort|admit|undefined|jww)'	|	\
		      egrep -v 'Definition undefined'			|	\
		      egrep -v '(old|new|research)/'

todo:
	-@$(MISSING) || exit 0
```

Two facts follow directly from that text and matter for the DoD wording:

1. The recipe is prefixed `-@` **and** ends `|| exit 0`, so `make todo` **can never fail**.
   Measured: `exit=0`. A checkbox reading "`make todo` clean" therefore cannot be
   discharged by an exit status; it can only mean "prints nothing".
2. The pattern is `-i` case-insensitive over `(Fail|abort|admit|undefined|jww)`, so it
   matches ordinary English prose in comments — "fails", "failure", "undefined",
   "Abort." — not just genuine TODO markers.

### Measured result

```
$ make todo | wc -l
89
$ make todo ; echo $?
0
```

**89 pre-existing hits across 33 files.** The count claimed in the Decision 5.6
justification is exact.

Distribution by file:

```
     10 ./Test/ProbeFunnyPoly.v
      7 ./Theory/Kan/Extension.v
      6 ./Test/Issue213.v
      6 ./Lib/Tactics.v
      6 ./Instance/Sets/Par.v
      5 ./Theory/Metacategory.v
      4 ./Test/Issue138.v
      4 ./Solver/Reify.v
      3 ./Theory/Metacategory/ArrowsOnly.v
      3 ./Theory/Coq/Maybe.v
      3 ./Solver/Denote.v
      3 ./Monad/Transformer.v
      2 ./Tools/Abstraction.v
      2 ./Test/HypergraphPROPResolution.v
      2 ./Structure/Pullback.v
      2 ./Structure/Discrete.v
      2 ./Structure/Closed.v
      2 ./Instance/StrictCat/Premonoid.v
      2 ./Instance/Coq/ParE.v
      2 ./Instance/Coq/Par.v
      1 ./Theory/Metacategory/DecideExample.v
      1 ./Theory/Isomorphism.v
      1 ./Theory/Coq/List.v
      1 ./Test/Poset.v
      1 ./Test/Issue139.v
      1 ./Test/FullIssue118.v
      1 ./Structure/Monoidal/Strict/Tactics.v
      1 ./Lib/Tactics2.v
      1 ./Lib/MapDecide.v
      1 ./Instance/Sets.v
      1 ./Instance/Lambda/Eval.v
      1 ./Instance/Coq/Monad.v
      1 ./Instance/Comp.v
```

Full output of `make todo`, verbatim (89 lines):

```
./Tools/Abstraction.v:215:Abort.
./Tools/Abstraction.v:237:Abort.
./Test/ProbeFunnyPoly.v:18:      - supplying a unitor is what fails.  The compiled [Funny_unit_left] of
./Test/ProbeFunnyPoly.v:26:        at the [unit_left] field (first [Fail] below);
./Test/ProbeFunnyPoly.v:29:        [Funny_Monoidal@{i}] to [@Monoidal StrictCat@{i v j v v}] fails with
./Test/ProbeFunnyPoly.v:31:        (second [Fail] below).
./Test/ProbeFunnyPoly.v:35:    the [Fail] commands here stop failing and this file breaks the build,
./Test/ProbeFunnyPoly.v:59:    tensor, so the failures below are not caused by [StrictCat], [_1] or
./Test/ProbeFunnyPoly.v:69:Fail Check (@Build_Monoidal StrictCat@{i v j v v} _1 FunnyTensor
./Test/ProbeFunnyPoly.v:77:Fail Check (Funny_Monoidal@{i} : @Monoidal StrictCat@{i v j v v}).
./Test/ProbeFunnyPoly.v:80:    own universe level.  This pins the two [Fail]s above to the specific
./Test/ProbeFunnyPoly.v:83:    transport up to level [v].  Without this control a [Fail] would pass on
./Test/Poset.v:42:    reference fails outright. *)
./Test/Issue139.v:49:   product UMP (exl_fork / exr_fork), so they fail for any non-product tensor --
./Test/HypergraphPROPResolution.v:86:    special law was dropped or mistyped would fail this test, not only one
./Test/HypergraphPROPResolution.v:122:    still fails to type-check inside a [HypergraphPROP] context (verified
./Test/FullIssue118.v:31:    definition and fails against the old one.  Finally we reference
./Test/Issue138.v:70:   Cat ⟶ QuiverCategory").  These [Fail] commands lock in that [Forgetful] is NOT
./Test/Issue138.v:75:Fail Check (Forgetful : Cat ⟶ QuiverCategory).
./Test/Issue138.v:76:Fail Definition A138_forgetful_over_Cat : Cat ⟶ QuiverCategory := Forgetful.
./Test/Issue138.v:106:   the weak setoid fails HERE, in the test body — not merely transitively
./Test/Issue213.v:16:   failing in Instance/Adjoints.v with
./Test/Issue213.v:84:(* Confirmation of the reported failure mode.  Denied the wide search, the old
./Test/Issue213.v:94:  assert_fails
./Test/Issue213.v:98:  (* The positive half, so this stays a live [Qed] rather than an aborted
./Test/Issue213.v:115:  assert_fails (solve [ repeat intro; simpl; try cat; intuition ]).
./Test/Issue213.v:142:   fails this example. *)
./Theory/Metacategory.v:184:  (* jww (TODO): The use of [->] below should be [/\]. The current form is
./Theory/Metacategory.v:430:Abort.
./Theory/Metacategory.v:436:Abort.
./Theory/Metacategory.v:442:Abort.
./Theory/Metacategory.v:444:(* jww (2017-06-10): This needs automation. A computational tactic that
./Theory/Isomorphism.v:261:   (The converse fails in general; see [Monic_Retraction_Iso] below for the
./Theory/Kan/Extension.v:141:  (* jww (2017-06-09): Rename this to ran_functor, RightKan to Ran, and then a
./Theory/Kan/Extension.v:170:   adjoint functor that an adjoint functor can fail to exist completely, but
./Theory/Kan/Extension.v:380:   proof sketch.  jww: complete the remaining isomorphism/identity obligations.
./Theory/Kan/Extension.v:433:      admit.
./Theory/Kan/Extension.v:435:      admit.
./Theory/Kan/Extension.v:437:    admit.
./Theory/Kan/Extension.v:438:Abort.
./Theory/Coq/List.v:61:   [pure id <*> v = v]; with [pure x = [x]] the identity law fails because
./Theory/Coq/Maybe.v:19:   way to track failure without exceptions or null references.  As a monad,
./Theory/Coq/Maybe.v:20:   failure short-circuits: [Nothing >>= f = Nothing] and [Just x >>= f = f x].
./Theory/Coq/Maybe.v:35:Notation Nothing := None.     (* [inr ()] : the absent/failure case *)
./Theory/Metacategory/DecideExample.v:36:   decider surfaces as a build failure here rather than silently downstream. *)
./Theory/Metacategory/ArrowsOnly.v:77:     jww (TODO): The two [->] below should be [/\]. The current form is
./Theory/Metacategory/ArrowsOnly.v:572:Abort.
./Theory/Metacategory/ArrowsOnly.v:585:Abort.
./Solver/Reify.v:123:  Fail (
./Solver/Reify.v:179:  Fail (
./Solver/Reify.v:207:  Fail (
./Solver/Reify.v:584:    fail "Solver only works with a single category"
./Solver/Denote.v:45:    path, since a missing [tys] entry forces [ith_exact] to fail. *)
./Solver/Denote.v:61:    typed; if either subterm fails to denote the whole [Comp] fails. *)
./Solver/Denote.v:102:    ([f ≈ g], the homset setoid equivalence); if either term fails to denote
./Instance/Sets.v:476:Abort.
./Instance/Comp.v:124:      (* jww (2020-02-23): How to remove this axiom?  It is hard to avoid
./Instance/StrictCat/Premonoid.v:73:    the unitor field (checked-in probe: Test/ProbeFunnyPoly.v, whose [Fail]
./Instance/StrictCat/Premonoid.v:74:    guards reproduce the failure).  Everything below therefore holds for
./Instance/Sets/Par.v:22:       arrows: partial setoid maps  f : A → option B   (None = undefined)
./Instance/Sets/Par.v:25:                  None => None | Some b => f b end  (undefined if either is) *)
./Instance/Sets/Par.v:238:Abort.
./Instance/Sets/Par.v:263:    admit.
./Instance/Sets/Par.v:265:    + admit.
./Instance/Sets/Par.v:267:Abort.
./Instance/Lambda/Eval.v:148:   the file header for the FLAG on the product cases, which fail to reduce pair
./Instance/Coq/ParE.v:29:   information rather than mere undefinedness, and several errors arising "in
./Instance/Coq/ParE.v:121:   fail; [exl]/[exr] project, falling back to [mempty] when their component is
./Instance/Coq/Monad.v:81:(* run x only when the guard fails (the dual of [when]) *)
./Instance/Coq/Par.v:27:   with [None] standing for "undefined". Identity is [Some] (the monad's
./Instance/Coq/Par.v:30:   propagating undefinedness. Morphisms are compared pointwise, [∀ x, f x =
./Lib/MapDecide.v:44:   [partial P], written [[P]], is the type of a verified-but-possibly-failing
./Lib/Tactics.v:27:   axiom; each either makes progress and closes goals or fails. *)
./Lib/Tactics.v:48:    Notation internal_eq_rew_r_dep := ltac:(fail "should not happen") (only parsing).
./Lib/Tactics.v:49:    Notation internal_eq_sym_involutive := ltac:(fail "should not happen") (only parsing).
./Lib/Tactics.v:50:    Notation internal_eq_sym_internal := ltac:(fail "should not happen") (only parsing).
./Lib/Tactics.v:185:   bullet script failed several lines later with an unrelated-looking error
./Lib/Tactics.v:210:   [simplify]+[cat]; if that [solve] fails, leave a [simpl]-reduced goal for the
./Lib/Tactics2.v:20:   ones) closes the goal, or fails; none introduces an axiom. *)
./Monad/Transformer.v:183:   fixed monad K. K M is a monad whenever K is, but the construction fails to
./Monad/Transformer.v:186:   the [Fail]ing definition below witnesses. *)
./Monad/Transformer.v:207:Fail Definition ConstT_MonadTransformer {C : Category} (K M : C ⟶ C)
./Structure/Closed.v:27:   below (see the jww TODO); only the two helper functors [Curry] and [Flip]
./Structure/Closed.v:154:(* jww (2018-10-05): TODO
./Structure/Pullback.v:254:(* jww (2017-06-01): TODO *)
./Structure/Pullback.v:267:(* jww (2017-06-02): *)
./Structure/Monoidal/Strict/Tactics.v:32:    fail if none applies. *)
./Structure/Discrete.v:21:   caveat recorded in the [jww] note below; the equivalence-respecting variant
./Structure/Discrete.v:29:  (* jww (2017-06-02): Equality is too much here. *)
```

Spot-checking that these are genuinely pre-existing and mostly not actionable:
`./Test/ProbeFunnyPoly.v` contributes 10 hits, of which several are *deliberate*
`Fail` commands that the file exists to assert (`Fail Check (Funny_Monoidal@{i} :
@Monoidal StrictCat@{i v j v v}).`); `./Test/Issue213.v:94` is `assert_fails`, a
regression guard; `./Lib/Tactics.v:48-50` are
`Notation internal_eq_rew_r_dep := ltac:(fail "should not happen") (only parsing).`
These can never be driven to zero without deleting working code. The justification for
Decision 5.6 is sound.

---

## 2. Method

For every issue in `#565 … #601` I pulled the full `userContentEdits` revision history via
GraphQL (each node's `diff` field returns the body **as of** that edit), and separately
pulled the current body. I then extracted every line containing `make todo` at every
revision. This distinguishes "edited to the new wording" from "never had the old wording".

I also enumerated **all 845 issues in the repository** (GraphQL, `states:[OPEN,CLOSED]`,
`--paginate`) and grouped every `make todo` line by exact string, to bound over- and
under-reach repo-wide rather than trusting the stated range.

---

## 3. The 19 audited issues, #566–#584

Old wording (present in the revision immediately preceding the sweep, in all 19):

> `- [ ] Full \`make\` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; \`make todo\` clean.`

New wording (present in the current body, in all 19):

> `- [ ] Full \`make\` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; \`make todo\` adds no new hits.`

| Issue | Title | Applied? | Sweep edit | Phrasing correct now? |
|---|---|---|---|---|
| #566 | MacLane IX.2: Coproducts commute with pullbacks, and pseudo-filtered colimits commute with pullbacks, in Set | **yes** | 2026-08-01T12:38:22Z | **yes** |
| #567 | MacLane IX.3: Final (cofinal) functors and final subcategories | **yes** | 2026-08-01T12:38:24Z | **yes** |
| #568 | MacLane IX.3: Final functors preserve colimits (and initial functors, limits) | **yes** | 2026-08-01T12:38:26Z | **yes** |
| #569 | MacLane IX.3: Properties of final functors and colimits of representables | **yes** | 2026-08-01T12:38:27Z | **yes** |
| #570 | MacLane IX.4: Canonical wedges — evaluation and the identity family | **yes** | 2026-08-01T12:38:29Z | **yes** |
| #571 | MacLane IX.4: The unit and counit of a parametrized adjunction are (di)natural in the parameter | **yes** | 2026-08-01T12:38:30Z | **yes** |
| #572 | MacLane IX.4: Multi-variable (di)natural transformations and dummy variables | **yes** | 2026-08-01T12:38:32Z | **yes** |
| #573 | MacLane IX.4: Composition calculus for dinatural transformations | **yes** | 2026-08-01T12:38:33Z | **yes** |
| #574 | MacLane IX.4: Euclidean self-duality as a dinatural transformation | **yes** | 2026-08-01T12:38:35Z | **yes** |
| #575 | MacLane IX.5: The end–limit correspondence (subdivision and twisted-arrow categories) | **yes** | 2026-08-01T12:38:36Z | **yes** |
| #576 | MacLane IX.5: Existence of ends from completeness and from products and equalizers | **yes** | 2026-08-01T12:38:38Z | **yes** |
| #577 | MacLane IX.5: The set of natural transformations is an end of the hom-functor | **yes** | 2026-08-01T12:38:40Z | **yes** |
| #578 | MacLane IX.5: Preservation and creation of ends; hom-functors are continuous for ends | **yes** | 2026-08-01T12:38:41Z | **yes** |
| #579 | MacLane IX.6: The tensor product of functors as a coend | **yes** | 2026-08-01T12:38:43Z | **yes** |
| #580 | MacLane IX.6: Module tensor products and free modules as coends | **yes** | 2026-08-01T12:38:45Z | **yes** |
| #581 | MacLane IX.7: Functoriality of ends in the integrand | **yes** | 2026-08-01T12:38:46Z | **yes** |
| #582 | MacLane IX.7: The Parameter Theorem for ends and coends | **yes** | 2026-08-01T12:38:48Z | **yes** |
| #583 | MacLane IX.7: A limit in a functor category that is not pointwise (Dubuc) | **yes** | 2026-08-01T12:38:49Z | **yes** |
| #584 | MacLane IX.8: The Fubini theorem and interchange of iterated ends | **yes** | 2026-08-01T12:38:51Z | **yes** |

19/19 applied. 19/19 read correctly. **Nothing here should be reverted.**

Verbatim current Definition of Done for #566, as a representative:

```
## Definition of Done
- [ ] Coproducts-commute-with-pullback in `Set` proved; pseudo-filtered-colimits-commute-with-pullbacks in `Set` proved.
- [ ] Isos via `≅`/two-sided inverse in setoid `≈`; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for both principal results.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` adds no new hits.
```

Note on #566 and #579: each shows a *second* later edit (`12:51:09Z` / `12:51:10Z`). Those
are unrelated whitespace/section-separator fixes to an appended "### Correction (QA audit)"
block; the `make todo` line is identical before and after. Neither disturbs this decision.

---

## 4. The stated complement, #585–#600 — no over-reach

All 16 carry a **different, already-correct** box:

> `- [ ] \`make todo\` adds no new hits`

Crucially, that line is **byte-identical in every revision of every one of those 16 issues,
going back to their creation on 2026-07-23**. They never carried "clean"; the sweep did not
touch them on this dimension.

| Issue | Ever carried "`make todo` clean"? | Current phrasing | Touched by the sweep? |
|---|---|---|---|
| #585 | no (all revisions identical) | `` - [ ] `make todo` adds no new hits `` | no |
| #586 | no (all revisions identical) | `` - [ ] `make todo` adds no new hits `` | no |
| #587 | no (all revisions identical) | `` - [ ] `make todo` adds no new hits `` | no |
| #588 | no (all revisions identical) | `` - [ ] `make todo` adds no new hits `` | no |
| #589 | no (all revisions identical) | `` - [ ] `make todo` adds no new hits `` | no |
| #590 | no (all revisions identical) | `` - [ ] `make todo` adds no new hits `` | no |
| #591 | no (all revisions identical) | `` - [ ] `make todo` adds no new hits `` | no |
| #592 | no (all revisions identical) | `` - [ ] `make todo` adds no new hits `` | no |
| #593 | no (all revisions identical) | `` - [ ] `make todo` adds no new hits `` | no |
| #594 | no (all revisions identical) | `` - [ ] `make todo` adds no new hits `` | no |
| #595 | no (all revisions identical) | `` - [ ] `make todo` adds no new hits `` | no |
| #596 | no (all revisions identical) | `` - [ ] `make todo` adds no new hits `` | no |
| #597 | no (all revisions identical) | `` - [ ] `make todo` adds no new hits `` | no |
| #598 | no (all revisions identical) | `` - [ ] `make todo` adds no new hits `` | no |
| #599 | no (all revisions identical) | `` - [ ] `make todo` adds no new hits `` | no |
| #600 | no (all revisions identical) | `` - [ ] `make todo` adds no new hits `` | no |

Ten of these issues *were* edited at 12:38:53Z–12:39:04Z, i.e. seconds after the #566–#584
sweep, which superficially looks like the sweep spilling over. It did not. Diffing #585's
`2026-07-29T23:23:14Z → 2026-08-01T12:38:53Z` revision pair shows the change was a
dependency/home-file correction, untouched `make todo` line:

```
@@ -42 +42,3 @@
-None in-catalog. Related in-tree: Freyd's adjoint functor theorem (issue #436) is the stronger-hypothesis route already filed; …
+Depends on: #334
+- Related (NOT blocking): #436 (Freyd's adjoint functor theorem — the stronger-hypothesis route, already filed). …
```

That is a different QA decision's work, correctly scoped. **No over-reach.**

#588 has zero recorded edits (`userContentEdits.nodes == []`) and its original body already
reads `- [ ] \`make todo\` adds no new hits` — consistent.

---

## 5. Repo-wide sweep: the audit MISSED six issues

Grouping the `make todo` line of all 845 issues by exact string:

| count | exact line | issues |
|---|---|---|
| 19 | `` - [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` adds no new hits. `` | 566–584 (the swept set) |
| **6** | ``- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.`` | **560–565 — STILL DEFECTIVE** |
| 378 | `` - [ ] `make todo` adds no new hits `` | many |
| 213 | `` - [ ] `make todo` adds no new hits. `` | many |
| 110 | `` - [ ] `make todo` reports no new hits. `` | many |
| 86 | `` - [ ] `make todo` reports no new hits `` | many |
| 19 | ``- `nix build .#category-theory_9_1 .#category-theory_8_20` pass; `make todo` unchanged.`` | 992–1010 |

The independent GitHub search agrees exactly:

```
$ gh search issues '"make todo" clean' --repo jwiegley/category-theory --limit 100
[560,561,562,563,564,565]
```

**Six issues outside #566–#584 carry the byte-identical defective box and were not fixed.**
Their revision histories show no edit after 2026-07-23; the sweep simply started one issue
too late. They are the immediately preceding block of the same Mac Lane Chapter IX
authoring run (created 09:27–09:30 on 2026-07-23, same template).

| Issue | State | Title | Current phrasing | Needs the same fix? |
|---|---|---|---|---|
| #560 | OPEN | MacLane IX.1: Small coproducts from finite coproducts and directed colimits | `` …`make todo` clean. `` | **YES** |
| #561 | OPEN | MacLane IX.1: Algebraic forgetful functors create filtered colimits | `` …`make todo` clean. `` | **YES** |
| #562 | OPEN | MacLane IX.1: Grp is cocomplete | `` …`make todo` clean. `` | **YES** |
| #563 | OPEN | MacLane IX.2: Finite limits commute with filtered colimits in Set | `` …`make todo` clean. `` | **YES** |
| #564 | OPEN | MacLane IX.2: Interchange of iterated limits and of iterated colimits | `` …`make todo` clean. `` | **YES** |
| #565 | OPEN | MacLane IX.2: Pseudo-filtered categories | `` …`make todo` clean. `` | **YES** |

Verbatim current Definition of Done for #560, showing the box is character-for-character the
one the sweep replaced elsewhere:

```
## Definition of Done
- [ ] The `J₊` poset, the finite-coproduct diagram, and the theorem proved.
- [ ] Setoid `≈` throughout; never `=` on morphisms.
- [ ] No `Admitted`/`admit`/`Axiom`; `Print Assumptions` closed for the principal theorem.
- [ ] File registered in `_CoqProject`.
- [ ] Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.
```

Note #565 is a stated dependency of #566 ("Depends on: #565 (`maclane:IX.2:ex2`)"), so the
missed block is not a distant tail — it is the direct upstream of the swept block.

---

## 6. Recommended coordinator action

1. **Revert nothing.** All 19 edits to #566–#584 are correct and correctly scoped.
2. **Extend the sweep to #560–#565**, applying the identical substitution:
   - from: ``Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` clean.``
   - to:   ``Full `make` green on Rocq 9.1; Coq 8.19/8.20 nix builds pass; `make todo` adds no new hits.``
   That brings the repo to zero occurrences of the unachievable wording.
3. Optional, cosmetic only, not a defect: the repo now carries five near-synonymous correct
   phrasings ("adds no new hits", "adds no new hits.", "reports no new hits",
   "reports no new hits.", "unchanged"). All are delta-based and achievable; normalising
   them is a style choice, not a correctness fix, and would churn ~800 issue bodies.

## 7. Confidence and evidence limits

- The 89-hit count is a direct measurement on HEAD `8e199145` with a clean working tree
  (only untracked `.claude/`, `doc/plan/`, `doc/wiggum-handoff.md`), reproducible.
- Applied/not-applied is established from GitHub's own `userContentEdits` revision history,
  not inferred from timestamps, so "the edit was applied" is verified rather than assumed.
- Repo-wide under-reach is established two independent ways (full 845-issue body
  enumeration, and GitHub's issue search) which agree exactly on {560,…,565}.
- **One thing I could not establish:** whether #560–#565 were *deliberately* excluded from
  Decision 5.6's scope (e.g. because the audited set was defined as #566+ for an unrelated
  reason) or were an oversight. I have no access to the decision's scoping rationale. What
  is certain is that they carry the identical unachievable box and the same argument applies
  to them verbatim.
