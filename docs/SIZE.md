# Size and foundations

How this library handles the questions Mac Lane settles in *Categories for the
Working Mathematician* §I.6 — universes, small sets, classes, large categories —
and why several of his definitions have no counterpart here.

The books are cited **by location only**. Their printed text was not consulted
in writing this document; the locations record where each item is stated, and
every claim below about the *library* is checked against the source, with the
file and line given.

---

## The short answer

Mac Lane fixes ZFC plus one Grothendieck universe `U` and calls a set, a
function, or a category **small** when it lies in `U`. This library declares no
universe, no membership relation, and no size axiom. The work `U` does is done
instead by **universe polymorphism**: `Class Category@{o h p | h <= p}`
(`Theory/Category.v:111`) gives every category its own three levels —

| level | what lives there | field |
|---|---|---|
| `o` | the objects | `obj : Type@{o}` |
| `h` | each hom-set | `hom : obj → obj → Type@{h}` |
| `p` | the hom-setoid's proofs | `homset : ∀ X Y, Setoid@{h p} (X ~> Y)` |

— and the constraint solver enforces stratification at every use site. The
audited consequence is that the core theory needs no size axiom at all
(`docs/AXIOMS.md`).

Since this issue's work, the *vocabulary* also exists: `Theory/Size.v` declares
`Small` and `LocallySmall`, which before had no declaration anywhere in the tree
(`Theory/Lawvere/Sets.v:44` records the gap in passing — "the library has no
smallness machinery").

---

## Mac Lane §I.6, item by item

### def1 — a universe `U`

**No counterpart, deliberately.** There is no `Universe` object with closure
conditions and no membership. Coq's own cumulative hierarchy `Type@{i}` plays
the role, but it is a feature of the metatheory rather than an object of the
theory: one cannot quantify over levels inside Coq, so `U` cannot be a variable.

The practical difference: Mac Lane's `U` is *one* fixed universe, and enlarging
it is a deliberate act. Here every construction is polymorphic, so it exists
simultaneously at **every** level, and the level is chosen per use site by
inference.

### def2 — small sets and small functions

Partially, and less than the summary row might suggest. A *small set* becomes
"a type at a designated level", which is expressible directly as `Type@{u}` —
but **no small-set predicate is declared**. `Small` is a predicate on
*categories* only; it uses the level-relative idea rather than supplying it.
There is likewise no notion of small *function*: a function between types at
level `u` automatically lives at `u`.

### def4 — small categories

**`Small` (`Theory/Size.v`).** Following Awodey Definition 1.11 and Riehl
Definition 1.1.6, a category is small when its objects and its arrows are both
matched by copies at strictly lower levels:

```coq
Class Small@{o h p uo uh up | h <= p, uh <= up, uo < o, uh < h} (C : Category@{o h p})
```

All of the content is in `uo < o` and `uh < h`. Without them one could discharge
`Small C` for every `C` by handing back `obj[C]` and `hom` themselves. That is
not an argument by assertion: `Test/Size.v`'s `A253_trivial_small` writes exactly
that discharge and it is **rejected**.

Objects are matched up to **`ObjEq`**, a level-polymorphic identity type
declared in `Theory/Size.v` — *not* stdlib `=`. Homs are matched up to a
**setoid isomorphism** (both directions respect `≈`).

Neither choice is stylistic. Morphisms cannot use `=` because CLAUDE.md forbids
it on them. Objects cannot use it either, and for a separate and more brutal
reason that applies to **both** halves: stdlib `eq` is pinned to a global
universe on Coq 8.19/8.20, so mentioning it inside a definition carrying an
explicit universe-constraint clause yields `Universe constraints are not implied
by the ones declared: o <= eq.u0`, which a binder has no syntax to discharge.
Objects carry no setoid in this library, so with `=` unavailable they need
*some* identity type, and a level-polymorphic predicate needs a
level-polymorphic one — hence `ObjEq`, following the `poly_unit@{u}` idiom at
`Lib/Setoid.v:56`.

### def5 — classes

**No counterpart.** A class is a subset of `U`, which needs membership. Nothing
here corresponds; a "class-sized" collection is simply a type at a higher level.
There is likewise no *proper class*: the distinction it draws — too big to be an
element — is what a universe inconsistency expresses instead.

### def6 — large categories

**No counterpart as a predicate**, and this is a real asymmetry worth naming.
`Small` is a predicate one can assume or conclude. "Large" is not its negation
in any usable sense: refuting `Small C` for a given `C` would require showing no
resizing exists at *any* lower levels, which is a statement about the metatheory,
not a Coq proposition. So the tree can say "this category is small" and cannot
say "this one is not".

### remark1 — `Set` is not an object of itself

This is where the issue that requested this document is **doubly mistaken**, and
the correction is the most interesting formal content here.

The issue asks for `Fail Check` witnesses that "`Sets` as an object of itself,
`Cat` as an object of itself" are universe inconsistencies.

**First: `Check (Cat : obj[Cat])` succeeds.** It is not a self-membership
witness at all. `Cat` is universe-polymorphic, so the elaborator instantiates the
two occurrences at *different* levels; what is actually checked is
`Cat@{i…} : obj[Cat@{j…}]` with the second strictly above the first. Confirmed by
`Set Printing Universes`, which shows two distinct instances, and by
`About Cat`: `Cat@{u u0 u1 u2 u3} : Category@{u u0 u0}` with `u2 < u`, `u3 < u`.
So `Fail Check (Cat : obj[Cat])` would not even compile — the command does not
fail. **This is a theorem of the design, not a failure**, and it is precisely
Riehl's "`Cat` is an object of `CAT`" (see §1.3 below).

The demonstration has to **pin one instance on both sides**:

```coq
Fail Definition B253_cat_self@{a b c d e} : obj[Cat@{a b c d e}] := Cat@{a b c d e}.
```

That is rejected, and rejected on universes alone — the ascription is
type-correct in shape, since `obj[Cat]` *is* `Category` and `Cat` *is* a
`Category`, so only the constraint solver can refuse it. This is the genuine
formal counterpart of Mac Lane's remark, and what `Instance/Cat.v:108-114` means
by "a universe inconsistency caught by the elaborator rather than a paradox to be
excluded by axiom".

**Second: for `Sets` it is not a universe question at all.** `obj[Sets]` is
`SetoidObject` — a carrier paired with a setoid — while `Sets` is a `Category`. A
category is not a setoid, so `Sets : obj[Sets]` is an **ordinary type error**,
and would remain one at any levels whatsoever. Pinning instances changes nothing.

### remark2 — which axioms are in force

`docs/AXIOMS.md` is the audit. The headline: **zero axioms** in every
proof-carrying constant of `Theory/` (excluding `Theory/Coq/`), `Structure/`, and
`Construction/`; the concrete instance layers (`Instance/`, `Theory/Coq/`) use
stdlib axioms, enumerated there. In particular no universe axiom is declared
anywhere — the stratification is structural.

### remark3 — set-free alternatives

Both of Mac Lane's pointers are **actually formalized**, which makes this the one
item that is more than mapped:

- *Category axioms on undefined terms* — `Theory/Metacategory.v`, the arrows-only
  axiomatization. Its header (`:116-118`) makes the same point this document
  does: "the size distinctions it once marked are, in this library, carried
  instead by universe polymorphism."
- *Elementary topos axioms for `Set`* — `Structure/Topos.v:112`'s
  `ElementaryTopos`, inhabited by `FinSet_Topos`.

---

## Awodey

### §1.8 Definition 1.11 — small

Matches `Small` above: objects `C₀` and arrows `C₁` both sets. The **arrows**
half is why `Small` needs two constraints and not just the hom one — the total
arrow collection bundles its endpoints, so its level is at least that of the
objects. `Theory/Size.v`'s `TotalMor` is that collection.

### §1.8 Definition 1.12 — locally small

`LocallySmall` (`Theory/Size.v`). The situation here is genuinely **two-sided**,
and both sides are recorded:

- What the library *provides* is **stronger** than the book's convention.
  `Class Category`'s `homset` field (`Theory/Category.v:116`) gives every
  category hom-setoids at a fixed level, so local smallness holds by
  construction and a non-locally-small category is not expressible. This is
  `locally_small_ambient`, stated as a **lemma** rather than as prose.
- What the library *lacked* is the predicate needed to state the distinction at
  all. That is what `LocallySmall` supplies.

Because of the first point, `LocallySmall` is declared with a **non-strict**
`uh <= h`, so the ambient instance exists; instantiating it at a strictly smaller
`uh` is the reading with content. `Small` by contrast is strict throughout.
Neither choice is an oversight.

### §8.3 Remark 8.4 — the Yoneda size trichotomy

Awodey's three cases, against the tree:

| case | Awodey | here |
|---|---|---|
| (i) `C` small ⇒ `Sets^(C^op)` locally small | needs smallness | expressible now; *not proved* — see below |
| (ii) `Hom(y C, P) ≅ P C` is a set even when `Sets^(C^op)` is not locally small | the interesting case | **presupposed, not concluded** |
| (iii) `C` not locally small ⇒ `y` not definable | — | **cannot arise**: local smallness is built into `Class Category` |

Case (ii) deserves the emphasis. The in-tree `Yoneda_Lemma` does not *conclude*
that `Hom(y C, P)` is a set — it **presupposes** it, and unavoidably so: both
sides of its `≅` must already be `Sets`-objects for the statement to typecheck,
via the coercion at `Functor/Hom.v:78`. Relatedly `Functor/Hom.v:49` defines
`Hom (C : Category) : C^op ∏ C ⟶ Sets` for an *arbitrary* `C` with no side
condition, so hom-collections always land in `Sets` at the ambient level.

**Neither case is stated in Coq.** This section is documentation only, and that
is a checkbox of #253 left undone rather than delivered:

- Case (i) is now *statable* with the vocabulary in place, but is **not proved**
  — it needs the level of a natural-transformation type to be computed from the
  level of `C`'s objects, which is beyond this issue's scope.
- Case (ii) is **described, not formalized**. The description is accurate —
  `Functor/Hom/Yoneda.v` states `Yoneda_Lemma : ∀ A : C, Presheaves [Hom ─,A] F ≅ F A`,
  and both sides are `Sets`-objects by construction via the coercion at
  `Functor/Hom.v:78` — but recording that the in-tree lemma presupposes the
  content is not the same as concluding it.

---

## Riehl

### §1.1 Remark 1.1.5 — a deliberate divergence

Riehl adopts a working convention of a countable tower of inaccessibles, so each
stage is a Grothendieck universe that can be enlarged as needed, **rather than**
parametrizing definitions by universe levels.

That is the *opposite* methodological choice from this library's, and it is worth
naming as a divergence rather than an omission. Riehl fixes a stage and enlarges
it when forced; here nothing is fixed — every definition is polymorphic and
level-agnostic, and the solver picks levels per use site. Neither is more
correct; the trade is that Riehl's convention keeps statements readable while
this library's keeps them axiom-free.

Checked: `rg -i 'Grothendieck universe|inaccessible|V_kappa|proper class|Russell'`
returns only prose hits (`Instance/Cat.v:109,111`) — **no universe axiom is
declared anywhere**; the only `Parameter`s in the tree are the three documented
ZX `Phase` ones at `Instance/ZX.v:189-191`. `Instance/Cat.v:108-114` already
explains that self-membership is blocked by polymorphism rather than by a size
axiom.

### §1.1 Definition 1.1.6 — small, and the arrows-with-`dom`-and-`cod` packaging

The smallness half is `Small`. The *packaging* half — a set of objects, a set of
morphisms, and `dom`, `cod`, `id` with `dom` and `cod` retracting `id` — is
`ArrowQuiver` and `ArrowQuiverOfCat` in `Theory/Size.v`.

Both presentations are given, because the difference is exactly **where the
retraction laws live**:

- The tree's `Quiver` (`Construction/Free/Quiver.v:54`) is the **indexed**
  presentation, `edges : nodes → nodes → Type`, in which `dom` and `cod` are
  carried by the indexing. It has no identity selection at all, so it supplies
  neither half of Riehl's retraction, and no reflexive quiver existed in the
  tree before this issue.
- `ArrowQuiver` is the **unindexed** presentation Riehl actually states. There
  the retractions are genuine equations a candidate must satisfy — and here they
  hold by `obj_refl` (the `ObjEq` constructor), because the identity arrow stores its endpoints.

That is a case where the library's formulation makes a book axiom *disappear*
rather than proving it, which is worth having on record.

### §1.1 Definition 1.1.7 — locally small

See Awodey 1.12 above. Riehl's use of it — "none of the categories of Example
1.1.3 is small, but each is locally small" — has an asymmetric fate here: the
second clause is `locally_small_ambient`, a lemma; the first clause is **not
statable**, for the reason given under Mac Lane def6.

### §1.3 — the two tiers `Cat` and `CAT`

Riehl draws a two-tier distinction: `Cat` has *small* categories as objects and
is locally small but not small; `CAT` has *locally small* categories as objects,
is not itself locally small, and receives an inclusion from `Cat`, of which `Cat`
is an object.

**This library renders the distinction as a single polymorphic construction, and
that is now backed by a machine-checked fact rather than by argument.** There is
one `Instance/Cat.v:142` `Cat`, and `Check (Cat : obj[Cat])` **succeeds** — at
two different universe instances, as shown under remark1 above. So "`Cat` is an
object of `CAT`" is not a separate tier to be built; it is what the polymorphic
`Cat` already says, with `CAT` being `Cat` at the next instance. There is no
`Cat'` to define, and defining a second tier over `LocallySmall` would produce
nothing new, since **every** category satisfies `LocallySmall` at the ambient
level (`locally_small_ambient`).

Worth recording alongside: `Cat`'s hom-setoid **is** natural isomorphism
(`Instance/Cat.v:145`), so `≅[Cat]` already means *equivalence*, not isomorphism
of categories — a distinction Riehl leans on. A genuine isomorphism of categories
must be stated in `StrictCat` (`Instance/StrictCat.v`).

---

## Where smallness is silently absent

One place is worth flagging for readers, since it is the strongest candidate for
a hidden smallness quantifier: `Structure/Complete.v:115` reads

```coq
Definition Complete {C : Category} := ∀ (D : Category) (F : D ⟶ C), Limit F.
```

which quantifies over **all** categories with no side condition — where the
classical definition asks only for *small* limits. What bounds it is not a
hypothesis but the universe instantiation that `F : D ⟶ C` forces on `D`. This
document records the shape of the situation; it does not assert that anything is
wrong, and no claim here depends on it.

---

## Summary table

| item | status |
|---|---|
| MacLane I.6 def1 (universe) | no counterpart — polymorphism, deliberately |
| def2 (small set/function) | idea present (`Type@{u}`); **no small-set predicate declared** |
| def4 (small category) | **`Small`**, content proved by rejected trivial discharge |
| def5 (class, proper class) | no counterpart — needs membership |
| def6 (large category) | **not statable** — negation is a metatheoretic claim |
| remark1 (`Set` not self-membered) | **corrected**: naive check *succeeds*; pinned form rejected; `Sets` case is a type error |
| remark2 (axioms in force) | `docs/AXIOMS.md` — zero in the core |
| remark3 (set-free alternatives) | **both formalized**: `Theory/Metacategory.v`, `Structure/Topos.v:112` |
| Awodey 1.11 (small) | `Small` |
| Awodey 1.12 (locally small) | `LocallySmall` + `locally_small_ambient` |
| Awodey 8.4 (Yoneda trichotomy) | (iii) cannot arise; (ii) presupposed at `Functor/Hom.v:78`; (i) open |
| Riehl 1.1.5 (universe convention) | recorded as a deliberate divergence |
| Riehl 1.1.6 (small + packaging) | `Small` + `ArrowQuiver`/`ArrowQuiverOfCat` (both supplied; their *equivalence* is not established) |
| Riehl 1.1.7 (locally small) | `locally_small_ambient`; the "not small" half not statable |
| Riehl 1.3 (`Cat`/`CAT`) | single polymorphic construction — witnessed by `Check (Cat : obj[Cat])` |
