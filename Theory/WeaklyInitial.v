Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Power.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * From a weakly initial family to a genuine initial object *)

(* nLab:      https://ncatlab.org/nlab/show/initial+object
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functor_theorem

   This file records the object-level input of Freyd's General Adjoint
   Functor Theorem: the passage from a *weakly* initial family to an actual
   initial object.  A family [wif_obj : wif_index -> C] is weakly initial
   when every object [c] is hit by some member, i.e. [wif_cover c] exhibits
   an index [i] and an arrow [wif_obj i ~> c] (existence, with no
   uniqueness).  The classical construction (Freyd, Mac Lane CWM V.6) forms
   the product [P] of the family — itself a single weakly initial object —
   and then carves out the joint equalizer of *all* endomorphisms of [P];
   that equalizer is genuinely initial.

   STATUS / hypothesis form.  The construction consumes exactly two limits
   over caller-chosen index [Type]s and a supply of binary equalizers:

     - [P]  : the product of the family [wif_obj] over [wif_index]
              (an indexed product = limit of a discrete diagram);
     - [Pe] : the product, over the hom-type of endomorphisms of that
              product object, of that object with itself — this is the
              [Type]-indexed limit whose universal cone lets a single
              parallel pair [P ~> Pe] "capture all endos" at once, so the
              wide equalizer of the endomorphism family reduces to one
              *binary* equalizer supplied by [E];
     - [E]  : binary equalizers for parallel pairs.

   Both products are passed as explicit hypotheses rather than harvested
   from a [Complete] / [HasIndexedProducts] instance.  This is deliberate
   (Risk (b)): the endomorphism-indexed product ranges over the hom-type
   [iprod .. ~> iprod ..], which sits at the hom universe [h]; routing it
   through a class that quantifies over every index [Type] would over-commit
   the ambient universes, whereas the explicit form leaves the smallness of
   the index (hence the relevant universe constraints) in the caller's
   hands.  Supplying [Pe] separately from [P] strengthens the hypotheses
   (an honest, leaner input) and never weakens the conclusion, which remains
   a full [Initial C].

   [Pe]'s family is CONSTANT -- [fun _ : P0 ~> P0 => P0] -- so [Pe] is a
   POWER of [P0] in the sense of Mac Lane III.3/III.4, and the proof below
   says so, through Structure/Limit/Power.v's [power_of_limit],
   [power_ev_of_limit] and [power_ump_of_limit].  Those are [iprod],
   [iprod_proj] and [iprod_ump] at the constant family, supplied by [:=], so
   the change is by conversion and the statement of the theorem is unaffected
   -- [Pe]'s type is written out in full above and is untouched.  [P]'s family
   [wif_obj W] genuinely varies and stays an indexed product.  Only
   Structure/Limit/Power.v is Required, not its Structure/Limit/Power/Hom.v
   satellite; [Instance/Sets] is in this file's closure anyway (measured:
   two hops since #435, Instance/Parallel → Instance/Sets; three before). *)

(* A weakly initial family: an index [Type], a family of objects, and for
   every object [c] a *choice* of covering member together with an arrow
   into [c].  No uniqueness of the covering arrow is required — that is what
   makes the family only *weakly* initial. *)
Record WeaklyInitialFamily (C : Category) := {
  wif_index : Type;
  wif_obj : wif_index -> C;
  wif_cover (c : C) : { i : wif_index & wif_obj i ~> c }
}.

Arguments wif_index {C} _.
Arguments wif_obj {C} _ _.
Arguments wif_cover {C} _ _.

(* The product [P] of a weakly initial family, together with equalizers and
   the endomorphism-indexed product [Pe] over the product object, yields a
   genuine initial object.

   Construction.  Write [P0] for the product object [iprod (wif_obj W) P].
   For any [c], the covering arrow [wif_cover c] composed with the matching
   projection gives a map [P0 ~> c], so [P0] is weakly initial (a single
   object now).  The projections of [Pe] separate all endomorphisms of
   [P0]: there is a map [m : P0 ~> Pe] with [proj u ∘ m ≈ u] for every endo
   [u], and a map [d : P0 ~> Pe] with [proj u ∘ d ≈ id] for every [u].  The
   binary equalizer [e : I ~> P0] of [m] and [d] then satisfies
   [u ∘ e ≈ e] for *every* endomorphism [u] of [P0], and is monic.  This
   [I] is initial:

     - existence  [I ~> c]:  [wmap c ∘ e], the weakly initial map post-
       composed with the equalizer inclusion;
     - uniqueness: given [f g : I ~> c], take the (binary) equalizer
       [k : K ~> I] of [f] and [g]; weak initiality gives [s : P0 ~> K], so
       [e ∘ (k ∘ s)] is an endomorphism of [P0], absorbed by [e]; monicity
       of [e] then makes [(k ∘ s) ∘ e ≈ id], i.e. [k] is split epi, and
       [f ∘ k ≈ g ∘ k] forces [f ≈ g]. *)
Theorem initial_from_weakly_initial `(W : WeaklyInitialFamily C)
  (P : Limit (DiscreteCat_Functor (wif_obj W)))
  (Pe : Limit (DiscreteCat_Functor
                 (fun _ : (iprod (wif_obj W) P ~> iprod (wif_obj W) P)
                  => iprod (wif_obj W) P)))
  (E : HasEqualizers C) : @Initial C.
Proof.
  (* Abbreviate the product object and fold it into [Pe]'s index. *)
  set (P0 := iprod (wif_obj W) P) in *.

  (* Weak initiality of [P0]: a chosen map into every object.  [wif_obj W] is
     a genuinely varying family, so this stays an indexed PRODUCT; it is only
     [Pe] below whose family is constant. *)
  pose (wmap := fun c : C =>
          projT2 (wif_cover W c)
            ∘ iprod_proj (wif_obj W) P (projT1 (wif_cover W c))).

  (* The tupling of all endomorphisms, and of the constant identity family,
     through the endomorphism-indexed POWER [Pe] -- the family there is
     [fun _ : P0 ~> P0 => P0], constant, so Structure/Limit/Power.v's
     vocabulary applies and is used.  Every step below is the same term as
     before, read through that vocabulary: [power_of_limit],
     [power_ev_of_limit] and [power_ump_of_limit] are [iprod], [iprod_proj]
     and [iprod_ump] at the constant family, supplied by [:=]. *)
  destruct (power_ump_of_limit P0 Pe P0 (fun u => u)) as [m Hm0 _].
  destruct (power_ump_of_limit P0 Pe P0 (fun _ => id[P0])) as [d Hd0 _].
  (* beta-normalized reads of the two universal families *)
  assert (Hm : ∀ u : P0 ~> P0, power_ev_of_limit P0 Pe u ∘ m ≈ u)
    by exact Hm0.
  assert (Hd : ∀ u : P0 ~> P0, power_ev_of_limit P0 Pe u ∘ d ≈ id[P0])
    by exact Hd0.

  (* The binary equalizer of the two tuplings. *)
  destruct (@equalizer C E P0 (power_of_limit P0 Pe) m d) as [I [e Eeq]].

  (* Every endomorphism of [P0] is absorbed by the equalizer inclusion. *)
  assert (endo_absorb : ∀ u : P0 ~> P0, u ∘ e ≈ e).
  { intro u.
    assert (Hu : power_ev_of_limit P0 Pe u ∘ (m ∘ e)
                   ≈ power_ev_of_limit P0 Pe u ∘ (d ∘ e)).
    { rewrite (fork_eq Eeq); reflexivity. }
    rewrite !comp_assoc in Hu.
    rewrite (Hm u) in Hu.
    rewrite (Hd u) in Hu.
    transitivity (id[P0] ∘ e).
    + exact Hu.
    + apply id_left. }

  (* The equalizer inclusion is monic. *)
  pose proof (equalizer_monic m d Eeq) as Me.
  destruct Me as [mon].

  (* Assemble the initial object as a terminal object of [C^op]. *)
  unshelve refine (@Build_Terminal (C^op) I _ _).
  - (* existence: [I ~> x] via weak initiality post-composed with [e] *)
    intro x.
    exact (wmap x ∘ e).
  - (* uniqueness: any two [f g : I ~> x] agree *)
    intros x f g.
    (* read the goal in [C]: [f], [g] are [C]-morphisms [I ~> x] *)
    change (unop f ≈ unop g).
    (* the binary equalizer of the competing pair *)
    destruct (@equalizer C E I x f g) as [K [k Ek]].
    (* weak initiality supplies a map [P0 ~> K] *)
    pose (s := wmap K).
    (* [e ∘ (k ∘ s)] is an endomorphism of [P0], absorbed by [e]; monicity
       of [e] then cancels it, exhibiting [s ∘ e] as a section of [k]. *)
    assert (Habs : (e ∘ (k ∘ s)) ∘ e ≈ e ∘ id[I]).
    { transitivity e.
      - exact (endo_absorb (e ∘ (k ∘ s))).
      - symmetry; apply id_right. }
    assert (Hk : (k ∘ s) ∘ e ≈ id[I]).
    { apply (mon _ ((k ∘ s) ∘ e) (id[I])).
      transitivity ((e ∘ (k ∘ s)) ∘ e).
      - apply comp_assoc.
      - exact Habs. }
    (* hence [k ∘ (s ∘ e) ≈ id]: [k] is a split epimorphism *)
    assert (Hkr : k ∘ (s ∘ e) ≈ id[I]).
    { transitivity ((k ∘ s) ∘ e).
      - apply comp_assoc.
      - exact Hk. }
    (* [k] equalizes [f] and [g] and is (split) epic, so [f ≈ g] *)
    transitivity (unop f ∘ (k ∘ (s ∘ e))).
    + transitivity (unop f ∘ id[I]).
      * symmetry; apply id_right.
      * apply compose_respects; [ reflexivity | symmetry; exact Hkr ].
    + transitivity (unop g ∘ (k ∘ (s ∘ e))).
      * transitivity ((unop f ∘ k) ∘ (s ∘ e)).
        -- apply comp_assoc.
        -- transitivity ((unop g ∘ k) ∘ (s ∘ e)).
           ++ apply compose_respects; [ exact (fork_eq Ek) | reflexivity ].
           ++ symmetry; apply comp_assoc.
      * transitivity (unop g ∘ id[I]).
        -- apply compose_respects; [ reflexivity | exact Hkr ].
        -- apply id_right.
Qed.

(** * The characterization: both directions (Mac Lane §V.6 Theorem 1)

    Everything above this line is the original file (#158/#328's Freyd
    construction), byte-identical up to a corrected sentence at lines
    64-65 (see below); the two external citations into it, Instance/Sets/
    Products.v:71 → :43-50 and Structure/Limit/Power.v:163 → :104-106,
    still point at what they cite.  What follows is #435 (Mac Lane §V.6
    Theorem 1, book p. 120, `maclane:V.6:thm1`, with the Awodey §9.8 and
    Riehl §4.7 clauses appended to the issue): the theorem as a
    CHARACTERIZATION.  Mac Lane's statement is "a category with small
    hom-sets that is small-complete has an initial object iff it has a
    small weakly initial family"; the tree carries no size class, so
    smallness is universe levels exactly as [initial_from_weakly_initial]
    already has it — the index [Type@{u}] of the family and the two [Limit]
    hypotheses that mention it.

    NECESSITY, the direction that was missing.  [weakly_initial_of_initial
    (I : Initial C) : WeaklyInitialFamily C] is the singleton family at the
    initial object, indexed by Lib/Setoid.v:56's universe-polymorphic
    [poly_unit] — written DIRECTLY, not through [wif_of_weakly_initial]:
    the direct form has an EMPTY universe constraint block and one binder
    fewer than the composite (measured; [unit] or [bool] as the index would
    pin the index universe at [Set]).  Its three readbacks are at [eq_refl]:
    the index IS [poly_unit], the member IS [initial_obj], the covering
    arrow IS [zero] — the family is built from the initial object, as the
    issue's reviewer asks, and not by any other route.

    THE BICONDITIONAL.  A plain [iff] is impossible because Freyd's
    direction consumes two products and the second one's index depends on
    the first, so [FreydProducts C] packages them per family (for every
    [W], the product of [wif_obj W] and the product of the endomorphisms of
    that product), and [initial_iff_weakly_initial_family (Ps :
    FreydProducts C) (E : HasEqualizers C) : Initial C ↔ WeaklyInitialFamily
    C] — Lib/Foundation.v:72's Type-valued [iffT], so both directions are
    extractable with [fst]/[snd] — keeps smallness caller-chosen exactly as
    the original theorem does.  It is [Defined], not [Qed]: it carries data
    in both directions, and the readback [initial_iff_weakly_initial_family_fst]
    pins that the forward half IS [weakly_initial_of_initial] (flipping the
    [Defined] to [Qed] stops that readback).  Awodey §9.8's convenience
    form harvests the two products from [Complete] and keeps the equalizers
    an explicit supply — [initial_from_weakly_initial_complete] and
    [initial_iff_weakly_initial_family_complete] (likewise [Defined], with
    its own [_fst] readback).  The [Complete]-only variant is NOT here:
    [Complete_HasEqualizers] lives downstream, in Adjunction/GAFT.v:193,
    which [Require]s this file, and re-deriving it here would duplicate a
    downstream definition.  Read the universes of the [_complete] form:
    [Complete]'s first two levels are the family's index level (the
    biconditional prints [Complete@{u0 u0 Set u2}], the wrapper
    [Complete@{u u Set u1}]), so the shape's object universe is identified
    with the family's index universe and the caller's choice of [Complete]
    IS the choice of admissible index size — the honest reading of
    "small-complete", with no size class.

    THE RIEHL CLAUSE.  [WeaklyInitial c : Type := ∀ x, c ~> x] (Definition
    4.7.4, the one-object form; the constant may take the module's own
    name — a structural replica of this file and of Wide.v using both was
    compiled to confirm the namespace does not clash), with
    [weakly_initial_obj_of_initial], [wif_of_weakly_initial] (the singleton
    family of a weakly initial object), and the relation lemma
    [weakly_initial_iprod : WeaklyInitial (iprod (wif_obj W) P)] — the
    [wmap] the proof above builds inline at lines 115-117 (and Wide.v at
    109-111), now named; the original theorem is [Qed]-opaque and is NOT
    re-proved through it, keeping docs/INDEX.md's "byte-identical" promise
    for the theorem.  Its converse — a family gives a weakly initial object
    at a chosen index — is FALSE without a singleton hypothesis, because
    [wif_cover] picks its own member per target: that is Riehl's
    distinction between weakly initial and jointly weakly initial, and
    probe N5 pins it.  Weak initiality is strictly weaker than initiality,
    proved rather than asserted, at Instance/Parallel.v's walking parallel
    pair (already in this file's closure): [Parallel_ParX_WeaklyInitial],
    [Parallel_ParX_not_initial] (two inequivalent arrows [ParX ~> ParY],
    [is_initial_unique] would identify them, [discriminate] closes it) and
    [Parallel_ParY_not_weakly_initial] (the separation is about the
    object, not the category).

    THE SOLUTION-SET VOCABULARY.  The issue's "hence the solution set
    condition" is Adjunction/GAFT.v's [sols_of_wif : WeaklyInitialFamily
    (=(d) ↓ U) → SolutionSet U d], the exact converse of [wif_of_sols] —
    same index, same members — with the special case
    [sols_of_comma_initial : Initial (=(d) ↓ U) → SolutionSet U d] defined
    as [sols_of_wif] of [weakly_initial_of_initial].  Both are appended at
    the END of that file so that none of its cited line numbers move
    (eleven external citations point at its line 241); the index of the
    general form and the index and member of the special case read back at
    [eq_refl].  (GAFT became a biconditional in #436, [GAFT_iff]; when
    this was written it had not.)

    THE WITNESS.  Theory/WeaklyInitial/Sets.v (a leaf satellite; its
    closure is 53, 25 more than this file's, which is why it is not here)
    runs the full round trip at [Sets]: [Sets_initial_characterization :=
    initial_iff_weakly_initial_family_complete Sets_Complete
    Sets_HasEqualizers], [Sets_wif := fst … Sets_Initial],
    [Sets_initial_recovered := snd … Sets_wif], and [Sets_roundtrip_iso :
    initial_obj Sets_initial_recovered ≅ initial_obj Sets_Initial] by
    [initial_unique]; the DERIVED singleton family's index and member read
    back at [eq_refl] (nothing about the recovered initial object does).
    It lands at [Sets@{Set u}], as Adjunction/GAFT/Sets.v's
    header already discloses for GAFT.  This turns the biconditional from a
    conditional into an inhabited result; docs/INHABITATION.md has the row.

    STALE PREMISES.  Every line number in the issue's "Current state" is
    stale (they match commit 00fc744b, and 820201bc, "Powers and
    copowers", shifted the file in TWO hunks — +13 above the proof body,
    +19 inside it): [initial_from_weakly_initial] is :102 not :89, [Record
    WeaklyInitialFamily] :71 not :58, [endo_absorb] :138 not :119, and the
    uniqueness chase's [assert (Hk : …)] :173 not :154; :44 and
    Adjunction/GAFT.v:210 happen to be right.  Every substantive absence
    claim is TRUE:
    [Build_WeaklyInitialFamily] has exactly one use tree-wide
    (Adjunction/GAFT.v:214), nothing built a family from an [Initial], no
    constant named [WeaklyInitial] existed (all 29 word hits over `*.v`,
    31 counting `_CoqProject`, were the module path).  Two sentences of
    the existing headers were FALSE and are
    corrected in place, line-count-preserving: lines 64-65 of this file said
    the [Power.v] choice "keeps [Instance/Sets] off this file's dependency
    closure" — [Instance/Sets] is in it, TWO hops now that this file
    [Require]s Instance/Parallel.v directly, three before through
    Structure/Equalizer/Fork.v (docs/INDEX.md's Power.v bullet records the
    one-hop route from Power.v itself, which is correct and is left alone);
    and Wide.v:67-68 attributed the [Set] pin to [Terminal] and the
    equalizer supply — both
    have empty constraint blocks, and the pin is [iprod]'s:
    [DiscreteCat_Functor] puts the discrete shape at [DiscreteCat@{u Set
    Set}] and [Limit] identifies the shape's hom universe with the
    ambient's.

    UNIVERSES ([About] under `Set Printing Universes`).  No [Set] on the
    Riehl-side constants: [WeaklyInitial@{u u0 u1}] carries only the
    Π-type's `u0 <= u`, `u1 <= u`, and so do [wif_of_weakly_initial] and
    [weakly_initial_obj_of_initial], whose types mention it;
    [weakly_initial_of_initial@{u u0 u1}] alone carries an EMPTY block,
    where the composite through [wif_of_weakly_initial] would carry four
    binders and two constraints; the Parallel constants are at that small
    category's levels.
    Everything that consumes [iprod] or a [Limit (DiscreteCat_Functor …)]
    — [weakly_initial_iprod], [FreydProducts], both biconditionals, the
    [_complete] wrapper and their readbacks — is over [C : Category@{_ Set
    Set}], the donor's pin, with the strict `Set < u` and the caps `JMeq`,
    `eq` and `Logic_lemmas.equality` the original theorem carries — and
    `Projections` on all of them but [FreydProducts].  A universe
    refutation at [Cat] was tried and does NOT refuse
    ([Cat]'s hom universe instantiates at [Set]); it is recorded here so it
    is not re-invented.

    MEASURED.  17 new `.glob` heads in this file (15 `def`, 2 `prf`; 22
    with the original five), 6 in Theory/WeaklyInitial/Sets.v, 5 in
    Adjunction/GAFT.v, no [Program] obligations, all 33 "Closed under the
    global context", zero `Axioms:` lines; the `make print-assumptions`
    gate carries all 33, the original five of this file included (it
    carried none of those five before).  Four `Defined` — the two
    biconditionals here, [sols_of_wif] and [sols_of_comma_initial] — each
    LOAD-BEARING (flipped to `Qed` one at a time in a copy of the whole
    file, the matching [eq_refl] readback stops); two new `Qed` (the two
    Parallel negations).  Closure of this
    file 29 excluding self, one more than before (Structure/Complete.v, the
    only new module on the GAFT critical path; Instance/Parallel.v was
    already inside, 0 at the margin); Sets.v 53 (Adjunction/GAFT/Sets.v 15
    at the margin, its other six `Require`s 0); Sets.v has no droppable
    `Require` and both of this file's new ones are needed, though its
    PRE-EXISTING Theory/Functor.v and Theory/Morphisms.v lines are
    droppable and are kept so that the cited lines above do not move.
    Zero name collisions for the 28 new names
    (`grep -rlw --include='*.v'`).  Test/ProbeWeaklyInitial435.v mirrors
    this file's `Require` list plus the satellite, Adjunction/GAFT.v and
    their supplies, binds its category per command (a [Section] variable
    would fix the hom level the pinned [Limit]s need at [Set]), and carries
    6 refutation commands = 1 instrument + N1 TYPING (an object is not a
    family) + N2-N3 CONVERSION (the index is [poly_unit], not [bool]; a
    [Terminal] is not an [Initial] — "cannot unify λ x y, y ~> x and
    hom[C]", the [C^op] pivot) + N4-N5 TYPING (the equalizer supply is not
    the second product; the cover does not make a chosen member weakly
    initial), each stripped one at a time in a copy of the whole file
    beside its accepted control; seven `eq_refl` readbacks; guard coverage
    34/27 with seven exhaustive exceptions (identifier tokens inside the
    six refutation commands / also named outside them, comments stripped:
    the two keywords, two bound variables, the two refuted names and the
    instrument's absent name); rename-simulated 15 library names —
    [WeaklyInitial], [WeaklyInitialFamily], [wif_index], [wif_obj],
    [wif_cover], [weakly_initial_of_initial], [initial_from_weakly_initial],
    [Terminal], [Limit], [DiscreteCat_Functor], [HasEqualizers], [Category],
    [eq_refl], [bool], [projT2] — every first break on a positive line.
    `make todo` grows by the 6 refutation lines only (2277 → 2283 over
    #434's tip), so the issue's "adds no new hits" box is not met as
    written (disclosed, as in #430-#434); Coq 8.19 and 8.20 are checked by
    nix source builds of the committed revision, which the PR records.

    NOT DELIVERED: any size class (smallness stays universe levels); any
    re-proof or restatement of [initial_from_weakly_initial] or of Wide.v's
    theorem (both stay [Qed] and byte-identical); a biconditional for the
    wide form, or a [HasWideEqualizers] instance; the [Complete]-only
    biconditional (see above); a witness at any category but [Sets]; an
    agreement proof between [Sets_wif] and a hand-built family, or an
    [eq_refl] reading of the round trip (only the canonical [≅]);
    [weakly_initial_of_wif] under a singleton hypothesis (contrived, and it
    drags in `eq_rect` caps); functoriality of anything here; GAFT as a
    biconditional; no edit to Structure/Complete.v, Structure/Limit/
    Product.v, Instance/Parallel.v, Instance/Sets/Complete.v or
    Adjunction/GAFT/Sets.v, and none to Adjunction/GAFT.v above its last
    line. *)

(* [Structure.Complete] for the convenience wrapper; [Instance.Parallel]
   for the separator (already in this file's closure through
   Structure/Equalizer/Fork.v). *)
Require Import Category.Structure.Complete.
Require Import Category.Instance.Parallel.

(** ** A weakly initial object (Riehl Definition 4.7.4) *)

(* One object with an arrow to every object, no uniqueness.  A weakly
   initial family is the jointly weakly initial version: [wif_cover] picks
   its own member per target. *)
Definition WeaklyInitial {C : Category} (c : C) : Type := ∀ x : C, c ~> x.

Definition weakly_initial_obj_of_initial {C : Category} (I : @Initial C) :
  WeaklyInitial (@initial_obj C I) := fun x => @zero C I x.

Definition wif_of_weakly_initial {C : Category} {c : C} (w : WeaklyInitial c) :
  WeaklyInitialFamily C :=
  {| wif_index := poly_unit
   ; wif_obj   := fun _ => c
   ; wif_cover := fun x => (ttt; w x) |}.

(* The product of a weakly initial family is a weakly initial object: the
   [wmap] the proof above builds inline, now named. *)
Definition weakly_initial_iprod {C : Category} (W : WeaklyInitialFamily C)
  (P : Limit (DiscreteCat_Functor (wif_obj W))) :
  WeaklyInitial (iprod (wif_obj W) P) :=
  fun c => projT2 (wif_cover W c)
             ∘ iprod_proj (wif_obj W) P (projT1 (wif_cover W c)).

(** ** Necessity: an initial object is a singleton weakly initial family *)

(* Written directly rather than through [wif_of_weakly_initial]: the direct
   form has an empty universe constraint block and one binder fewer. *)
Definition weakly_initial_of_initial {C : Category} (I : @Initial C) :
  WeaklyInitialFamily C :=
  {| wif_index := poly_unit
   ; wif_obj   := fun _ => @initial_obj C I
   ; wif_cover := fun x => (ttt; @zero C I x) |}.

(* The family is built from the initial object, on the nose. *)
Example weakly_initial_of_initial_index {C : Category} (I : @Initial C) :
  wif_index (weakly_initial_of_initial I) = poly_unit := eq_refl.

Example weakly_initial_of_initial_obj {C : Category} (I : @Initial C)
  (u : poly_unit) :
  wif_obj (weakly_initial_of_initial I) u = @initial_obj C I := eq_refl.

Example weakly_initial_of_initial_cover {C : Category} (I : @Initial C)
  (x : C) :
  projT2 (wif_cover (weakly_initial_of_initial I) x) = @zero C I x := eq_refl.

(** ** The biconditional *)

(* The Freyd inputs, per family, so smallness stays caller-chosen: the
   product of the family and the product of the endomorphisms of that
   product (the second index depends on the first). *)
Definition FreydProducts (C : Category) : Type :=
  ∀ W : WeaklyInitialFamily C,
    { P : Limit (DiscreteCat_Functor (wif_obj W))
    & Limit (DiscreteCat_Functor
               (fun _ : iprod (wif_obj W) P ~> iprod (wif_obj W) P
                => iprod (wif_obj W) P)) }.

(* Transparent, so that each direction can be read back: the forward one
   IS [weakly_initial_of_initial]. *)
Definition initial_iff_weakly_initial_family {C : Category}
  (Ps : FreydProducts C) (E : HasEqualizers C) :
  @Initial C ↔ WeaklyInitialFamily C.
Proof.
  split.
  - exact (@weakly_initial_of_initial C).
  - intro W.
    destruct (Ps W) as [P Pe].
    exact (initial_from_weakly_initial W P Pe E).
Defined.

Example initial_iff_weakly_initial_family_fst {C : Category}
  (Ps : FreydProducts C) (E : HasEqualizers C) (I : @Initial C) :
  fst (initial_iff_weakly_initial_family Ps E) I = weakly_initial_of_initial I
  := eq_refl.

(** ** The convenience wrapper: the two products from completeness *)

(* Awodey §9.8's reading: harvest both products from [Complete] and keep
   the equalizers an explicit supply — [Complete_HasEqualizers] lives
   downstream, in Adjunction/GAFT.v, and is not re-derived here. *)
Definition initial_from_weakly_initial_complete {C : Category}
  (HC : @Complete C) (E : HasEqualizers C) (W : WeaklyInitialFamily C) :
  @Initial C :=
  initial_from_weakly_initial W
    (HC (DiscreteCat (wif_index W)) (DiscreteCat_Functor (wif_obj W)))
    (HC (DiscreteCat _)
        (DiscreteCat_Functor
           (fun _ : iprod (wif_obj W)
                      (HC (DiscreteCat (wif_index W))
                          (DiscreteCat_Functor (wif_obj W)))
                    ~> iprod (wif_obj W)
                         (HC (DiscreteCat (wif_index W))
                             (DiscreteCat_Functor (wif_obj W)))
            => iprod (wif_obj W)
                 (HC (DiscreteCat (wif_index W))
                     (DiscreteCat_Functor (wif_obj W))))))
    E.

Definition initial_iff_weakly_initial_family_complete {C : Category}
  (HC : @Complete C) (E : HasEqualizers C) :
  @Initial C ↔ WeaklyInitialFamily C.
Proof.
  split.
  - exact (@weakly_initial_of_initial C).
  - exact (initial_from_weakly_initial_complete HC E).
Defined.

Example initial_iff_weakly_initial_family_complete_fst {C : Category}
  (HC : @Complete C) (E : HasEqualizers C) (I : @Initial C) :
  fst (initial_iff_weakly_initial_family_complete HC E) I
    = weakly_initial_of_initial I := eq_refl.

(** ** Weakly initial is strictly weaker than initial *)

(* At the walking parallel pair: [ParX] reaches every object, is not
   initial (two inequivalent arrows to [ParY]), and [ParY] is not even
   weakly initial — the separation is about the object, not the category. *)
Definition Parallel_ParX_WeaklyInitial : @WeaklyInitial Parallel ParX :=
  fun x => match x with
           | ParX => (true; ParIdX)
           | ParY => (true; ParOne)
           end.

Theorem Parallel_ParX_not_initial : @IsInitialObj Parallel ParX → False.
Proof.
  intro H.
  pose proof (@is_initial_unique Parallel ParX H ParY
                (true; ParOne) (false; ParTwo)) as E.
  simpl in E.
  discriminate E.
Qed.

Theorem Parallel_ParY_not_weakly_initial :
  @WeaklyInitial Parallel ParY → False.
Proof.
  intro w.
  destruct (w ParX) as [b h].
  exact (ParHom_Y_X_absurd b h).
Qed.
