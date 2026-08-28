(** * Set-indexed coproducts of categories *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.

(* PORTABILITY, learned the hard way: this MUST be the [Coq.Logic.]
   spelling, not [From Stdlib Require Import EqdepFacts].  The tree
   builds on Coq 8.19/8.20 as well as Rocq 9.1, and the [Stdlib] prefix
   does not exist on the 8.x line -- Docker CI rejects it with "Cannot
   find a physical path bound to logical path EqdepFacts with prefix
   Stdlib".  An earlier revision of this file shipped the [Stdlib]
   spelling and was the only file in the tree to use it.  Note that the
   nix [category-theory_8_19] target ACCEPTS both spellings, so a green
   nix build is not evidence here; the tree's own convention is
   [Require Import Coq.Logic.Eqdep_dec.] (Structure/Bicartesian/Matrix.v,
   Instance/Ordinal.v, Instance/FinSet/Pushout.v) and this follows it. *)
Require Import Coq.Logic.EqdepFacts.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §III.5 Exercise 4, printed p. 74 (PDF p. 84) —
              maclane:III.5:ex4
   Book:      Riehl, "Category Theory in Context", 2nd ed., §3.6 —
              riehl:3.6:construction-cat-coproducts
   nLab:      https://ncatlab.org/nlab/show/coproduct

   The disjoint union of an [I]-indexed family of categories: objects are
   the dependent pairs [(i; x)] with [x : C i], and a morphism
   [(i; x) ~> (j; y)] is a proof [e : i = j] together with a morphism
   [ob_cast C e x ~> y] of [C j].  Across summands — [i] and [j]
   distinct — the hom is EMPTY, because [i = j] is; within a summand it
   is that summand's own hom TOGETHER WITH the loop of the index proof
   it carries, and the two coincide EXACTLY under [IdxUIP] — see point
   3, where that is what [sigma_inj_Full_forces_UIP] proves and what
   [SigmaCat_inj_Full] therefore has to assume.  (An earlier revision of
   this sentence said "up to the transport that typing forces", which
   asserts the identification point 3 shows costs a hypothesis.)
   Functors out of the coproduct are given by case analysis
   ([SigmaCat_case]), and that correspondence is the universal property
   ([SigmaCat_ump]).

     - [SigmaCat C]: the coproduct category ∐_{i:I} C i
     - [SigmaCat_inj C i]: the injection C i ⟶ ∐ C
     - [SigmaCat_case F]: the case functor ∐ C ⟶ D of a family
       [F : ∀ i, C i ⟶ D], with [SigmaCat_case_inj] the triangle,
       [SigmaCat_case_unique] the uniqueness half, and [SigmaCat_ump]
       the bundled ∃! (the packaging of Structure/Limit/Product.v's
       [iprod_ump] and Construction/Product/Indexed.v's [PiCat_ump])

   The [Cat]-level packaging — [IsIndexedCoproduct], and the
   [HasIndexedCoproducts Cat] instance — is Instance/Cat/Coproduct.v,
   which also carries the comparison with the binary coproduct of
   Construction/Coproduct.v and the concrete witnesses.

   1. THE INDEX-EQUALITY ENCODING, WHICH IS THIS FILE'S REAL CONTENT.
      To say "the hom is empty across summands and the summand's hom
      within one summand" one must say when two INDICES agree, and [I]
      is an arbitrary [Type] with no decider.  Three encodings present
      themselves and they are not equivalent:

      (a) match on a DECIDER [∀ i j : I, {i = j} + {i <> j}].  Not
          taken: the exercise grants no decider, and demanding one
          would exclude, for instance, an index type of functions.

      (b) index the hom by a Leibniz equality and transport —
          [hom (i;x) (j;y) := ∃ e : i = j, ob_cast C e x ~> y] — with
          the hom-setoid comparing the two index proofs at Leibniz
          equality and the two morphisms at [≈] after transport.  THIS
          IS THE ENCODING TAKEN.

      (c) quantify over the proof — [∀ e : i = j, …] — with the setoid
          comparing pointwise.  REFUTED, and for two independent
          reasons, neither of which is about UIP.  First, it gets the
          MATHEMATICS wrong: for [i] and [j] provably distinct the type
          [∀ e : i = j, X e] is INHABITED (by the vacuous function), so
          this reading adds a morphism between every pair of objects in
          different summands — the indiscrete category on the summands,
          not their disjoint union.  Second, it does not even define a
          category: the identity at [(i;x)] would have to be a family
          [∀ e : i = i, ob_cast C e x ~> x], and for a loop [e] the
          object [ob_cast C e x] is not [x], so no identity is
          definable.  A hybrid — pair the sigma (for emptiness) with the
          ∀-family (for a proof-independent hom) — inherits the second
          failure and is refuted with it.

      A FOURTH encoding is excluded by a different argument.  One might
      try to make the hom-setoid FINER, comparing the two index proofs
      only up to CONVERSION rather than up to Leibniz equality (an
      inductive relation whose one constructor takes a single [e]).
      That relation is an equivalence and a congruence, but the
      resulting structure is not a category: associativity of the index
      component is the associativity of proof composition, which holds
      only PROPOSITIONALLY, and — whichever way the composition of index
      proofs is made to reduce — only one of the two unit laws follows
      it (this file's [sigma_compose] matches on the OUTER proof and so
      buys [id ∘ f], leaving [f ∘ id] propositional).  So the setoid
      must tolerate propositional equality of index proofs, which is
      encoding (b).  That the remaining unit law could not be bought by
      some other arrangement is an argument, not a theorem: no
      impossibility is proved.

   2. NO HYPOTHESIS IS SPENT ON THE CONSTRUCTION OR ON ITS UNIVERSAL
      PROPERTY.  [SigmaCat], [SigmaCat_inj], [SigmaCat_case],
      [SigmaCat_case_inj], [SigmaCat_case_unique] and [SigmaCat_ump]
      take NO decidability and NO uniqueness-of-identity-proofs
      hypothesis, on [I] or on anything else.  This was not the
      expected outcome and it deserves its reason.  Every proof
      obligation quantifies over the two ENDPOINT indices, so the
      index proof [e : i = j] it must reason about relates two
      universally quantified variables and can be ELIMINATED by
      [destruct]; after that elimination every transport disappears and
      the goal is the corresponding law of one summand.  Uniqueness in
      particular goes through because a family of natural isomorphisms
      [∀ i, G ◯ inj i ≈ F i] is a DEPENDENT FUNCTION of [i], so it
      already carries whatever coherence the index type's own paths
      demand; the naturality square for the comparison is proved by
      destructing the index proof of the morphism it is stated at, and
      lands exactly on the naturality of the given family at that
      index.

   3. WHERE A HYPOTHESIS IS SPENT, AND THAT IT IS NECESSARY.  What does
      need one is the classically automatic statement that the
      injections are FULL — that every endomorphism of [(i;x)] comes
      from [C i].  A loop [e : i = i] cannot be eliminated, so a
      morphism carrying one need not be [≈] to any morphism carrying
      [eq_refl].  [SigmaCat_inj_Full] therefore takes [IdxUIP I]
      explicitly, and [sigma_inj_Full_forces_UIP] proves the hypothesis
      NECESSARY rather than convenient: fullness of a single injection,
      for a family whose [i]-summand has an object with the relevant
      hom-sets inhabited, ENTAILS uniqueness of identity proofs at that
      index.  (The pattern is this tree's: Theory/OGraph.v's
      [coarse_respectfulness_entails_UIP], Theory/Category/Monoid.v's
      [arrow_mul_respects_forces_UIP], and
      Instance/Discrete/Reconstruct.v's
      [Discrete_DiscreteUpToIso_forces_UIP].)  Faithfulness splits: for
      a CONSTANT family it is free ([SigmaCat_const_inj_Faithful], by
      the retraction [SigmaCat_case (fun _ => Id)], which is
      definitionally the identity on the summand), while for a general
      family [SigmaCat_inj_Faithful] takes [IdxUIP I] and spends it one
      level up, through the stdlib's axiom-free [UIP_shift].  NO
      necessity result is proved for faithfulness — no countermodel is
      exhibited and none is claimed.

   4. UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS.  [SigmaCat] is
      declared with explicit binders, and that is LOAD-BEARING: written
      unannotated, universe minimization IDENTIFIES the summands' hom
      and proof universes — the definitions below then read
      [(I → Category@{u2 u0 u0}) → Category@{u1 u0 u0}] — and a family
      at [Category@{uo uh up}] declared under [Constraint uh < up] is
      rejected with "Cannot enforce up = uh".  Measured for BOTH
      shapes: the single [Program Definition] this file started from,
      and the pieces below with their annotations stripped.  With the
      binders written out the block is all BOUNDS and no
      identification.  The FULL block is six constraints, not three —

        ui <= us,  uo <= us,  oh <= op,
        ui <= Projections.u0,  uo <= Projections.u1,
        oh <= Projections.u1

      — and an earlier revision of this header listed only the first
      row, which understated it.  [oh <= op] is [Class Category]'s own
      [h <= p].  The three [Projections.*] bounds are the stdlib's:
      [projT1] and [projT2] are NOT universe polymorphic ([About projT1]
      says so, and [Set < Projections.u0 < Projections.u1]), so every
      universe that passes through a sigma here is additionally capped
      below a FIXED global level.  That is nothing of this file's doing
      either, and it does not disturb the headline — no constraint in
      the block is an EQUATION — but it is part of the block and is now
      stated.  So the index universe [ui] and the summands'
      object universe [uo] bound only [us], the object universe of the
      COPRODUCT, and the summands' hom and proof universes pass through
      untouched.  [SigmaCat_inj] carries the same block, and
      [SigmaCat_case] adds only the four bounds [oh <= dh], [oh <= dp],
      [op <= dp] and [dh <= dp] relating the two categories a functor
      spans, which are [Class Functor]'s.  In particular the index
      universe does NOT bound the hom universe, and the reason is worth
      naming: [eq] is Prop-valued, so the index proof carried inside
      every hom costs nothing there.  That is the point of contrast
      with the dual construction: in Construction/Product/Indexed.v's
      [PiCat] a hom IS an [I]-indexed dependent FUNCTION, so there
      [I]'s level bounds the hom universe as well — the asymmetry is
      real, not a difference of annotation.  The minimization defect
      repaired here is of the family
      Construction/Free/Quiver/Examples.v records for
      [Build_Quiver_Standard_Eq].

      THE UMP-LEVEL LEMMAS DO NOT SHARE THAT FREEDOM, AND THE CAUSE IS
      A DONOR.  [SigmaCat_case_inj], [SigmaCat_case_unique] and
      [SigmaCat_ump] all display [C : Category@{a b b}] and
      [D : Category@{c b b}] — hom and proof identified in BOTH, and
      the two categories' hom universes identified with each other.
      That is [Functor_Setoid]'s (Theory/Functor.v:149, itself an
      unannotated [Program Instance]) and not this file's: under
      [Constraint uh < up], [@Functor_Setoid C D] is REJECTED for a
      source at those levels and again for a target at those levels,
      while the functor TYPE [C ⟶ D] and [@Unique _ (@homset C x y) P]
      both elaborate there as positive controls.  Since [≈] on functors
      IS that setoid, no statement of the universal property in this
      library's vocabulary can avoid it; nothing here attempts to lift
      it, and it is NOT claimed unavoidable.  What it costs a consumer
      is recorded at the point of use, in Instance/Cat/Coproduct.v.

   5. PRIOR ART, AND WHAT IS *NOT* REUSED.
      - Construction/Product/Indexed.v's [PiCat] is the dual — the
        set-indexed PRODUCT of categories, Mac Lane §II.3 Ex 3 — and is
        a STRUCTURAL precedent only, not a donor: the coproduct is not
        [PiCat] of opposites, and no definition below mentions it.  The
        numbered-discussion shape of this header, and the binary-case
        note, follow that file.
      - Construction/Coproduct.v's binary [C ∐ D] is the two-summand
        case, where the index is [bool] and the case analysis is on
        CONSTRUCTORS, so it needs no index-equality machinery at all.
        The comparison at [I := bool] is made in Instance/Cat/Coproduct.v.
      - THE GROTHENDIECK ROUTE EXISTS AND WOULD COST STRICTLY MORE.
        [Construction/Displayed/Total.v]'s [Total] has
        [obj := ∃ x : C, dobj x], and over a discrete base its total
        category is a disjoint union; the way in is
        Construction/Grothendieck/Strict.v's
        [IndexedCat_of_StrictFunctor], which takes a functor into
        [StrictCat] together with the explicit hypothesis
        [Fuip : ∀ (b : B) (x y : F b) (p q : x = y), p = q] — UIP on
        the OBJECTS of every fibre — with
        [IndexedCat_of_StrictFunctor_dec] discharging it from decidable
        fibre equality via [UIP_dec].  So that route would buy the
        construction at the price of UIP on every summand's object
        type, where the direct construction pays nothing.  This is a
        MEASUREMENT of the donor's stated hypothesis, not an attempt to
        run the route: nothing here builds a [Displayed] or an
        [IndexedCat], and it is NOT claimed that the route could not be
        rearranged to spend less.

   WHAT IS NOT DELIVERED.  No notation for the indexed coproduct (the
   binary [∐] is taken and no unambiguous indexed spelling was found).
   THE COMPANION PROBE is Test/ProbeCatCoproduct338.v, which pins the
   universe measurements of point 4 as [Fail] commands and compiles the
   inhabitedness half of point 1's encoding-(c) refutation as
   [probe_forall_encoding_inhabited].  So "refuted by argument, not by
   a compiled [Fail]" below is exact as written — that half is compiled
   there as a POSITIVE, not as a [Fail] — and a reader looking for what
   IS machine-checked should look in that file.

   No [Colimit]/[DiscreteCat_Functor] reading — see
   Instance/Cat/Coproduct.v, which explains why.  No functoriality of
   [SigmaCat] in the family [C] or in the index [I], and hence no
   comparison of [∐] over a reindexing.  No dual, no relation to
   [PiCat] beyond the header remark, and no distributivity of products
   over these coproducts.  No claim that the injections are jointly
   surjective on objects other than the definitional one.  Faithfulness
   of the injections is not shown to FORCE anything.  No countermodel
   is built for any of the refuted encodings of point 1: they are
   refuted by argument in this header — the inhabitedness of a vacuous
   function type, the non-existence of an identity, and the merely
   propositional associativity of proof composition — and not by a
   compiled [Fail]. *)

(** ** Casting along index equalities *)

(* Transport an object of [C i] to [C j] along [e : i = j].  Every
   dependency on the index equality in this file goes through this one
   definition. *)
Definition ob_cast@{ui uo oh op} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) {i j : I} (e : i = j) (x : C i) : C j :=
  match e in _ = k return C k with eq_refl => x end.

(* Transport a morphism along an equality BETWEEN two index equalities.
   This is what the hom-setoid needs in order to compare two morphisms
   whose index components are only propositionally equal. *)
Definition mor_cast@{ui uo oh op} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) {i j : I} {x : C i} {y : C j}
  {e1 e2 : i = j} (p : e1 = e2) (f : ob_cast C e1 x ~> y) :
  ob_cast C e2 x ~> y :=
  match p in _ = e return ob_cast C e x ~> y with eq_refl => f end.

(* Casting along a proof and back along its inverse is the identity —
   at LEIBNIZ equality, not merely at [≈].  Both endpoints are
   universally quantified here, which is exactly why [destruct p]
   is available; the same statement instantiated at a loop is not
   provable, and that is the content of section [Fullness] below. *)
Lemma mor_cast_sym@{ui uo oh op} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) {i j : I} {x : C i} {y : C j}
  {e1 e2 : i = j} (p : e1 = e2) (f : ob_cast C e1 x ~> y) :
  mor_cast C (eq_sym p) (mor_cast C p f) = f.
Proof. destruct p; reflexivity. Qed.

(** ** The data of the coproduct category *)

(* Objects, homs and the hom-relation are named separately so that each
   carries its own universe annotation.  A NOTE ON WHAT THAT DOES AND
   DOES NOT BUY, corrected before landing: an earlier revision of this
   comment claimed that "an explicitly annotated [Program Definition] of
   this record does not elaborate at all".  That is FALSE, and was
   refuted by compiling one — with obj, hom and the hom-relation fully
   inlined and the law fields supplied BY NAME, an annotated
   [Program Definition] elaborates and prints a constraint block
   character-for-character identical to [SigmaCat]'s.  What actually
   provokes "Universe … is unbound" is proving the obligations by
   TACTIC in place, which generates constants carrying universes the
   declared binder list cannot mention.  So what is load-bearing is
   naming the obligation PROOFS, not naming the data. *)
Definition sigma_obj@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) : Type@{us} := ∃ i : I, C i.

Definition sigma_hom@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} (X Y : sigma_obj@{ui uo oh op us} C) :
  Type@{oh} := ∃ e : `1 X = `1 Y, ob_cast C e (`2 X) ~> `2 Y.

Definition sigma_equiv@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {X Y : sigma_obj@{ui uo oh op us} C}
  (f g : sigma_hom X Y) : Type@{op} :=
  ∃ p : `1 f = `1 g, mor_cast C p (`2 f) ≈ `2 g.

Definition sigma_id@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} (X : sigma_obj@{ui uo oh op us} C) :
  sigma_hom X X := (eq_refl; id).

(* Composition.  The match is on the index proof of the OUTER morphism:
   in the [eq_refl] branch the middle and target indices coincide, that
   morphism's transport disappears, and the two morphisms compose in one
   summand with the inner morphism's index proof carried along
   unchanged.  Matching this way round is what makes [id ∘ f] reduce
   definitionally — see [sigma_id_left]. *)
Definition sigma_compose@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {X Y Z : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom Y Z) (g : sigma_hom X Y) : sigma_hom X Z :=
  (match `1 f as e0 in _ = m
     return ∀ z0 : C m, (ob_cast C e0 (`2 Y) ~> z0) →
            (∃ e : `1 X = m, ob_cast C e (`2 X) ~> z0)
   with
   | eq_refl => fun z0 h => (`1 g; h ∘ `2 g)
   end) (`2 Z) (`2 f).

(** ** The category laws *)

Lemma sigma_equiv_Equivalence@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} (X Y : sigma_obj@{ui uo oh op us} C) :
  Equivalence (@sigma_equiv@{ui uo oh op us} I C X Y).
Proof.
  constructor.
  - intros [e f]; exists eq_refl; reflexivity.
  - intros [e1 f] [e2 g] [p Hp]; simpl in *.
    destruct p; simpl in *.
    exists eq_refl; simpl; now symmetry.
  - intros [e1 f] [e2 g] [e3 h] [p Hp] [q Hq]; simpl in *.
    destruct p, q; simpl in *.
    exists eq_refl; simpl; now transitivity g.
Qed.

Lemma sigma_compose_respects@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {X Y Z : sigma_obj@{ui uo oh op us} C}
  (f f' : sigma_hom Y Z) (Hf : sigma_equiv f f')
  (g g' : sigma_hom X Y) (Hg : sigma_equiv g g') :
  sigma_equiv (sigma_compose f g) (sigma_compose f' g').
Proof.
  destruct X as [i x], Y as [j y], Z as [k z]; simpl in *.
  destruct f as [e1 f1], f' as [e2 f2], Hf as [p Hp].
  destruct g as [d1 g1], g' as [d2 g2], Hg as [q Hq]; simpl in *.
  destruct p, q; simpl in *.
  destruct e1; simpl in *.
  exists eq_refl; simpl.
  now rewrite Hp, Hq.
Qed.

(* [id ∘ f] REDUCES, because [sigma_compose] matches on the index proof
   of its first argument and the identity's is [eq_refl]. *)
Lemma sigma_id_left@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {X Y : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom X Y) : sigma_equiv (sigma_compose (sigma_id Y) f) f.
Proof.
  destruct X as [i x], Y as [j y], f as [e f]; simpl in *.
  exists eq_refl; simpl; apply id_left.
Qed.

Lemma sigma_id_right@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {X Y : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom X Y) : sigma_equiv (sigma_compose f (sigma_id X)) f.
Proof.
  destruct X as [i x], Y as [j y], f as [e f]; simpl in *.
  destruct e; simpl in *.
  exists eq_refl; simpl; apply id_right.
Qed.

Lemma sigma_comp_assoc@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}}
  {X Y Z W : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom Z W) (g : sigma_hom Y Z) (h : sigma_hom X Y) :
  sigma_equiv (sigma_compose f (sigma_compose g h))
              (sigma_compose (sigma_compose f g) h).
Proof.
  destruct X as [i x], Y as [j y], Z as [k z], W as [l w].
  destruct f as [e1 f], g as [e2 g], h as [e3 h]; simpl in *.
  destruct e1, e2, e3; simpl in *.
  exists eq_refl; simpl; apply comp_assoc.
Qed.

Lemma sigma_comp_assoc_sym@{ui uo oh op us} {I : Type@{ui}}
  {C : I → Category@{uo oh op}}
  {X Y Z W : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom Z W) (g : sigma_hom Y Z) (h : sigma_hom X Y) :
  sigma_equiv (sigma_compose (sigma_compose f g) h)
              (sigma_compose f (sigma_compose g h)).
Proof.
  destruct X as [i x], Y as [j y], Z as [k z], W as [l w].
  destruct f as [e1 f], g as [e2 g], h as [e3 h]; simpl in *.
  destruct e1, e2, e3; simpl in *.
  exists eq_refl; simpl; apply comp_assoc_sym.
Qed.

(** ** The coproduct category *)

(* The explicit universe binders are load-bearing; see header point 4. *)
Definition SigmaCat@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) : Category@{us oh op} := {|
  obj := sigma_obj@{ui uo oh op us} C;
  hom := @sigma_hom@{ui uo oh op us} I C;
  homset := fun X Y =>
    {| equiv := @sigma_equiv@{ui uo oh op us} I C X Y
     ; setoid_equiv := sigma_equiv_Equivalence@{ui uo oh op us} X Y |};
  id := @sigma_id@{ui uo oh op us} I C;
  compose := @sigma_compose@{ui uo oh op us} I C;
  compose_respects := fun X Y Z f f' Hf g g' Hg =>
    sigma_compose_respects f f' Hf g g' Hg;
  id_left := @sigma_id_left@{ui uo oh op us} I C;
  id_right := @sigma_id_right@{ui uo oh op us} I C;
  comp_assoc := @sigma_comp_assoc@{ui uo oh op us} I C;
  comp_assoc_sym := @sigma_comp_assoc_sym@{ui uo oh op us} I C
|}.

(** ** The injections *)

Definition sigma_inj_obj@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) (x : C i) :
  sigma_obj@{ui uo oh op us} C := (i; x).

Definition sigma_inj_map@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) {x y : C i} (f : x ~> y) :
  sigma_hom (sigma_inj_obj@{ui uo oh op us} C i x)
            (sigma_inj_obj@{ui uo oh op us} C i y) := (eq_refl; f).

Lemma sigma_inj_map_respects@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) {x y : C i} (f g : x ~> y) :
  f ≈ g → sigma_equiv (sigma_inj_map@{ui uo oh op us} C i f)
                      (sigma_inj_map@{ui uo oh op us} C i g).
Proof. intros H; exists eq_refl; exact H. Qed.

Lemma sigma_inj_map_id@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) (x : C i) :
  sigma_equiv (sigma_inj_map@{ui uo oh op us} C i (@id (C i) x))
              (sigma_id (sigma_inj_obj@{ui uo oh op us} C i x)).
Proof. exists eq_refl; reflexivity. Qed.

Lemma sigma_inj_map_comp@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) {x y z : C i}
  (f : y ~> z) (g : x ~> y) :
  sigma_equiv (sigma_inj_map@{ui uo oh op us} C i (f ∘ g))
              (sigma_compose (sigma_inj_map@{ui uo oh op us} C i f)
                             (sigma_inj_map@{ui uo oh op us} C i g)).
Proof. exists eq_refl; reflexivity. Qed.

Definition SigmaCat_inj@{ui uo oh op us} {I : Type@{ui}}
  (C : I → Category@{uo oh op}) (i : I) :
  C i ⟶ SigmaCat@{ui uo oh op us} C :=
  @Build_Functor (C i) (SigmaCat@{ui uo oh op us} C)
    (sigma_inj_obj@{ui uo oh op us} C i)
    (fun x y f => sigma_inj_map@{ui uo oh op us} C i f)
    (fun x y f g H => sigma_inj_map_respects C i f g H)
    (fun x => sigma_inj_map_id C i x)
    (fun x y z f g => sigma_inj_map_comp C i f g).

(* Across summands the hom is EMPTY, and it is empty for the only
   reason it could be: the index equality it carries is. *)
Lemma sigma_hom_cross_empty {I : Type} (C : I → Category)
  {X Y : SigmaCat C} (H : `1 X = `1 Y → False) : (X ~> Y) → False.
Proof. intros [e _]; exact (H e). Qed.

(* An empty index leaves the coproduct with no objects at all. *)
Lemma SigmaCat_empty_no_obj (C : Empty_set → Category) :
  obj[SigmaCat C] → False.
Proof. intros [i _]; destruct i. Qed.

(** ** The case functor and the universal property *)

(* A family of functors out of the summands assembles into one functor
   out of the coproduct.  On a morphism the match eliminates the index
   proof: in the [eq_refl] branch source and target lie in the same
   summand and the answer is that summand's functor applied to the
   (now untransported) morphism. *)
Definition sigma_case_obj@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) (X : sigma_obj@{ui uo oh op us} C) : D :=
  F (`1 X) (`2 X).

Definition sigma_case_map@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) {X Y : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom X Y) :
  sigma_case_obj@{ui uo oh op us do dh dp} F X ~>
  sigma_case_obj@{ui uo oh op us do dh dp} F Y :=
  (match `1 f as e0 in _ = m
     return ∀ y0 : C m, (ob_cast C e0 (`2 X) ~> y0) →
            (F (`1 X) (`2 X) ~> F m y0)
   with
   | eq_refl => fun y0 h => fmap[F (`1 X)] h
   end) (`2 Y) (`2 f).

Lemma sigma_case_map_respects@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) {X Y : sigma_obj@{ui uo oh op us} C}
  (f g : sigma_hom X Y) (H : sigma_equiv f g) :
  sigma_case_map@{ui uo oh op us do dh dp} F f
    ≈ sigma_case_map@{ui uo oh op us do dh dp} F g.
Proof.
  destruct X as [i x], Y as [j y]; simpl in *.
  destruct f as [e1 f], g as [e2 g], H as [p Hp]; simpl in *.
  destruct p; simpl in *.
  destruct e1; simpl in *.
  exact (@fmap_respects _ _ (F i) x y f g Hp).
Qed.

Lemma sigma_case_map_id@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) (X : sigma_obj@{ui uo oh op us} C) :
  sigma_case_map@{ui uo oh op us do dh dp} F (sigma_id X) ≈ id.
Proof. destruct X as [i x]; simpl; apply fmap_id. Qed.

Lemma sigma_case_map_comp@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) {X Y Z : sigma_obj@{ui uo oh op us} C}
  (f : sigma_hom Y Z) (g : sigma_hom X Y) :
  sigma_case_map@{ui uo oh op us do dh dp} F (sigma_compose f g)
    ≈ sigma_case_map@{ui uo oh op us do dh dp} F f
        ∘ sigma_case_map@{ui uo oh op us do dh dp} F g.
Proof.
  destruct X as [i x], Y as [j y], Z as [k z]; simpl in *.
  destruct f as [e1 f], g as [e2 g]; simpl in *.
  destruct e1, e2; simpl in *.
  apply fmap_comp.
Qed.

Definition SigmaCat_case@{ui uo oh op us do dh dp} {I : Type@{ui}}
  {C : I → Category@{uo oh op}} {D : Category@{do dh dp}}
  (F : ∀ i : I, C i ⟶ D) : SigmaCat@{ui uo oh op us} C ⟶ D :=
  @Build_Functor (SigmaCat@{ui uo oh op us} C) D
    (sigma_case_obj@{ui uo oh op us do dh dp} F)
    (fun X Y f => sigma_case_map@{ui uo oh op us do dh dp} F f)
    (fun X Y f g H => sigma_case_map_respects F f g H)
    (fun X => sigma_case_map_id F X)
    (fun X Y Z f g => sigma_case_map_comp F f g).

(* The triangle.  Both actions of the composite are DEFINITIONALLY
   those of [F i] — the two Examples below pin that at [eq_refl] — so
   the witnessing natural isomorphism is the identity family, as in
   [PiCat_Pair_Proj]. *)
Example sigma_case_inj_fobj {I : Type} {C : I → Category} {D : Category}
  (F : ∀ i : I, C i ⟶ D) (i : I) :
  fobj[SigmaCat_case F ◯ SigmaCat_inj C i] = fobj[F i] := eq_refl.

Example sigma_case_inj_fmap {I : Type} {C : I → Category} {D : Category}
  (F : ∀ i : I, C i ⟶ D) (i : I) (x y : C i) (f : x ~> y) :
  fmap[SigmaCat_case F ◯ SigmaCat_inj C i] f = fmap[F i] f := eq_refl.

(* The whole functor RECORD is not recovered, however: the composite
   rebuilds the three law fields, and they are distinct opaque terms.
   Measured, not assumed. *)
Fail Example sigma_case_inj_strict {I : Type} {C : I → Category}
  {D : Category} (F : ∀ i : I, C i ⟶ D) (i : I) :
  SigmaCat_case F ◯ SigmaCat_inj C i = F i := eq_refl.

Lemma SigmaCat_case_inj {I : Type} {C : I → Category} {D : Category}
  (F : ∀ i : I, C i ⟶ D) (i : I) :
  SigmaCat_case F ◯ SigmaCat_inj C i ≈ F i.
Proof.
  simpl; exists (fun _ => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right; reflexivity.
Qed.

(* Uniqueness, up to [Cat]'s hom-equivalence.  NO hypothesis: the
   comparison's components are read off the given family, and its
   naturality square is proved by eliminating the index proof of the
   morphism it is stated at, which reduces it to the naturality of the
   given family at that index. *)
Lemma SigmaCat_case_unique {I : Type} {C : I → Category} {D : Category}
  (F : ∀ i : I, C i ⟶ D) (G : SigmaCat C ⟶ D) :
  (∀ i : I, G ◯ SigmaCat_inj C i ≈ F i) → G ≈ SigmaCat_case F.
Proof.
  intros H.
  unshelve eexists.
  - intros [i x]; exact (`1 (H i) x).
  - intros [i x] [j y] [e f]; simpl in *.
    destruct e; simpl in *.
    exact (`2 (H i) x y f).
Qed.

(* The universal property, bundled: existence is the case functor with
   its triangle, uniqueness the lemma above. *)
Lemma SigmaCat_ump {I : Type} {C : I → Category} {D : Category}
  (F : ∀ i : I, C i ⟶ D) :
  ∃! G : SigmaCat C ⟶ D, ∀ i : I, G ◯ SigmaCat_inj C i ≈ F i.
Proof.
  unshelve eapply Build_Unique.
  - exact (SigmaCat_case F).
  - exact (SigmaCat_case_inj F).
  - intros G HG; symmetry; exact (SigmaCat_case_unique F G HG).
Qed.

(** ** Fullness and faithfulness of the injections *)

(* Uniqueness of identity proofs on the index, in the Streicher-K form
   Theory/OGraph.v's [NodeUIP] uses — which is also the form the
   stdlib's [UIP_shift] consumes. *)
Definition IdxUIP (I : Type) : Type := ∀ (i : I) (p : i = i), p = eq_refl.

Lemma IdxUIP_pair {I : Type} (U : IdxUIP I) {i j : I} (p q : i = j) : p = q.
Proof. destruct p; symmetry; apply U. Qed.

(* Faithfulness for a GENERAL family spends [IdxUIP] one level up: the
   hypothesis hands over an equality [p] between two proofs of [i = i],
   and only [UIP_shift] — the axiom-free "a type with unique identity
   proofs has unique identity-proof-proofs" of the stdlib's
   EqdepFacts — makes [p] itself [eq_refl], which is what erases the
   transport. *)
Program Definition SigmaCat_inj_Faithful {I : Type} (C : I → Category)
  (U : IdxUIP I) (i : I) : Faithful (SigmaCat_inj C i) := {|
  fmap_inj := _
|}.
Next Obligation.
  intros I C U i x y f g [p Hp]; simpl in *.
  rewrite (UIP_shift I U i eq_refl p) in Hp.
  exact Hp.
Qed.

(* Faithfulness for a CONSTANT family is free.  The case functor of the
   constantly-identity family retracts the injection — definitionally,
   by [sigma_case_inj_fmap] — and a functor whose composite with
   another is faithful is faithful. *)
Lemma Faithful_cancel {C D E : Category} (F : C ⟶ D) (G : D ⟶ E) :
  Faithful (G ◯ F) → Faithful F.
Proof.
  intros H; construct.
  apply (@fmap_inj _ _ (G ◯ F) H); simpl.
  now rewrite X.
Qed.

Definition SigmaCat_const_retract {I : Type} (D : Category) (i : I) :
  Faithful (SigmaCat_case (fun _ : I => Id[D])
              ◯ SigmaCat_inj (fun _ : I => D) i).
Proof.
  constructor; intros x y f g H; exact H.
Defined.

Definition SigmaCat_const_inj_Faithful {I : Type} (D : Category) (i : I) :
  Faithful (SigmaCat_inj (fun _ : I => D) i) :=
  Faithful_cancel _ _ (SigmaCat_const_retract D i).

(* Fullness needs [IdxUIP] outright: the chosen preimage of a morphism
   is its second component read back through the index proof's collapse
   to [eq_refl]. *)
Program Definition SigmaCat_inj_Full {I : Type} (C : I → Category)
  (U : IdxUIP I) (i : I) : Full (SigmaCat_inj C i) := {|
  prefmap := fun x y g => mor_cast C (U i (`1 g)) (`2 g)
|}.
Next Obligation.
  intros I C U i x y g; simpl.
  exists (eq_sym (U i (`1 g))); simpl.
  rewrite mor_cast_sym; reflexivity.
Qed.

(* …and the hypothesis is NECESSARY, not merely convenient.  Given an
   object [x] of the [i]-summand whose hom-sets out of every
   loop-transport of [x] are inhabited — as they are for the terminal
   category, the instantiation carried out in Instance/Cat/Coproduct.v
   — fullness of the injection at [i] ENTAILS that every loop at [i] is
   [eq_refl].  The chosen preimage's own section condition supplies an
   equality [eq_refl = e] for an arbitrary loop [e], and that is
   Streicher's K at [i]. *)
Theorem sigma_inj_Full_forces_UIP {I : Type} (C : I → Category) (i : I)
  (x : C i) (pt : ∀ e : i = i, ob_cast C e x ~> x)
  (H : Full (SigmaCat_inj C i)) : ∀ e : i = i, e = eq_refl.
Proof.
  intros e.
  exact (eq_sym (`1 (@fmap_sur _ _ _ H x x (e; pt e)))).
Qed.

(** ** The singleton index *)

(* Over a one-element index the coproduct collapses onto its single
   summand.  The two comparison functors are the case functor of the
   constantly-identity family and the injection; one composite is the
   identity with identity components, and the other needs uniqueness of
   identity proofs on [poly_unit], which Hedberg supplies from its
   (trivial) decidable equality, so nothing is assumed. *)
Definition SigmaCat_unit_collapse {D : Category} :
  SigmaCat (fun _ : poly_unit => D) ⟶ D := SigmaCat_case (fun _ => Id[D]).

Definition SigmaCat_unit_expand {D : Category} :
  D ⟶ SigmaCat (fun _ : poly_unit => D) :=
  SigmaCat_inj (fun _ : poly_unit => D) ttt.

Definition sigma_poly_unit_dec (x y : poly_unit) : {x = y} + {x <> y} :=
  match x, y with ttt, ttt => left eq_refl end.

Definition poly_unit_IdxUIP : IdxUIP poly_unit :=
  fun i p => Eqdep_dec.UIP_dec sigma_poly_unit_dec p eq_refl.

Lemma SigmaCat_unit_round_l {D : Category} :
  SigmaCat_unit_collapse ◯ SigmaCat_unit_expand ≈ Id[D].
Proof.
  simpl; exists (fun _ => iso_id).
  intros x y f; simpl.
  rewrite id_left, id_right; reflexivity.
Qed.

Lemma SigmaCat_unit_round_r {D : Category} :
  SigmaCat_unit_expand ◯ SigmaCat_unit_collapse
    ≈ Id[SigmaCat (fun _ : poly_unit => D)].
Proof.
  unshelve eexists.
  - intros [u x]; destruct u; exact iso_id.
  - intros [u x] [v y] [e f]; destruct u, v; simpl in *.
    assert (He : e = eq_refl) by apply poly_unit_IdxUIP.
    subst e; simpl.
    exists eq_refl; simpl.
    rewrite id_left, id_right; reflexivity.
Qed.
