Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.

Generalizable All Variables.

(** * Wide pullbacks, and products as wide pullbacks over a terminal object *)

(* nLab:      https://ncatlab.org/nlab/show/wide+pullback
   nLab:      https://ncatlab.org/nlab/show/pullback
   Wikipedia: https://en.wikipedia.org/wiki/Pullback_(category_theory)

   A WIDE PULLBACK replaces the two legs of an ordinary pullback by an
   I-indexed family of them.  Given objects A i and a common codomain z
   with maps f i : A i ~> z, a wide pullback is an object P carrying
   projections p i : P ~> A i on which all the composites agree,

       ∀ i j,  f i ∘ p i ≈ f j ∘ p j,

   universal with that property: every competing family q i : Q ~> A i
   whose composites agree factors through the p i by a unique mediator.
   At I = 2 this is the ordinary pullback of a cospan; at I = 1 it is the
   identity; at I = 0 it is the terminal object (see below).

   THE HEADLINE is Riehl's observation (Category Theory in Context, 2nd
   ed., §3.5, printed p. 114 = PDF p. 134, catalogued as riehl:3.5:lem15):
   the pullback of A → * ← B over a TERMINAL object is the binary product,
   and more generally the I-indexed PRODUCT of a family is the WIDE
   PULLBACK of the maps A i → *.  Her reason is entirely about the shape of
   the condition rather than about any construction: a terminal codomain
   imposes NO commutativity condition, because any two maps into 1 agree by
   [one_unique], so a cone over that diagram is exactly an I-indexed family
   of maps and nothing more.  Her corollary — a category with pullbacks and
   a terminal object has all binary, hence all finite, products — is the
   binary case of the same remark and is a companion file,
   Structure/Pullback/Reduction.v; this file owns the WIDE generalization.

   WHERE [one_unique] IS SPENT, and it is spent TWICE, in complementary
   directions.  In [wide_pullback_product] it DISCHARGES the commutativity
   field: the goal [one ∘ p i ≈ one ∘ p j] is closed by [one_unique]
   directly, and the universal property is then [iprod_desc] with the
   competing family's hypothesis DISCARDED unused.  In the converse
   [product_wide_pullback] it MANUFACTURES that same hypothesis: to invoke
   [wpull_ump] on an arbitrary family [pi] one must supply
   [∀ i j, one ∘ pi i ≈ one ∘ pi j], and [one_unique] supplies it.  Both
   uses are single, named [apply (@one_unique C T)] steps, deliberately not
   folded into [cat] or any other automation, so that the one step carrying
   Riehl's argument is visible in the proof script.

   THE EMPTY INDEX IS A REAL BOUNDARY, AND THIS FORMULATION GETS IT RIGHT.
   With I empty the [∀ i j] condition is vacuous and the mediator's
   condition [∀ i, p i ∘ u ≈ q i] is vacuous too, so the record degenerates
   to "every object has exactly one map to P" — which is terminality.
   That is proved in BOTH directions, [wide_pullback_empty_terminal] and
   [terminal_wide_pullback_empty], and it is a biconditional at fixed data:
   over an empty index [IsWidePullback f P p] holds exactly when P is
   terminal, for the (necessarily empty) family p and ANY codomain z.  Both
   directions genuinely consume [Hempty] — the forward one to build the
   empty competing family to instantiate [wpull_ump] at, the backward one
   to make both the commutativity field and the mediator's condition
   vacuous — so neither is an artifact of the proof.

   This is worth contrasting with the sibling construction.
   Structure/Equalizer/Wide.v's empty case is a SHARPNESS OBSTRUCTION: its
   elementary record is satisfied there by [id[x]], which does NOT agree
   with the limit over the same shape, and that file proves the mismatch by
   deriving an inhabitant of an empty hom-set.  Here the empty case is
   instead a clean IDENTIFICATION.

   AN EARLIER DRAFT OF THIS HEADER EXPLAINED THAT CONTRAST BY SAYING THAT A
   WIDE FORK "CARRIES A SECOND LEG WHICH THE EMPTY CONDITION LEAVES
   UNCONSTRAINED".  THAT IS FALSE, AND IT IS FALSE ABOUT ANOTHER FILE'S
   RECORD, SO IT IS RECORDED HERE AS BAD EVIDENCE RATHER THAN QUIETLY
   DELETED.  [IsWideEqualizer] (Structure/Equalizer/Wide.v:141) has exactly
   TWO fields and ONE leg [e : q ~> x]; it carries no second leg, and that
   file says three separate times that a leg-carrying record is NOT built
   there.  The second leg belongs to the CONE, and is MANUFACTURED from a
   chosen index as [fs i0 ∘ h] -- which is precisely why that development
   needs a pointed section.  The polarity of the original explanation was
   therefore inverted: the fork's LACK of a second leg is the cause, not its
   possession of one.

   What should be said instead is weaker and is the honest statement.  The
   sibling's empty case is an obstruction RELATIVE TO ITS LIMIT
   PRESENTATION.  This file builds no limit presentation at all (see NOT
   DELIVERED below), so no analogous disagreement can arise here.  The
   contrast is therefore NOT evidence that the wide-pullback notion is
   better behaved; it partly reflects that less is claimed here, and a
   wide-cospan shape would retain its codomain object at I = ∅ much as the
   fork's does.
   Nothing here needs a chosen inhabitant of I, so this file has no pointed
   section at all and no analogue of that file's [i0] hypothesis.

   STRENGTHS, MEASURED STRICT-FIRST.

     - BOTH round trips between [IsWidePullback] and the bundled
       [WidePullback] close by [eq_refl], on the WHOLE RECORD, in BOTH
       directions ([wide_pullback_predicate_round],
       [wide_pullback_bundled_round]).  Both records have primitive
       projections with eta (Lib/Foundation.v's [Set Primitive Projections]
       reaches them), so the two conversions are definitional inverses and
       not merely mutually inverse up to ≈.
     - The BINARY round trip is REFUTED at [eq_refl] on the whole record,
       and the obstruction is LOCATED rather than guessed:
       [wide_pullback_binary_commutes] shows the [is_pullback_commutes]
       FIELD does convert by [eq_refl] (the [∀ i j] condition iota-reduces
       at the literals [true] and [false]), so what blocks the record
       equality is the [is_pullback_ump] field alone, which is rebuilt
       through a fresh [Build_Unique].  The whole-record equality is
       therefore stated nowhere below; it is a negative for a [Fail] probe.
     - [wide_pullback_unique] delivers a bare [≅], exactly as its binary
       donor [pullback_unique] and its sibling [wide_equalizer_unique] do.
       It is NOT upgraded to a leg-carrying essential uniqueness in the
       manner of Structure/Limit/Unique.v.

   UNIVERSES, read from the CONSTRAINT BLOCKS and not off the binders
   (reproduce with [Set Printing Universes. Print IsWidePullback. About
   wide_pullback_product.]).  [IsWidePullback@{u u0 u1 u2}] is over
   [C : Category@{u1 u2 u2}] and [I : Type@{u}] with constraint block
   [u <= u0, u2 <= u0], where u0 is the record's own sort level.  Two
   readings matter.

     - The INDEX universe u and the OBJECT universe u1 are INDEPENDENT: u1
       occurs in no constraint at all, and u is merely BOUNDED by the sort
       level, not identified with anything.  This is not inferred from the
       binder: it is checked by two probe sections that declare the levels
       SEPARATELY and impose a STRICT inequality, [Constraint uo < ui] and
       [Constraint ui < uo], and the record elaborates under BOTH.  (An
       unannotated probe collapses the two by minimization and would have
       reported nothing.)
     - The hom and proof universes ARE identified, and that identification
       is REAL but INHERITED.  A probe declaring [Constraint uh < up]
       rejects [IsWidePullback]; the SAME probe rejects the donor
       [IsIndexedProduct] just as flatly, while a control at the same
       levels accepts the bare hom-setoid statement [f ≈ g].  So the
       identification belongs to the house's [Record … {C : Category}]
       idiom that this file shares with its donor, is not a consequence of
       the setoid on homs, and is not introduced here.  Correspondingly
       [wide_pullback_product]'s constraint block is [u <= u0, u2 <= u0] —
       the same block [IsIndexedProduct] itself carries.

   NON-VACUITY.  [Sets_wide_pullback_over_one] instantiates the headline at
   [Sets], exhibiting [Sets_iprod_obj F] with its projections as a wide
   pullback of the family [F i → 1].  Its universe constraint is INFERRED --
   there is no annotation on it, an earlier draft of this header said there
   was -- and identifies
   the index universe with the carrier universe of [Sets]; that is the
   DONOR's constraint, documented in Instance/Sets/Products.v's own header
   for [Sets_HasIndexedProducts], and the probes above show this file's
   record does not force it.  The [Instance/Sets] dependency is taken for
   this witness alone; the sibling takes [Instance/Parallel] and
   [Instance/Two] on the same footing.

   NOT DELIVERED, and the scope of each statement is this file rather than
   the tree.  No limit presentation: nothing below builds the wide-cospan
   shape category or relates [IsWidePullback] to [Limit] of a diagram over
   it, so there is no analogue here of Structure/Pullback/Limit.v's
   reconciliation and none of the sibling's limit round trips.  No
   [HasWidePullbacks] instance for any concrete category — the class is
   declared and left uninhabited, and [Sets_wide_pullback_over_one] is a
   single family, not an instance.  No wide-pullback stability, pasting, or
   preservation statements.  No wide PUSHOUT dual.  No claim that the
   binary specialization below agrees with whatever the other delegate's
   Structure/Pullback/Reduction.v proves: the two files are independent and
   nothing here cites that one. *)

(** ** The elementary universal property *)

(* [P] with projections [p] is a wide pullback of the family [f] when all
   the composites into the common codomain agree and every family agreeing
   in the same way factors uniquely.  The commutativity condition
   quantifies over PAIRS of indices, exactly as [wfork_eq] does in
   Structure/Equalizer/Wide.v; no distinguished index is named, so nothing
   in this record requires I to be inhabited. *)
Record IsWidePullback {C : Category} {I : Type} {A : I → C} {z : C}
  (f : ∀ i : I, A i ~> z) (P : C) (p : ∀ i : I, P ~> A i) := {
  (* every leg is carried to the common codomain in the same way *)
  wpull_commutes : ∀ i j : I, f i ∘ p i ≈ f j ∘ p j;

  (* universal property: every jointly agreeing family factors uniquely *)
  wpull_ump {Q : C} (q : ∀ i : I, Q ~> A i)
    (Hq : ∀ i j : I, f i ∘ q i ≈ f j ∘ q j) :
    ∃! u : Q ~> P, ∀ i : I, p i ∘ u ≈ q i
}.

Arguments wpull_commutes {_ _ _ _ _ _ _} _ _ _.
Arguments wpull_ump {_ _ _ _ _ _ _} _ {_} _ _.

(** ** The bundled record *)

(* The apex-carrying form, shaped after [Pullback] of Structure/Pullback.v
   rather than after the ∃-valued [HasWideEqualizers] of the sibling: a
   wide pullback is CHOSEN here, so consumers read the object off the
   record instead of destructing an existential. *)
Record WidePullback {C : Category} {I : Type} {A : I → C} {z : C}
  (f : ∀ i : I, A i ~> z) := {
  WPull : C;                             (* the wide pullback object *)
  wide_pullback_proj : ∀ i : I, WPull ~> A i;   (* the projections *)

  wide_pullback_commutes : ∀ i j : I,
    f i ∘ wide_pullback_proj i ≈ f j ∘ wide_pullback_proj j;

  ump_wide_pullbacks : ∀ (Q : C) (q : ∀ i : I, Q ~> A i),
    (∀ i j : I, f i ∘ q i ≈ f j ∘ q j)
    → ∃! u : Q ~> WPull, ∀ i : I, wide_pullback_proj i ∘ u ≈ q i
}.

Arguments WPull {_ _ _ _ _} _.
Arguments wide_pullback_proj {_ _ _ _ _} _ _.
Arguments wide_pullback_commutes {_ _ _ _ _} _ _ _.
Arguments ump_wide_pullbacks {_ _ _ _ _} _ _ _ _.

Coercion WPull : WidePullback >-> obj.

(* Both conversions are field repackagings, mirroring
   [pullback_is_pullback] and [is_pullback_pullback] of
   Theory/Morphisms/Stability.v. *)

Definition wide_pullback_is_pullback {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} (W : WidePullback f) :
  IsWidePullback f (WPull W) (wide_pullback_proj W) :=
  {| wpull_commutes := wide_pullback_commutes W
   ; wpull_ump      := fun Q q Hq => ump_wide_pullbacks W Q q Hq |}.

Definition is_wide_pullback_pullback {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} {P : C} {p : ∀ i : I, P ~> A i}
  (W : IsWidePullback f P p) : WidePullback f :=
  {| WPull                  := P
   ; wide_pullback_proj     := p
   ; wide_pullback_commutes := wpull_commutes W
   ; ump_wide_pullbacks     := fun Q q Hq => wpull_ump W q Hq |}.

(* MEASURED STRICT: both composites are the identity on the nose, on the
   WHOLE record, because both records have primitive projections with eta.
   Neither is merely an equivalence up to ≈. *)

Example wide_pullback_predicate_round {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} {P : C} {p : ∀ i : I, P ~> A i}
  (W : IsWidePullback f P p) :
  wide_pullback_is_pullback (is_wide_pullback_pullback W) = W := eq_refl.

Example wide_pullback_bundled_round {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} (W : WidePullback f) :
  is_wide_pullback_pullback (wide_pullback_is_pullback W) = W := eq_refl.

(* A category has all wide pullbacks when every family over a common
   codomain carries one.  As with [HasIndexedProducts], the index [Type] is
   a universe PARAMETER of the class and not a quantifier over every
   universe; a consumer whose index is a hom-type instantiates it there. *)
Class HasWidePullbacks (C : Category) := {
  wide_pullback {I : Type} {A : I → C} {z : C} (f : ∀ i : I, A i ~> z) :
    WidePullback f
}.

Arguments wide_pullback {C _ I A z} f.

(** ** The projections are jointly monic *)

(* Two maps into the apex agreeing after every projection are equal: both
   are the mediator of one and the same family.  As with the sibling's
   [wide_equalizer_monic], no index is ever named, so this holds for every
   index type, the empty one included — where it degenerates to the (then
   true) statement that any two maps into a terminal object agree. *)
Lemma wide_pullback_jointly_monic {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} {P : C} {p : ∀ i : I, P ~> A i}
  (W : IsWidePullback f P p) {Q : C} (u v : Q ~> P)
  (Hd : ∀ i : I, p i ∘ u ≈ p i ∘ v) : u ≈ v.
Proof.
  assert (Hq : ∀ i j : I, f i ∘ (p i ∘ u) ≈ f j ∘ (p j ∘ u)).
  { intros i j.
    rewrite !comp_assoc.
    now rewrite (wpull_commutes W i j). }
  transitivity (unique_obj (wpull_ump W (fun i => p i ∘ u) Hq)).
  - symmetry.
    apply (uniqueness (wpull_ump W (fun i => p i ∘ u) Hq)).
    intro i; reflexivity.
  - apply (uniqueness (wpull_ump W (fun i => p i ∘ u) Hq)).
    intro i; symmetry; apply Hd.
Qed.

(** ** Wide pullbacks are unique up to isomorphism *)

(* The binary argument verbatim, one index at a time: each apex mediates
   into the other along the other's projections, and the round trips agree
   with the canonical self-mediator, which is the identity. *)
Lemma wide_pullback_unique {C : Category} {I : Type} {A : I → C} {z : C}
  {f : ∀ i : I, A i ~> z} {P1 P2 : C}
  {p1 : ∀ i : I, P1 ~> A i} {p2 : ∀ i : I, P2 ~> A i}
  (W1 : IsWidePullback f P1 p1) (W2 : IsWidePullback f P2 p2) : P1 ≅ P2.
Proof.
  pose proof (wpull_ump W2 p1 (wpull_commutes W1)) as D12.
  pose proof (wpull_ump W1 p2 (wpull_commutes W2)) as D21.
  pose proof (wpull_ump W1 p1 (wpull_commutes W1)) as D11.
  pose proof (wpull_ump W2 p2 (wpull_commutes W2)) as D22.
  unshelve refine {| to := unique_obj D12; from := unique_obj D21 |}.
  - transitivity (unique_obj D22).
    + symmetry.
      apply (uniqueness D22).
      intro i.
      rewrite comp_assoc, (unique_property D12 i).
      exact (unique_property D21 i).
    + apply (uniqueness D22).
      intro i; apply id_right.
  - transitivity (unique_obj D11).
    + symmetry.
      apply (uniqueness D11).
      intro i.
      rewrite comp_assoc, (unique_property D21 i).
      exact (unique_property D12 i).
    + apply (uniqueness D11).
      intro i; apply id_right.
Defined.

(** ** The empty index: the wide pullback is the terminal object *)

(* Over an empty index there is exactly one family of legs into any apex,
   namely the empty function. *)
Definition wpull_empty_legs {C : Category} {I : Type} {A : I → C}
  (Hempty : I → False) (Q : C) : ∀ i : I, Q ~> A i.
Proof. intro i; destruct (Hempty i). Defined.

(* ... and it agrees with itself vacuously. *)
Lemma wpull_empty_comm {C : Category} {I : Type} {A : I → C} {z : C}
  (f : ∀ i : I, A i ~> z) (Hempty : I → False) {Q : C}
  (q : ∀ i : I, Q ~> A i) : ∀ i j : I, f i ∘ q i ≈ f j ∘ q j.
Proof. intros i j; destruct (Hempty i). Qed.

(* So a wide pullback over an empty index is a terminal object: the
   mediator exists for every Q, and its defining condition being vacuous,
   EVERY map into P satisfies it and is therefore that mediator. *)
Lemma wide_pullback_empty_terminal {C : Category} {I : Type} {A : I → C}
  {z : C} {f : ∀ i : I, A i ~> z} {P : C} {p : ∀ i : I, P ~> A i}
  (Hempty : I → False) (W : IsWidePullback f P p) : IsTerminalObj P.
Proof.
  intro Q.
  pose proof (wpull_ump W (wpull_empty_legs Hempty Q)
                (wpull_empty_comm f Hempty (wpull_empty_legs Hempty Q)))
    as U.
  unshelve eapply Build_Unique.
  - exact (unique_obj U).
  - exact Logic.I.
  - intros v _.
    apply (uniqueness U).
    intro i; destruct (Hempty i).
Defined.

(* Conversely a terminal object is a wide pullback of the empty family over
   ANY codomain, with its (empty) family of projections.  Emptiness is used
   twice, once for each field. *)
Definition terminal_wide_pullback_empty {C : Category} {I : Type}
  {A : I → C} {z : C} (f : ∀ i : I, A i ~> z) {P : C}
  (p : ∀ i : I, P ~> A i) (Hempty : I → False) (H : IsTerminalObj P) :
  IsWidePullback f P p.
Proof.
  unshelve refine {| wpull_commutes := _ |}.
  - intros i j; destruct (Hempty i).
  - intros Q q Hq.
    unshelve eapply Build_Unique.
    + exact (is_terminal_one H).
    + intro i; destruct (Hempty i).
    + intros v _; apply (is_terminal_unique H).
Defined.

(** ** Riehl's lemma: products are wide pullbacks over a terminal object *)

(* An indexed product IS the wide pullback of the family of unique maps to
   the terminal object.  The commutativity condition is discharged by
   [one_unique] — that single step is the whole of Riehl's argument — and
   the universal property is then [iprod_desc] with the competing family's
   agreement hypothesis discarded, since a terminal codomain constrains
   nothing. *)
Theorem wide_pullback_product {C : Category} `{T : @Terminal C}
  {I : Type} (A : I → C) (P : C) (p : ∀ i : I, P ~> A i)
  (H : IsIndexedProduct A P p) :
  IsWidePullback (fun i : I => @one C T (A i)) P p.
Proof.
  unshelve refine {| wpull_commutes := _ |}.
  - (* both composites are maps into 1, hence equal *)
    intros i j.
    apply (@one_unique C T).
  - (* the hypothesis [Hq] is discarded: it says nothing over 1 *)
    intros Q q _.
    exact (iprod_desc H q).
Defined.

(* ... and conversely.  Here [one_unique] runs the other way: it is what
   MANUFACTURES the agreement hypothesis that [wpull_ump] demands of an
   arbitrary competing family, which is exactly why the two universal
   properties have the same content over a terminal codomain. *)
Theorem product_wide_pullback {C : Category} `{T : @Terminal C}
  {I : Type} (A : I → C) (P : C) (p : ∀ i : I, P ~> A i)
  (W : IsWidePullback (fun i : I => @one C T (A i)) P p) :
  IsIndexedProduct A P p.
Proof.
  unshelve refine {| iprod_desc := _ |}.
  intros c pi.
  refine (wpull_ump W pi _).
  (* the condition Riehl observes to be no condition at all *)
  intros i j.
  apply (@one_unique C T).
Defined.

(** ** The binary specialization *)

(* At I := bool the wide notion is the ordinary pullback.  The family and
   the two leg families are written with an explicit [return] annotation so
   that [two_fam x y true] and [two_fam x y false] reduce by iota, which is
   what lets the four-case [∀ i j] condition collapse to the single square
   and back. *)
Definition two_fam {C : Category} (x y : C) : bool → C :=
  fun b => if b then x else y.

Definition two_maps {C : Category} {x y z : C} (f : x ~> z) (g : y ~> z) :
  ∀ b : bool, two_fam x y b ~> z :=
  fun b => if b as b' return (two_fam x y b' ~> z) then f else g.

Definition two_legs {C : Category} {x y P : C} (p1 : P ~> x) (p2 : P ~> y) :
  ∀ b : bool, P ~> two_fam x y b :=
  fun b => if b as b' return (P ~> two_fam x y b') then p1 else p2.

Theorem wide_pullback_binary {C : Category} {x y z : C}
  {f : x ~> z} {g : y ~> z} {P : C} {p1 : P ~> x} {p2 : P ~> y}
  (W : IsWidePullback (two_maps f g) P (two_legs p1 p2)) :
  IsPullback f g P p1 p2.
Proof.
  unshelve refine {| is_pullback_commutes := _ |}.
  - (* the square is the [∀ i j] condition at [true], [false] *)
    exact (wpull_commutes W true false).
  - intros Q q1 q2 Hq.
    assert (Hc : ∀ i j : bool,
              two_maps f g i ∘ two_legs q1 q2 i
                ≈ two_maps f g j ∘ two_legs q1 q2 j).
    { intros i j; destruct i, j; simpl;
        [ reflexivity | exact Hq | now symmetry | reflexivity ]. }
    pose proof (wpull_ump W (two_legs q1 q2) Hc) as U.
    unshelve eapply Build_Unique.
    + exact (unique_obj U).
    + split.
      * exact (unique_property U true).
      * exact (unique_property U false).
    + intros v [Hv1 Hv2].
      apply (uniqueness U).
      intro b; destruct b; assumption.
Defined.

Theorem binary_wide_pullback {C : Category} {x y z : C}
  {f : x ~> z} {g : y ~> z} {P : C} {p1 : P ~> x} {p2 : P ~> y}
  (H : IsPullback f g P p1 p2) :
  IsWidePullback (two_maps f g) P (two_legs p1 p2).
Proof.
  unshelve refine {| wpull_commutes := _ |}.
  - intros i j; destruct i, j; simpl;
      [ reflexivity
      | exact (is_pullback_commutes H)
      | now symmetry; exact (is_pullback_commutes H)
      | reflexivity ].
  - intros Q q Hq.
    pose proof (is_pullback_ump H Q (q true) (q false) (Hq true false)) as U.
    unshelve eapply Build_Unique.
    + exact (unique_obj U).
    + intro b; destruct b; simpl.
      * exact (fst (unique_property U)).
      * exact (snd (unique_property U)).
    + intros v Hv.
      apply (uniqueness U).
      split; [ exact (Hv true) | exact (Hv false) ].
Defined.

(* MEASURED STRICT, and REFUTED at the whole record: the binary round trip
   is NOT [eq_refl].  This Example localizes the obstruction to a single
   field — the square itself DOES convert, the [∀ i j] condition
   iota-reducing at the two literals — so what fails is [is_pullback_ump]
   alone, rebuilt through a fresh [Build_Unique].  The whole-record
   equality is therefore not stated here. *)
Example wide_pullback_binary_commutes {C : Category} {x y z : C}
  {f : x ~> z} {g : y ~> z} {P : C} {p1 : P ~> x} {p2 : P ~> y}
  (H : IsPullback f g P p1 p2) :
  is_pullback_commutes (wide_pullback_binary (binary_wide_pullback H))
  = is_pullback_commutes H := eq_refl.

(** ** Non-vacuity: the identification at [Sets] *)

(* [Sets] has all indexed products (Instance/Sets/Products.v) and a
   terminal object (Instance/Sets.v), so Riehl's lemma applies: the
   dependent-function setoid ∀ i, F i, with its projections, is a wide
   pullback of the family of unique maps F i → 1.  Nothing is reproved —
   this is [wide_pullback_product] applied to [Sets_IsIndexedProduct]. *)
Definition Sets_wide_pullback_over_one {A : Type} (F : A → obj[Sets]) :
  IsWidePullback (fun i : A => @one Sets Sets_Terminal (F i))
    (Sets_iprod_obj F) (Sets_iprod_proj F) :=
  wide_pullback_product F (Sets_iprod_obj F) (Sets_iprod_proj F)
    (Sets_IsIndexedProduct F).

(* ... and the converse direction is available at the same witness, so the
   two readings of that object genuinely coincide in a concrete category
   rather than only in the abstract statement. *)
Definition Sets_iprod_of_wide_pullback {A : Type} (F : A → obj[Sets]) :
  IsIndexedProduct F (Sets_iprod_obj F) (Sets_iprod_proj F) :=
  product_wide_pullback F (Sets_iprod_obj F) (Sets_iprod_proj F)
    (Sets_wide_pullback_over_one F).
