(** * Set-indexed products of categories *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Two.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §II.3 Exercise 3, printed p. 40 (PDF p. 50) — maclane:II.3:ex3
   nLab:      https://ncatlab.org/nlab/show/product+category

   For a set-indexed family of categories, the product category has as
   objects the choice functions of objects and as arrows the
   componentwise families of arrows, with projection functors satisfying
   the evident universal property: a family of functors into the
   components factors through the product, uniquely up to [Cat]'s
   hom-equivalence — the setoid rendering of the book's on-the-nose
   uniqueness.

     - [PiCat C]: objects [∀ i, C i], homs the dependent families of
       component homs, everything componentwise
     - [PiCat_Proj i]: the projections
     - [PiCat_Pair R]: the pairing ⟨R⟩ of a family [R i : D ⟶ C i],
       with [PiCat_Pair_Proj] the triangle [P i ◯ ⟨R⟩ ≈ R i] — its
       components are [iso_id], the composite being DEFINITIONALLY
       [R i] on both objects and arrows — [PiCat_ump_unique] the
       uniqueness half, and [PiCat_ump] the bundled ∃! (the same
       packaging as Structure/Limit/Product.v's [iprod_ump])

   Design:

   1. ONE CATEGORY INSTANCE FOR THE WHOLE FAMILY.  [C : I → Category]
      forces every member onto the same universe instance of
      [Category], so no per-member level juggling arises; the product's
      objects live at the maximum of [I]'s level and the members'
      object level — and [I]'s level also bounds the HOM universe,
      since a hom is itself an [I]-indexed family — exactly as the
      library's {o h p} polymorphism prescribes.  This is the "set-indexed" of the exercise made
      precise: [I] is a [Type], with no smallness apparatus needed.

   2. CONTRAST WITH Structure/Limit/Product.v.  That file's indexed
      products ([iprod] over Instance/Discrete.v's discrete diagrams)
      are products of OBJECTS INSIDE one category; this file's [PiCat]
      is a product OF CATEGORIES — the same distinction as between
      [Cartesian]'s binary product and Construction/Product.v's [∏].
      The two meet at [Cat]: [PiCat] exhibits the data that would make
      [Cat] complete under set-indexed products, the binary case of
      which is Instance/Cat/Cartesian.v's [Cat_Cartesian].

   3. THE BINARY CASE.  At [I := bool], [PiCat] specializes to a
      category equivalent to [C ∏ D] — a choice function on [bool]
      against a pair — recovering [Cat_Cartesian]'s fork; the
      identification is a NOTE, as in the exercise, rather than a
      formalized equivalence, since nothing downstream consumes it; the
      bridge is real but not free — [prod] is not a primitive record,
      so the pair side needs [fst]/[snd] destructs (the obstruction
      Construction/Product/Special.v documents), and the dependent
      identity family needs explicit match motives. *)

(** ** The product category *)

Program Definition PiCat {I : Type} (C : I → Category) : Category := {|
  obj := ∀ i : I, C i;
  hom := fun f g => ∀ i : I, f i ~> g i;
  homset := fun f g =>
    {| equiv := fun η θ => ∀ i : I, η i ≈ θ i |};
  id := fun f i => id;
  compose := fun f g h η θ i => η i ∘ θ i
|}.
Next Obligation.
  intros I C f g; constructor.
  - intros η i; reflexivity.
  - intros η θ Hηθ i; symmetry; apply Hηθ.
  - intros η θ ρ H1 H2 i.
    transitivity (θ i); [ apply H1 | apply H2 ].
Qed.
Next Obligation.
  intros I C f g h η η' Hη θ θ' Hθ i.
  exact (compose_respects _ _ (Hη i) _ _ (Hθ i)).
Qed.
Next Obligation.
  intros I C f g η i; exact (id_left (η i)).
Qed.
Next Obligation.
  intros I C f g η i; exact (id_right (η i)).
Qed.
Next Obligation.
  intros I C f g h k η θ ρ i; exact (comp_assoc (η i) (θ i) (ρ i)).
Qed.
Next Obligation.
  intros I C f g h k η θ ρ i; exact (comp_assoc_sym (η i) (θ i) (ρ i)).
Qed.

(** ** Projections *)

Program Definition PiCat_Proj {I : Type} (C : I → Category) (i : I) :
  PiCat C ⟶ C i := {|
  fobj := fun f => f i;
  fmap := fun f g η => η i
|}.
Next Obligation.
  intros I C i f g η θ Hηθ; exact (Hηθ i).
Qed.
Next Obligation.
  intros I C i f; reflexivity.
Qed.
Next Obligation.
  intros I C i f g h η θ; reflexivity.
Qed.

(** ** The universal property *)

(* Pairing: a family of functors into the components assembles into one
   functor into the product, componentwise. *)
Program Definition PiCat_Pair {I : Type} {C : I → Category}
  {D : Category} (R : ∀ i : I, D ⟶ C i) : D ⟶ PiCat C := {|
  fobj := fun d i => R i d;
  fmap := fun x y h i => fmap[R i] h
|}.
Next Obligation.
  intros I C D R x y h h' Hh i.
  exact (fmap_respects _ _ _ _ Hh).
Qed.
Next Obligation.
  intros I C D R x i; exact (@fmap_id _ _ (R i) x).
Qed.
Next Obligation.
  intros I C D R x y z h h' i; exact (@fmap_comp _ _ (R i) _ _ _ h h').
Qed.

(* The triangle: projecting the pairing IS the component, definitionally
   on both objects and arrows, so the natural isomorphism is the
   identity family. *)
Lemma PiCat_Pair_Proj {I : Type} {C : I → Category}
  {D : Category} (R : ∀ i : I, D ⟶ C i) (i : I) :
  PiCat_Proj C i ◯ PiCat_Pair R ≈ R i.
Proof.
  simpl; exists (fun d => iso_id).
  intros x y h; simpl.
  rewrite id_left, id_right; reflexivity.
Qed.

(* Uniqueness, up to Cat's hom-equivalence: any functor whose
   projections agree with the family agrees with the pairing.  The
   witnessing isomorphism is assembled componentwise from the given
   ones, and its naturality is their naturality, component by
   component. *)
Lemma PiCat_ump_unique {I : Type} {C : I → Category} {D : Category}
  (R : ∀ i : I, D ⟶ C i) (H : D ⟶ PiCat C) :
  (∀ i : I, PiCat_Proj C i ◯ H ≈ R i) →
  H ≈ PiCat_Pair R.
Proof.
  intros HP; simpl.
  unshelve eexists.
  - intro d.
    unshelve refine
      (@Build_Isomorphism (PiCat C) (H d) (fun i => R i d)
         (fun i => to (projT1 (HP i) d))
         (fun i => from (projT1 (HP i) d)) _ _).
    + intro i; exact (iso_to_from (projT1 (HP i) d)).
    + intro i; exact (iso_from_to (projT1 (HP i) d)).
  - intros x y h i; simpl.
    exact (projT2 (HP i) x y h).
Qed.

(* The whole universal property, bundled: existence is the pairing with
   its triangle, uniqueness the lemma above. *)
Lemma PiCat_ump {I : Type} {C : I → Category} {D : Category}
  (R : ∀ i : I, D ⟶ C i) :
  ∃! F : D ⟶ PiCat C, ∀ i : I, PiCat_Proj C i ◯ F ≈ R i.
Proof.
  unshelve eapply Build_Unique.
  - exact (PiCat_Pair R).
  - exact (fun i => PiCat_Pair_Proj R i).
  - intros H HP; symmetry; exact (PiCat_ump_unique R H HP).
Qed.

(* F6-style sanity: the product over a constant two-member family
   projects a choice function to its component, by computation. *)
Example PiCat_witness :
  fobj[PiCat_Proj (fun _ : bool => _2) true] (fun _ => TwoX) = TwoX
  := eq_refl.
