Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Proofs.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Algebra.Comonoid.Hom.

Generalizable All Variables.

(** * Monoidal structure on the opposite category *)

(* nLab: https://ncatlab.org/nlab/show/opposite+category
   nLab: https://ncatlab.org/nlab/show/monoidal+category

   A monoidal structure (I, ⨂, λ, ρ, α) on C induces one on C^op: the tensor
   acts the same way on objects, morphisms are tensored by reading the same
   [bimap] against the reversed hom-sets, and the structural isomorphisms are
   the original ones read in the opposite category (so their [to] components
   are the original [from] components, via [Isomorphism_Opposite]).  Every
   coherence obligation is discharged by the corresponding law of C in the
   opposite orientation: the library records both directions of each
   naturality square, and the inverse-direction triangle and pentagon are
   already derived in Structure/Monoidal/Proofs.v, precisely so that this
   dualization is cheap.  A braiding or symmetry likewise transports, with
   the two hexagon identities exchanging roles — the reason Braided.v
   carries both hexagons as data.

   [Monoidal_op], [Braided_op] and [Symmetric_op] are Definitions rather
   than global Instances: registering them would let resolution silently
   equip C^op with a monoidal structure whenever C has one, which is rarely
   what an unannotated goal means (cf. the deferral rationale in
   Theory/Algebra/Comonoid.v).  Callers select them explicitly.

   The payoff is duality transfer for internal algebra: a comonoid in C is
   exactly a monoid in (C^op, Monoidal_op) and vice versa, on the nose (the
   round trips are definitional), and comonoid homomorphisms in C are
   exactly monoid homomorphisms in C^op with source and target exchanged.
   This is packaged both pointwise ([Comonoid_to_op_Monoid] and companions)
   and functorially, as functors Mon(C^op) ⟶ Comon(C)^op and back.

   No involution claim is made for [Monoidal_op]: although (C ∏ C)^op and
   C^op ∏ C^op are convertible, [Opposite_Tensor] and the [Monoidal_op]
   obligations rebuild the functor-law and coherence fields as fresh
   Qed-opaque proof terms, so [Monoidal_op (Monoidal_op M)] is not
   definitionally M even though (C^op)^op = C holds by reflexivity. *)

Section OppositeMonoidal.

Context {C : Category}.

#[local] Obligation Tactic := intros.

(* The tensor on C^op: the same object action, with the morphism action
   given componentwise by the tensor of C read against the reversed
   hom-sets.  Note that the domain is the product category C^op ∏ C^op —
   we do not route through a mediating (C ∏ C)^op. *)
Program Definition Opposite_Tensor `{M : @Monoidal C} :
  C^op ∏ C^op ⟶ C^op := {|
  fobj := fun p => (fst p ⨂[M] snd p)%object;
  fmap := fun x y f => (fst f ⨂[M] snd f)
|}.
Next Obligation.
  (* fmap respects ≈, componentwise. *)
  intros f g e; destruct e as [e1 e2]; simpl.
  apply bimap_respects; assumption.
Qed.
Next Obligation.
  simpl.
  apply bimap_id_id.
Qed.
Next Obligation.
  simpl.
  apply bimap_comp.
Qed.

(* The monoidal structure on C^op.  The unit is that of C; the unitors and
   associator are those of C read in the opposite category.  Each law of the
   [Monoidal] class then dualizes to a law of C: the to/from naturality
   squares trade places, and the triangle and pentagon become their
   inverse-direction forms from Structure/Monoidal/Proofs.v.

   A Definition, NOT an Instance — callers select it explicitly. *)
Program Definition Monoidal_op `{M : @Monoidal C} : @Monoidal (C^op) := {|
  I            := @I C M;
  tensor       := Opposite_Tensor;
  unit_left    := fun x => Isomorphism_Opposite (@unit_left C M x);
  unit_right   := fun x => Isomorphism_Opposite (@unit_right C M x);
  tensor_assoc := fun x y z => Isomorphism_Opposite (@tensor_assoc C M x y z)
|}.
Next Obligation.
  (* to_unit_left_natural in C^op = from_unit_left_natural in C *)
  simpl; symmetry; apply from_unit_left_natural.
Qed.
Next Obligation.
  (* from_unit_left_natural in C^op = to_unit_left_natural in C *)
  simpl; symmetry; apply to_unit_left_natural.
Qed.
Next Obligation.
  simpl; symmetry; apply from_unit_right_natural.
Qed.
Next Obligation.
  simpl; symmetry; apply to_unit_right_natural.
Qed.
Next Obligation.
  simpl; symmetry; apply from_tensor_assoc_natural.
Qed.
Next Obligation.
  simpl; symmetry; apply to_tensor_assoc_natural.
Qed.
Next Obligation.
  (* Triangle in C^op: ρ⁻¹ ⨂ id ≈ α⁻¹ ∘ (id ⨂ λ⁻¹) in C, the triangle
     identity of C solved for the inverse unitors. *)
  simpl.
  assert (X : (@unit_right C M x)⁻¹ ⨂ to (@unit_left C M y)
                ≈ (@tensor_assoc C M x I y)⁻¹).
  { symmetry.
    rewrite <- (bimap_id_right_left
                  ((@unit_right C M x)⁻¹) (to (@unit_left C M y))).
    rewrite inverse_triangle_identity.
    rewrite comp_assoc.
    rewrite <- bimap_comp.
    rewrite iso_from_to.
    cat. }
  rewrite <- X.
  rewrite <- bimap_comp.
  rewrite iso_to_from.
  cat.
Qed.
Next Obligation.
  (* Pentagon in C^op = the inverse pentagon of C. *)
  simpl.
  rewrite comp_assoc.
  apply inverse_pentagon_identity.
Qed.

(* A braiding on C transports to C^op: the braid at (x, y) in C^op is the
   braid at (y, x) in C.  Naturality dualizes to naturality, and the two
   hexagon identities exchange roles. *)
Program Definition Braided_op `{B : @BraidedMonoidal C} :
  @BraidedMonoidal (C^op) := {|
  braided_is_monoidal := Monoidal_op;
  braid := fun x y => @braid C B y x
|}.
Next Obligation.
  (* braid_natural in C^op = braid_natural in C, sides exchanged. *)
  intros; simpl.
  symmetry.
  rewrite !comp_assoc.
  exact (@braid_natural C B w z h y x g).
Qed.
Next Obligation.
  (* hexagon_identity in C^op = hexagon_identity_sym in C. *)
  simpl.
  rewrite !comp_assoc.
  exact (@hexagon_identity_sym C B y z x).
Qed.
Next Obligation.
  (* hexagon_identity_sym in C^op = hexagon_identity in C. *)
  simpl.
  rewrite !comp_assoc.
  exact (@hexagon_identity C B z x y).
Qed.

(* A symmetry on C transports to C^op: the involution law at (x, y) in C^op
   is literally the involution law at (x, y) in C. *)
Program Definition Symmetric_op `{S : @SymmetricMonoidal C} :
  @SymmetricMonoidal (C^op) := {|
  symmetric_is_braided := Braided_op
|}.
Next Obligation.
  simpl.
  apply braid_invol.
Qed.

(** ** Duality transfer for internal (co)monoids

    A comonoid on x in C is exactly a monoid on x in (C^op, Monoidal_op):
    the comultiplication reads as a multiplication against the reversed
    hom-sets, coassociativity as associativity, and the counit laws as the
    unit laws.  All four passages below are definitional on the underlying
    data, and the round trips are literal (proved by reflexivity). *)

Program Definition Comonoid_to_op_Monoid `{M : @Monoidal C} {x : C}
  (Cm : @Comonoid C M x) : @Monoid (C^op) Monoidal_op x := {|
  mu  := delta[Cm];
  eta := epsilon[Cm]
|}.
Next Obligation.
  (* mu_assoc in C^op unfolds to delta_coassoc in C. *)
  simpl.
  rewrite comp_assoc.
  apply delta_coassoc.
Qed.
Next Obligation.
  simpl.
  apply delta_counit_left.
Qed.
Next Obligation.
  simpl.
  apply delta_counit_right.
Qed.

Program Definition Monoid_to_op_Comonoid `{M : @Monoidal C} {x : C}
  (Mn : @Monoid C M x) : @Comonoid (C^op) Monoidal_op x := {|
  delta   := mu[Mn];
  epsilon := eta[Mn]
|}.
Next Obligation.
  (* delta_coassoc in C^op unfolds to mu_assoc in C. *)
  simpl.
  rewrite comp_assoc.
  apply mu_assoc.
Qed.
Next Obligation.
  simpl.
  apply mu_unit_left.
Qed.
Next Obligation.
  simpl.
  apply mu_unit_right.
Qed.

Program Definition op_Monoid_to_Comonoid `{M : @Monoidal C} {x : C}
  (Mn : @Monoid (C^op) Monoidal_op x) : @Comonoid C M x := {|
  delta   := mu[Mn];
  epsilon := eta[Mn]
|}.
Next Obligation.
  spose (@mu_assoc (C^op) Monoidal_op x Mn) as X.
  rewrite <- comp_assoc.
  apply X.
Qed.
Next Obligation.
  spose (@mu_unit_left (C^op) Monoidal_op x Mn) as X.
  apply X.
Qed.
Next Obligation.
  spose (@mu_unit_right (C^op) Monoidal_op x Mn) as X.
  apply X.
Qed.

Program Definition op_Comonoid_to_Monoid `{M : @Monoidal C} {x : C}
  (Cm : @Comonoid (C^op) Monoidal_op x) : @Monoid C M x := {|
  mu  := delta[Cm];
  eta := epsilon[Cm]
|}.
Next Obligation.
  spose (@delta_coassoc (C^op) Monoidal_op x Cm) as X.
  rewrite <- comp_assoc.
  apply X.
Qed.
Next Obligation.
  spose (@delta_counit_left (C^op) Monoidal_op x Cm) as X.
  apply X.
Qed.
Next Obligation.
  spose (@delta_counit_right (C^op) Monoidal_op x Cm) as X.
  apply X.
Qed.

(* Both round trips are definitional on the underlying data. *)

Lemma Comonoid_op_roundtrip `{M : @Monoidal C} {x : C}
  (Cm : @Comonoid C M x) :
  delta[op_Monoid_to_Comonoid (Comonoid_to_op_Monoid Cm)] ≈ delta[Cm]
    ∧ epsilon[op_Monoid_to_Comonoid (Comonoid_to_op_Monoid Cm)] ≈ epsilon[Cm].
Proof. split; reflexivity. Qed.

Lemma Monoid_op_roundtrip `{M : @Monoidal C} {x : C}
  (Mn : @Monoid C M x) :
  mu[op_Comonoid_to_Monoid (Monoid_to_op_Comonoid Mn)] ≈ mu[Mn]
    ∧ eta[op_Comonoid_to_Monoid (Monoid_to_op_Comonoid Mn)] ≈ eta[Mn].
Proof. split; reflexivity. Qed.

(** ** Duality transfer for homomorphisms

    A comonoid homomorphism in C is exactly a monoid homomorphism in C^op
    between the transported monoids, with source and target exchanged (and
    vice versa): the preservation squares are the same equations read
    against the reversed hom-sets. *)

Lemma ComonoidHom_to_op_MonoidHom `{M : @Monoidal C} {x y : C}
      {Cx : @Comonoid C M x} {Cy : @Comonoid C M y} {f : x ~{C}~> y} :
  ComonoidHom Cx Cy f →
  MonoidHom (Comonoid_to_op_Monoid Cy) (Comonoid_to_op_Monoid Cx) f.
Proof.
  intros F; destruct F as [Fd Fe].
  split; simpl.
  - apply Fd.
  - apply Fe.
Qed.

Lemma op_MonoidHom_to_ComonoidHom `{M : @Monoidal C} {x y : C}
      {Mx : @Monoid (C^op) Monoidal_op x} {My : @Monoid (C^op) Monoidal_op y}
      {f : x ~{C^op}~> y} :
  MonoidHom Mx My f →
  ComonoidHom (op_Monoid_to_Comonoid My) (op_Monoid_to_Comonoid Mx) f.
Proof.
  intros F; destruct F as [Fm Fe].
  split; simpl.
  - apply Fm.
  - apply Fe.
Qed.

#[local] Obligation Tactic := cat_simpl.

(* Functorially: Mon(C^op) and Comon(C)^op agree up to the identity on
   underlying data.  The two functors below are mutually inverse on that
   underlying data — the mu/eta/delta/epsilon components and the carrier
   morphisms round-trip definitionally (fmap is the identity on the
   underlying C-morphism) — but NOT on the nose at the record level: each
   object round trip rebuilds the law fields (delta_coassoc etc.) as fresh
   Qed-opaque proof terms, so the round-tripped sigma objects are not
   definitionally equal to the originals (proof-irrelevant, but opaque).
   No isomorphism-of-categories lemma is claimed here; nothing downstream
   needs one. *)

Program Definition Mon_op_to_Comon_op `{M : @Monoidal C} :
  @Mon (C^op) Monoidal_op ⟶ (@Comon C M)^op := {|
  fobj := fun X => (`1 X; op_Monoid_to_Comonoid `2 X);
  fmap := fun X Y f => (`1 f; op_MonoidHom_to_ComonoidHom `2 f)
|}.

Program Definition Comon_op_to_Mon_op `{M : @Monoidal C} :
  (@Comon C M)^op ⟶ @Mon (C^op) Monoidal_op := {|
  fobj := fun X => (`1 X; Comonoid_to_op_Monoid `2 X);
  fmap := fun X Y f => (`1 f; ComonoidHom_to_op_MonoidHom `2 f)
|}.

End OppositeMonoidal.
