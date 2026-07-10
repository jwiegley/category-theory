Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The category of commutative monoids *)

(* nLab:      https://ncatlab.org/nlab/show/CMon
   nLab:      https://ncatlab.org/nlab/show/commutative+monoid
   Wikipedia: https://en.wikipedia.org/wiki/Monoid#Commutative_monoid

   [CMon] is the category of commutative monoids over [Sets]: an object is a
   setoid carrying a commutative, associative binary operation [cmon_plus]
   with unit [cmon_zero]; a morphism is a setoid map preserving both; two
   morphisms are equivalent when their underlying maps agree pointwise.

   The in-tree alternative — commutative monoid OBJECTS in a symmetric
   monoidal category (Theory/Algebra/CommutativeMonoid.v, instantiable at
   [Sets_Product_Monoidal], with the hom-category pattern of
   Theory/Algebra/Monoid/Hom.v) — is deliberately not taken here: the
   biproduct/preadditive development (Instance/CMon/Biproduct.v) wants
   direct carrier-level access to [cmon_plus] and [cmon_zero], without the
   monoidal-object indirection.  Since [Mon] already names the internal
   monoid category of Theory/Algebra/Monoid/Hom.v, the vocabulary here is
   [CMonObject], [CMonHom], [CMon]. *)

(* A commutative monoid: a setoid together with a unit element and a binary
   operation that respects `≈` and satisfies the commutative monoid laws up
   to `≈`. *)
Record CMonObject := {
  cmon_setoid :> SetoidObject;

  cmon_zero : carrier cmon_setoid;
  cmon_plus : carrier cmon_setoid → carrier cmon_setoid → carrier cmon_setoid;

  cmon_plus_respects : Proper (equiv ==> equiv ==> equiv) cmon_plus;

  cmon_plus_assoc : ∀ a b c,
    cmon_plus (cmon_plus a b) c ≈ cmon_plus a (cmon_plus b c);
  cmon_plus_comm : ∀ a b, cmon_plus a b ≈ cmon_plus b a;
  cmon_plus_zero_l : ∀ a, cmon_plus cmon_zero a ≈ a
}.

#[export] Existing Instance cmon_plus_respects.

(* The right unit law follows from the left one by commutativity. *)
Corollary cmon_plus_zero_r (M : CMonObject) (a : carrier (cmon_setoid M)) :
  cmon_plus M a (cmon_zero M) ≈ a.
Proof.
  rewrite cmon_plus_comm.
  apply cmon_plus_zero_l.
Qed.

(* A homomorphism of commutative monoids: a setoid map on the carriers that
   preserves the unit and the operation. *)
Record CMonHom (M N : CMonObject) := {
  cmon_map :> SetoidMorphism (cmon_setoid M) (cmon_setoid N);

  cmon_map_zero : cmon_map (cmon_zero M) ≈ cmon_zero N;
  cmon_map_plus : ∀ a b,
    cmon_map (cmon_plus M a b) ≈ cmon_plus N (cmon_map a) (cmon_map b)
}.

Arguments cmon_map {M N} _.
Arguments cmon_map_zero {M N} _.
Arguments cmon_map_plus {M N} _ _ _.

#[local] Obligation Tactic := idtac.

(* The hom-setoid: homomorphisms are compared by their underlying maps,
   pointwise up to the codomain's `≈` (as in [Sets]). *)
#[export]
Program Instance CMonHom_Setoid {M N : CMonObject} : Setoid (CMonHom M N) := {|
  equiv := fun f g => ∀ a, cmon_map f a ≈ cmon_map g a
|}.
Next Obligation.
  intros M N.
  constructor.
  - intros f a.
    reflexivity.
  - intros f g Hfg a.
    symmetry.
    apply Hfg.
  - intros f g h Hfg Hgh a.
    transitivity (cmon_map g a).
    + apply Hfg.
    + apply Hgh.
Qed.

(* The identity homomorphism: the identity setoid map, which preserves the
   unit and the operation on the nose. *)
Program Definition cmon_hom_id {M : CMonObject} : CMonHom M M := {|
  cmon_map := setoid_morphism_id
|}.
Next Obligation.
  intros M; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros M a b; simpl.
  reflexivity.
Qed.

(* Composition of homomorphisms: composition of the underlying setoid maps;
   preservation of unit and operation composes. *)
Program Definition cmon_hom_compose {M N P : CMonObject}
        (f : CMonHom N P) (g : CMonHom M N) : CMonHom M P := {|
  cmon_map := setoid_morphism_compose (cmon_map f) (cmon_map g)
|}.
Next Obligation.
  intros M N P f g; simpl.
  unfold Basics.compose.
  rewrite (cmon_map_zero g).
  apply (cmon_map_zero f).
Qed.
Next Obligation.
  intros M N P f g a b; simpl.
  unfold Basics.compose.
  rewrite (cmon_map_plus g).
  apply (cmon_map_plus f).
Qed.

Lemma cmon_hom_compose_respects {M N P : CMonObject} :
  Proper (equiv ==> equiv ==> equiv) (@cmon_hom_compose M N P).
Proof.
  intros f f' Hf g g' Hg a; simpl.
  unfold Basics.compose.
  rewrite (Hg a).
  apply Hf.
Qed.

(* The category of commutative monoids.

       objects: commutative monoids over setoids
        arrows: unit- and operation-preserving setoid maps
      identity: the identity setoid map
   composition: composition of setoid maps *)
Program Definition CMon : Category := {|
  obj     := CMonObject;
  hom     := CMonHom;
  homset  := @CMonHom_Setoid;
  id      := @cmon_hom_id;
  compose := @cmon_hom_compose;

  compose_respects := @cmon_hom_compose_respects
|}.
Next Obligation.
  intros x y f a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y f a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y z w f g h a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros x y z w f g h a; simpl.
  reflexivity.
Qed.

(* The forgetful functor to [Sets], dropping the monoid structure.  It is
   faithful by construction, since equivalence of homomorphisms in [CMon] is
   equivalence of the underlying setoid maps. *)
Program Definition CMon_Forget : CMon ⟶ Sets := {|
  fobj := fun M => cmon_setoid M;
  fmap := fun _ _ f => cmon_map f
|}.
Next Obligation.
  intros M N f g Hfg a.
  exact (Hfg a).
Qed.
Next Obligation.
  intros M a; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros M N P f g a; simpl.
  reflexivity.
Qed.
