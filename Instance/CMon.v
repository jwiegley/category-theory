Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.

Generalizable All Variables.

(** * The category of commutative monoids *)

(* nLab:      https://ncatlab.org/nlab/show/CMon
   nLab:      https://ncatlab.org/nlab/show/commutative+monoid
   Wikipedia: https://en.wikipedia.org/wiki/Monoid#Commutative_monoid

   [CMon] is the category of commutative monoids over [Sets]: an object is a
   setoid carrying a commutative, associative binary operation [cmon_plus]
   with unit [cmon_zero], whose `≈` is PROPOSITIONAL ([cmon_prop]); a morphism
   is a setoid map preserving both; two morphisms are equivalent when their
   underlying maps agree pointwise.

   An earlier revision of this paragraph named only the operation, the unit and
   the laws.  Since the PR "algebraic carriers are sets" (2026-09-17) the record
   carries a fourth kind of datum, the field [cmon_prop] of
   Lib/Setoid/Propositional.v's class [PropEquiv]: a [Prop]-valued relation on
   the carrier that holds exactly when `≈` does.  A commutative monoid in this
   library is therefore a commutative monoid on a SET in Bishop's sense, not on
   an arbitrary proof-relevant setoid.  Lib/Setoid/Propositional.v's header says
   why -- a type of congruences on a carrier is carrier-sized exactly when the
   congruences are [Prop]-valued, which is what the solution-set condition of
   Mac Lane's general adjoint functor theorem needs at a concrete algebraic
   category.  The whole tower over [CMon] -- [Ab], [RMod R], and everything
   coerced into them -- inherits the field through [ab_cmon] and [rm_ab], and
   [RigObject] carries the twin field [rig_prop] (Theory/Algebra/Rig.v), since
   [rig_cmon] builds a [CMonObject] out of a rig's own carrier setoid.

   The in-tree alternative — commutative monoid OBJECTS in a symmetric
   monoidal category (Theory/Algebra/CommutativeMonoid.v, instantiable at
   [Sets_Product_Monoidal], with the hom-category pattern of
   Theory/Algebra/Monoid/Hom.v) — is deliberately not taken here: the
   biproduct/preadditive development (Instance/CMon/Biproduct.v) wants
   direct carrier-level access to [cmon_plus] and [cmon_zero], without the
   monoidal-object indirection.  Since [Mon] already names the internal
   monoid category of Theory/Algebra/Monoid/Hom.v, the vocabulary here is
   [CMonObject], [CMonHom], [CMon]. *)

(* A commutative monoid: a setoid whose `≈` is propositional, together with a
   unit element and a binary operation that respects `≈` and satisfies the
   commutative monoid laws up to `≈`.

   [cmon_prop] is the LAST field deliberately.  Every construction site in the
   tree writes the record with named fields under [Program], and [Program]
   emits its obligations in field order; putting the new field last leaves the
   numbering of every existing obligation alone and adds one at the end. *)
Record CMonObject := {
  cmon_setoid :> SetoidObject;

  cmon_zero : carrier cmon_setoid;
  cmon_plus : carrier cmon_setoid → carrier cmon_setoid → carrier cmon_setoid;

  cmon_plus_respects : Proper (equiv ==> equiv ==> equiv) cmon_plus;

  cmon_plus_assoc : ∀ a b c,
    cmon_plus (cmon_plus a b) c ≈ cmon_plus a (cmon_plus b c);
  cmon_plus_comm : ∀ a b, cmon_plus a b ≈ cmon_plus b a;
  cmon_plus_zero_l : ∀ a, cmon_plus cmon_zero a ≈ a;

  (* The carrier is a SET: its `≈` is logically equivalent to a [Prop]-valued
     relation.  See Lib/Setoid/Propositional.v. *)
  cmon_prop : PropEquiv (is_setoid cmon_setoid)
}.

#[export] Existing Instance cmon_plus_respects.
#[export] Existing Instance cmon_prop.

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

(* L1: the hom-setoid is propositional, pointwise into the CODOMAIN's own
   [cmon_prop].  The domain needs nothing -- the relation quantifies over its
   carrier but never compares two of its elements.  This is the same shape as
   [hom_PropEquiv] (Instance/Sets/Propositional.v:91), restated here because
   [CMonHom_Setoid] is a setoid on [CMonHom M N] rather than on
   [SetoidMorphism]s, and the two records are not convertible.

   Measured (About under Set Printing Universes):

     CMonHom_PropEquiv@{u} :
       ∀ {M N : CMonObject@{u u u}}, PropEquiv@{u u} CMonHom_Setoid@{u}
     (* u |=  *)

   -- one universe and no constraint: the transport neither raises the level
   nor pins it. *)
#[export] Instance CMonHom_PropEquiv {M N : CMonObject} :
  PropEquiv (@CMonHom_Setoid M N).
Proof.
  unshelve refine
    {| pequiv := fun f g : CMonHom M N =>
                   forall a : carrier (cmon_setoid M),
                     @pequiv _ _ (cmon_prop N) (cmon_map f a) (cmon_map g a) |}.
  - intros f g H a; exact (pequiv_to _ _ (H a)).
  - intros f g H a; exact (pequiv_from _ _ (H a)).
Defined.

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
(* The universes are pinned by hand.  [CMonObject]'s sort is
   [Type@{max(Set+1,s,o+1,p+1)}] once [cmon_prop] is a field -- the [Set+1] is
   the sort of [Prop] and enters through [PropEquiv] -- and left to itself the
   elaborator will not identify the record's own sort variable [s] with the
   category's object universe, so [CMon] acquires a third, redundant universe
   and every `CMon@{u o}` annotation in the tree is refused for arity.  Naming
   [Category@{u p p}] and every field's instance keeps the arity at two,
   exactly as before the field landed; measured after the change,
   [CMon@{u p} : Category@{u p p}] with the single new constraint [Set < u],
   which [Unset Universe Minimization ToSet] (Lib.v:17) makes harmless. *)
Program Definition CMon@{u p} : Category@{u p p} := {|
  obj     := CMonObject@{p p p};
  hom     := CMonHom@{p};
  homset  := @CMonHom_Setoid@{p};
  id      := @cmon_hom_id@{p};
  compose := @cmon_hom_compose@{u p};

  compose_respects := @cmon_hom_compose_respects@{u p}
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

(* [CMon] is therefore locally propositional: its hom-setoid IS
   [CMonHom_Setoid].  This is what lets Theory/Algebra/Rig.v's [EndRig] -- the
   endomorphism rig of an object of a preadditive category, which since the PR
   "algebraic carriers are sets" (2026-09-17) asks its ambient category for a
   [Prop] equality on homs -- be applied at [CMon] itself
   (Theory/Algebra/Rig/Connections.v:69). *)
#[export] Instance CMon_LocallyPropositional : LocallyPropositional CMon.
Proof.
  constructor.
  intros M N.
  exact (@CMonHom_PropEquiv M N).
Defined.

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
