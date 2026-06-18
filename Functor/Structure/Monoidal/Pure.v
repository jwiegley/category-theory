Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Strong.
Require Import Category.Functor.Structure.Monoidal.

Generalizable All Variables.

(** The applicative [pure] from a strong lax monoidal functor. *)

(* nLab: https://ncatlab.org/nlab/show/applicative+functor
   Wikipedia: https://en.wikipedia.org/wiki/Applicative_functor

   For a strong lax monoidal endofunctor F on a monoidal category, the unit
   comparison lax_pure : I ~> F I and the tensorial strength combine into the
   point operation pure : A ~> F A.  This is the categorical source of the
   Haskell [Applicative] method pure : a -> F a (McBride and Paterson,
   "Applicative programming with effects", JFP 18(1), 2008).

   Following nLab, pure[A] is the composite (read right to left, with ρ the
   right unitor unit_right, ε = lax_pure the unit comparison and st = strength)

       A  --ρ⁻¹-->  A ⨂ I  --id ⨂ ε-->  A ⨂ F I
          --st-->  F (A ⨂ I)  --F ρ-->  F A,

   i.e. pure ≈ fmap unit_right ∘ strength ∘ (id ⨂ lax_pure) ∘ unit_right⁻¹.
   The right unitor is used here, matching the nLab presentation; the left
   unitor would give the mirror-image construction. *)

Section Pure.

Context {C : Category}.
Context `{@Monoidal C}.
Context {F : C ⟶ C}.
Context `{@StrongFunctor C _ F}.
Context `{@LaxMonoidalFunctor C C _ _ F}.

Definition pure {A} : A ~> F A :=
  fmap unit_right ∘ strength ∘ id[A] ⨂ lax_pure ∘ unit_right⁻¹.

(* pure is natural in A: it is a natural transformation Id ⟹ F. *)
Lemma pure_natural : natural (@pure).
Proof.
  simpl; intros.
  unfold pure.
  normal.
  rewrite to_unit_right_natural.
  rewrite fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  spose (strength_natural _ _ g I I id) as X.
  normal.
  rewrites.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite <- from_unit_right_natural.
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  normal.
  rewrite fmap_id; cat.
Qed.

(* The naturality square of pure as a rewrite: fmap f commutes past pure. *)
Lemma fmap_pure {a b} (f : a ~> b) : pure ∘ f ≈ fmap f ∘ pure.
Proof.
  symmetry.
  sapply pure_natural.
Qed.

End Pure.

Arguments pure {C _ F _ _ A}.

Notation "pure[ F ]" := (@pure _ _ F _ _ _)
  (at level 0, format "pure[ F ]") : morphism_scope.
