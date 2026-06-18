Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Naturality.
Require Import Category.Functor.Construction.Product.

Generalizable All Variables.

(** Strong functors (functors with a tensorial strength) *)

(* nLab: https://ncatlab.org/nlab/show/tensorial+strength
   Wikipedia: https://en.wikipedia.org/wiki/Strong_monad

   A strong functor is an endofunctor F : C ⟶ C on a monoidal category
   (C, ⊗, I) equipped with a tensorial (left) strength: a natural family

     strength[x,y] : x ⨂ F y ~> F (x ⨂ y)          (left strength)

   subject to two coherence laws relating it to the monoidal structure.  In
   library notation, writing λ = [unit_left] and α = [tensor_assoc]:

     - unit:  F(λ) ∘ strength[I,x]                 ≈ λ_{F x}    ([strength_id_left])
     - assoc: F(α) ∘ strength[x⨂y,z]
                ≈ strength[x,y⨂z] ∘ (id ⨂ strength[y,z]) ∘ α    ([strength_assoc])

   These are Kock's two conditions; the correspondence between such families
   and strengths is what justifies the name "tensorial strength" (Kock 1972,
   "Strong functors and monoidal monads").  The dual [RightStrongFunctor]
   carries a right strength F x ⨂ y ~> F (x ⨂ y), with the mirror laws stated
   via ρ = [unit_right] and α⁻¹.  On a symmetric monoidal C the two strengths
   are interderivable by twisting with the braiding, and they coincide.

   "Strong" here means tensorial strength, NOT "strong (i.e. pseudo) monoidal
   functor"; the two notions are unrelated.  On a closed monoidal C a strength
   is equivalently a C-enrichment of F, and a strength on a monad's underlying
   functor (compatible with η and μ) is exactly what is needed to internalize
   Kleisli composition, yielding a strong monad. *)

Class StrongFunctor `{@Monoidal C} (F : C ⟶ C) := {
  strength {x y} : x ⨂ F y ~> F (x ⨂ y);          (* left strength A ⨂ FB ~> F(A ⨂ B) *)
  strength_natural : natural (@strength);          (* natural in both arguments *)

  strength_id_left {x} :                           (* unit law: F(λ) ∘ str ≈ λ *)
    fmap[F] (to unit_left) ∘ strength
      << I ⨂ F x ~~> F x >>
    to (@unit_left _ _ (F x));

  strength_assoc {x y z} :                          (* associativity law w.r.t. α *)
    fmap[F] (to (@tensor_assoc _ _ x y z)) ∘ strength
      << (x ⨂ y) ⨂ F z ~~> F (x ⨂ y ⨂ z) >>
    strength ∘ bimap id strength ∘ to (@tensor_assoc _ _ x y (F z))
}.

Class RightStrongFunctor `{@Monoidal C} (F : C ⟶ C) := {
  rstrength_nat : (⨂) ◯ F ∏⟶ Id ⟹ F ◯ (⨂);        (* right strength as a natural transformation *)

  rstrength {x y} : F x ⨂ y ~> F (x ⨂ y) := transform[rstrength_nat] (x, y);

  rrstrength_id_right {x} :                          (* unit law: F(ρ) ∘ rstr ≈ ρ *)
    fmap[F] (to unit_right) ∘ rstrength ≈ to (@unit_right _ _ (F x));
  rstrength_assoc {x y z} :                          (* associativity law w.r.t. α⁻¹ *)
    rstrength ∘ bimap rstrength id ∘ from (@tensor_assoc _ _ (F x) y z)
      ≈ fmap[F] (from (@tensor_assoc _ _ x y z)) ∘ rstrength
}.

Section Strong.

Context `{@Monoidal C}.
Context {F : C ⟶ C}.

(* The identity functor is strong, with the identity as its strength. *)
#[export] Program Instance Id_StrongFunctor : StrongFunctor Id[C] := {
  strength := fun _ _ => id
}.

#[local] Obligation Tactic := program_simpl.

(* Strong functors are closed under composition: the strength of F ◯ G is
   built by first sliding through G, then lifting that through F's strength. *)
#[export] Program Instance Compose_StrongFunctor (F G : C ⟶ C) :
  StrongFunctor F → StrongFunctor G → StrongFunctor (F ◯ G) := {
  strength := fun _ _ => fmap[F] strength ∘ strength
}.
Next Obligation.
  repeat match reverse goal with [ H : StrongFunctor _ |- _ ] => destruct H end; simpl in *.
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (strength0 _ _)).
  rewrite <- strength_natural0; clear strength_natural0.
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- strength_natural1; clear strength_natural1.
  rewrite <- fmap_comp.
  reflexivity.
Qed.
Next Obligation.
  repeat match reverse goal with [ H : StrongFunctor _ |- _ ] => destruct H end; simpl in *.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite strength_id_left1.
  apply strength_id_left0.
Qed.
Next Obligation.
  repeat match reverse goal with [ H : StrongFunctor _ |- _ ] => destruct H end; simpl in *.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite strength_assoc1.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  rewrite strength_assoc0.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  specialize (strength_natural0
                x x (id[x]) (y ⨂ G z)%object (G (y ⨂ z))%object
                (strength1 y z)).
  rewrite !bimap_id_id in strength_natural0.
  rewrite !fmap_id in strength_natural0.
  rewrite !id_right in strength_natural0.
  rewrite strength_natural0.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite comp_assoc.
  apply compose_respects; [|reflexivity].
  rewrite <- bimap_comp.
  apply fmap_respects.
  split; simpl; cat.
Qed.

End Strong.

(* [strength[F]] names the strength of a given strong functor F at implicit
   arguments, mirroring the [fmap[F]] convention. *)
Notation "strength[ F ]" := (@strength _ _ F%functor _ _ _)
  (at level 9, format "strength[ F ]") : morphism_scope.
