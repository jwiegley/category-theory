Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Natural.
Require Export Category.Functor.Hom.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* jww (2017-04-16): How to represent heteromorphisms? *)

(*
Program Definition Profunctor `(C : Category) `(D : Category) :
  C^op ∏ D ⟶ Sets := {|
  fobj := fun p => {| carrier   := @hom D (_ (fst p)) (snd p)
                    ; is_setoid := @homset D (_ (fst p)) (snd p) |};
  fmap := fun X Y (f : X ~{C^op ∏ D}~> Y) =>
            {| morphism := fun g => snd f ∘ g ∘ fmap[_] (fst f) |}
|}.
Next Obligation.
  intros ?? HA.
  rewrite HA; reflexivity.
Qed.
Next Obligation.
  intros ?? HA ?; simpl.
  rewrite HA; reflexivity.
Qed.
Next Obligation. cat. Qed.
Next Obligation.
  unfold Basics.compose.
  rewrite comp_assoc; reflexivity.
Qed.
Next Obligation.
  repeat intro; intuition.
Qed.
Next Obligation.
  unfold Basics.compose.
  rewrite comp_assoc; reflexivity.
Qed.
Next Obligation.
  repeat intro; intuition; simpl in *.
  unfold op.
  rewrite X0; reflexivity.
Qed.
Next Obligation.
  intro; simpl; unfold op; intros; cat.
Qed.
Next Obligation.
  intro; simpl; unfold op, Basics.compose; intros.
  rewrite comp_assoc; reflexivity.
Qed.

Notation "C ⇸ D" := (@Profunctor C D) (at level 9) : functor_type_scope.
*)

(* Wikipedia: "Lifting functors to profunctors

   "A functor F : C → D can be seen as a profunctor ϕ F : C ↛ D by
   postcomposing with the Yoneda functor:

       ϕ F = Y D ∘ F

   "It can be shown that such a profunctor ϕF has a right adjoint. Moreover,
   this is a characterization: a profunctor ϕ : C ↛ D has a right adjoint if
   and only if ϕ^ : C → D^ factors through the Cauchy completion of D, i.e.
   there exists a functor F : C → D such that ϕ^ = Y D ∘ F." *)
