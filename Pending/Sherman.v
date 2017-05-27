Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Structure.BiCCC.
Require Export Category.Functor.Structure.Cartesian.
Require Export Category.Functor.Structure.Closed.
Require Export Category.Functor.Structure.Terminal.
Require Export Category.Instance.Coq.
Require Export Category.Tools.Abstraction.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Numerical (C : Category) `{@Cartesian C} := {
  Num : ob;

  add : Num × Num ~> Num
}.

Section NumericalFunctor.

Context `{F : C ⟶ D}.
Context `{@Cartesian C}.
Context `{@Numerical C _}.
Context `{@Cartesian D}.
Context `{@Numerical D _}.
Context `{@CartesianFunctor _ _ F _ _}.

Class NumericalFunctor := {
  map_num : Num ≅ F Num;

  fmap_add : fmap add ≈ map_num ∘ @add D _ _ ∘ split (map_num⁻¹) (map_num⁻¹)
                                ∘ @prod_out _ _ F _ _ _ Num Num
}.

End NumericalFunctor.

Instance Coq_Numerical : @Numerical Coq Coq_Cartesian := {
  Num := nat;
  add := prod_curry Nat.add
}.

Section Sherman.

Infix ">==>" := rel (at level 99) : category_scope.

(*
Theorem ccc_arity2 :
  ∀ (a b c : Type)
    (f : a -> b) (f' : F a ~> F b)
    (g : a -> b) (g' : F a ~> F b)
    (p : b -> b -> c) (p' : F b ~> F c ^ F b),
  f >==> f' ->
  g >==> g' ->
  p >==> exp_in ∘ p' ->
  (λ x : a, p (f x) (g x)) >==> uncurry p' ∘ f' △ g'.
Proof.
Admitted.

Theorem ccc_plus :
  ∀ (f : nat -> nat) (f' : F nat ~> F nat)
    (g : nat -> nat) (g' : F nat ~> F nat),
  f >==> f' ->
  g >==> g' ->
  (λ x : nat, (f x + g x)%nat)
    >==> map_num ∘ add ∘ split (map_num⁻¹) (map_num⁻¹) ∘ f' △ g'.
Proof.
  intros.
  pose proof (ccc_arity2 nat nat nat f f' g g' Nat.add
                         (curry (map_num ∘ add ∘ split (map_num⁻¹) (map_num⁻¹)))
                         X X0).
  simpl in X1.
  unfold rel in *; repeat intros.
  rewrite uncurry_curry in X1.
  rewrite <- X1; [reflexivity|]; clear X1.
  pose proof (@fmap_add Coq _ _ _ _ _ _ _ _) as HA.
  simpl in HA.
  assert (Nat.add = prod_uncurry (λ p : nat * nat, (fst p + snd p)%nat)) by auto.
  rewrite H2; clear H2.
Admitted.
*)

(* f : A -->[Setoid] R *)
(* g : A -->[Setoid] R *)
(* + : R * R -->[Setoid] R *)
(* ============== *)
(* lambda x. f x + g x  : A -->[Setoid] R *)

(* Definition generic_add := fmap Nat.add. *)

End Sherman.

(* Eval simpl in @generic_add. *)
