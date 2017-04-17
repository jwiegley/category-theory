Require Import Category.Lib.
Require Export Category.Structure.BiCCC.
Require Export Category.Instance.Coq.
Require Export Category.Misc.Reified.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

(* Coq abstract data types are represented in CCC by identifying their
   equivalent construction. *)
Class Represented (A : Type) `{@Terminal C} `(Repr : ob) := {
  repr : A -> One ~> Repr;
  abst : One ~> Repr -> A;

  repr_abst : ∀ x, repr (abst x) ≈ x
}.

Arguments Represented A {_ _} Repr.

Program Instance prod_Represented
        `{HA : @Represented A _ Hom_Terminal C}
        `{HB : @Represented B _ Hom_Terminal D} :
  Represented (@Datatypes.prod A B) (Prod_ C D) := {
  repr := fun p => repr (fst p) △ repr (snd p);
  abst := fun h => (abst (Represented:=HA) (exl ∘ h), abst (exr ∘ h))
}.
Obligation 1.
  destruct HA, HB; simpl in *.
  rewrite repr_abst0, repr_abst1.
  simpl.
  rewrite fork_comp; cat.
Qed.

Program Instance unit_Represented : Represented (unit : Type) One_ := {
  repr := fun _ : unit => one;
  abst := fun _ : _ => tt
}.
Obligation 1. cat. Qed.

Program Instance false_Represented : Represented False Zero_ := {
  repr := fun _ : False => False_rect _ _;
  abst := fun h => interp (C:=Coq) h tt
}.
Obligation 2.
  unfold false_Represented_obligation_1.
  destruct (interp x).
Qed.

(*
Program Instance bool_Represented : Represented bool (Coprod One_ One_) := {
  repr := fun b => if b then inl else inr;
  abst := fun h => _
}.
*)
