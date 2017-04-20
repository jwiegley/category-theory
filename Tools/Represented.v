Require Import Category.Lib.
Require Export Category.Structure.BiCCC.
Require Export Category.Instance.Coq.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Represented.

Context `{C : Category}.
Context `{@Cartesian C}.
Context `{@Cocartesian C}.
Context `{@Terminal C}.
Context `{@Initial C}.

(* Coq abstract data types are represented in CCC by identifying their
   equivalent construction. *)
Class Represented (A : Type) `(Repr : C) := {
  repr : A -> One ~> Repr;
  abst : One ~> Repr -> A;

  repr_abst : ∀ x, repr (abst x) ≈ x
}.

Program Instance prod_Represented
        `{HA : @Represented A X}
        `{HB : @Represented B Y} :
  Represented (@Datatypes.prod A B) (Prod X Y) := {
  repr := fun p => repr (fst p) △ repr (snd p);
  abst := fun h => (abst (Represented:=HA) (exl ∘ h), abst (exr ∘ h))
}.
Obligation 1.
  destruct HA, HB; simpl in *.
  rewrite repr_abst0, repr_abst1.
  simpl.
  rewrite fork_comp; cat.
Qed.

Program Instance unit_Represented : Represented (unit : Type) One := {
  repr := fun _ : unit => one;
  abst := fun _ : _ => tt
}.
Obligation 1. cat. Qed.

(*
Program Instance false_Represented : Represented False Zero := {
  repr := fun _ : False => False_rect _ _;
  abst := fun h => _
}.

Program Instance bool_Represented : Represented bool (One + (One × One)) := {
  repr := fun b => if b then inr ∘ one △ one else inl;
  abst := fun h => interp (C:=Coq) h
}.
*)

End Represented.
