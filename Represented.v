Require Import Lib.
Require Export BiCCC.
Require Export Coq.
Require Export Reified.

Generalizable All Variables.

(* Coq abstract data types are represented in CCC by identifying their
   equivalent construction. *)
Class Represented (A : Type) `{Terminal ob} `(Repr : ob) := {
  repr : A -> One ~> Repr;
  abst : One ~> Repr -> A;

  repr_abst : ∀ x, abst (repr x) = x
}.

Arguments Represented A {_ _} Repr.

Global Program Instance unit_Represented : Represented (unit : Type) One := {
  repr := fun _ : unit => one;
  abst := fun _ : _ => tt
}.
Obligation 1.
  destruct x.
  reflexivity.
Qed.

Global Program Instance bool_Represented : Represented bool (Coprod One One) := {
  repr := fun b => if b
                   then inl
                   else inr;
  abst := fun h => _
}.
Obligation 1.
  pose proof (@interp _ _ h Type _ _ _ _).
  destruct (X tt).
    exact true.
  exact false.
Defined.
Obligation 2.
  unfold bool_Represented_obligation_1.
  destruct x; auto.
Defined.

Global Program Instance prod_Represented
        `{H1 : @Represented A _ Hom_Terminal C}
        `{H2 : @Represented B _ Hom_Terminal D} :
  Represented (@Datatypes.prod A B) (C × D) := {
  repr := fun p => repr (fst p) △ repr (snd p);
  abst := fun h => (abst (Represented:=H1) (exl ∘ h), abst (exr ∘ h))
}.
Obligation 1.
  simpl.
  (* jww (2017-04-11): Define what it means to abstract composition. *)
Admitted.
