Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Cocartesian.
Require Export Category.Structure.Closed.
Require Export Category.Structure.Initial.
Require Export Category.Structure.Terminal.

Require Import Coq.Logic.ProofIrrelevance.

(* Proof irrelevant equality. *)
Definition proof_eq {P : Prop} (x y : P) := (x = y)%type.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.
Set Implicit Arguments.

(* The category of propositions. Note that since proofs are opaque, we must
   assert proof irrelevance and judge them always equivalent if they have the
   same type. *)

Local Obligation Tactic :=
  first [ proper; apply proof_irrelevance | program_simpl ].

Program Definition Props : Category := {|
  ob      := Prop;
  hom     := Basics.impl;
  homset  := fun P Q =>
               {| equiv := fun f g => forall x, proof_eq (f x) (g x) |};
  id      := fun _ x => x;
  compose := fun _ _ _ g f x => g (f x)
|}.
Next Obligation. equivalence; autounfold in *; congruence. Qed.

Program Instance Props_Terminal : @Terminal Props := {
  One := True;
  one := fun _ _ => I
}.

Program Instance Props_Initial : @Initial Props := {
  Zero := False;
  zero := fun _ _ => False_rect _ _
}.

Program Instance Props_Cartesian : @Cartesian Props := {
  Prod := and;
  fork := fun _ _ _ f g x => conj (f x) (g x);
  exl  := fun _ _ p => proj1 p;
  exr  := fun _ _ p => proj2 p
}.

Program Instance Props_Cocartesian : @Cocartesian Props := {
  Coprod := or;
  merge := fun _ _ _ f g x =>
            match x with
            | or_introl v => f v
            | or_intror v => g v
            end;
  inl  := fun _ _ p => or_introl p;
  inr  := fun _ _ p => or_intror p
}.

Program Instance Props_Closed : @Closed Props _ := {
  Exp := Basics.impl;
  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f a b => f (conj a b) |}
     ; from := {| morphism := fun f p => f (proj1 p) (proj2 p) |} |}
}.
