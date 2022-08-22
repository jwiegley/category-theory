Set Warnings "-notation-overridden".

Require Import Coq.PArith.PArith.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Solver.Expr.
Require Import Category.Solver.Normal.

Set Universe Polymorphism.

Section Categories.

(** In the category of simple terms, the best we can do to determine
    equivalence of morphisms is to check that they refer to the same
    arrows. *)

Program Definition STerms : Category := {|
  obj     := positive;
  hom     := λ _ _, STerm;
  homset  := λ _ _, {| equiv := λ f g, sindices f = sindices g |};
  id      := λ _, SIdent;
  compose := λ _ _ _, SComp
|}.
Next Obligation.
  equivalence.
  now transitivity (sindices y).
Qed.
Next Obligation.
  proper.
  now rewrite H, H0.
Qed.
Next Obligation. now rewrite List.app_nil_r. Defined.
Next Obligation. now rewrite List.app_assoc. Defined.
Next Obligation. now symmetry; rewrite List.app_assoc. Defined.

End Categories.
