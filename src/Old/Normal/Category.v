Set Warnings "-notation-overridden".

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Recdef.

Require Import Equations.Equations.
Unset Equations WithK.

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Solver.Lib.
Require Import Solver.Env.
Require Import Solver.Expr.Term.
Require Import Solver.Expr.Denote.
Require Import Solver.Normal.TList.
Require Import Solver.Normal.Arrow.
Require Import Solver.Normal.Denote.
Require Import Solver.Normal.Sound.
Require Import Solver.Normal.Valid.

Generalizable All Variables.

Section NormalCategory.

Context `{Env}.

(** The category of terms, with equivalence up to normalization. *)

Program Definition Terms : Category := {|
  obj := obj_idx;
  hom := fun _ _ => Term;
  homset := fun x y => {| equiv := fun f g => arrows f = arrows g |};
  id := fun _ => Identity;
  compose := fun _ _ _ => Compose
|}.
Next Obligation. now rewrite app_nil_r. Defined.
Next Obligation. now rewrite app_assoc. Defined.
Next Obligation. now rewrite app_assoc. Defined.

Program Definition DefinedTerms : Category := {|
  obj := obj_idx;
  hom := fun dom cod => ∃ f f', termD dom cod f = Some f';
  homset := fun x y => {| equiv := fun f g => `1 `2 f ≈ `1 `2 g |};
  id := fun _ => (Identity; (id; _));
  compose := fun _ _ _ '(f; (f'; Hf)) '(g; (g'; Hg)) =>
    (Compose f g; (f' ∘ g'; _))
|}.
Next Obligation. now apply termD_Identity. Defined.
Next Obligation. now apply termD_Compose. Defined.

Program Definition Arrows : Category := {|
  obj := obj_idx;
  hom := fun _ _ => list arr_idx;
  homset := fun x y => {| equiv := fun f g => f = g |};
  id := fun _ => [];
  compose := fun _ _ _ f g => f ++ g
|}.
Next Obligation. now rewrite app_nil_r. Defined.
Next Obligation. now rewrite app_assoc. Defined.
Next Obligation. now rewrite app_assoc. Defined.

Program Definition DefinedArrows : Category := {|
  obj := obj_idx;
  hom := fun dom cod => ∃ f f', arrowsD dom cod f ≈ Some f';
  homset := fun x y => {| equiv := fun f g => `1 `2 f ≈ `1 `2 g |};
  id := fun _ => ([]; (id; _));
  compose := fun _ _ _ '(f; (f'; Hf)) '(g; (g'; Hg)) =>
    (f ++ g; (f' ∘ g'; _))
|}.
Next Obligation.
  unfold arrowsD; simpl; rewrite Pos_eq_dec_refl.
  reflexivity.
Qed.
Next Obligation.
  unfold arrowsD in *; simpl in *.
  destruct (arrowsD_work H1 pat0) eqn:?; [|contradiction]; cat.
  destruct (arrowsD_work H0 pat) eqn:?; [|contradiction]; cat.
  equalities'; auto.
  equalities; cat.
  simpl_eq.
  destruct (arrowsD_compose_r Heqo Heqo0), p.
  rewrite e2, Pos_eq_dec_refl; simpl.
  now rewrite e1, X2, X0.
Qed.

Global Program Instance ArrowList_Setoid dom cod :
  Setoid (ArrowList dom cod) := {
  equiv := fun f g => getArrMorph f ≈ getArrMorph g
}.

(** The category of defined arrows, with equivalence up to equivalence of
    denoted morphisms. *)

Program Definition ArrowLists : Category := {|
  obj     := obj_idx;
  hom     := ArrowList;
  homset  := ArrowList_Setoid;
  id      := fun _ => tnil;
  compose := fun _ _ _ => tlist_app
|}.
Next Obligation. proper; now rewrite !getArrMorph_ArrowList_compose, X, X0. Qed.
Next Obligation. now rewrite getArrMorph_ArrowList_compose; cat. Qed.
Next Obligation. now rewrite tlist_app_assoc. Qed.
Next Obligation. symmetry; now rewrite tlist_app_assoc. Qed.

End NormalCategory.
