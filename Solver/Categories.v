Set Warnings "-notation-overridden".

Require Import Coq.Vectors.Vector.
Require Import Coq.PArith.PArith.

Require Import Category.Lib.
Require Import Category.Lib.Equality.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.One.
Require Import Category.Solver.Env.
Require Import Category.Solver.Expr.
Require Import Category.Solver.Denote.
Require Import Category.Solver.Reflect.
Require Import Category.Solver.Tactics.
Require Import Category.Construction.Coproduct.

Generalizable All Variables.

Section Categories.

(** In the category of simple terms, the best we can do to determine
    equivalence of morphisms is to check that they refer to the same
    arrows. *)

Program Definition STerms : Category := {|
  obj := positive;
  hom := fun _ _ => STerm;
  homset := fun _ _ =>
    {| equiv := fun f g => sarrows f = sarrows g |};
  id  := fun _ => SIdent;
  compose := fun _ _ _ => SComp
|}.
Next Obligation. now rewrite List.app_nil_r. Qed.
Next Obligation. now rewrite List.app_assoc. Qed.
Next Obligation. now symmetry; rewrite List.app_assoc. Qed.

Context `{Env}.

(** In the category of rich terms, equivalence of morphisms refers to the
    equivalence defined by the source category. *)

Program Definition Terms : Category := {|
  obj := obj_idx num_objs;
  hom := Term tys;
  homset := fun _ _ =>
    {| equiv := fun f g => termD f ≈ termD g |};
  id  := fun _ => Ident;
  compose := fun _ _ _ => Comp
|}.

Import VectorNotations.

Program Instance Denote : Terms ⟶ cat := {
  fobj := nth objs;
  fmap := fun _ _ => termD
}.

(*
Program Instance Strip : Terms ⟶ STerms := {
  fobj := Fin_to_pos;
  fmap := fun _ _ => Term_strip
}.

Program Instance Embed : STerms ⟶ Terms ∐ 1 := {
  fobj := fun x =>
    match Pos_to_fin x with
    | None => Datatypes.inr tt
    | Some x => Datatypes.inl x
    end;
  fmap := fun x y f =>
    match Pos_to_fin x, Pos_to_fin y with
    | Some x, Some y =>
      match STerm_embed x y f with
      | Some f => _
      | None => _
      end
    | _, _ => _
    end
}.
*)

End Categories.
