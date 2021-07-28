Set Warnings "-notation-overridden".

Require Import Coq.Vectors.Vector.
Require Import Coq.PArith.PArith.
Require Import Coq.micromega.Lia.

Require Import Category.Lib.
Require Import Category.Solver.Env.

Generalizable All Variables.

Import VectorNotations.

(** Richly-typed terms, always correct by construction, and isomorphic to the
    denoted terms. *)

Inductive Term {a o} (tys : Vector.t (obj_pair o) a) :
  obj_idx o -> obj_idx o -> Type :=
  | Ident : ∀ dom, Term tys dom dom
  | Morph (f : arr_idx a) : Term tys (fst (tys[@f])) (snd (tys[@f]))
  | Comp (dom mid cod : obj_idx o)
         (f : Term tys mid cod) (g : Term tys dom mid) :
      Term tys dom cod.

Arguments Ident {a o tys dom}.
Arguments Morph {a o tys} f.
Arguments Comp {a o tys dom mid cod} f g.

(** Weakly-typed terms, only correct in certain environments, but if that
    holds, then isomorphic to the denoted terms. *)

Inductive STerm : Type :=
  | SIdent : STerm
  | SMorph (a : positive) : STerm
  | SComp (f : STerm) (g : STerm) : STerm.

Fixpoint sterm_size (t : STerm) : nat :=
  match t with
  | SIdent    => 1%nat
  | SMorph _  => 1%nat
  | SComp f g => 1%nat + sterm_size f + sterm_size g
  end.

Inductive SExpr : Type :=
  | STop
  | SBottom
  | SEquiv (x y : positive) (f g : STerm)
  | SAnd   (p q : SExpr)
  | SOr    (p q : SExpr)
  | SImpl  (p q : SExpr).

Fixpoint sexpr_size (t : SExpr) : nat :=
  match t with
  | STop           => 1%nat
  | SBottom        => 1%nat
  | SEquiv _ _ f g => 1%nat + sterm_size f + sterm_size g
  | SAnd p q       => 1%nat + sexpr_size p + sexpr_size q
  | SOr p q        => 1%nat + sexpr_size p + sexpr_size q
  | SImpl p q      => 1%nat + sexpr_size p + sexpr_size q
  end.

Remark all_sexprs_have_size e : (0 < sexpr_size e)%nat.
Proof. induction e; simpl; lia. Qed.
