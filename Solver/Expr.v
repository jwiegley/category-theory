Set Warnings "-notation-overridden".

Require Import Coq.Vectors.Vector.
Require Import Coq.PArith.PArith.
Require Import Coq.micromega.Lia.

From Equations Require Import Equations.
Require Import Equations.Type.EqDec.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Solver.Env.

Generalizable All Variables.

Import VectorNotations.

(** Transform a 0-based [Fin.t] into a 1-based [positive]. *)
Fixpoint Fin_to_pos {n} (f : Fin.t n) : positive :=
  match f with
  | Fin.F1 => 1%positive
  | Fin.FS x => Pos.succ (Fin_to_pos x)
  end.

Definition Pos_to_fin {n} (p : positive) : option (Fin.t n).
Proof.
  generalize dependent n.
  induction p using Pos.peano_rect; intros.
    destruct n.
      exact None.
    exact (Some Fin.F1).
  destruct n.
    exact None.
  destruct (IHp n).
    exact (Some (Fin.FS t)).
  exact None.
Defined.

(** Weakly-typed terms, only correct in certain environments. *)

Inductive STerm : Set :=
  | SIdent : STerm
  | SMorph (a : positive) : STerm
  | SComp (f : STerm) (g : STerm) : STerm.

Derive NoConfusion NoConfusionHom Subterm EqDec for positive STerm.

(** Richly-typed terms, always correct by construction, and isomorphic to the
    denoted terms. *)

Inductive Term {a o} (tys : Vector.t (obj_pair o) a) :
  obj_idx o → obj_idx o → Type :=
  | Ident {dom} : Term tys dom dom
  | Morph (f : arr_idx a) :
    Term tys (fst (tys[@f])) (snd (tys[@f]))
  | Comp {dom mid cod : obj_idx o}
         (f : Term tys mid cod) (g : Term tys dom mid) :
    Term tys dom cod.

Derive Signature NoConfusion for Term.

Arguments Ident {a o tys dom}.
Arguments Morph {a o tys} f.
Arguments Comp {a o tys dom mid cod} f g.

Inductive TermRel {a o} (tys : Vector.t (obj_pair o) a) :
  STerm → ∀ {dom cod : obj_idx o}, Term tys dom cod → Type :=
  | IsIdent {dom} : TermRel tys SIdent (Ident (dom:=dom))
  | IsMorph (f : arr_idx a) :
    @TermRel _ _ tys (SMorph (Fin_to_pos f))
       (fst (tys[@f])) (snd (tys[@f])) (Morph f)
  | IsComp {dom mid cod : obj_idx o} {sf sg}
      (f : Term tys mid cod) (g : Term tys dom mid) :
    TermRel tys sf f →
    TermRel tys sg g →
    TermRel tys (SComp sf sg) (Comp f g).

Derive Signature for TermRel.

Inductive SExpr : Set :=
  | STop
  | SBottom
  | SEquiv (x y : positive) (f g : STerm)
  | SAnd   (p q : SExpr)
  | SOr    (p q : SExpr)
  | SImpl  (p q : SExpr).

Derive NoConfusion NoConfusionHom Subterm for SExpr.
