Set Warnings "-notation-overridden".

Require Import Coq.Bool.Bool.
Require Import Coq.PArith.PArith.
Require Import Coq.omega.Omega.

Require Import Equations.Equations.

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Solver.Lib.
Require Import Solver.Env.
Require Import Solver.Expr.Term.
Require Import Solver.Expr.Denote.

Generalizable All Variables.

Section ExprValid.

Context `{Env}.

Inductive ValidTerm (dom : obj_idx) : obj_idx -> Term -> Type :=
  | IdentityTerm : ValidTerm dom dom Identity
  | MorphTerm : forall cod f f',
      arrs f = Some (dom; (cod; f'))
        -> ValidTerm dom cod (Morph f)
  | ComposeTerm : forall mid cod f g,
      ValidTerm mid cod f
        -> ValidTerm dom mid g
        -> ValidTerm dom cod (Compose f g).

Definition getTerm {dom cod} `(a : ValidTerm dom cod f) : Term := f.
Arguments getTerm {dom cod f} a /.

Equations getMorph {dom cod} `(a : ValidTerm dom cod f) :
  objs dom ~> objs cod :=
  getMorph IdentityTerm := id;
  getMorph (MorphTerm f _) := f;
  getMorph (ComposeTerm _ _ f g) := getMorph f ∘ getMorph g.

Definition ValidTerm_size {dom cod} `(a : ValidTerm dom cod f) : nat :=
  term_size f.
Arguments ValidTerm_size {dom cod f} a /.

Definition ValidTerm_compose {dom mid cod}
           `(f : ValidTerm mid cod t)
           `(g : ValidTerm dom mid u) : ValidTerm dom cod (Compose t u) :=
  ComposeTerm dom mid cod t u f g.
Arguments ValidTerm_compose {dom mid cod t} f {u} g /.

End ExprValid.
