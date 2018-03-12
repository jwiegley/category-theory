Set Warnings "-notation-overridden".

Require Export Solver.Expr.

Unset Equations WithK.

Generalizable All Variables.

Section Denote.

Context `{Env}.

Import VectorNotations.

(** The denotation Functor from syntactic terms over environment indices. *)

Corollary helper {f} :
  (let '(dom, cod) := tys[@f] in objs dom ~> objs cod)
    -> objs (fst (tys[@f])) ~> objs (snd (tys[@f])).
Proof. destruct (tys[@f]); auto. Defined.
Arguments helper {f} /.

Fixpoint termD {dom cod} (t : Term tys dom cod) : objs dom ~> objs cod :=
  match t with
  | Ident => id
  | Morph f => helper (ith arrs f)
  | Comp f g => termD f ∘ termD g
  end.

Fixpoint exprD (e : Expr) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv _ _ f g => termD f ≈ termD g
  | And p q       => exprD p ∧ exprD q
  | Or p q        => exprD p + exprD q
  | Impl p q      => exprD p -> exprD q
  end.

End Denote.
