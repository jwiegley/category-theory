Set Warnings "-notation-overridden".

Require Export Solver.Env.

Generalizable All Variables.

Import VectorNotations.

Inductive Term {a} (tys : Vector.t (obj_idx * obj_idx) a) :
  obj_idx -> obj_idx -> Type :=
  | Ident : ∀ dom, Term tys dom dom
  | Morph (f : arr_idx a) : Term tys (fst (tys[@f])) (snd (tys[@f]))
  | Comp (dom mid cod : obj_idx)
         (f : Term tys mid cod) (g : Term tys dom mid) :
      Term tys dom cod.

Arguments Ident {a tys dom}.
Arguments Morph {a tys} f.
Arguments Comp {a tys dom mid cod} f g.

Section Expr.

Context `{Env}.

Fixpoint term_size `(t : Term tys d c) : nat :=
  match t with
  | Ident    => 1%nat
  | Morph _  => 1%nat
  | Comp f g => 1%nat + term_size f + term_size g
  end.

Inductive Expr : Type :=
  | Top
  | Bottom
  | Equiv (d c : obj_idx) (f g : Term tys d c)
  | And   (p q : Expr)
  | Or    (p q : Expr)
  | Impl  (p q : Expr).

Fixpoint expr_size (t : Expr) : nat :=
  match t with
  | Top           => 1%nat
  | Bottom        => 1%nat
  | Equiv _ _ f g => 1%nat + term_size f + term_size g
  | And p q       => 1%nat + expr_size p + expr_size q
  | Or p q        => 1%nat + expr_size p + expr_size q
  | Impl p q      => 1%nat + expr_size p + expr_size q
  end.

End Expr.
