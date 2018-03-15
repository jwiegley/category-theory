Set Warnings "-notation-overridden".

Require Export Category.Solver.Env.

Generalizable All Variables.

Import VectorNotations.

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
  | Equiv (d c : obj_idx num_objs) (f g : Term tys d c)
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
