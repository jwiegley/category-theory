Inductive type : Type :=
  | base : type
  | arrow : type -> type -> type.

Notation " t ==> t' " := (arrow t t') (at level 20, t' at next level).

Inductive ctx : Type :=
  | empty : ctx
  | snoc : ctx -> type -> ctx.

Notation " G , tau " := (snoc G tau) (at level 20, t at next level).

Fixpoint conc (G D : ctx) : ctx :=
  match D with
    | empty => G
    | snoc D' x => snoc (conc G D') x
  end.

Notation " G ; D " := (conc G D) (at level 20).

Inductive term : ctx -> type -> Type :=
  | var  : forall G tau,      term (G, tau) tau
  | weak : forall G tau,      term G tau -> forall tau', term (G, tau') tau
  | abs  : forall G tau tau', term (G, tau) tau' -> term G (tau ==> tau')
  | app  : forall G tau tau', term G (tau ==> tau') -> term G tau -> term G tau'.

Lemma inf_rule_fun : forall term (G, x) a -> abs G x a