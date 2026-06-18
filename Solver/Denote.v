From Equations Require Import Equations.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Solver.Expr.

(** * Denotation: interpreting reified terms back into a category

    This file is the semantic anchor of the reflective solver: the decision
    procedure works by reflection, computing on a syntactic mirror of the goal
    rather than reasoning about it directly
    (https://en.wikipedia.org/wiki/Computational_reflection).  Reification
    (Solver/Reify.v) turns a goal about concrete morphisms into a syntactic
    [Term]/[Expr]; here we interpret that syntax back into the morphisms it
    came from, using the environment carried by [Arrows].  Soundness of the
    decision procedure means: every rewrite Normal.v performs on the syntax
    must be invisible under this denotation.

    The [Term] grammar is the free category on the reified arrows
    (https://ncatlab.org/nlab/show/free+category): objects are [nat] indices
    into [objs] (via [objD]), [Ident] denotes the identity, [Comp] denotes
    composition, and [Morph a] denotes the [a]th reified generator.  A [Term]
    is intrinsically untyped (it does not record its own domain/codomain), so
    [termD_work] is given a domain and *computes* the codomain by threading
    types through the composition, returning the result as a dependent pair
    [∃ cod, objD dom ~> objD cod]; partiality ([option]) absorbs ill-typed
    syntax such as a [Comp] whose middle objects disagree or a [Morph]
    referring to a generator of the wrong domain. *)

Section Denote.

Context `{Arrows}.

Open Scope nat_scope.

(** Look up the [f]th reified generator, requiring its domain to be [dom].
    The stored type [tys[f] = (d', c')] supplies the codomain [cod := c']; we
    then ask [ith_exact] (Lib/IList.v) for the arrow at position [f] indexed by
    [(dom, cod)], which succeeds only when [dom] matches the stored domain
    [d'].  On success we return the arrow paired with its computed codomain;
    an out-of-range [f] or a domain mismatch yields [None].  The default
    index [(0, 0)] handed to [List.nth] is never observed on the success
    path, since a missing [tys] entry forces [ith_exact] to fail. *)
Definition lookup_arr (f : nat) dom :
  option (∃ cod, objD dom ~> objD cod) :=
  let cod := snd (List.nth f tys (0, 0)) in
  match ith_exact f (dom, cod) arrs with
  | Some f => Some (cod; f)
  | _ => None
  end.

(** Denote a [Term] starting from domain [dom], computing its codomain.
    [Ident] is the identity [id : objD dom ~> objD dom].  For [Comp f g] we
    interpret the *right* argument [g] first (from [dom] to some middle object
    [mid]), then [f] from [mid] onward; the result [f ∘ g] composes them in
    diagrammatic-domain order, so [Comp f g] denotes [f ∘ g] exactly as
    reification produced it from [f ∘ g].  The middle object [mid] computed
    for [g] is fed as the domain of [f], which is what makes [f ∘ g] well
    typed; if either subterm fails to denote the whole [Comp] fails. *)
Fixpoint termD_work dom (e : Term) :
  option (∃ cod, objD dom ~> objD cod) :=
  match e with
  | Ident => Some (dom; id)
  | Morph a => lookup_arr a dom
  | Comp f g =>
    match termD_work dom g with
    | Some (mid; g) =>
      match termD_work mid f with
      | Some (y; f) => Some (y; f ∘ g)
      | _ => None
      end
    | _ => None
    end
  end.

Import EqNotations.

(** Denote a [Term] at a *fixed* codomain [cod].  [termD_work] computes
    whatever codomain [y] the term actually has; we then check [y = cod] with
    decidable equality on [Obj] and, on a match, rewrite the morphism along
    that proof to land in [objD dom ~> objD cod].  A codomain mismatch yields
    [None].  The rewrite uses only the [eq_dec] evidence, so this remains
    axiom-free. *)
Definition termD dom cod (e : Term) :
  option (objD dom ~> objD cod) :=
  match termD_work dom e with
  | Some (y; f) =>
    match eq_dec y cod with
    | left H => Some (rew [fun y => _ ~> objD y] H in f)
    | _ => None
    end
  | _ => None
  end.

(** Denote an [Expr] (a propositional combination of morphism equations) as
    a [Type], reading the logical connectives into their [Type]-level
    counterparts: [Top]/[Bottom] as [True]/[False], [And]/[Or]/[Impl] as
    [∧]/[+]/[→].  A leaf [Equiv d c f g] denotes the proposition that the two
    terms, interpreted at domain [d] and codomain [c], are equal morphisms
    ([f ≈ g], the homset setoid equivalence); if either term fails to denote
    at those types the equation is read as [False].  This is the goal that
    Reify.v changes the original conjecture into, and whose truth Decide.v
    establishes by reflection. *)
Fixpoint exprD (e : Expr) : Type :=
  match e with
  | Top      => True
  | Bottom   => False
  | And p q  => exprD p ∧ exprD q
  | Or p q   => exprD p + exprD q
  | Impl p q => exprD p → exprD q

  | Equiv d c f g =>
    match termD d c f, termD d c g with
    | Some f, Some g => f ≈ g
    | _, _ => False
    end
  end.

End Denote.
