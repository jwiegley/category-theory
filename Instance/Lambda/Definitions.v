(*************************************************************************)
(** * Definition of STLC *)
(*************************************************************************)

(** This file containes all of the definitions for a locally-nameless
    representation of a Curry-Style simply-typed lambda calculus.

    This file was generated via Ott from `stlc.ott` and then edited to
    include explanation about the definitions. As a result, it is gathers
    all of the STLC definitions in one place, but the associated exercises
    are found elsewhere in the tutorial.  You'll want to refer back to
    this file as you progress through the rest of the material. *)


Require Import Metalib.Metatheory.

(*************************************************************************)
(** * Syntax of STLC *)
(*************************************************************************)

(** We use a locally nameless representation for the simply-typed lambda
    calculus, where bound variables are represented as natural numbers (de
    Bruijn indices) and free variables are represented as [atom]s.

    The type [atom], defined in the Metatheory library, represents names.
    Equality on names is decidable, and it is possible to generate an atom
    fresh for any given finite set of atoms ([atom_fresh]).

    Note: the type [var] is notation for [atom].
*)

Inductive typ : Set :=  (*r types *)
 | typ_base : typ
 | typ_arrow (T1:typ) (T2:typ).

Inductive exp : Set :=  (*r expressions *)
 | var_b (_:nat)
 | var_f (x:var)
 | abs (e:exp)
 | app (e1:exp) (e2:exp).


(*************************************************************************)
(** * Substitution *)
(*************************************************************************)

(** Substitution replaces a free variable with a term.  The definition
    below is simple for two reasons:
      - Because bound variables are represented using indices, there
        is no need to worry about variable capture.
      - We assume that the term being substituted in is locally
        closed.  Thus, there is no need to shift indices when
        passing under a binder.
*)

(** The [Fixpoint] keyword defines a Coq function.  As all functions in Coq
    must be total.  The annotation [{struct e}] indicates the termination
    metric---all recursive calls in this definition are made to arguments that
    are structurally smaller than [e].

    Note also that [subst_exp] uses [x == y] for decidable equality.  This
    operation is defined in the Metatheory library.  *)

Fixpoint subst_exp (u:exp) (y:var) (e:exp) {struct e} : exp :=
  match e with
  | (var_b n)   => var_b n
  | (var_f x)   => (if x == y then u else (var_f x))
  | (abs e1)    => abs (subst_exp u y e1)
  | (app e1 e2) => app (subst_exp u y e1) (subst_exp u y e2)
end.

(*************************************************************************)
(** * Free variables *)
(*************************************************************************)

(** The function [fv_exp], defined below, calculates the set of free
    variables in an expression.  Because we are using a locally
    nameless representation, where bound variables are represented as
    indices, any name we see is a free variable of a term.  In
    particular, this makes the [abs] case simple.
*)

Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (var_b nat)   => {}
  | (var_f x)   => {{x}}
  | (abs e)     => fv_exp e
  | (app e1 e2) => fv_exp e1 \u fv_exp e2
end.

(** The type [vars] represents a finite set of elements of type [atom].
    The notations for the finite set definitions (empty set `{}`, singleton
    `{{x}}` and union `\u`) is also defined in the Metatheory library.  *)



(*************************************************************************)
(** * Opening *)
(*************************************************************************)

(** Opening replaces an index with a term.  It corresponds to informal
    substitution for a bound variable, such as in the rule for beta reduction.
    Note that only "dangling" indices (those that do not refer to any
    abstraction) can be opened.  Opening has no effect for terms that are
    locally closed.

    Natural numbers are just an inductive datatype with two constructors: [O]
    (as in the letter 'oh', not 'zero') and [S], defined in
    Coq.Init.Datatypes.  Coq allows literal natural numbers to be written
    using standard decimal notation, e.g., 0, 1, 2, etc.
    The function [lt_eq_lt_dec] compares its two arguments for ordering.

    We do not assume that zero is the only unbound index in the term.
    Consequently, we must substract one when we encounter other unbound
    indices (i.e. the [inright] case).

    However, we do assume that the argument [u] is locally closed.  This
    assumption simplifies the implementation since we do not need to shift
    indices in [u] when passing under a binder. *)

Fixpoint open_exp_wrt_exp_rec (k:nat) (u:exp) (e:exp) {struct e}: exp :=
  match e with
  | (var_b n) =>
      match lt_eq_lt_dec n k with
        | inleft (left _) => var_b n
        | inleft (right _) => u
        | inright _ => var_b (n - 1)
      end
  | (var_f x) => var_f x
  | (abs e) => abs (open_exp_wrt_exp_rec (S k) u e)
  | (app e1 e2) => app (open_exp_wrt_exp_rec k u e1)
                      (open_exp_wrt_exp_rec k u e2)
end.

(** Many common applications of opening replace index zero with an
    expression or variable.  The following definition provides a
    convenient shorthand for such uses.  Note that the order of
    arguments is switched relative to the definition above.  For
    example, [(open e x)] can be read as "substitute the variable [x]
    for index [0] in [e]" and "open [e] with the variable [x]."
*)

Definition open_exp_wrt_exp e u := open_exp_wrt_exp_rec 0 u e.


(*************************************************************************)
(** * Notations *)
(*************************************************************************)

Module StlcNotations.
Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0) : exp_scope.
Notation open e1 e2     := (open_exp_wrt_exp e1 e2).
Notation "e ^ x"        := (open_exp_wrt_exp e (var_f x)) : exp_scope.
End StlcNotations.
Import StlcNotations.
Open Scope exp_scope.

(*************************************************************************)
(** * Local closure *)
(*************************************************************************)

(** Recall that [exp] admits terms that contain unbound indices.  We say that
    a term is locally closed when no indices appearing in it are unbound.  The
    proposition [lc_exp e] holds when an expression [e] is locally closed.

    The inductive definition below formalizes local closure such that the
    resulting induction principle serves as the structural induction principle
    over (locally closed) expressions.  In particular, unlike induction for
    type [exp], there are no cases for bound variables.  Thus, the induction
    principle corresponds more closely to informal practice than the one
    arising from the definition of pre-terms.  *)


Inductive lc_exp : exp -> Prop :=
 | lc_var_f : forall (x:var),
     lc_exp (var_f x)
 | lc_abs : forall (e:exp),
      (forall x , lc_exp (open e (var_f x)))  ->
     lc_exp (abs e)
 | lc_app : forall (e1 e2:exp),
     lc_exp e1 ->
     lc_exp e2 ->
     lc_exp (app e1 e2).


(*************************************************************************)
(** * Typing contexts *)
(*************************************************************************)

(** We represent typing contexts as association lists (lists of pairs of
    keys and values) whose keys are [atom]s.
*)

Definition ctx : Set := list (atom * typ).

(** For STLC, contexts bind [atom]s to [typ]s.

    Lists are defined in Coq's standard library, with the constructors [nil]
    and [cons].  The list library includes the [::] notation for cons as well
    as standard list operations such as append, map, and fold. The infix
    operation [++] is list append.

    The Metatheory library extends this reasoning by instantiating the
    AssocList library to provide support for association lists whose keys are
    [atom]s.  Everything in this library is polymorphic over the type of
    objects bound in the environment.  Look in AssocList.v for additional
    details about the functions and predicates that we mention below.
 *)


(*************************************************************************)
(** * Typing relation *)
(*************************************************************************)

(** The definition of the typing relation is straightforward.  In
    order to ensure that the relation holds for only well-formed
    environments, we check in the [typing_var] case that the
    environment is [uniq].  The structure of typing derivations
    implicitly ensures that the relation holds only for locally closed
    expressions.

    Finally, note the use of cofinite quantification in
    the [typing_abs] case.
*)

Inductive typing : ctx -> exp -> typ -> Prop :=
 | typing_var : forall (G:ctx) (x:var) (T:typ),
     uniq G ->
     binds x T G  ->
     typing G (var_f x) T
 | typing_abs : forall (L:vars) (G:ctx) (T1:typ) (e:exp) (T2:typ),
     (forall x , x \notin L -> typing ([(x,T1)] ++ G) (e ^ x) T2)  ->
     typing G (abs e) (typ_arrow T1 T2)
 | typing_app : forall (G:ctx) (e1 e2:exp) (T2 T1:typ),
     typing G e1 (typ_arrow T1 T2) ->
     typing G e2 T1 ->
     typing G (app e1 e2) T2 .


(*************************************************************************)
(** * Values and Small-step Evaluation *)
(*************************************************************************)

(** Finally, we define values and a call-by-name small-step evaluation
    relation. In STLC, abstractions are the only value. *)

Definition is_value (e : exp) : Prop :=
  match e with
  | abs _   => True
  | _       => False
  end.

(** For [step_beta], note that we use [open_exp_wrt_exp] instead of
    substitution --- no variable names are involved.

    Note also the hypotheses in [step] that ensure that the relation holds
    only for locally closed terms.  *)

Inductive step : exp -> exp -> Prop :=
 | step_beta : forall (e1 e2:exp),
     lc_exp (abs e1) ->
     lc_exp e2 ->
     step (app  (abs e1) e2)  (open e1 e2)
 | step_app : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (app e1 e2) (app e1' e2).


Hint Constructors typing step lc_exp.
