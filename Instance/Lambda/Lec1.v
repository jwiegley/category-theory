(*************************************************************************)
(** * Language specification and variable binding *)
(*************************************************************************)

(** This tutorial demonstrates the use of the Coq proof assistant for
    reasoning about higher-order programming languages, such as those based
    on the lambda calculus, and their implementations. We use a
    simply-typed lambda calculus as a running example.

    Reasoning about languages with first-class functions is difficult because
    of variable binding. In particular, there are two important
    complications that make working with lambda-terms difficult.

  - First, we would like to work up to _alpha-equivalence_. In other words, we
    would like our reasoning about lambda terms to not depend on the names
    that we use for free variables.

    For example, we would like to show that these two terms are
    indistinguishable to the semantics

              [\x.x]  and  [\y.y]

  - Second, substitution should be _capture avoiding_. When we substitute
    terms with free variables, those free variables should never become bound
    by the terms they are being substituted into. This means that sometimes we
    need to rename bound variables to avoid capture. For example,

          [  [ z ~> \x.y ](\y.z) ]    should be   [  \y1.\x.y ]
*)

(** ** Approaches to variable binding

    Unfortunately, variable binding is an _old_ problem. The issue isn't that
    we don't know how to solve this problem, in fact there are _many_, _many_
    different ways to solve this problem and they all have their trade offs.
    I won't include an entire taxonomy of solutions here, but before we go
    further, I want to mention a few relevant alternatives.

    - Only working with closed terms, never reasoning about equivalence

    If we never have to substitute an _open_ term, then we never have to worry
    about variable capture. We can represent binding variables in lambda terms
    using names in a straightforward manner. This approach is the simplest and
    side-steps the two problems shown above. For example, it can be used to
    show type soundness, as is done in Software Foundations.

    However, this approach does not scale. For example, reasoning about
    compiler optimizations requires reasoning about the equivalence of
    transformed open terms.

    - Named terms, with swapping

    We can still work with named terms, even in the presence of free
    variables, as long as we _define_ alpha equivalence and substitution
    appropriately. There are, again, many approaches to these definitions.
    However, the most elegant approach is inspired by Nominal Logic.

    - Locally nameless representation (LN)

    When working in Coq, it is convenient to use a representation that makes
    all alpha-equivalent terms _definitionally_ equivalent. LN does this while
    still providing an interface that is mostly similar to paper proofs.

Other approaches to variable binding include de Bruijn indices, de Bruijn
levels, weak HOAS, PHOAS, locally named, canonically named... etc. Of these,
de Bruijn representations are by far the most commonly used representation in
Coq. *)

(** ** Overview

In this tutorial, we will promote the following approach to variable binding.

- Use a locally nameless representation to _specify_ and reason about the
  semantics

- Use a named representation to _implement_ environment-based interpreters for
  lambda calculus terms. If binders are mostly unique, then this
  implementation avoids additional work.

- The definitions, lemmas and proofs that are needed to work with
  lambda-calculus terms are highly automatable.


In the first part of the tutorial, we will demonstrate the use of a locally
nameless representation to reason about a specification of a call-by-name
lambda calculus. We will state the operational semantics of this language
using a small-step substitution-based inductive relation.  We will use this
specification for metatheoretic reasoning: we will prove _preservation_ and
_progress_ as in Software Foundations.

Next, we will represent the same language using a _nominal representation_ but
specify the semantics using an abstract machine. This abstract machine is
given as a Coq function from machine configurations to machine configurations,
and can be used as an efficient interpreter. This abstract machine features a
heap (i.e. runtime environment for variables) so we will not need to define
capture-avoiding substitution as part of our semantics.

Finally, we will prove that the abstract machine implements the same semantics
as the locally nameless based substitution semantics. *)

(** ** Tool support

The development of this tutorial draws from two coordinating tools that
support working with LN representations.

The Ott tool provides a direct way of generating LN language definitions from
a simple specification language.  The file [stlc.ott] contains the input
specification of the language of this tutorial.  [Definitions.v] is a
commented version of the Ott output. (For comparison, the raw output is in
[Stlc.v]).  The same specifications can also be used to produce LaTeX macros
for typesetting language definitions, demonstrated in [stlc.pdf].


The LNgen tool works with Ott to generate a number of lemmas and auxiliary
definitions for working with LN terms. The file [Lemmas.v] is commented
version of that output. (For comparison, the raw output is in [Stlc_inf.v].)
*)

(*************************************************************************)
(** * The simply-typed lambda calculus in Coq. *)
(*************************************************************************)



(** First, we import a number of definitions from the Metatheory library
    (see Metatheory.v).  The following command makes those definitions
    available in the rest of this file.

    This command will only succeed if you have already run [make] and [make
    install] in the Metatheory directory to compile the Metatheory library. *)
Require Import Metalib.Metatheory.

(** Next, we import the definitions of the simply-typed lambda calculus.
    If you haven't skimmed this file yet, you should do so now. You don't
    need to understand everything in the file at first, but you will need to
    refer back to it in the material below. *)
Require Import Stlc.Definitions.

(** And some notations (defined in `Stlc.Definitions`), but not automatically
    brought into scope. *)
Import StlcNotations.

(** For the examples below, we introduce some sample variable names to
    play with. *)

Definition X : atom := fresh nil.
Definition Y : atom := fresh (X :: nil).
Definition Z : atom := fresh (X :: Y :: nil).

(*************************************************************************)
(** ** Encoding STLC terms *)
(*************************************************************************)


(** We start with examples of encodings in STLC.

  For example, we can encode the expression [(\x. Y x)] as below. We use the
  index [0] because it refers to the closest [abs] to the bound variable
  occurrence. *)

Definition demo_rep1 := abs (app (var_f Y) (var_b 0)).
(*                       ^                        |                   *)
(*                       |                        |                   *)
(*                       --------------------------                   *)



(**  Here is another example: the encoding of [(\x. \y. (y x))].      *)

Definition demo_rep2 := abs (abs (app (var_b 0) (var_b 1))).
(*                       ^    ^              |         |              *)
(*                       |    |              |         |              *)
(*                       |    ----------------         |              *)
(*                       |                             |              *)
(*                       -------------------------------              *)

(** Finally, here is an example where the same bound variable has two
    different indices, and the same index refers to two different
    bound variables.
                         [\y. ((\x. (x y)) y)]                        *)

Definition demo_rep3 :=
           abs (app (abs (app (var_b 0) (var_b 1))) (var_b 0)).
(*          ^         ^              |         |           |          *)
(*          |         |              |         |           |          *)
(*          |         ----------------         |           |          *)
(*          |                                  |           |          *)
(*          ------------------------------------------------          *)


(** *** Exercise: term representation

    Define the following lambda calculus terms using the locally
	 nameless representation.

       "two" : \s. \z. s (s z)

       "COMB_K" : \x. \y. x

       "COMB_S" : \x. \y. \z. x z (y z)

*)

(* SOLUTION *)
Definition two
  := abs (abs (app (var_b 1) (app (var_b 1) (var_b 0)))).

Definition COMB_K :=
	abs (abs (var_b 1)).

Definition COMB_S :=
   abs (abs (abs
        (app (app (var_b 2) (var_b 0)) (app (var_b 1) (var_b 0))))).

(* /SOLUTION *)

(** There are two important advantages of the locally nameless
    representation:
     - Alpha-equivalent terms have a unique representation.
       We're always working up to alpha-equivalence.
     - Operations such as free variable substitution and free
       variable calculation have simple recursive definitions
       (and therefore are simple to reason about).

    Weighed against these advantages are two drawbacks:
     - The [exp] datatype admits terms, such as [abs 3], where
       indices are unbound.
       A term is called "locally closed" when it contains
       no unbound indices.
     - We must define *both* bound variable & free variable
       substitution and reason about how these operations
       interact with each other.
*)


(*************************************************************************)
(** ** Substitution *)
(*************************************************************************)

(* FULL *)
(** The substitution function replaces a free variable with a term.  For
    simplicity, we define a notation for free variable substitution that
    mimics standard mathematical notation.  *)

Check [Y ~> var_f Z](abs (app (var_b 0)(var_f Y))).

(** To demonstrate how free variable substitution works, we need to
    reason about var equality.
*)
Check (Y == Z).

(** The decidable var equality function returns a sum. If the two
    vars are equal, the left branch of the sum is returned, carrying
    a proof of the proposition that the vars are equal.  If they are
    not equal, the right branch includes a proof of the disequality.

    The demo below uses three new tactics:
    - The tactic [simpl] reduces a Coq expression to its normal
      form.
    - The tactic [destruct (Y==Y)] considers the two possible
      results of the equality test.
*)
(* /FULL *)

Example demo_subst1:
  [Y ~> var_f Z] (abs (app (var_b 0) (var_f Y))) = (abs (app (var_b 0) (var_f Z))).
Proof.
(* WORKINCLASS *)
  simpl.
  destruct (Y==Y).
  - auto.
  - destruct n. auto.
Qed. (* /WORKINCLASS *)


(** *** Exercise [subst_eq_var]

    We can use almost the same proof script as
    above to show how substitution works in the variable case. Try it
    on your own.  *)

Lemma subst_eq_var: forall (x : var) u,
  [x ~> u](var_f x) = u.
Proof.
  (* ADMITTED *)
  intros x u.
  simpl.
  destruct (x == x).
  - Case "left".
    auto.
  - Case "right".
    destruct n. auto.
Qed. (* /ADMITTED *)

(** *** Exercise [subst_neq_var] *)

Lemma subst_neq_var : forall (x y : var) u,
  y <> x -> [x ~> u](var_f y) = var_f y.
Proof.
  (* ADMITTED *)
  intros x y u.
  simpl.
  intro Neq.
  destruct (y == x).
  - Case "left".
    destruct Neq. auto.
  - Case "right".
    auto.
Qed. (* /ADMITTED *)

(** *** Exercise [subst_same] *)

Lemma subst_same : forall y e, [y ~> var_f y] e = e.
Proof.
  (* ADMITTED *)
  induction e; simpl; intros; eauto.
  destruct (x == y); subst; eauto.
  rewrite IHe. auto.
  rewrite IHe1. rewrite IHe2. auto.
Qed. (* /ADMITTED *)


(*************************************************************************)
(** ** Free variables *)
(*************************************************************************)

(** The function [fv_exp] calculates the set of free variables in an
    expression.  This function returns a value of type `atoms` --- a finite
    set of variable names.  *)

(** Demo [fsetdec]

   The tactic [fsetdec] solves a certain class of propositions
   involving finite sets. See the documentation in [FSetWeakDecide]
   for a full specification.
*)

Lemma fsetdec_demo : forall (x : atom) (S : atoms),
  x `in` (singleton x `union` S).
Proof.
  fsetdec.
Qed.

(** *** Recommended Exercise [subst_exp_fresh_eq]

    To show the ease of reasoning with these definitions, we will prove a
    standard result from lambda calculus: if a variable does not appear free
    in a term, then substituting for it has no effect.

    HINTS: Prove this lemma by induction on [e].

    - You will need to use [simpl] in many cases.  You can [simpl] everything
      everywhere (including hypotheses) with the pattern [simpl in *].

    - Part of this proof includes a false assumption about free variables.
      Destructing this hypothesis produces a goal about finite set membership
      that is solvable by [fsetdec].

    - The [f_equal] tactic converts a goal of the form [f e1 = f e1'] in to
      one of the form [e1 = e1'], and similarly for [f e1 e2 = f e1' e2'],
      etc.  *)

Lemma subst_exp_fresh_eq : forall (x : var) e u,
  x `notin` fv_exp e -> [x ~> u] e = e.
Proof.
  (* ADMITTED *)
  intros x e u H.
  induction e.
  - Case "var_b".
    auto.
  - Case "var_f".
    simpl.
    destruct (x0 == x).
    + SCase "x0=x".
      subst. simpl fv_exp in H. fsetdec.
    + SCase "x0<>x".
      auto.
  - Case "abs".
    simpl.
    f_equal.
    auto.
  - Case "app".
    simpl in *.
    f_equal.
    auto.
    auto.
Qed. (* /ADMITTED *)

(*************************************************************************)
(** ** Additional Exercises                                              *)
(*************************************************************************)

(**
   Step through the proof that free variables are not introduced by substitution.

   This proof actually is very automatable ([simpl in *; auto.] takes care of
   all but the var_f case), but the explicit proof below demonstrates two
   parts of the finite set library. These two parts are the tactic
   [destruct_notin] and the lemma [notin_union], both defined in the module
   [FSetWeakNotin].

   Before stepping through this proof, you should go to that module to read
   about those definitions and see what other finite set reasoning is
   available.

  *)
Lemma fv_exp_subst_exp_notin : forall x y u e,
   x `notin` fv_exp e ->
   x `notin` fv_exp u ->
   x `notin` fv_exp ([y ~> u]e).
Proof.
  intros x y u e Fr1 Fr2.
  induction e; simpl in *.
  - Case "var_b".
    assumption.
  - Case "var_f".
    destruct (x0 == y).
      assumption.
      simpl. assumption.
  - Case "abs".
    apply IHe. assumption.
  - Case "app".
    destruct_notin.
    apply notin_union.
    apply IHe1.
    assumption.
    apply IHe2.
    assumption.
Qed.

(** Now prove the following properties of substitution and fv *)

(** *** Exercise [subst_exp_fresh_same] *)

Lemma subst_exp_fresh_same :
forall u e x,
  x `notin` fv_exp e ->
  x `notin` fv_exp ([x ~> u] e).
Proof.
 (* ADMITTED *)
  intros.
  induction e; simpl in *; auto.
  - destruct (x0 == x).
    ++ subst. fsetdec.
    ++ simpl. auto.
Qed. (* /ADMITTED *)

(** *** Exercise [fv_exp_subst_exp_fresh] *)

Lemma fv_exp_subst_exp_fresh :
forall e u x,
  x `notin` fv_exp e ->
  fv_exp ([x ~> u] e) [=] fv_exp e.
Proof.
  (* ADMITTED *)
  intros.
  induction e; simpl in *; auto.
  - fsetdec.
  - destruct (x0 == x).
    ++ subst. fsetdec.
    ++ simpl. fsetdec.
  - rewrite IHe1.
    rewrite IHe2.
    fsetdec.
    fsetdec.
    fsetdec.
Qed. (* /ADMITTED *)

(** *** Exercise [fv_exp_subst_exp_upper] *)

Lemma fv_exp_subst_exp_upper :
forall e1 e2 x1,
  fv_exp (subst_exp e2 x1 e1) [<=] fv_exp e2 `union` remove x1 (fv_exp e1).
Proof.
  (* ADMITTED *)
  intros. induction e1; simpl in *.
  - fsetdec.
  - destruct (x == x1); simpl; fsetdec.
  - rewrite IHe1. fsetdec.
  - rewrite IHe1_1. rewrite IHe1_2.
    fsetdec.
Qed. (* /ADMITTED *)


(*************************************************************************)
(*************************************************************************)
(** * LN specific operations and relations *)
(*************************************************************************)
(*************************************************************************)

(** Because we are working with a locally nameless representation, we have
    a few more operations to consider when working with these terms. *)

(*************************************************************************)
(** ** Opening *)
(*************************************************************************)

(** Opening replaces an index with a term and is defined in the Definitions
    module.
*)


(** This next demo shows the operation of [open].  For example, the
    locally nameless representation of the term [(\y. (\x. (y x)) y)] is
    [abs (app (abs (app 1 0)) 0)].  To look at the body _without_ the
    outer abstraction, we need to replace the indices that refer to
    that abstraction with a name.  Therefore, we show that we can open
    the body of the abs above with [Y] to produce
    [app (abs (app Y 0)) Y)].
*)

Lemma demo_open :
  (app (abs (app (var_b 1) (var_b 0))) (var_b 0)) ^ Y =
  (app (abs (app (var_f Y) (var_b 0))) (var_f Y)).
Proof.
  cbn.   (* Like simpl, but unfolds definitions *)
  auto.
Qed.


(*************************************************************************)
(** ** Local closure *)
(*************************************************************************)

(** The local closure judgement classifies terms that have _no_ dangling
   indices.

   Step through this derivation to see why the term [((\x. Y x) Y)]
   is locally closed.
*)

Lemma demo_lc :
  lc_exp (app (abs (app (var_f Y) (var_b 0))) (var_f Y)).
Proof.
  eapply lc_app.
    eapply lc_abs.
     intro x. cbn.
     auto.
    auto.
Qed.

(*************************************************************************)
(** ** Properties about basic operations *)
(*************************************************************************)

(** The most important properties about open and lc_exp concern their
    relationship with the free variable and subst functions.

    For example, one important property is shown below: that we can commute
    free and bound variable substitution.

    We won't prove this lemma as part of the tutorial (it is proved in
    [Lemmas.v]), but it is an important building block for reasoning about
    LN terms.

    NOTE: the name of this lemma was automatically generated by LNgen. If
    we have multiple syntactic classes and multiple sorts of variables,
    we need to distinguish the different forms of substitution from
    eachother.

 *)

Lemma subst_exp_open_exp_wrt_exp :
forall e3 e1 e2 x1,
  lc_exp e1 ->
  [x1 ~> e1] (open e3 e2) = open ([x1 ~> e1] e3) ([x1 ~> e1] e2).
Proof.
Admitted.

(** *** Exercise [subst_var] *)

(** The lemma above is most often used with [e2] as some fresh
    variable. Therefore, it simplifies matters to define the following useful
    corollary.

    HINT: Do not use induction.  Rewrite with [subst_exp_open_exp_wrt_exp] and
    [subst_neq_var].

*)

Lemma subst_var : forall (x y : var) u e,
  y <> x ->
  lc_exp u ->
  ([x ~> u] e) ^ y = [x ~> u] (e ^ y).
Proof.
  (* ADMITTED *)
  intros x y u e Neq H.
  rewrite subst_exp_open_exp_wrt_exp with (e2 := var_f y); auto.
  rewrite subst_neq_var; auto.
Qed.   (* /ADMITTED *)

(** *** Exercise [subst_exp_intro] *)

(** This next lemma states that opening can be replaced with variable
    opening and substitution.

    This lemma, like many about [open_exp_wrt_exp], should be proven
    via induction on the term [e]. However, during this induction, the
    binding depth of the term changes, so to make sure that we have
    a flexible enough induction hypothesis, we must generalize the
    argument to [open_exp_wrt_exp_rec].  *)

Lemma subst_exp_intro : forall (x : var) u e,
  x `notin` (fv_exp e) ->
  open e u = [x ~> u](e ^ x).
Proof.
  intros x u e FV_EXP.
  unfold open.
  generalize 0.
  induction e; intro n0; simpl.
  (* ADMITTED *)
  - Case "var_b".
    destruct (lt_eq_lt_dec n n0).
    destruct s. simpl. auto.
    rewrite subst_eq_var. auto.
    simpl. auto.
  - Case "var_f".
    destruct (x0 == x). subst. simpl in FV_EXP. fsetdec. auto.
  - Case "abs".
    f_equal. simpl in FV_EXP. apply IHe. auto.
  - Case "app".
    simpl in FV_EXP.
    f_equal.
    apply IHe1. auto.
    apply IHe2. auto.
Qed. (* /ADMITTED *)


(** *** Exercise [fv_exp_open_exp_wrt_exp_upper] *)

(** Now prove the following lemmas about the free variables of an opened
    term.

    The structure of this proof follows that of the proof above. You should
    prove this by induction on the term [e1], after appropriately
    generalizing the induction hypothesis. Remember to use [fsetdec] for
    reasoning about properties of atom sets. Also note that you can
    [rewrite] with atom set inequalities in the hypotheses list. *)

Lemma fv_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  fv_exp (open_exp_wrt_exp e1 e2) [<=] fv_exp e2 `union` fv_exp e1.
Proof.
  (* ADMITTED *)
  intros e1 e2.
  unfold open.
  generalize 0.
  induction e1; intro n0; simpl.
  - destruct (lt_eq_lt_dec n n0).
    destruct s. simpl. fsetdec.
    fsetdec.
    simpl. fsetdec.
  - fsetdec.
  - rewrite IHe1. fsetdec.
  - rewrite IHe1_1. rewrite IHe1_2.
    fsetdec.
Qed. (* /ADMITTED *)

(*************************************************************************)
(** ** Forall quantification in [lc_exp].                                *)
(*************************************************************************)

(** Let's look more closely at lc_abs and lc_exp_ind. *)

Check lc_exp_ind.

(** The induction principle for the lc_exp relation is particularly strong
   in the abs case.

<<
 forall P : exp -> Prop,
       ...
       (forall e : exp,
        (forall x : atom, lc_exp (e ^ x)) ->
        (forall x : atom, P (e ^ x)) -> P (abs e)) ->
       ...
       forall e : exp, lc_exp e -> P e
>>

  This principle says that to prove that a property holds for an abstraction,
  we can assume that the property holds for the body of the abstraction,
  opened with *any* variable that we like.

*)


Check lc_abs.

(** However, on the other hand, when we show that an abstraction is locally
   closed, we need to show that its body is locally closed, when
   opened by any variable.

   That can sometimes be a problem. *)

Lemma subst_lc0 : forall (x : var) u e,
  lc_exp e ->
  lc_exp u ->
  lc_exp ([x ~> u] e).
Proof.
  intros x u e He Hu.
  induction He.
  - Case "lc_var_f".
    simpl.
    destruct (x0 == x).
      auto.
      auto.
  - Case "lc_abs".
    simpl.
    eapply lc_abs.
    intros x0.
    rewrite subst_var.
    apply H0.
Abort.

(** Here we are stuck. We don't know that [x0] is not equal to [x],
    which is a preconduction for [subst_var].

    The solution is to prove an alternative introduction rule for
    local closure for abstractions.  In the current rule, we need
    to show that the body of the abstraction is locally closed,
    no matter what variable we choose for the binder.


<<
  | lc_abs : forall e,
      (forall x:var, lc_exp (open e x)) ->
      lc_exp (abs e)
>>

    An easier to use lemma requires us to only show that the body
    of the abstraction is locally closed for a _single_ variable.

    As before, we won't prove this lemma as part of the tutorial,
    (it too is proved in Lemmas.v) but we will use it as part of
    our reasoning.
*)
Lemma lc_abs_exists : forall (x : var) e,
      lc_exp (e ^ x) ->
      lc_exp (abs e).
Admitted.

(** For example, with this addition, we can complete the proof above. *)

Lemma subst_exp_lc_exp : forall (x : var) u e,
  lc_exp e ->
  lc_exp u ->
  lc_exp ([x ~> u] e).
Proof.
  intros x u e He Hu.
  induction He.
  - Case "lc_var_f".
    simpl.
    destruct (x0 == x); auto.
  - Case "lc_abs".
    simpl.
    pick fresh x0 for {{x}}.  (* a tactic to generate x0 <> x *)
    apply (lc_abs_exists x0).
    rewrite subst_var; auto.
  - Case "lc_app".
    simpl. eauto.
Qed.

(*************************************************************************)
(** ** Local closure and relations                                       *)
(*************************************************************************)

(** All of our semantics only hold for locally closed terms, and we can
    prove that.

    Sometimes, the proofs are straightforward; sometimes a little work is
    needed.
*)

Lemma step_lc_exp1 : forall e1 e2, step e1 e2 -> lc_exp e1.
Proof. intros e1 e2 H. induction H; auto. Qed.

(** *** Exercise [typing_to_lc_exp]

    Use [lc_abs_exists] below to show that well-typed terms
    are locally closed. *)

Lemma typing_to_lc_exp : forall E e T,
  typing E e T -> lc_exp e.
Proof.
  (* ADMITTED *)
  intros E e T H. induction H; eauto.
  pick fresh x1 for L.
  apply (lc_abs_exists x1).
  auto.
Qed.
(* /ADMITTED *)

(** *** Exercise [step_lc_exp2]

    Use properties such as [subst_exp_intro] and [subst_exp_lc_exp]
    to show that the result of a step is _also_ locally closed.
 *)

Lemma step_lc_exp2 : forall e1 e2, step e1 e2 -> lc_exp e2.
Proof.
  (* ADMITTED *)
  induction 1; auto.
  pick fresh x for (fv_exp e1).
  inversion H; subst.
  rewrite (subst_exp_intro x).
  apply subst_exp_lc_exp; auto.
  fsetdec.
Qed. (* /ADMITTED *)
