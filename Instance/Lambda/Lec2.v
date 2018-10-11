(*************************************************************************)
(**                                                                      *)
(** * Typing: preservation and progress                                  *)
(**                                                                      *)
(*************************************************************************)

Require Import Metalib.Metatheory.
Require Import Stlc.Definitions.
Import StlcNotations.

Require Import Stlc.Lemmas.

Require Import Stlc.Lec1.

(*************************************************************************)
(** * Typing contexts *)
(*************************************************************************)

(** We represent contexts as association lists (lists of pairs of
    keys and values) whose keys are [atom]s.   *)

(** For STLC, contexts bind [atom]s to [typ]s.  We define an
    abbreviation [ctx] for the type of these contexts.

    Lists are defined in Coq's standard library, with the constructors
    [nil] and [cons].  The list library includes the [::] notation
    for cons as well as standard list operations such as append, map,
    and fold. The infix operation "++" is list append.

    The Metatheory library extends this reasoning by instantiating the
    AssocList library to provide support for association lists whose
    keys are [atom]s.  Everything in this library is polymorphic over
    the type of objects bound in the context.  Look in AssocList
    for additional details about the functions and predicates that we
    mention below.  *)

(** Context equality *)

(** When reasoning about contexts, we often need to talk about
    bindings in the "middle" of an context. Therefore, it is common
    for lemmas and definitions to use list append in their statements.
    Unfortunately, list append is associative, so two Coq expressions may
    denote the same context even though they are not equal.

    The tactic [simpl_env] reassociates all concatenations of
    contexts to the right.  *)

Lemma append_assoc_demo : forall (E0 E1 E2 E3:ctx),
  E0 ++ (E1 ++ E2) ++ E3 = E0 ++ E1 ++ E2 ++ E3.
Proof.
  intros.
  auto. (* Does nothing. *)
  simpl_env.
  reflexivity.
Qed.

(** To make contexts easy to read, instead of building them from
    [nil] and [cons], we prefer to build them from the following
    components:
      - [nil]: The empty list.
      - [one]: Lists consisting of exactly one item.
      - [++]:  List append.
*)

(** The simpl_env tactic actually puts lists built from only nil, one
    and [++] into a "normal form". This process reassociates all appends
    to the right, removes extraneous nils and converts cons to singleton
    lists with an append.
*)
(* /FULL *)



Lemma simpl_env_demo : forall (x y:atom) (T1 T2:typ) (E F:ctx),
   ([(x, T1)] ++ nil) ++ (y,T2) :: (nil ++ E) ++ F =
   [(x,T1)] ++ [(y, T2)] ++ E ++ F.
Proof.
   intros.
   (* simpl_env puts the left side into the normal form. *)
   simpl_env.
   reflexivity.
Qed.


(** Context operations. *)

(** The ternary predicate [binds] holds when a given binding is
    present somewhere in an context.
*)

Lemma binds_demo : forall (x:atom) (T:typ) (E F:ctx),
  binds x T (E ++ [(x, T)] ++ F).
Proof.
  auto.
Qed.

(** The function [dom] computes the domain of an context,
    returning a finite set of [atom]s. Note that we cannot use Coq's
    equality for finite sets, we must instead use a defined relation
    [=] for atom set equality.
 *)

Lemma dom_demo : forall (x y : atom) (T : typ),
  dom [(x, T)] [=] singleton x.
Proof.
  auto.
Qed.

(** The unary predicate [uniq] holds when each atom is bound at most
    once in an context.
*)

Lemma uniq_demo : forall (x y : atom) (T : typ),
  x <> y -> uniq ([(x,T)] ++ [(y, T)]).
Proof.
  auto.
Qed.

(*************************************************************************)
(** * Typing relation and cofinite quantification *)
(*************************************************************************)

(** The typing relation in the STLC definition states the typing rule for
    abstractions in a particular way.

<<
typing_abs
     : forall (L : atoms) (G : ctx) (T1 : typ) (e : exp) (T2 : typ),
       (forall x : atom,
        x `notin` L -> typing ([(x, T1)] ++ G) (open e (var_f x)) T2) ->
       typing G (abs e) (typ_arrow T1 T2)
>>

   To show that abstractions are well-typed, we must show that the body
   of the abstraction is well-typed for any choice of variable, except
   those from some unspecified set `L`.

   This type of rule differs from the quantification in the
   [lc_abs] rule (which does not restrict the variables at all) or
   the [lc_abs_exists] version (which only applies for one particular
   variable. We call this version "co-finite" quantification.

   To see why this version is necessary, we will start with a more
   traditional version of the rules that only uses a single variable
   in the abs rule and then see what goes wrong.
   (We say that the [typing_e] judgement below uses "exists-fresh"
   quantification in the abs rule.)

*)

Inductive typing_e : ctx -> exp -> typ -> Prop :=
  | typing_e_var : forall E (x : atom) T,
      uniq E ->
      binds x T E ->
      typing_e E (var_f x) T
  | typing_e_abs : forall x E e T1 T2,
      x `notin` dom E \u fv_exp e ->
      typing_e ([(x, T1)] ++ E) (e ^ x) T2 ->
      typing_e E (abs e) (typ_arrow T1 T2)
  | typing_e_app : forall E e1 e2 T1 T2,
      typing_e E e1 (typ_arrow T1 T2) ->
      typing_e E e2 T1 ->
      typing_e E (app e1 e2) T2.
Hint Constructors typing_e.


(*************************************************************************)
(** ** Weakening  *)
(*************************************************************************)

(** Weakening states that if an expression is typeable in some
    context, then it is typeable in any well-formed extension of
    that context.  This property is needed to prove the
    substitution lemma.

    As stated below, this lemma is not directly proveable.  The
    natural way to try proving this lemma proceeds by induction on the
    typing derivation for [e].
*)


Lemma typing_weakening_0 : forall E F e T,
  typing_e E e T ->
  uniq (F ++ E) ->
  typing_e (F ++ E) e T.
Proof.
  intros E F e T H J.
  induction H; auto.
  Case "typing_abs".
    apply (typing_e_abs x).
    (* ... stuck here ... *)
Abort.

(** We are stuck in the [typing_abs] case because the induction
    hypothesis [IHtyping_e] applies only when we weaken the context at its
    head.  In this case, however, we need to weaken the context in
    the middle; compare the conclusion at the point where we're stuck
    to the hypothesis [H], which comes from the given typing derivation.

    We can obtain a more useful induction hypothesis by changing the
    statement to insert new bindings into the middle of the
    context, instead of at the head.  However, the proof still
    gets stuck, as can be seen by examining each of the cases in
    the proof below.

    Note: To view subgoal n in a proof, use the command "[Show n]".
    To work on subgoal n instead of the first one, use the command
    "[Focus n]".
*)

Lemma typing_weakening_strengthened_0 : forall (E F G : ctx) e T,
  typing_e (G ++ E) e T ->
  uniq (G ++ F ++ E) ->
  typing_e (G ++ F ++ E) e T.
Proof.
  intros E F G e T H J.
  induction H.
  Case "typing_var".
    (* The G0 looks strange in the [typing_var] case. *)
  Focus 2.
  Case "typing_abs".
    (* The [typing_abs] case still does not have a strong enough IH. *)
Abort.

(** The hypotheses in the [typing_var] case include an context
    [G0] that that has no relation to what we need to prove.  The
    missing fact we need is that [G0 = (G ++ E)].

    The problem here arises from the fact that Coq's [induction]
    tactic lets us only prove something about all typing derivations.
    While it's clear to us that weakening applies to all typing
    derivations, it's not clear to Coq, because the context is
    written using concatenation.  The [induction] tactic expects that
    all arguments to a judgement are variables.  So we see [E0] in the
    proof instead of [(G ++ E)].

    The solution is to restate the lemma.  For example, we can prove

<<
  forall E F E' e T, typing E' e T ->
  forall G, E' = G ++ E -> uniq (G ++ F ++ E) -> typing (G ++ F ++ E) e T.
>>

    The equality gets around the problem with Coq's [induction]
    tactic.  The placement of the [(forall G)] quantifier gives us a
    sufficiently strong induction hypothesis in the [typing_abs] case.

    However, we prefer not to state the lemma in the way shown above,
    since it is not as readable as the original statement.  Instead,
    we use a tactic to introduce the equality within the proof itself.
    The tactic [(remember t as t')] replaces an object [t] with the
    identifier [t'] everywhere in the goal and introduces an equality
    [t' = t] into the context.  It is often combined with [generalize
    dependent], as illustrated below.
*)

Lemma typing_weakening_strengthened_1 :  forall (E F G : ctx) e T,
  typing_e (G ++ E) e T ->
  uniq (G ++ F ++ E) ->
  typing_e (G ++ F ++ E) e T.
Proof.
  intros E F G e T H.
  remember (G ++ E) as E'.
  generalize dependent G.
  induction H; intros G0 Eq Uniq; subst.
  - Case "typing_var". auto.
  - Case "typing_abs".
    eapply (typing_e_abs x).
    (* STILL STUCK! *)
Abort.

Print typing_abs.

(** At this point, we are very close. However, there is still one issue. We
    cannot show that [x] is fresh for the weakened context [F].

    This is the difficulty with the definition of [typing_e]. As in the local
    closure judgement, the induction hypotheses is not strong enough in the
    [abs] case.

    However, this time, we take a slightly different solution, with the
    cofinite quantification of the [typing_abs] rule.

<<
| typing_abs :
    forall (L : atoms) (G : ctx) (T1 : typ) (e : exp) (T2 : typ),
    (forall x, x `notin` L -> typing ([(x, T1)] ++ G) (e ^ x) T2) ->
    typing (abs e) (typ_arrow T1 T2) >>
>>

   The advantage of this definition is that it is easier to derive
   the "exists-fresh" version of the rule
   [typing_e_abs] as a lemma, than the version we used in [lc_exp].
   (See below, we prove this lemma after we show substitution.) At the same
   time, this version of the rule is sufficiently expressive to complete
   the proof of weakening.

*)


(** *** Exercise [typing_weakening_strengthened]

    Complete the proof below, using the [typing] relation from [Definitions.v].

    HINTS:

       - The [typing_var] case follows from [binds_weaken], the
         weakening lemma for the [binds] relation.

       - The [typing_abs] case follows from the induction
         hypothesis, but the [apply] tactic may be unable to unify
         things as you might expect.

           -- You'll need to specify the set to avoid with
              (L := dom (G0 ++ F ++ E) \u L)).

           -- In order to apply the induction hypothesis, use
              [rewrite_env] to reassociate the list operations.

           -- After applying the induction hypothesis, use
              [simpl_env] to use [uniq_push].

           -- Here, use [auto] to solve facts about finite sets of
              atoms, since it will simplify the [dom] function behind
              the scenes.  [fsetdec] does not work with the [dom]
              function.

       - The [typing_app] case follows directly from the induction
         hypotheses.
  *)

Lemma typing_weakening_strengthened :  forall (E F G : ctx) e T,
  typing (G ++ E) e T ->
  uniq (G ++ F ++ E) ->
  typing (G ++ F ++ E) e T.
Proof.
  intros E F G e T H.
  remember (G ++ E) as E'.
  generalize dependent G.
  induction H; intros G0 Eq Uniq; subst.
 (* ADMITTED *)
  - Case "typing_var".
    apply typing_var.
      apply Uniq.
      apply binds_weaken. auto.
  - Case "typing_abs".
    apply typing_abs with (L := dom (G0 ++ F ++ E) \u L).
    intros x Frx.
    rewrite_env (([(x, T1)] ++ G0) ++ F ++ E).
    apply H0.
      auto.
      simpl_env. reflexivity.
      simpl_env. apply uniq_push.
        apply Uniq.
        auto.
  - Case "typing_app".
    eapply typing_app.
      eapply IHtyping1. reflexivity. apply Uniq.
      eapply IHtyping2. reflexivity. apply Uniq.
Qed. (* /ADMITTED *)


(** *** Demo [typing_weakening]

    We can now prove our original statement of weakening.  The only
    interesting step is the use of the rewrite_env tactic.
*)

Lemma typing_weakening : forall (E F : ctx) e T,
    typing E e T ->
    uniq (F ++ E) ->
    typing (F ++ E) e T.
Proof.
  intros E F e T H J.
  rewrite_env (nil ++ F ++ E).
  apply typing_weakening_strengthened; auto.
Qed.



(*************************************************************************)
(** ** Substitution *)
(*************************************************************************)

(** Having proved weakening, we can now prove the usual substitution
    lemma, which we state both in the form we need and in the
    strengthened form needed to make the proof go through.

<<
  typing_subst_simple : forall E e u S T z,
    typing ([(z,S)] ++ E) e T ->
    typing E u S ->
    typing E ([z ~> u] e) T

  typing_subst : forall E F e u S T z,
    typing (F ++ [(z,S)] ++ E) e T ->
    typing E u S ->
    typing (F ++ E) ([z ~> u] e) T
>>

    The proof of the strengthened statement proceeds by induction on
    the given typing derivation for [e].  The most involved case is
    the one for variables; the others follow from the induction
    hypotheses.
*)


(** *** Exercise [typing_subst_var_case]

    Below, we state what needs to be proved in the [typing_var] case
    of the substitution lemma.  Fill in the proof.

    Proof sketch: The proof proceeds by a case analysis on [(x == z)],
    i.e., whether the two variables are the same or not.

      - If [(x = z)], then we need to show [(typing (F ++ E) u T)].
        This follows from the given typing derivation for [u] by
        weakening and the fact that [T] must equal [S].

      - If [(x <> z)], then we need to show [(typing (F ++ E) x T)].
        This follows by the typing rule for variables.

    HINTS: Lemmas [binds_mid_eq], [uniq_remove_mid],
    and [binds_remove_mid] are useful.

  *)

Lemma typing_subst_var_case : forall (E F : ctx) u S T (z x : atom),
  binds x T (F ++ [(z,S)] ++ E) ->
  uniq (F ++ [(z,S)] ++ E) ->
  typing E u S ->
  typing (F ++ E) ([z ~> u] (var_f x)) T.
Proof.
  intros E F u S T z x H J K.
  simpl.
 (* ADMITTED *)
  destruct (x == z).
  Case "x = z".
    subst.
    assert (T = S).
      eapply binds_mid_eq. apply H. apply J.
    subst.
    apply typing_weakening.
      apply K.
      eapply uniq_remove_mid. apply J.
  Case "x <> z".
    apply typing_var.
      eapply uniq_remove_mid. apply J.
      eapply binds_remove_mid. apply H. apply n.
Qed. (* /ADMITTED *)




(** *** Exercise [typing_subst]

    Complete the proof of the substitution lemma. The proof proceeds
    by induction on the typing derivation for [e].  The initial steps
    should use [remember as] and [generalize dependent] in a manner
    similar to the proof of weakening.

   HINTS:
      - Use the lemma proved above for the [typing_var] case.

      - The [typing_abs] case follows from the induction hypothesis.
          -- Use [simpl] to simplify the substitution.

          -- In order to use the induction hypothesis, use [subst_var]
             to push the substitution under the opening operation.

          -- Recall the lemma [typing_to_lc_c] and the [rewrite_env]
             and [simpl_env] tactics.

      - The [typing_app] case follows from the induction hypotheses.
        Use [simpl] to simplify the substitution.
*)

Lemma typing_subst : forall (E F : ctx) e u S T (z : atom),
  typing (F ++ [(z,S)] ++ E) e T ->
  typing E u S ->
  typing (F ++ E) ([z ~> u] e) T.
Proof.
(* ADMITTED *)
  intros E F e u S T z He Hu.
  remember (F ++ [(z,S)] ++ E) as E'.
  generalize dependent F.
  induction He.
  - Case "typing_var".
    intros F Eq.
    subst.
    eapply typing_subst_var_case. apply H0. apply H. apply Hu.
  - Case "typing_abs".
    intros F Eq.
    subst.
    simpl.
    apply typing_abs with (L := {{z}} \u L).
    intros y Fry.
    rewrite subst_var.
    rewrite_env (([(y,T1)] ++ F) ++ E).
    apply H0.
      auto.
      simpl_env. reflexivity.
    (* The following subgoals are from [rewrite subst_var]. *)
    auto.
    eapply typing_to_lc_exp. apply Hu.
  - Case "typing_app".
    intros F Eq. subst. simpl. eapply typing_app.
      apply IHHe1. reflexivity.
      apply IHHe2. reflexivity.
Qed. (* /ADMITTED *)

(** *** Exercise [typing_subst_simpl]

    Complete the proof of the substitution lemma stated in the form we
    need it.  The proof is similar to that of [typing_weakening].

    HINT: You'll need to use [rewrite_env] to prepend [nil],
    and [simpl_env] to simplify nil away.
*)

Lemma typing_subst_simple : forall (E : ctx) e u S T (z : atom),
  typing ([(z,S)] ++ E) e T ->
  typing E u S ->
  typing E ([z ~> u] e) T.
Proof.
(* ADMITTED *)
  intros E e u S T z H J.
  rewrite_env (nil ++ E).
  eapply typing_subst.
    simpl_env. apply H.
    apply J.
Qed. (* /ADMITTED *)

(*************************************************************************)
(** * Type soundness *)
(*************************************************************************)


(*************************************************************************)
(** ** Preservation *)
(*************************************************************************)

(** *** Recommended Exercise [preservation]

    Complete the proof of preservation.  In this proof, we proceed by
    induction on the given typing derivation.  The induction
    hypothesis has already been appropriately generalized by the given
    proof fragment.

    Proof sketch: By induction on the typing derivation for [e].

      - [typing_var] case: Variables don't step.

      - [typing_abs] case: Abstractions don't step.

      - [typing_app] case: By case analysis on how [e] steps. The
        [step_beta] case is interesting, since it follows by the
        substitution lemma.  The others follow directly from the
        induction hypotheses.
*)

  (* HINTS:

       - Use [auto] and [eauto], especially with [;], to solve
         "uninteresting" subgoals.

       - Use [inversion] to perform case analyses and to rule out
         impossible cases.

       - In the [step_beta] subcase of the [typing_app] case:

          -- Use [inversion] on a typing judgement to obtain a
             hypothesis about when the body of the abstraction is
             well-typed.

          -- Use [subst_exp_intro] to rewrite the [open] operation
             into an [open] followed by a [subst].  You'll need to
             pick a fresh variable first.

  *)

Lemma preservation : forall (E : ctx) e e' T,
  typing E e T ->
  step e e' ->
  typing E e' T.
Proof.
  intros E e e' T H.
  generalize dependent e'.
  induction H; intros e' J.
(* ADMITTED *)
  Case "typing_var".
    inversion J.
  Case "typing_abs".
    inversion J.
  Case "typing_app".
    inversion J; subst; eauto.
    SCase "step_beta".
      inversion H; subst.
      pick fresh y for (L \u fv_exp e0).
      rewrite (subst_exp_intro y); auto.
      eapply typing_subst_simple; auto.
Qed. (* /ADMITTED *)

(*************************************************************************)
(** ** Progress *)
(*************************************************************************)

(** *** Exercise [progress]

    Complete the proof of the progress lemma.  The induction
    hypothesis has already been appropriately generalized by the given
    proof fragment.

    Proof sketch: By induction on the typing derivation for [e].

      - [typing_var] case: Can't happen; the empty context doesn't
        bind anything.

      - [typing_abs] case: Abstractions are values.

      - [typing_app] case: Applications reduce.  The result follows
        from an exhaustive case analysis on whether the two components
        of the application step or are values and the fact that a
        value must be an abstraction.
*)

  (* HINTS:

       - Use [auto] and [eauto], especially with [;], to solve
         "uninteresting" subgoals.

       - Use [inversion] to rule out impossible cases.

       - The lemma [typing_to_lc] will be useful for reasoning
         about local closure.

       - In the [typing_app] case:

          -- Use [destruct] to perform a case analysis on the
             conclusions of the induction hypotheses.

          -- Use [inversion] on a [value] judgement to determine that
             the value must be an abstraction.
  *)



Lemma progress : forall e T,
  typing nil e T ->
  is_value e \/ exists e', step e e'.
Proof.
  intros e T H.

  (* It will be useful to have a "non-destructed" form of the given
     typing derivation, since [induction] takes apart the derivation
     it is called on. *)
  assert (typing nil e T); auto.

  (* [remember nil as E] fails here because [nil] takes an implicit
     argument that Coq is unable to infer.  By prefixing [nil] with
     [@], we can supply the argument to nil explicitly. *)
  remember (@nil (atom * typ)) as E.

  induction H; subst.

(* ADMITTED *)
  - Case "typing_var".
    inversion H1.
  - Case "typing_abs".
    left.
    simpl. auto.
  - Case "typing_app".
    right.
    destruct IHtyping1 as [V1 | [e1' Step1]]; auto.
      + SCase "e1 is a value".
        destruct e1; inversion V1; subst.
        inversion H.
        exists (open_exp_wrt_exp e1 e2); eauto using typing_to_lc_exp.
      + SCase "e1 is not a value".
        exists (app e1' e2).
        apply step_app.
          eapply typing_to_lc_exp; eauto.
          assumption.
Qed. (* /ADMITTED *)


(*************************************************************************)
(** * Tactic support *)
(*************************************************************************)

(** When picking a fresh var or applying a rule that uses cofinite
    quantification, choosing a set of vars to be fresh for can be
    tedious.  In practice, it is simpler to use a tactic to choose the
    set to be as large as possible.

    The tactic [gather_atoms] is used to collect together all the
    atoms in the context.  It relies on an auxiliary tactic,
    [gather_atoms_with] (from MetatheoryAtom), which maps a function
    that returns a finite set of atoms over all hypotheses with the
    appropriate type.
*)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  constr:(A `union` B `union` C `union` D).

(** A number of other, useful tactics are defined by the Metatheory
    library, and each depends on [gather_atoms].  By redefining
    [gather_atoms], denoted by the [::=] in its definition below, we
    automatically update these tactics so that they use the proper
    notion of "all atoms in the context."

    For example, the tactic [(pick fresh x)] chooses an atom fresh for
    "everything" in the context.  It is the same as [(pick fresh x for
    L)], except where [L] has been computed by [gather_atoms].

*)



(*************************************************************************)
(** * Renaming *)
(*************************************************************************)

(** Substitution and weakening together give us a property we call
   renaming: (see [typing_rename below] that we can change the name
   of the variable used to open an expression in a typing
   derivation. In practice, this means that if a variable is not
   "fresh enough" during a proof, we can use this lemma to rename it
   to one with additional freshness constraints.

   Renaming is used below to show the correspondence between the
   exists-fresh version of the rules with the cofinite version, and
   also to show that typechecking is decidable.
*)

(** However, before we prove renaming, we need an auxiliary lemma about
    typing judgments which says that terms are well-typed only in
    unique contexts.
*)

Lemma typing_uniq : forall E e T,
  typing E e T -> uniq E.
Proof.
  intros E e T H.
  induction H; auto.
  - Case "typing_abs".
    pick fresh x.
    assert (uniq ([(x, T1)] ++ G)); auto.
    solve_uniq.
Qed.


(** Demo: the proof of renaming.

   Note that this proof does not proceed by induction: even if we add
   new typing rules to the language, as long as the weakening and
   substution properties hold we can use this proof.
*)
Lemma typing_rename : forall (x y : atom) E e T1 T2,
  x `notin` fv_exp e ->
  y `notin` dom E ->
  typing ([(x, T1)] ++ E) (e ^ x) T2 ->
  typing ([(y, T1)] ++ E) (e ^ y) T2.
Proof.
  intros x y E e T1 T2 Fr1 Fr2 H.
  destruct (x == y).
  - Case "x = y".
    subst; eauto.
  - Case "x <> y".
    assert (J : uniq ([(x, T1)] ++ E)).
      eapply typing_uniq; eauto.
    assert (J' : uniq E).
      inversion J; eauto.
    rewrite (@subst_exp_intro x); eauto.
    rewrite_env (nil ++ [(y, T1)] ++ E).
    apply typing_subst with (S := T1).
    simpl_env.
    + SCase "(open x s) is well-typed".
      apply typing_weakening_strengthened. eauto. auto.
    + SCase "y is well-typed".
      eapply typing_var; eauto.
Qed.


(*************************************************************************)
(** ** Exists-Fresh Definition *)
(*************************************************************************)

(** The use of cofinite quantification may make some people worry that we
    are not formalizing the "right" language. Below, we show that
    the "exists-fresh" version of the rules is the same as the cofinite
    version. *)

Lemma typing_abs_exists : forall E e T1 T2 (x : atom),
      x `notin` dom E \u fv_exp e ->
      typing ([(x,T1)] ++ E) (e ^ x) T2 ->
      typing E (abs e) (typ_arrow T1 T2).
Proof.
  intros.
  apply typing_abs with (L := dom E \u fv_exp e).
  intros y Fr.
  apply typing_rename with (x:=x); auto.
Qed.

(** *** Exercise [exists_cofinite] *)

Lemma exists_cofinite : forall E e T,
    typing_e E e T -> typing E e T.
Proof.
  (* ADMITTED *)
  intros.
  induction H; eauto.
  eapply typing_abs_exists with (x:=x); eauto.
Qed. (* /ADMITTED *)

(** *** Exercise [cofinite_exists] *)

Lemma cofinite_exists : forall G e T,
    typing G e T -> typing_e G e T.
Proof. (* ADMITTED *)
  intros. induction H; eauto.
  pick fresh x.
  eapply typing_e_abs with (x:=x); eauto.
Qed. (* /ADMITTED *)

(***********************************************************************)
(** ** Additional Exercises                                            *)
(***********************************************************************)

(** *** Challenge Exercise [fv_in_dom]

   We also want a property that states that the free variables of well-typed
   terms are contained within the domain of their typing contexts.

 *)
Lemma fv_in_dom : forall G e T,
    typing G e T -> fv_exp e [<=] dom G.
Proof.
  (* ADMITTED *)
  intros G e T H.
  induction H; simpl.
  - Case "typing_var".
    apply binds_In in H0.
    fsetdec.
  - Case "typing_abs".
    pick fresh x.
    assert (Fx : fv_exp (e ^ x) [<=] dom ([(x,T1)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (e ^ x)) by
        eapply fv_exp_open_exp_wrt_exp_lower.
    fsetdec.
  - Case "typing_app".
    fsetdec.
Qed. (* /ADMITTED *)
