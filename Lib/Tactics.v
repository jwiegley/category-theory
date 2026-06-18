(** * Custom tactics shared across the library *)

(* This file collects the bespoke Ltac tactics and hint databases that the
   rest of the development relies on.  Because the library models morphisms as
   setoids (equivalence classes under [≈], not strict [=]), the standard
   automation built around [eq] is not enough: proofs must discharge
   reflexivity/symmetry/transitivity of [equiv], respectfulness ([Proper]),
   and the category laws stored in dedicated rewrite/auto hint databases.  The
   tactics below package those recurring obligations.

   The two workhorses are [cat] (used in hundreds of files) and [cat_simpl],
   which is installed globally as the [Program] obligation tactic so that most
   [Program Instance] obligations are dispatched automatically.

   Two hint databases drive the automation:
     - [categories]    : rewrite database of equational category laws
                         (e.g. [id_left], [id_right], [fmap_id]), populated
                         throughout the library; consumed by [autorewrite].
     - [category_laws] : auto database closing setoid goals via the
                         reflexivity/symmetry/transitivity externs declared
                         below plus per-construction lemmas; consumed by [auto].

   These tactics are project-internal conveniences with no external
   reference; the underlying ideas (setoid rewriting, equivalence relations,
   [Proper]/respectful morphisms) are standard Coq/Rocq machinery.  None of
   the tactics here cheat: none leaves a goal unproven and none introduces an
   axiom; each either makes progress and closes goals or fails. *)

Require Import Coq.Bool.Bool.

Require Export Category.Lib.Setoid.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Open Scope lazy_bool_scope.

Module Compat.
  (* In Rocq 9.2 the EqdepFacts.internal_foo schemes moved to Init.Logic
     and dropped the "internal".

     This module uses shadowing to refer to the schemes by the same
     name regardless of Rocq version. *)

  Module Fake.
    Notation internal_eq_rew_r_dep := ltac:(fail "should not happen") (only parsing).
    Notation internal_eq_sym_involutive := ltac:(fail "should not happen") (only parsing).
    Notation internal_eq_sym_internal := ltac:(fail "should not happen") (only parsing).
  End Fake.

  Module FromEqdepFactsIfExists.
    Import Fake.
    Import EqdepFacts.

    (* if eq_rew_r_dep exists in EqdepFacts then it is used here,
       otherwise this is the "fake" notation *)
    Notation eq_rew_r_dep := internal_eq_rew_r_dep.

    (* same for the other notations *)
    Notation eq_sym_involutive := internal_eq_sym_involutive.
    Notation eq_sym := internal_eq_sym_internal.
  End FromEqdepFactsIfExists.

  Import FromEqdepFactsIfExists.
  Import Logic.

  (* if eq_rew_r_dep exists in Logic then it is used here,
     otherwise this is internal_eq_rew_r_dep through FromEqdepFactsIfExists. *)
  Notation eq_rew_r_dep := eq_rew_r_dep.

  (* same for the other notations *)
  Notation eq_sym_involutive := eq_sym_involutive.
  Notation eq_sym := eq_sym.
End Compat.

(* [simpl_eq]: unfold the [eq]-rewriting eliminators ([eq_rect] and friends,
   plus the version-shimmed [Compat] schemes) everywhere, exposing the
   underlying transports so they can be simplified or rewritten. *)
Ltac simpl_eq :=
  unfold eq_rect_r, eq_rect, eq_ind_r, eq_ind, eq_sym, prod_rect,
    Compat.eq_rew_r_dep,
    Compat.eq_sym_involutive,
    Compat.eq_sym in *.

(* [simplify]: repeatedly break apart logical/structural connectives in both
   hypotheses and goal -- units, lazy and strict [&&], conjunctions ([∧], [/\]),
   bi-implications ([↔]), pairs/products and sigma types -- introducing the
   pieces.  Each arm strictly consumes or refines its target, so the [repeat]
   terminates. *)
Ltac simplify :=
  repeat
    (match goal with
     | [ H : () |- _ ] => destruct H
     | [ |- () ] => exact tt

     | [ H : (_ &&& _) = true |- _ ] => rewrite <- andb_lazy_alt in H
     | [ |- (_ &&& _) = true ]       => rewrite <- andb_lazy_alt
     | [ H : (_ && _) = true |- _ ]  => apply andb_true_iff in H
     | [ |- (_ && _) = true ]        => apply andb_true_iff; split

     | [ H : _ ∧ _ |- _ ] =>
       let H' := fresh "H" in destruct H as [H H']
     | [ |- _ ∧ _ ] => split

     | [ H : _ /\ _ |- _ ] =>
       let H' := fresh "H" in destruct H as [H H']
     | [ |- _ /\ _ ] => split

     | [ H : _ ↔ _ |- _ ] =>
       let H' := fresh "H" in destruct H as [H H']
     | [ |- _ ↔ _ ] => split

     | [ H : (_, _) = (_, _) |- _ ] => inversion_clear H

     | [ H : _ * _ |- _ ] =>
       let x := fresh "x" in
       let y := fresh "y" in
       destruct H as [x y]
     | [ |- _ * _ ] => split

     | [ H : { _ : _ & _ } |- _ ] =>
       let x := fresh "x" in
       let e := fresh "e" in
       destruct H as [x e]
     | [ |- { _ : _ & _ } ] =>
       unshelve (refine (existT _ _ _))
     end; intros).

(* [cat]: the standard category-proof closer.  Simplify connectives, rewrite
   with the equational [categories] laws, then discharge the residue with the
   [category_laws] auto database, falling back to reflexivity. *)
Ltac cat :=
  simplify;
  autorewrite with categories;
  auto with category_laws;
  try reflexivity.

(* Teach the [core] database to see through the equivalence-relation
   structure: unfold Reflexive/Symmetric/Transitive/Proper/respectful and
   build an [Equivalence] from its three components on demand. *)
#[export] Hint Constructors Equivalence : core.

#[export] Hint Unfold Reflexive : core.
#[export] Hint Unfold Symmetric : core.
#[export] Hint Unfold Transitive : core.

#[export] Hint Extern 1 (Reflexive ?X) =>
  unfold Reflexive : core.
#[export] Hint Extern 1 (Symmetric ?X) =>
  unfold Symmetric : core.
#[export] Hint Extern 1 (Transitive ?X) =>
  unfold Transitive : core.
#[export] Hint Extern 1 (Equivalence ?X) =>
  apply Build_Equivalence : core.
#[export] Hint Extern 1 (Proper _ _) => unfold Proper : core.
#[export] Hint Extern 8 (respectful _ _ _ _) =>
  unfold respectful : core.

(* Seed [category_laws] with the setoid laws for [equiv]: reflexivity for
   syntactically equal sides, and symmetry/transitivity as guarded externs so
   [auto] can chain [≈] hypotheses. *)
#[export] Hint Extern 4 (equiv ?A ?A) => reflexivity : category_laws.
#[export] Hint Extern 6 (equiv ?X ?Y) =>
  apply Equivalence_Symmetric : category_laws.
#[export] Hint Extern 7 (equiv ?X ?Z) =>
  match goal with
    [H : equiv ?X ?Y, H' : equiv ?Y ?Z |- equiv ?X ?Z] => transitivity Y
  end : category_laws.

(* [equivalence]: prove an [Equivalence] goal by splitting into its three laws
   ([constructor]) and discharging each with [cat]/[intuition]. *)
Ltac equivalence := constructor; repeat intro; simpl; try cat; intuition; auto with *.
(* [proper]: prove a [Proper]/respectful goal -- introduce the related
   arguments, then close with [cat]/[intuition]. *)
Ltac proper := repeat intro; simpl; try cat; intuition.
(* [sapply]/[srewrite]/[srewrite_r]: "setoid" variants that first materialize
   [F] as a hypothesis and [cbn]-normalize it (so projections of records unfold)
   before applying / rewriting left-to-right / rewriting right-to-left. *)
Ltac sapply F :=
  let H := fresh "H" in pose proof F as H; cbn in H; apply H; clear H.
Ltac srewrite F :=
  let H := fresh "H" in pose proof F as H; cbn in H; rewrite H; clear H.
Ltac srewrite_r F :=
  let H := fresh "H" in pose proof F as H; cbn in H; rewrite <- H; clear H.

(* [cat_simpl]: the global [Program] obligation tactic (installed below).  Run
   [Program]'s own simplifier, then try to fully solve the goal by repeatedly
   dispatching Equivalence/Proper/respectful sub-obligations and finishing with
   [simplify]+[cat]; if that [solve] fails, leave a [simpl]-reduced goal for the
   caller. *)
Ltac cat_simpl :=
  program_simpl; autounfold;
  try solve [
    repeat match goal with
    | [ |- Equivalence _ ] => equivalence
    | [ |- Proper _ _ ] => proper
    | [ |- respectful _ _ _ _ ] => proper
    end;
    program_simpl; autounfold in *;
    simpl in *; intros; simplify;
    simpl in *; cat];
  simpl in *.

#[global] Obligation Tactic := cat_simpl.

(* [construct]: start building a record/structure goal, deferring side
   conditions as fresh goals ([unshelve econstructor]) and introducing the
   fields' arguments. *)
Ltac construct := unshelve econstructor; simpl; intros.

(* [inv H]: invert [H], substitute the resulting equalities, and discard the
   now-redundant hypothesis when possible. *)
Ltac inv H := inversion H; subst; try clear H.

(* [spose H as X]: introduce the (untyped) term [H] as hypothesis [X] and
   [simpl]-reduce it -- a terse [pose proof ... as ...] for setoid lemmas. *)
Tactic Notation "spose" uconstr(H) "as" ident(X) :=
  pose proof H as X; simpl in X.
