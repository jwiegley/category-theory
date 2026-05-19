Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Strict.

Generalizable All Variables.

(** * Tactics for strict monoidal categories

    In a [StrictMonoidal] category, the structural isomorphisms
    [tensor_assoc], [unit_left], [unit_right] are identities
    (transported along the object-level Leibniz equalities
    [strict_assoc_obj], [strict_unit_left_obj], [strict_unit_right_obj]).

    The [strict_collapse] tactic rewrites these isomorphisms to their
    transported-identity forms.  After [strict_collapse], the goal is
    free of explicit [tensor_assoc] / [unit_left] / [unit_right]
    references — what remains are dependent-transport-of-identity
    expressions.  In a CONCRETE strict monoidal category where the
    object-level equations are [eq_refl], these transports reduce
    further via [cbn] / [simpl]; in an ABSTRACT setting the transport
    is opaque but can be reasoned about via the [transported_iso_*]
    lemmas in [Strict.v]. *)

(** ** [strict_collapse]: replace structural isos with transported-id form

    Rewrites until fixpoint using the six [strict_*_to] / [strict_*_from]
    lemmas.  Use [?] so each pattern is optional — the tactic does not
    fail if none applies. *)
Ltac strict_collapse :=
  repeat (rewrite ?strict_assoc_to ||
          rewrite ?strict_assoc_from ||
          rewrite ?strict_unit_left_to ||
          rewrite ?strict_unit_left_from ||
          rewrite ?strict_unit_right_to ||
          rewrite ?strict_unit_right_from).

(** ** [strict_collapse_in H]: same, targeting hypothesis [H]. *)
Tactic Notation "strict_collapse" "in" hyp(H) :=
  repeat (rewrite ?strict_assoc_to in H ||
          rewrite ?strict_assoc_from in H ||
          rewrite ?strict_unit_left_to in H ||
          rewrite ?strict_unit_left_from in H ||
          rewrite ?strict_unit_right_to in H ||
          rewrite ?strict_unit_right_from in H).

(** ** [strict_collapse_all]: rewrite EVERYWHERE.

    Goal AND every hypothesis. *)
Ltac strict_collapse_all :=
  repeat (rewrite ?strict_assoc_to in * ||
          rewrite ?strict_assoc_from in * ||
          rewrite ?strict_unit_left_to in * ||
          rewrite ?strict_unit_left_from in * ||
          rewrite ?strict_unit_right_to in * ||
          rewrite ?strict_unit_right_from in *).
