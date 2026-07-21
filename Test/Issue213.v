Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Adjoints.

Generalizable All Variables.

(* Regression test for issue #213 ("Broken in Rocq CI").

   Rocq's own CI builds this library against Rocq master, and it started
   failing in Instance/Adjoints.v with

       File "./Instance/Adjoints.v", line 104, characters 35-45:
       Error: No such assumption.

   Characters 35-45 of that line are the [assumption] of

       Next Obligation.
         equivalence.
         - transitivity (free_functor y); assumption.
         - transitivity (forgetful_functor y); assumption.
       Qed.

   the [Equivalence] obligation of [adj_morphism_setoid], whose relation is a
   PAIR of natural isomorphisms.  Nothing about that proof mentions symmetry,
   and that was the problem.  [equivalence] splits the goal into its three laws
   and discharges each; the reflexivity and symmetry components of the pair
   were closed only because the tactic reached [solve_crelation], a
   PATTERN-LESS [Hint Extern] in the standard library's [crelations] database,
   through a wide [auto].  Which pattern-less hints a wide [auto] reaches, and
   in what order, is a property of the hint database, not anything this library
   states.

   The break was introduced on our side: the commit that narrowed
   [equivalence]'s fallback from [auto with *] to [auto with category_laws]
   removed the tactic's own path to that hint.  The proofs kept building on the
   released Rocq versions only because the [intuition] step inside
   [equivalence] has its own wide [auto with *] leaf, which on those versions
   still reached [solve_crelation].  On Rocq master that leaf no longer reaches
   it, so symmetry stopped being discharged, the first bullet landed on
   [free_functor y ≅ free_functor x] instead of the transitivity goal it was
   written for, and [assumption] was left facing [free_functor y ≅ free_functor
   y].

   The repair is to stop guessing: [adj_morphism_setoid]'s three laws are now
   proved componentwise from [iso_equivalence] (Theory/Isomorphism.v), and
   [equivalence] closes reflexivity and symmetry deterministically and falls
   back only on [category_laws], a database this library populates itself.

   This file pins the invariant that actually matters -- those proofs go
   through with NO wide hint search available at all -- by re-running both the
   old and the repaired script in an environment where the search has been
   taken away, so the fault reproduces on any Rocq version rather than only on
   master. *)

(* Take the wide search away.  [intuition]'s default solver is
   [first [solve [auto] | tryif solve [auto with *] then <warn> else idtac]];
   stubbing it out with [idtac] leaves [intuition] its structural work (it
   still splits the pair) while denying it the [auto with *] leaf -- exactly
   the reach that the released Rocq versions still had and Rocq master lost. *)
Ltac Tauto.intuition_solver ::= idtac.

(* [equivalence]'s body without the deterministic pass and with no wide
   fallback: what the tactic amounts to once neither the explicit search nor
   [intuition]'s implicit one reaches [solve_crelation]. *)
Ltac equivalence_old :=
  constructor; repeat intro; simpl; try cat; intuition.

Section Issue213.

Context {C : Category}.
Context {D : Category}.

(* Verbatim the relation of [adj_morphism_setoid]. *)
Definition issue_213_rel (f g : @adj_morphism C D) : Type :=
  (free_functor f ≅[Fun] free_functor g) *
  (forgetful_functor f ≅[Fun] forgetful_functor g).

(* Confirmation of the reported failure mode.  Denied the wide search, the old
   tactic body leaves the two symmetry components open, so the old script's
   bullets no longer line up with the goals they were written for and no amount
   of [transitivity ...; assumption] closes them.  This is the state Rocq
   master reached; it is recorded here so that a future "simplification" back
   to the old script cannot pass unnoticed. *)
Example issue_213_old_script_needs_the_wide_search : Equivalence issue_213_rel.
Proof.
  unfold issue_213_rel.
  (* The negative half: the old script cannot close the goal here. *)
  assert_fails
    (equivalence_old;
     solve [ transitivity (free_functor y); assumption
           | transitivity (forgetful_functor y); assumption ]).
  (* The positive half, so this stays a live [Qed] rather than an aborted
     sketch: the relation is an equivalence, closed the deterministic way. *)
  constructor.
  - intros f.
    split; reflexivity.
  - intros f g [Hfree Hforget].
    split; symmetry; assumption.
  - intros f g h [Hfree Hforget] [Hfree' Hforget'].
    split; etransitivity; eassumption.
Qed.

(* The mechanism, isolated to the one law that went missing: denied the wide
   search, the old tactic body cannot close symmetry -- though symmetry does
   hold, and closes at once by hand. *)
Example issue_213_symmetry_is_the_missing_law : Symmetric issue_213_rel.
Proof.
  unfold issue_213_rel.
  assert_fails (solve [ repeat intro; simpl; try cat; intuition ]).
  intros f g [Hfree Hforget].
  split; symmetry; assumption.
Qed.

(* The repaired script, run in that same hostile environment: the three laws
   come from [iso_equivalence] componentwise, so no hint search of any width
   is consulted. *)
Example issue_213_equivalence_unaided : Equivalence issue_213_rel.
Proof.
  unfold issue_213_rel.
  constructor.
  - intros f.
    split; reflexivity.
  - intros f g [Hfree Hforget].
    split; symmetry; assumption.
  - intros f g h [Hfree Hforget] [Hfree' Hforget'].
    split; etransitivity; eassumption.
Qed.

(* And the library's own [equivalence] -- the real tactic, not a copy of it --
   still takes the very script that broke in Rocq CI.  This is a guard on
   [Lib/Tactics.v] and not merely on a transcript of it: [intuition]'s
   [auto with *] leaf is stubbed out above, and the tactic's remaining
   fallback is [auto with category_laws], a database that carries no hint
   closing [_ ≅ _].  So it is the tactic's own deterministic reflexivity /
   symmetry pass that discharges those two laws here, and deleting that pass
   fails this example. *)
Example issue_213_tactic_is_deterministic : Equivalence issue_213_rel.
Proof.
  unfold issue_213_rel.
  equivalence.
  - transitivity (free_functor y); assumption.
  - transitivity (forgetful_functor y); assumption.
Qed.

(* Finally, the instance the library actually exports really is an equivalence
   on [adj_morphism], and [≈] resolves to it. *)
Example issue_213_setoid_reflexive (f : @adj_morphism C D) : f ≈ f.
Proof. reflexivity. Qed.

Example issue_213_setoid_symmetric (f g : @adj_morphism C D) : f ≈ g → g ≈ f.
Proof. intros; symmetry; assumption. Qed.

Example issue_213_setoid_transitive (f g h : @adj_morphism C D) :
  f ≈ g → g ≈ h → f ≈ h.
Proof. intros; etransitivity; eassumption. Qed.

End Issue213.
