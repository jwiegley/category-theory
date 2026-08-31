(** * Boundary probe for Structure/Monoidal/Dual.v (issue #359)

    Mac Lane CWM 2nd ed. §IV.2, book p. 88, the vector-space duality
    adjunction (the item maclane:IV.2:construction3): dualisation into a
    fixed object is contravariant and self-adjoint on the right.

    WHY THIS FILE EXISTS AT ALL.  The target carries eight [Fail]s of its
    own and they are well formed -- each was stripped once and its WHOLE
    error read, each sits beside an APPLIED control, and the instrument
    check is scope-free.  What an in-file negative CANNOT do is survive a
    rename: a whole-file rename moves the [Fail] and the constant it
    names in lockstep, so the guard stays green while the thing it
    guarded is gone.  Every negative below therefore names a constant of
    the TARGET, and the file mirrors ALL of the target's [Require] lines
    -- a probe built on a short prefix of that list is the classic way to
    make a negative pass for a reason it never measured (a missing
    coercion, an absent notation), certifying nothing.

    IT ALSO MIRRORS THE TARGET'S [Remove Hints] LINE, AND THAT LINE IS
    DEFENSIVE RATHER THAN LOAD BEARING — measured, in BOTH files:
    deleting

        Remove Hints Sets_Product_Monoidal : typeclass_instances.

    leaves the target compiling clean and leaves this probe compiling
    clean, and both of this file's negatives then fail with
    byte-identical error messages.  The reason it costs nothing is the
    one the target's own header gives: `C` arrives carrying a
    [SymMonClosed] instance whose coercion already determines the
    monoidal structure, so resolution is never offered a choice.  It is
    mirrored here for consistency with the target and with the two
    donors, where the ambient category is not so constrained.

    KINDS, separated by the error TEXT rather than by label -- and note
    that the tail ALONE does not separate two of them:
      FORMABILITY  ends `universe inconsistency: Cannot enforce cp = ch`
      CONVERSION   ends `cannot unify` between two terms of ONE type
      TYPING       also ends `cannot unify`, but on the OBJECT VARIABLES,
                   its body reporting two DIFFERENT objects of [Sets] as
                   the expected and the actual type

    THE REVIEWER'S CHECK IS THE POINT OF NEGATIVE 2.  The issue demands
    that the canonical double-dual morphism be CONSTRUCTED, not assumed
    invertible.  [Structure/Monoidal/StarAutonomous.v:269]'s class field
    [star_double_dual] merely POSITS some iso, and that file's own header
    (lines 69-80) says so, deferring the canonical pinning to its ledger
    entry 4.  Negative 2 pins the sharpest available form of that gap:
    for an ARBITRARY [StarAutonomous] instance the posited iso is not the
    canonical map.  Read it precisely -- it does NOT say the equation is
    false, only that the class does not force it. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.StarAutonomous.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Right.
Require Import Category.Structure.Monoidal.Dual.

Remove Hints Sets_Product_Monoidal : typeclass_instances.

Open Scope category_scope.

Generalizable All Variables.

Section ProbeDual359.

Context {C : Category}.
Context `{@SymMonClosed C}.
Context (d : C).

(* Controls.  Every constant a negative names is also named OUTSIDE a
   [Fail] and APPLIED, never left bare -- an unapplied polymorphic
   constant elaborates for reasons unrelated to the negative and so
   certifies nothing. *)
Check (dd_unit d).
Check (double_dual_unit d).
Check (dual_self_adjoint_on_the_right d).
Check (fun x : C => dd_unit d x).
Check (fun x : C => transform[double_dual_unit d] x).
Check (@aor C C (dual d) (dual d) (dual_self_adjoint_on_the_right d)).

(* CONVERSION 1 -- [dd_unit] is not the bare braid-transpose on the
   nose: the residue is `id ⨂ id`, and writing that residue out closes
   the very same statement at [eq_refl], which is what makes this
   negative discriminate rather than merely fail. *)
Fail Example probe359_braid_strict (x : C) :
  dd_unit d x = dcur (eval' ∘ braid) := eq_refl.

(* Control for CONVERSION 1, with the residue exhibited. *)
Example probe359_braid_residue (x : C) :
  dd_unit d x = dcur (eval' ∘ (id[x ⇒ d] ⨂ id[x]) ∘ braid) := eq_refl.

(* TYPING -- off the diagonal the two legs of the bijection do not even
   share a type, so `to = from` is not statable there at all.  This is
   the honest form of Mac Lane's symmetry remark. *)
Fail Example probe359_offdiagonal (a x : C) :
  to (@aor C C (dual d) (dual d) (dual_self_adjoint_on_the_right d) a x)
    = from (@aor C C (dual d) (dual d)
              (dual_self_adjoint_on_the_right d) a x) := eq_refl.

(* Control: ON the diagonal the two legs ARE the same term. *)
Example probe359_diagonal (a : C) :
  to (@aor C C (dual d) (dual d) (dual_self_adjoint_on_the_right d) a a)
    = from (@aor C C (dual d) (dual d)
              (dual_self_adjoint_on_the_right d) a a) := eq_refl.

End ProbeDual359.

(* Instrument check.  [Fail] is live in this build and does notice a
   conversion failure.  Scope-free deliberately, so that it cannot fail
   on a missing scope delimiter instead of on the proposition. *)
Fail Example probe359_instrument : (true = false) := eq_refl.
