(** * Boundary probe for Adjunction/Right.v (issue #358)

    Mac Lane CWM 2nd ed. §IV.2 Definition 2, book p. 89 (the item
    maclane:IV.2:def2) -- a pair of contravariant
    functors each adjoint on the right, together with Mac Lane's own
    warning that this relation is NOT the ordinary adjunction read
    through an opposite category.

    WHY THIS FILE EXISTS AT ALL.  [Adjunction/Right.v] carries ten
    [Fail]s of its own and they are well formed -- each was stripped
    once and its whole error message read, each sits beside a control
    that must succeed, and the instrument check is scope-free.  What an
    in-file negative CANNOT do is survive a rename: a whole-file rename
    moves the [Fail] and the constant it names in lockstep, so the guard
    stays green while the thing it guarded is gone.  Every negative
    below therefore names a constant of the TARGET, and the file mirrors
    ALL of the target's [Require] lines -- a probe built on a short
    prefix of that list is the classic way to make a negative pass for a
    reason it never measured (a missing coercion, an absent notation),
    certifying nothing.

    KINDS, separated by the error TEXT rather than by label:
      TYPING       a plain `The term "H" has type ... while it is
                   expected to have type ...`, with NO `cannot unify`
                   and no universe clause
      CONVERSION   ends `(cannot unify "X" and "Y")`
      FORMABILITY  ends `(universe inconsistency: Cannot enforce ...)`

    THE FIRST NEGATIVE IS THE REVIEWER'S BAR.  The question that decides
    whether this issue has content at all is whether
    [AdjointOnTheRight S T] is merely an abbreviation for the ordinary
    [T^op ⊣ S].  It is not, and negative 1 is what says so: stripped, it
    reports

      The term "H" has type "T^op ⊣ S" while it is expected to have type
       "AdjointOnTheRight S T".

    -- a plain type mismatch.  The two are nevertheless INTERDERIVABLE,
    which is what the controls name: [Adjunction_of_AdjointOnTheRight]
    and [AdjointOnTheRight_of_Adjunction] pass both ways and all four
    round trips hold at [eq_refl] in the target.  So the class is a
    genuine record that is equivalent to, and not definitionally equal
    to, the ordinary adjunction at the opposite categories.

    NOTE THE ORIENTATION, which is easy to get backwards.  BOTH
    readings are correct and both are delivered: [T^op ⊣ S] is the one
    matching the direction of the book's bijection
    [A(a, T x) ≅ X(x, S a)], while [S^op ⊣ T] matches its INVERSE, and
    the target ships the second as the primed orientation with passages
    both ways.  So which one is "the" reduction is a question of which
    way the bijection is read, NOT an error in either spelling.
    Negative 2 is the reverse direction of negative 1, and negative 3
    separates the right-adjoint class from the left-adjoint one.

    WHAT IS NOT GUARDED HERE.  The target's four FORMABILITY negatives
    need section-local [Universes]/[Constraint] declarations naming
    levels that do not exist outside them, so they stay in the target
    beside their controls.  They measure TWO DIFFERENT identifications,
    two negatives each: that hom is identified with proof (rejected at
    [Opposite], and independently at [Sets] with no functor in the
    command at all), and that A's hom is identified with X's.  Neither
    is a claim about a name this file could rename-test. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Adjunction.Right.

Open Scope category_scope.

Generalizable All Variables.

Section ProbeRight358.

Context {A X : Category}.
Context {S : (A^op) ⟶ X}.
Context {T : (X^op) ⟶ A}.

(* Controls.  Every constant a negative names is also named OUTSIDE a
   [Fail] and APPLIED, never left bare -- an unapplied polymorphic
   constant elaborates for reasons unrelated to the negative and so
   certifies nothing. *)
Check (AdjointOnTheRight S T).
Check (AdjointOnTheLeft S T).
Check (@Adjunction (A^op) X (Opposite_Functor T) S).
Check @Adjunction_of_AdjointOnTheRight.
Check @AdjointOnTheRight_of_Adjunction.
Check (MutuallyRightAdjoint S T).
Check (fun H : AdjointOnTheRight S T =>
         MutuallyRightAdjoint_of_AdjointOnTheRight S T H).
Check (fun H : MutuallyRightAdjoint S T =>
         AdjointOnTheRight_of_MutuallyRightAdjoint S T H).
Check @AdjointOnTheRight_sym.
Check @right_does_not_imply_left.
Check @Chain3_not_AdjointOnTheLeft.
Check @Chain3_AdjointOnTheRight.
Check @Powerset_not_AdjointOnTheLeft.
Check @right_does_not_imply_left_in_Sets.

(* TYPING 1 -- the reviewer's bar: the class is not an abbreviation. *)
Fail Definition probe358_not_an_abbreviation
  (H : @Adjunction (A^op) X (Opposite_Functor T) S) :
  AdjointOnTheRight S T := H.

(* TYPING 2 -- and not in the other direction either. *)
Fail Definition probe358_not_an_abbreviation_rev
  (H : AdjointOnTheRight S T) :
  @Adjunction (A^op) X (Opposite_Functor T) S := H.

(* TYPING 3 -- right and left are different classes, not one class
   spelled two ways.  The MATHEMATICAL separation is the target's
   [right_does_not_imply_left], a theorem over all categories; this
   negative only records that they are not definitionally equal. *)
Fail Definition probe358_right_is_not_left
  (H : AdjointOnTheRight S T) : AdjointOnTheLeft S T := H.

(* CONVERSION 4-5 -- the hom-set presentation and the unit/counit
   presentation are interderivable but their round trips are NOT
   [eq_refl]: the classes are rebuilt rather than returned.  Contrast
   the FOUR round trips against the ordinary adjunction, which the
   target pins at [eq_refl]. *)
Fail Example probe358_MRA_round_strict (H : MutuallyRightAdjoint S T) :
  MutuallyRightAdjoint_of_AdjointOnTheRight S T
    (AdjointOnTheRight_of_MutuallyRightAdjoint S T H) = H := eq_refl.

Fail Example probe358_aor_MRA_round_strict (H : AdjointOnTheRight S T) :
  AdjointOnTheRight_of_MutuallyRightAdjoint S T
    (MutuallyRightAdjoint_of_AdjointOnTheRight S T H) = H := eq_refl.

End ProbeRight358.

(* Instrument check.  [Fail] is live in this build and does notice a
   conversion failure.  Scope-free deliberately, so that it cannot fail
   on a missing scope delimiter instead of on the proposition. *)
Fail Example probe358_instrument : (true = false) := eq_refl.
