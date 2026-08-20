(** * Boundary probes for the wide walking parallel pair

    Companion to Instance/Parallel/Wide.v, Structure/Equalizer/Wide.v and
    Structure/Coequalizer/Wide.v (issue #322, Mac Lane §III.3, book
    pp. 64-65).  Those files make three strength claims whose negative
    side is a conversion or a universe boundary.  A measurement taken
    only in a header would not be noticed by a refactor, so the negatives
    are pinned here.  **If the [Fail] commands below stop failing, this
    file breaks the build.**

    Each negative is paired with a positive control that must SUCCEED,
    for the reason Test/ProbeQuiverConstructions.v gives: a [Fail] alone
    passes just as happily when a name has been renamed out from under
    it.  The instrument itself was checked — wrapping [Fail] around a
    succeeding command reports "The command has not failed!" and aborts
    compilation — and every negative below was compiled once with the
    [Fail] stripped, to confirm the reported error is the intended one
    and not a syntax, scope or resolution failure: three [cannot unify]
    conversion errors and one genuine universe inconsistency naming the
    declared level.

    The import list is the union of the three target files' own, in
    their order, so that nothing here passes for want of a definition
    that the targets do have in scope.

    THE THREE BOUNDARIES.

    (1) [WideParallel bool] IS NOT [Parallel], AS A TERM.  What is proved
    in Instance/Parallel/Wide.v is [WideParallel_bool_Parallel], an
    isomorphism in [StrictCat] — the strong reading, since [≅[Cat]] in
    this library is equivalence of categories.  It is NOT an equality of
    [Category] records, and the two hom-families are not convertible
    either: the wide shape's hom [ParX ~> ParY] IS the index type, while
    [Parallel]'s is a dependent pair over [bool].  Both are pinned.

    (2) THE DIAGRAM COMPARISON IS AT [Functor_StrictEq_Setoid], NOT AT
    [eq].  [AWide_bool_APair] identifies the wide diagram at a
    two-element family with the binary diagram pulled back along the
    comparison, with [eq_refl] object components — but the two [Functor]
    records are built from different arrow actions and different law
    proofs, so no Leibniz equality is available.

    (3) THE INDEX UNIVERSE IS BOUNDED BY THE AMBIENT HOM UNIVERSE.
    [AWide]'s constraint block contains [i <= h].  Instance/Parallel/
    Wide.v attributes that to [Functor]'s [fmap_respects] field rather
    than to anything this development does; the probe holds it to the
    claim, rejecting [AWide] at an index universe declared strictly
    above the target's hom universe and accepting it strictly below. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Equalizer.Wide.
Require Import Category.Structure.Coequalizer.Wide.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Parallel.Wide.
Require Import Category.Instance.Two.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Cat.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Local Open Scope category_scope.

(** ** (1) The two shapes are isomorphic, not equal *)

(** Positive control: the isomorphism itself, at both strengths. *)
Check (WideParallel_bool_Parallel :
         @Isomorphism StrictCat (WideParallel bool) Parallel).
Check (WideParallel_bool_Parallel_Cat :
         @Isomorphism Cat (WideParallel bool) Parallel).

(** Positive control: an arrow of the wide shape from [ParX] to [ParY] IS
    an index, by conversion.  This is the fact that makes the negative
    below a genuine measurement rather than an accident of packaging. *)
Definition probe_wide_hom_is_index :
  (ParX ~{WideParallel bool}~> ParY) = bool := eq_refl.

(** Negative: the two [Category] records are not Leibniz-equal.  (With
    the [Fail] stripped: cannot unify [WideParallel bool] with
    [Parallel].) *)
Fail Definition wide_bool_is_Parallel :
  WideParallel bool = Parallel := eq_refl.

(** Negative: nor are the hom-families convertible at [ParX], [ParY] —
    [bool] against [∃ b : bool, ParHom b ParX ParY].  (With the [Fail]
    stripped: cannot unify the two types.) *)
Fail Definition wide_bool_hom_is_Parallel_hom :
  (ParX ~{WideParallel bool}~> ParY) = (ParX ~{Parallel}~> ParY) := eq_refl.

(** ** (2) The diagram comparison is up to strict functor equality *)

Section DiagramComparison.

(* [Functor_StrictEq_Setoid] identifies the hom and proof universes of its
   two categories, so a strict comparison against a diagram over
   [WideParallel bool] is a statement about categories with [h = p].  The
   level is FREE, not [Set]; the section declares it strictly above [Set]
   so that the control is not passing for the degenerate reason. *)
Universes dco dch.
Constraint Set < dco.
Constraint Set < dch.

Context (C : Category@{dco dch dch}).
Context (x y : C).
Context (f g : x ~{C}~> y).

(** Positive control: the comparison that IS proved, and the [eq_refl]
    identification of the arrow action that it rests on. *)
Check (AWide_bool_APair f g).

Definition probe_awide_true_is_f :
  fmap[AWide (fun b : bool => if b then f else g)]
    (true : ParX ~{WideParallel bool}~> ParY) = f := eq_refl.

(** Negative: the two functors are not Leibniz-equal.  (With the [Fail]
    stripped: cannot unify the two [Functor] records.) *)
Fail Definition awide_bool_is_APair :
  AWide (fun b : bool => if b then f else g) = APair f g ◯ Par_of_Wide
  := eq_refl.

End DiagramComparison.

(** ** (3) The index universe is bounded by the ambient hom universe *)

(** Positive control: with the index universe declared strictly BELOW the
    target's hom universe, the diagram and both round trips build. *)
Section SmallIndex.

Universes si so sh sp.
Constraint si < sh.
Constraint sh <= sp.

Context (C : Category@{so sh sp}).
Context (I : Type@{si}).
Context (a b : C).
Context (fs : I → a ~{C}~> b).
Context (i0 : I).

Check (AWide fs : WideParallel I ⟶ C).
Check (is_wide_equalizer_limit fs i0).
Check (is_wide_coequalizer_colimit fs i0).

End SmallIndex.

(** Negative: with the index universe declared strictly ABOVE the
    target's hom universe, [AWide] is rejected.  (With the [Fail]
    stripped this reports a universe inconsistency naming the declared
    [bh] against [bi].) *)
Section BigIndex.

Universes bi bo bh bp.
Constraint bh < bi.
Constraint bh <= bp.

Context (C : Category@{bo bh bp}).
Context (I : Type@{bi}).
Context (a b : C).
Context (fs : I → a ~{C}~> b).

Fail Check (AWide fs : WideParallel I ⟶ C).

End BigIndex.

(** ** Sharpness of the pointedness hypothesis, as a standing control

    The two theorems below are not probes — they are proved in the
    target files — but they are the statements the [i0] hypothesis of
    both round trips rests on, so they are checked here alongside the
    [Fail]s that guard the rest. *)
Check (wide_round_trip_needs_point :
         (∀ (q : _2) (e : q ~{_2}~> TwoY),
            IsWideEqualizer two_empty_family q e
            → IsALimit (AWide two_empty_family) q) → False).
Check (wide_coround_trip_needs_point :
         (∀ (q : _2) (e : TwoX ~{_2}~> q),
            IsWideCoequalizer two_empty_family q e
            → IsAColimit (AWide two_empty_family) q) → False).

(** The instrument is not a no-op: a [Fail] on a succeeding command
    aborts compilation with "The command has not failed!".  The
    following line, uncommented, would do exactly that — it is left as a
    comment because a passing build cannot contain it.

      Fail Definition probe_wide_hom_is_index :
  (ParX ~{WideParallel bool}~> ParY) = bool := eq_refl.

    The controls above are the standing check that the [Fail]s are not
    passing for the wrong reason. *)
