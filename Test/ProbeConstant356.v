(** * Boundary probe for Structure/Limit/Constant.v (issue #356)

    Mac Lane CWM 2nd ed. §IV.2, book p. 90, Exercise 8.

    WHY THIS FILE EXISTS.  The target carries five [Fail]s of its own and
    they are well formed -- the universe controls are APPLIED, which is
    what makes them discriminate at all (an unapplied polymorphic
    constant never meets the declared levels).  What an in-file negative
    CANNOT do is survive a rename: a whole-file rename moves the [Fail]
    and the constant it names together, so the guard stays green while
    the thing it guarded is gone.  Every negative below therefore names a
    constant of the TARGET, and this file mirrors the target's FULL
    import list -- a probe built on a short prefix is the classic way to
    make a negative pass for a reason it never measured.

    KINDS, separated by the error TEXT rather than by label:
      CONVERSION   ends `(cannot unify "X" and "Y")`
      FORMABILITY  ends `(universe inconsistency: Cannot enforce ...)`
    A [Fail] that SUCCEEDS prints NOTHING under this repo's [coqc], so
    every negative here was stripped and run alone before being trusted.

    WHAT IS PINNED:

    N1 -- the opposite of a constant diagram is NOT the constant diagram
          on the opposite categories, on the nose.  This is why the
          colimit half is built DIRECTLY rather than by instantiating the
          limit half at [C^op]/[J^op]: [ACone n G] is not convertible for
          non-convertible [G].  BOTH DATA FIELDS agree at [eq_refl]
          (controls below), so the difference is confined to the three
          rebuilt law fields.

    N2 -- a functor does not carry a constant diagram to a constant
          diagram on the nose at the ARROW action.
*)
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Limit.Components.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Theory.Connected.Components.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Coq.
Require Import Category.Structure.Limit.Constant.

(** ** Instrument check — must ERROR ("The command has not failed!"). *)
Fail Fail Check Category.

Section OppositeConstant.
Context {J C : Category}.
Context (c : C).

(* CONTROLS: both DATA fields agree on the nose, which is what locates
   the failure of N1 in the LAW fields rather than in the actions. *)
Example probe_op_diag_fobj (x : J) :
  fobj[Opposite_Functor Δ[J](c)] x
    = fobj[@Diagonal (C^op) (J^op) c] x := eq_refl.

Example probe_op_diag_fmap {x y : J^op} (f : x ~{J^op}~> y) :
  fmap[Opposite_Functor Δ[J](c)] f
    = fmap[@Diagonal (C^op) (J^op) c] f := eq_refl.

(* N1. *)
Fail Example probe_op_diag_strict :
  Opposite_Functor Δ[J](c) = @Diagonal (C^op) (J^op) c := eq_refl.

(* CONTROL for N2: the target proves the ≈ form. *)
Check @const_image_fmap_equiv.

(* N2. *)
Fail Example probe_const_image_fmap {D : Category} (F : C ⟶ D)
  {x y : J} (f : x ~{J}~> y) :
  fmap[F ◯ Δ[J](c)] f = fmap[Δ[J](F c)] f := eq_refl.

End OppositeConstant.

(** ** POSITIVE CONTROLS naming the surface, so a rename of any of these
    breaks this file at a NON-[Fail] line. *)

Check @const_acone.
Check @const_cone.
Check @const_IsALimit.
Check @const_IsLimitCone.
Check @const_Limit.
Check @const_acocone.
Check @const_cocone.
Check @const_IsAColimit.
Check @const_IsColimitCocone.
Check @leg_zigzag.
Check @const_cone_step.
Check @const_cone_zigzag.
Check @const_cocone_step.
Check @const_cocone_zigzag.
Check @Diagonal_Faithful.
Check @Diagonal_Full.
Check @Diagonal_Full_via_limit.
Check @const_AbsoluteLimit.
Check @const_AbsoluteColimit.
Check @TwoX_not_terminal.
Check @zero_const_limit_IsTerminalObj.
Check @const_limit_not_from_bare_connected.
Check @two_discrete_const_not_limit.
Check @const_limit_not_from_point_alone.
Check @td_const_IsALimit_product.
Check @Diagonal_Zero_not_Faithful.
Check @Diagonal_Two_Discrete_not_Full.
(* Donor names the negatives depend on: without these a rename would
   leave a [Fail] passing for reference-not-found (#151). *)
Check @Diagonal.
Check @Opposite_Functor.
Check @ConnectedNonempty.
