Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Span.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Limit.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cocomplete.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Adjunction.Diagonal.Finite.

Generalizable All Variables.

(** * Probe: the boundaries Adjunction/Diagonal/Finite.v measures

   That file records its rejections and carries no [Fail] of its own. A
   measurement is not a guard. This file pins them beside controls that
   must SUCCEED.

   The import list is the target's own, in its order, with the target
   appended. A probe on a shorter prefix can fail for a missing-reference
   reason and read as a mathematical rejection.

   TWO PROBE HAZARDS THIS FILE WAS WRITTEN AROUND, both of which cost a
   FALSE PASS when first attempted and are recorded here so the next
   reader does not repeat them:

   (1) A [Fail] that succeeds PRINTS NOTHING under this repo's [coqc]. You
       cannot read a negative's reason from the compile log; every one must
       be stripped and run on its own. That is how each was classified.

   (2) **[Roof^op = Roof] IS A FALSE PASS.** `Functor/Opposite.v` opens
       `functor_scope`, and inside an [eq] argument there is no expected
       type for the category scope to win on, so `^op` parses as the
       FUNCTOR opposite and the command fails with
       "The term "Roof" has type "Category" while it is expected to have
       type "?C ⟶ ?D"" — NOTATION, not mathematics. Written that
       way the negative certifies nothing. Both are therefore spelled
       [Opposite Roof] and [Opposite Parallel] below. (Measured: the
       `^op` spelling really does fail with that message.)

   KINDS, separated by the error TEXT:
     CONVERSION  ends `(cannot unify "X" and "Y")`
     TYPING      reports a type mismatch with no `cannot unify` clause
     FORMABILITY ends `(universe inconsistency: Cannot enforce ...)` *)

(** ** Instrument check — must ERROR ("The command has not failed!"). *)
Fail Fail Check Category.

(** ** CONVERSION — the four elementary arrows are the adjunction's
    unit/counit components only up to a residual identity.

    Each control is the SAME statement with the residue restored, which is
    what locates the difference at a `∘ id` (limit side) or `id ∘`
    (colimit side) rather than at the leg. *)

Section FiniteConversion.
Context {C : Category} (L : HasLimitsOfShape Parallel C).
Context (M : HasColimitsOfShape Parallel C).

(* NEGATIVE 1 — the equalizing arrow. *)
Fail Definition probe_eq_arrow (F : Parallel ⟶ C) :
  eq_arrow L F = lim_leg L F ParX := eq_refl.

(* CONTROL 1. *)
Definition probe_eq_arrow_id (F : Parallel ⟶ C) :
  eq_arrow L F = lim_leg L F ParX ∘ id := eq_refl.

(* NEGATIVE 2 — the coequalizing arrow, dual residue. *)
Fail Definition probe_coeq_arrow (F : Parallel ⟶ C) :
  coeq_arrow M F = colim_inj M F ParY := eq_refl.

(* CONTROL 2 — note the residue is on the OTHER side, which is the
   handedness the colimit rows carry throughout. *)
Definition probe_coeq_arrow_id (F : Parallel ⟶ C) :
  coeq_arrow M F = id ∘ colim_inj M F ParY := eq_refl.

End FiniteConversion.

Section FiniteConversionRoof.
Context {C : Category} (P : HasLimitsOfShape (Opposite Roof) C).
Context (Q : HasColimitsOfShape Roof C).

(* NEGATIVE 3 — the pullback's first projection. *)
Fail Definition probe_pb_fst (F : Opposite Roof ⟶ C) :
  pb_fst P F = lim_leg P F RNeg := eq_refl.

(* CONTROL 3. *)
Definition probe_pb_fst_id (F : Opposite Roof ⟶ C) :
  pb_fst P F = lim_leg P F RNeg ∘ id := eq_refl.

(* NEGATIVE 4 — the pushout's first injection. *)
Fail Definition probe_po_in1 (F : Roof ⟶ C) :
  pushout_inj1 Q F = colim_inj Q F RNeg := eq_refl.

(* CONTROL 4. *)
Definition probe_po_in1_id (F : Roof ⟶ C) :
  pushout_inj1 Q F = id ∘ colim_inj Q F RNeg := eq_refl.

End FiniteConversionRoof.

(** ** TYPING — "the unit is the identity" is not merely false, it does not
    typecheck, and that is the sharper statement.

    For `Δ ⊣ lim` the unit at x is `x ~> lim (Δ[J](x))`: a morphism between
    two DIFFERENT objects. So the exercise's "unit the identity" cannot be
    read literally. What the target delivers instead is invertibility under
    a sufficient connectedness condition on the shape. *)

Section UnitTyping.
Context {C : Category} (L : HasLimitsOfShape Parallel C) (x : C).

(* NEGATIVE 5. Stripped, this reports a TYPE MISMATCH with NO `cannot
   unify` clause and no universe clause:
     The term "id" has type "x ~> x" while it is expected to have type
     "x ~> lim_obj L (fobj[Diagonal Parallel] x)".                       *)
Fail Definition probe_unit_is_id : dia_unit L x = id[x] := eq_refl.

(* CONTROL 5: the unit IS nameable and well-typed at its real type, so the
   negative is about the identity, not about `dia_unit`. *)
Check (dia_unit L x).

End UnitTyping.

(** ** CONVERSION — neither walking shape is its own opposite

    This is why the pushout row is CONSTRUCTED rather than read off the
    pullback row, and why `Δ[Roof^op]` appears on the pullback side. Both
    are spelled with `Opposite` by name; see hazard (2) above. *)

(* NEGATIVE 6. *)
Fail Definition probe_roof_op : Opposite Roof = Roof := eq_refl.

(* NEGATIVE 7. *)
Fail Definition probe_parallel_op : Opposite Parallel = Parallel := eq_refl.

(* CONTROLS: both shapes are nameable and `Opposite` applies to each. *)
Check Roof.
Check Parallel.
Check (Opposite Roof).
Check (Opposite Parallel).

(** ** FORMABILITY — hom and proof are identified, and the CONE RECORD IS
    NOT THE CAUSE.

    The target measures nine donors each rejected ALONE at these levels,
    and all nine are pinned below, together with the discriminating
    control: `Cone` is ACCEPTED at the very levels where every one of the
    nine is rejected, so "the cone vocabulary" would be the wrong
    attribution.

    Read "nine" as nine DONORS, not nine independent causes:
    `HasLimitsOfShape` is defined as `∀ F, Limit F`, so it cannot be
    rejected for a reason of its own, and no claim of independence is
    made for it.  The control has to be APPLIED to discriminate --
    `Check @Cone.` alone succeeds, but so does `Check @Limit.`, a
    polymorphic constant with no argument never meeting `Cu`; it is
    `@Cone Parallel Cu` against `@Limit Parallel Cu` that separates. *)

Section FormabilityHomProof.
Universes uo uh up.
Constraint uh < up.
Context (Cu : Category@{uo uh up}).

(* CONTROLS accepted with hom and proof declared strictly apart. *)
Check (fun x y : Cu => x ~{Cu}~> y).
Check (obj[Cu]).
Check (fun x : Cu => id[x]).

(* THE DISCRIMINATING CONTROL: the cone RECORD is formable here. *)
Check (@Cone Parallel Cu).

(* NEGATIVES 8-16, each rejected on its own.  Each was stripped and run
   alone, and each reports exactly

       (universe inconsistency: Cannot enforce up = uh because uh < up)

   so all nine are FORMABILITY and none is a conversion failure in
   disguise.  Nine donors, not four: an earlier revision of this file
   measured all nine in the target's header but pinned only the first
   four, which by this file's own rule ("a measurement is not a guard")
   left five unguarded.  They are pinned here. *)
Fail Check (@Limit Parallel Cu).
Fail Check (Opposite Cu).
Fail Check (@IsEqualizer Cu).
Fail Check (@IsPullback Cu).
Fail Check (@HasLimitsOfShape Parallel Cu).
Fail Check (@Diagonal Cu Parallel).
Fail Check ([Parallel, Cu]).
Fail Check (@IsCoequalizer Cu).
Fail Check (@IsPushoutSquare Cu).

End FormabilityHomProof.

(** ** Controls naming every constant the negatives depend on, OUTSIDE a
    [Fail], so a rename breaks a succeeding command rather than turning a
    negative vacuously green. *)

Check @eq_arrow.
Check @coeq_arrow.
Check @pb_fst.
Check @pb_snd.
Check @pushout_inj1.
Check @pushout_inj2.
Check @dia_unit.
Check @dia_counit.
Check @lim_leg.
Check @colim_inj.
Check @HasLimitsOfShape.
Check @HasColimitsOfShape.
Check @Limit.
Check @IsEqualizer.
Check @IsCoequalizer.
Check @IsPullback.
Check @IsPushoutSquare.
Check @Opposite.

Check @EqualizerFunctor.
Check @CoequalizerFunctor.
Check @PullbackFunctor.
Check @PushoutFunctor.
Check @Diagonal_Equalizer_Adjunction.
Check @Coequalizer_Diagonal_Adjunction.
Check @Diagonal_Pullback_Adjunction.
Check @Pushout_Diagonal_Adjunction.
Check @eq_counit_IsEqualizer.
Check @coeq_unit_IsCoequalizer.
Check @pb_counit_IsPullback.
Check @po_unit_IsPushoutSquare.
Check @ShapeLinked.
Check @dia_unit_iso.
Check @dia_counit_iso.
Check @Parallel_linked.
Check @Roof_linked.
