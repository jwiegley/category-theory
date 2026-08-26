(** * Boundary probes for Functor/Hom/Limit.v (issue #331)

    Mac Lane CWM 2nd ed. §III.4, book p. 70.

    This file pins the two measurements the target's header rests on, so
    that a later edit which quietly makes either FALSE breaks the build
    rather than silently invalidating the prose.

    The two negatives are of DIFFERENT KINDS and are kept lexically apart:

      * FORMABILITY (universe) -- the target proves its product corollaries
        DIRECTLY rather than deriving them from the cone-level headline,
        and the header's stated reason is that routing them through the
        discrete-diagram presentation would pin the ambient category's
        hom and proof universes to [Set].  Negative 2 pins exactly that,
        and it localizes the cause: [DiscreteCat_Functor] ALONE is formable
        over a category whose hom universe is strictly above [Set] (the
        control immediately above it), and what fails is the COMBINATION --
        [IsLimitCone] identifies the shape's hom-and-proof universe with
        the ambient category's, while [DiscreteCat_Functor]'s UNANNOTATED
        declaration instantiates [DiscreteCat@{u Set Set}].  Stripped, the
        error reads
          "universe inconsistency: Cannot enforce Set = uh",
        displaying [Cone@{_ Set Set uo uh uh}] against a [Cone] whose
        shape and ambient levels are one and the same.

        ATTRIBUTE IT TO THE FUNCTOR, NOT THE SHAPE.  [DiscreteCat] itself
        is [DiscreteCat@{o h p} (A : Type@{o}) : Category@{o h p}] with hom
        and proof FREE, and [DiscreteCat@{Set uh uh} bool] elaborates under
        [Constraint Set < uh].  An audit further showed that a re-annotated
        discrete-diagram functor LIFTS this blocking step entirely, so what
        this negative pins is a donor ANNOTATION defect, not a structural
        obstruction -- see the target's header.

        An earlier draft of this probe aimed the negative at
        [DiscreteCat_Functor] by itself and it did NOT fail -- the guard
        was pointed at the wrong constant.  Recorded because a negative
        aimed at the wrong constant is a false guard, not a small slip;
        and an earlier draft ALSO mis-attributed the [Set] to the shape.

      * TYPING -- written [FCone (HomFrom unit) (…)] elaboration reports
          "HomFrom () has type Coq ⟶ Sets while it is expected to have
           type Coq ⟶ Coq".
        THE CAUSE IS [HomFrom]'s IMPLICIT [{C : Category}], undeterminable
        from a bare [unit : Type] -- NOT [FCone]'s category arguments.
        Those may be left implicit: [FCone (HomFrom (unit : obj[Coq])) (…)]
        and [fun u : Coq => FCone (HomFrom u) (…)] both elaborate, and the
        target's own [coq_hom_limit_cone] writes them implicitly.  An
        earlier revision of this header said the three category arguments
        "cannot be implicit" and that an ascription does not repair it;
        both were wrong, and the controls below now name the object
        ascription that does repair it.

    NOT PINNED HERE, and said plainly: the header's claim that the direct
    product statements carry no [Set] at all is exercised as a positive
    CONTROL below (they elaborate over a category with hom universe above
    [Set]), not as a negative -- there is nothing to refute.

    Every negative is paired with a positive control NAMING ITS OWN
    CONSTANTS, and the pairing was verified by RENAME SIMULATION over the
    constants appearing in the NEGATIVES.  The measured score is recorded
    at the end of this file. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Limit.Cartesian.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Coq.
Require Import Category.Functor.Hom.Limit.

(** ** Instrument check

    A [Fail] that never fails would make every negative below vacuous. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negative 1 (TYPING): HomFrom's implicit category is undeterminable *)

Fail Check (FCone (HomFrom unit) (coq_two_limit (Pick_Two bool nat))).

(* Positive controls naming the negative's own constants.  The EXPLICIT
   spelling is what the target ships, and every constant in the rejected
   expression is independently well-formed here. *)
Check coq_hom_bool_nat_limit.
Check (@FCone Two_Discrete Coq Sets (HomFrom unit)).
Check (HomFrom unit).
Check coq_two_limit.
Check (Pick_Two bool nat).
(* The repair, named: ascribing the object determines [HomFrom]'s implicit
   category, and then FCone's own arguments may stay implicit. *)
Check (FCone (HomFrom (unit : obj[Coq])) (coq_two_limit (Pick_Two bool nat))).

(** ** Negative 2 (FORMABILITY, universe): the discrete route pins Set

    Different KIND from Negative 1. *)

Section AboveSet.

Universe uo uh.
Constraint Set < uh.

Context (C : Category@{uo uh uh}) (c : obj[C]) (fam : bool -> obj[C]).

(* Control (a): the DIRECT product statements carry no [Set] -- they
   elaborate over this category, whose hom universe is strictly above it.
   This is the header's positive claim, exercised rather than asserted. *)
Check (@hom_IsIndexedProduct C c).
Check (@hom_IsCartesianProduct C c).

(* Control (b): the discrete-diagram functor ALONE is formable here, which
   is what makes the negative a statement about the COMBINATION. *)
Check (@DiscreteCat_Functor bool C fam).

(* The negative. *)
Fail Check (fun N : Cone (@DiscreteCat_Functor bool C fam) => IsLimitCone N).

(* Control (c): [IsLimitCone] itself is fine at this ambient category when
   the SHAPE is not the Set-pinned discrete one. *)
Check (fun (J : Category@{uo uh uh}) (K : J ⟶ C) (N : Cone K) =>
         IsLimitCone N).

End AboveSet.

(** ** Controls for the delivered results *)

Check hom_PreservesLimitCone.
Check hom_ContinuousFunctor.
Check hom_PreservesLimit.
Check hom_PreservesAllLimits.
Check hom_preserved_leg.
Check hom_preserved_mediator.
Check hom_med_commutes.
Check hom_med_unique.
Check hom_IsIndexedProduct.
Check hom_IsCartesianProduct.
Check HomFrom.
Check HomTo.
Check hom_to_is_op_hom_from.
Check cohom_ContinuousFunctor.
Check cohom_PreservesLimitCone.
Check cohom_colimit_to_limit.
Check cohom_IsIndexedProduct.
Check cohom_IsCartesianProduct.
Check cartesian_IsCartesianProduct.
Check coq_hom_product.
Check coq_hom_limit_cone.

(** ** MEASURED RENAME-SIMULATION SCORE

    The two negatives name these constants:

      Negative 1: [FCone], [HomFrom], [coq_two_limit], [Pick_Two]
      Negative 2: [DiscreteCat_Functor], [Cone], [IsLimitCone]

    All SEVEN are named by a positive control above, so renaming any one
    of them breaks this file rather than turning its negative vacuously
    green.  Score: 7/7, counted rather than recalled. *)
