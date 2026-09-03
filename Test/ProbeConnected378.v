Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Shapes.
Require Import Category.Theory.Skeleton.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Theory.Connected.Components.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Limit.Constant.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Coq.
Require Import Category.Instance.One.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Monoidal.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Adjunction.FullFaithful.
Require Import Category.Adjunction.Diagonal.Connected.

Generalizable All Variables.

(** * Boundary probe for Adjunction/Diagonal/Connected.v

    Every rejection the target's header records is pinned here, from
    OUTSIDE the target -- an in-file [Fail] renames in lockstep with the
    constant it guards and so cannot detect a rename.  The probe mirrors
    the target's whole [Require] list, plus Structure/Limit/Unique.v for
    negative 4; a short prefix is what makes a probe pass for the wrong
    reason.

    TEN [Fail] commands = 1 instrument check + 9 negatives of THREE
    kinds, kept lexically apart:

      - 3 CONVERSION (negatives 2, 4 and 10), each ending "cannot unify"
        between two terms of one type;
      - 2 TYPING (negatives 3 and 5), each a plain "has type ... while
        it is expected to have type" with NO "cannot unify" and NO
        universe clause.  Negative 3 is the sharper of the two and was
        measured rather than predicted: at an arbitrary choice of
        colimits the strict injection clause is not merely unprovable,
        it is NOT WELL-TYPED, the two sides having different codomains
        until the apex equation is supplied.  Negative 5 says the
        headline does not accept a bare family of colimits where the
        record is wanted;
      - 4 FORMABILITY (negatives 6-9), each ending "universe
        inconsistency: Cannot enforce ...".

    Each was stripped ONE AT A TIME, with the others left as [Fail],
    compiled alone, and its whole error read to confirm the kind and the
    command it fires at.

    Every constant a negative names also appears in a command OUTSIDE a
    [Fail], so a rename breaks the probe at a non-[Fail] line.  The
    universe sections carry the discriminating controls beside their
    negatives: [Ju ⟶ Cu] elaborates at hom levels declared strictly
    apart, so [Functor] is NOT a donor of either identification, and
    that is what makes the four rejections attributable. *)

(* ------------------------------------------------------------------ *)
(** ** Instrument check *)

Fail Check probe378_no_such_constant_anywhere.

(* ------------------------------------------------------------------ *)
(** ** Controls: every guarded constant named outside a [Fail] *)

Check @diagonal_counit.
Check @diagonal_counit_strict.
Check @diagonal_counit_commutes.
Check @diagonal_counit_iso.
Check @diagonal_counit_Isomorphism.
Check @diagonal_counit_inverse.
Check @colim_const_inj_agree.
Check @colim_delta_nat.
Check @colim_diagonal_iso_Id.
Check @Diagonal_InjectiveOnObjects.
Check @diagonal_FFI.
Check @diagonal_RI.
Check @diagonal_fully_faithful_of_counit.
Check @ConstantColimits.
Check @cc_colim.
Check @cc_obj.
Check @cc_inj.
Check @constant_colimits_counit.
Check @colimit_is_lali_of_diagonal.
Check @colimit_lali_ffi.
Check @colimit_lali_ri.
Check @colim_diagonal_strict_Id.
Check @terminal_colimits.
Check @terminal_ConstantColimits.
Check @terminal_lali_of_diagonal.
Check @terminal_shape_connected.
Check @EvalAt.
Check @EvalAt_retracts.
Check @colimit_is_EvalAt.
Check @ordinal_ConstantColimits.
Check @ordinal_lali.
Check @two_ConstantColimits.
Check @two_lali.
Check @TwoGap.
Check @eval_not_left_adjoint.
Check @diagonal_limit_unit.
Check @diagonal_unit_commutes.
Check @lim_const_leg_agree.
Check @diagonal_unit_limit_iso.
Check @ConstantLimits.
Check @cl_limit.
Check @cl_obj.
Check @cl_leg.
Check @constant_limits_unit.
Check @diagonal_is_lari_of_limit.
Check @initial_limits.
Check @initial_ConstantLimits.
Check @initial_lari_of_limit.
Check @one_ConstantLimits.
Check @omega_ConstantLimits.
Check @omega_lari.
Check @two_discrete_counit_not_iso.
Check @two_discrete_no_ffi.
Check @two_discrete_no_lali.
Check @two_discrete_no_constant_colimits.
Check @two_discrete_objects_distinct.
Check @ordinal_two_not_degenerate.
Check @diagonal_counit_Isomorphism_to.
Check @lali_left_strict.
Check @lali_obj_strict.
Check @terminal_colimit_obj_strict.
Check @terminal_colimit_inj_strict.
Check @TwoGap_X.
Check @TwoGap_Y.
Check @lari_left_strict.
Check @lari_obj_strict.
Check @initial_limit_obj_strict.
Check @initial_limit_leg_strict.
Check @colim_diagonal_iso_Id_component.
Check @colim_diagonal_strict_Id_obj.

(* Donor constants the negatives below name. *)

Check @HasColimitsOfShape.
Check @colim_obj.
Check @colim_inj.
Check @LeftAdjointLeftInverse.
Check @colimit_unique_iso.
Check @const_IsAColimit.
Check @colim_acolimit.
Check @Diagonal.
Check @Two_Terminal.
Check @Fun.
Check @to.
Check @from.

(* ------------------------------------------------------------------ *)
(** ** (1) The unconditional strict clauses are REJECTED

    At an ARBITRARY choice of colimits the apex of the colimit of a
    constant diagram is the chosen one, and nothing reduces it to the
    constant -- which is exactly why [colimit_is_lali_of_diagonal]
    carries a hypothesis and section (A) of the target delivers only an
    isomorphism. *)

Section StrictClauses.

Context {J C : Category}.
Context (L : HasColimitsOfShape J C).
Context (K : ConnectedNonempty J).
Context (P : ConstantColimits J C).

(* Negative 2 (CONVERSION). *)
Fail Example probe_apex_strict (c : C) :
  colim_obj L Δ[J](c) = c := eq_refl.

(* Control: with the record in hand the SAME equation is available, and
   under the terminal choice it holds by [eq_refl]. *)
Definition probe_apex_control (c : C) : colim_obj (cc_colim P) Δ[J](c) = c
  := cc_obj P c.

Example probe_apex_terminal (T : @Terminal J) (c : C) :
  colim_obj (@terminal_colimits J C T) Δ[J](c) = c := eq_refl.

(* Negative 3 (TYPING).  Measured, not predicted: at an arbitrary
   choice the strict injection clause is not even WELL-TYPED, the
   injection landing at [colim_obj L Δ[J](c)] where [id[c]] lands at
   [c].  Under the terminal choice the codomain reduces and the same
   statement is a passing control. *)
Fail Example probe_inj_strict (c : C) (j : J) :
  colim_inj L Δ[J](c) j = id[c] := eq_refl.

Example probe_inj_terminal (T : @Terminal J) (c : C) (j : J) :
  colim_inj (@terminal_colimits J C T) Δ[J](c) j = id[c] := eq_refl.

(* Negative 4 (CONVERSION): the counit and the leg of
   Structure/Limit/Unique.v's essential-uniqueness isomorphism are the
   same morphism up to [≈] -- both are mediators out of the chosen
   colimit into the constant cocone -- but they are DIFFERENT TERMS, so
   conversion rejects the identification. *)
Fail Example probe_counit_is_unique_iso (c : C) :
  diagonal_counit L c
    = to (@colimit_unique_iso J C Δ[J](c) _ _
            (colim_acolimit L Δ[J](c)) (const_IsAColimit c K))
  := eq_refl.

(* Control: the same statement at [≈] is what section (A) delivers, and
   the counit's own triangle is what proves it. *)
Definition probe_counit_control (c : C) (j : J) :
  diagonal_counit L c ∘ colim_inj L Δ[J](c) j ≈ id
  := diagonal_counit_commutes L c j.

(* Controls: both legs of the isomorphism read back on the nose. *)
Example probe_to_strict (c : C) :
  to (diagonal_counit_Isomorphism L K c) = diagonal_counit L c := eq_refl.

Example probe_inverse_strict (c : C) :
  from (diagonal_counit_Isomorphism L K c)
    = colim_inj L Δ[J](c) (cn_obj K) := eq_refl.

End StrictClauses.

(* ------------------------------------------------------------------ *)
(** ** (2) The headline does not accept a bare family of colimits

    Negative 5 (TYPING).  [colimit_is_lali_of_diagonal] takes a point of
    the shape and a [ConstantColimits] record; feeding it the family
    alone is a plain type mismatch with no universe clause, which is the
    whole content of section 2 of the target's header. *)

Section Arity.

Context {J C : Category}.
Context (j0 : J).
Context (L : HasColimitsOfShape J C).
Context (P : ConstantColimits J C).

Fail Definition probe_lali_from_bare :
  LeftAdjointLeftInverse (@Diagonal C J) :=
  colimit_is_lali_of_diagonal j0 L.

(* Control: with the record it is exactly the headline. *)
Definition probe_lali_control :
  LeftAdjointLeftInverse (@Diagonal C J) :=
  colimit_is_lali_of_diagonal j0 P.

Example probe_lali_left_strict :
  lali_left probe_lali_control = ColimitFunctor (cc_colim P) := eq_refl.

End Arity.

(* ------------------------------------------------------------------ *)
(** ** (3) Universes: the shape's and the ambient's hom levels coincide

    Negatives 6-8 (FORMABILITY).  With the two hom levels declared
    strictly apart, three donors are each rejected ALONE -- [Fun],
    [HasColimitsOfShape] and [Diagonal] -- while the functor type
    [Ju ⟶ Cu] elaborates at those very levels.  So [Functor] is not the
    cause, and the identification the target reports as [jh = ch] has
    three independent donors, none of them introduced here. *)

Section ShapeAmbientHom.

Universes jo jh co ch.
Constraint jh < ch.

Context (Ju : Category@{jo jh jh}).
Context (Cu : Category@{co ch ch}).

(* Discriminating controls, accepted at the declared levels. *)
Check (obj[Ju]).
Check (obj[Cu]).
Check (Ju ⟶ Cu).

(* Negative 6 (FORMABILITY): the functor category itself. *)
Fail Check ([Ju, Cu]).

(* Negative 7 (FORMABILITY): the colimit hypothesis. *)
Fail Check (HasColimitsOfShape Ju Cu).

(* Negative 8 (FORMABILITY): the diagonal. *)
Fail Check (@Diagonal Cu Ju).

End ShapeAmbientHom.

(* ------------------------------------------------------------------ *)
(** ** (4) Universes: hom and proof coincide in both categories

    Negative 9 (FORMABILITY).  [LeftAdjointLeftInverse] is rejected at a
    category whose hom and proof levels are declared apart, while
    [Au ⟶ Xu] is accepted there -- so this identification too is a
    donor's and not this development's.  [HasColimitsOfShape] and
    [Diagonal] are rejected at the same levels (measured, not pinned
    separately: they are already pinned above at the other
    identification, and one command cannot separate two).

    [ConstantColimits] is rejected there as well, but that says nothing
    of its own: [HasColimitsOfShape] is one of its fields, so it cannot
    be tested apart from a donor -- the trap Test/ProbeRingLattice340.v
    records for [MonoidObject]. *)

Section HomProof.

Universes ao ah ap xo xh xp.
Constraint ah < ap.

Context (Au : Category@{ao ah ap}).
Context (Xu : Category@{xo xh xp}).

Check (obj[Au]).
Check (Au ⟶ Xu).

Fail Check (@LeftAdjointLeftInverse Au Xu).

End HomProof.

(* ------------------------------------------------------------------ *)
(** ** (5) Readbacks the target's header claims, and the one it
       withdraws *)

Example probe_eval_retracts {J C : Category} (j : J) (c : C) :
  fobj[@EvalAt J C j] Δ[J](c) = c := eq_refl.

Example probe_colimit_is_EvalAt {J C : Category} (T : @Terminal J)
  (F : [J, C]) :
  fobj[ColimitFunctor (@terminal_colimits J C T)] F
    = fobj[@EvalAt J C (@terminal_obj J T)] F := eq_refl.

(* Negative 10 (CONVERSION).  The ARROW action of the same comparison
   does not convert: [ColimitFunctor]'s arrow action is the colimit
   mediator and [EvalAt]'s is the component, two different terms.  Only
   the object clause above is claimed. *)
Fail Example probe_colimit_is_EvalAt_arrow {J C : Category}
  (T : @Terminal J) (F G : [J, C]) (t : F ~{[J, C]}~> G) :
  fmap[ColimitFunctor (@terminal_colimits J C T)] t
    = fmap[@EvalAt J C (@terminal_obj J T)] t := eq_refl.

Example probe_two_lali_left (C : Category) :
  lali_left (two_lali C)
    = ColimitFunctor (@terminal_colimits _2 C Two_Terminal) := eq_refl.

Example probe_lari_left {J C : Category} (I : @Initial J) :
  lari_left (@initial_lari_of_limit J C I) = @Diagonal C J := eq_refl.
