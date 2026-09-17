Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Limit.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Limit.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.

Generalizable All Variables.

(** * Probe for Instance/Mod/Limit.v

    Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.1
    Theorems 2 and 3 and §V.7 Construction 1, printed pp. 111-112 and
    p. 128.  Issue #449.  The target creates every limit of [RMod R]
    from [Ab] along [RMod_Forget_Ab] and reads [RMod_Complete] off
    [Ab_Complete].

    The first fifteen requires above are the target file's own import
    list, unabbreviated, and the sixteenth is the target.  A short
    prefix is what makes a probe pass vacuously, so nothing is trimmed
    even where a require is redundant.  The last two are the probe's
    own, and are the only additions: the adjoint-functor-theorem
    boundary below names [PreservesImageLimit]
    (Construction/Comma/Limit.v:110) and its repair
    [Continuous_PreservesImageLimit] (Construction/Comma/Creation.v:245),
    neither of which the target imports.

    Every statement asserted to be refuted below has been STRIPPED of its
    refutation keyword in a copy of this WHOLE file, compiled alone, and
    its complete error read; a refutation that holds prints nothing under
    this repo's coqc.  Kinds, under THIS import list, the rubric being
    Test/ProbeSpanningArrow448.v's:

      CONVERSION  - "cannot unify A and B" parenthetical present.
      TYPING      - the "has type X while it is expected to have type Y"
                    opener with NO such parenthetical.
      INSTANCE    - "(no type class instance found)": such a negative
                    must be a [Definition], since a [Check] tolerates the
                    open evar and is then vacuously green.
      UNIVERSE    - "universe inconsistency".

    MEASURED, AND WORTH SAYING PLAINLY: all four negatives here open with
    the "has type ... while it is expected to have type ..." line AND
    carry the "cannot unify" parenthetical, so by that rubric all four
    are CONVERSION, not TYPING.  The issue brief anticipated TYPING for
    F2 and F3; the parenthetical decides it, and the exact text of each
    is quoted at the command.  F3's parenthetical is also not the one
    anticipated -- it reads "cannot unify "Cone (RMod_Forget_Ab R ◯ K)"
    and "IsLimitCone N"", the short names being those this import list
    puts in scope.

    The instrument check comes first; every library constant a negative
    names has a positive control outside any refutation command, and
    each negative is followed by the term that DOES ascribe there. *)

(** ** Instrument check *)

(* "The reference rmod_limit_449_no_such_constant was not found in the
   current environment." *)
Fail Check rmod_limit_449_no_such_constant.

(** ** Positive controls *)

Check @RingObject.
Check @RMod.
Check @RMod_Complete.
Check @RMod_Forget_Ab.
Check @RMod_Forget.
Check @Ab_Forget.
Check @Ab_Complete.
Check @RMod_Forget_Ab_StrictlyCreatesLimit.
Check @RMod_Forget_Ab_CreatesLimit.
Check @RMod_Forget_Ab_StrictlyCreatesLimits.
Check @RMod_Forget_Ab_creates_limits.
Check @RMod_Forget_Ab_reflects_limits.
Check @RMod_Forget_Ab_creates_continuous.
Check @RMod_Forget_Ab_PreservesAllLimits.
Check @RMod_Forget_Ab_lifts_limits.
Check @RMod_Forget_composite_continuous.
Check @RMod_Forget_creates_continuous.
Check @RMod_Forget_PreservesAllLimits.
Check @RMod_lift_cone_unique.
Check @LimitMod.
Check @mlim_cone.
Check @mlim_leg.
Check @mlim_smul.
Check @mlim_smul_triangle.
Check @mlim_smul_unique.
Check @mlim_created.
Check @rmod_reflects.
Check @rmod_abcone_of.
Check @ContinuousFunctor.
Check @PreservesImageLimit.
Check @Continuous_PreservesImageLimit.
Check @Complete.
Check @Cone.
Check @FCone.
Check @cone_leg.
Check @vertex_obj.
Check @Limit.
Check @limit_cone.
Check @limit_leg.
Check @limit_is_alimit.
Check @IsLimitCone.
Check @Sets_limit_obj.
Check @Sets_limit_leg.
Check @rm_ab.
Check @rm_hom.
Check @rm_smul.
Check @cmon_setoid.
Check @cmon_map.
Check @cmon_plus.
Check @cmon_zero.
Check @ab_cmon.
Check @ab_neg.
Check @carrier.

(** ** The fourteen [eq_refl] readbacks, restated

    Each is the statement of one of the target's fourteen [:= eq_refl]
    lines, re-elaborated here from library constants alone, at exactly
    the strength the target claims for it and no more.  Five compare
    morphisms, five objects, four elements; every witness is [eq_refl],
    so each of these is a positive control on a definitional identity,
    not a proof.  Two of them rest on transparency measured in the
    target: R5 and R6 stop if [RMod_Forget_Ab_StrictlyCreatesLimit] is
    closed opaquely, and that in turn rests on [mlim_created]. *)

(* R1 = [mlim_over_obj]: the lifted module's group IS the apex of [L]. *)
Example p449_r1 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) :
  RMod_Forget_Ab R (LimitMod K L) = vertex_obj[L] := eq_refl.

(* R2 = [mlim_over_legs]: and its legs ARE the legs of [L]. *)
Example p449_r2 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) (j : J) :
  fmap[RMod_Forget_Ab R] (cone_leg (mlim_cone K L) j) = mlim_leg K L j
  := eq_refl.

(* R3 = [rmod_fcone_apex]. *)
Example p449_r3 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (N : Cone K) :
  vertex_obj[FCone (RMod_Forget_Ab R) N] = rm_ab vertex_obj[N] := eq_refl.

(* R4 = [rmod_fcone_leg]. *)
Example p449_r4 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (N : Cone K) (j : J) :
  cone_leg (FCone (RMod_Forget_Ab R) N) j = rm_hom (cone_leg N j) := eq_refl.

(* R5 = [rmod_lift_apex]: the lifted limit lies over [L] on the nose. *)
Example p449_r5 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) :
  RMod_Forget_Ab R (vertex_obj[RMod_Forget_Ab_lifts_limits K L])
    = vertex_obj[L] := eq_refl.

(* R6 = [rmod_lift_legs]. *)
Example p449_r6 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) (j : J) :
  fmap[RMod_Forget_Ab R]
    (cone_leg (@limit_cone _ _ _ (RMod_Forget_Ab_lifts_limits K L)) j)
    = limit_leg (limit_is_alimit L) j := eq_refl.

(* R7 = [rmod_forget_obj_agrees]: the two forgetful functors agree on
   objects -- the positive half of the bridge whose negative half is F1
   below. *)
Example p449_r7 {R : RingObject} (M : RMod R) :
  RMod_Forget R M = (Ab_Forget ◯ RMod_Forget_Ab R) M := eq_refl.

(* R8 = [rmod_forget_map_agrees]: and on morphisms. *)
Example p449_r8 {R : RingObject} {M N : RMod R} (f : M ~{RMod R}~> N) :
  fmap[RMod_Forget R] f = fmap[Ab_Forget ◯ RMod_Forget_Ab R] f := eq_refl.

Section RModComputed449.

Context {R : RingObject}.
Context {J : Category}.
Context (K : J ⟶ RMod R).

(* R9 = [rmod_complete_carrier]: the chosen limit's carrier IS the
   compatible-families setoid of Instance/Sets/Complete.v. *)
Example p449_r9 :
  cmon_setoid (ab_cmon (rm_ab (vertex_obj[RMod_Complete R J K])))
    = Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K)) := eq_refl.

(* R10 = [rmod_complete_plus]. *)
Example p449_r10
  (a b : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (cmon_plus (rm_ab (vertex_obj[RMod_Complete R J K])) a b) d
    = cmon_plus (rm_ab (K d)) (`1 a d) (`1 b d) := eq_refl.

(* R11 = [rmod_complete_zero]. *)
Example p449_r11 (d : J) :
  `1 (cmon_zero (rm_ab (vertex_obj[RMod_Complete R J K]))) d
    = cmon_zero (rm_ab (K d)) := eq_refl.

(* R12 = [rmod_complete_neg]. *)
Example p449_r12
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (ab_neg (rm_ab (vertex_obj[RMod_Complete R J K])) a) d
    = ab_neg (rm_ab (K d)) (`1 a d) := eq_refl.

(* R13 = [rmod_complete_smul]: the ONE readback with no counterpart in
   Instance/Ab/Limit.v -- the created ACTION is componentwise at the
   chosen limit, even though that limit reaches its mediator through
   [creates_limiting].  F4 below pins what this does NOT say. *)
Example p449_r13 (r : R)
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K))))
  (d : J) :
  `1 (rm_smul (vertex_obj[RMod_Complete R J K]) r a) d
    = rm_smul (K d) r (`1 a d) := eq_refl.

(* R14 = [rmod_complete_leg]. *)
Example p449_r14 (d : J) :
  cmon_map (rm_hom (cone_leg (@limit_cone _ _ _ (RMod_Complete R J K)) d))
    = Sets_limit_leg (Ab_Forget ◯ (RMod_Forget_Ab R ◯ K)) d := eq_refl.

End RModComputed449.

(** ** The measured boundaries

    Four, each followed by the term that does stand there. *)

(* F1 -- CONVERSION: the two forgetful functors of Instance/Mod.v are not
   the same record, the three law fields being opaque.  "The term
   "eq_refl" has type "RMod_Forget R = RMod_Forget R" while it is
   expected to have type "RMod_Forget R = Ab_Forget ◯ RMod_Forget_Ab R"
   (cannot unify "RMod_Forget R" and "Ab_Forget ◯ RMod_Forget_Ab R")".
   R7 and R8 above are the positive halves: fobj and fmap DO agree. *)
Fail Definition p449_f1 (R : RingObject) :
  RMod_Forget R = Ab_Forget ◯ RMod_Forget_Ab R := eq_refl.

(* F2 -- CONVERSION, the consequence of F1 for continuity: "The term
   "RMod_Forget_composite_continuous R" has type "ContinuousFunctor
   (Ab_Forget ◯ RMod_Forget_Ab R)" while it is expected to have type
   "ContinuousFunctor (RMod_Forget R)" (cannot unify "Cone (RMod_Forget R
   ◯ K)" and "Cone (Ab_Forget ◯ RMod_Forget_Ab R ◯ K)")".  This is why
   the target carries the [rmod_abcone_of] bridge; the repaired term is
   next. *)
Fail Definition p449_f2 (R : RingObject) : ContinuousFunctor (RMod_Forget R) :=
  RMod_Forget_composite_continuous R.

Example p449_f2_repair (R : RingObject) : ContinuousFunctor (RMod_Forget R) :=
  RMod_Forget_creates_continuous R.

(* F3 -- CONVERSION: continuity does NOT ascribe where Freyd's theorem
   and [representability_theorem] ask for [PreservesImageLimit], so
   [Continuous_PreservesImageLimit] must stand in the term.  "The term
   "RMod_Forget_Ab_creates_continuous R" has type "ContinuousFunctor
   (RMod_Forget_Ab R)" while it is expected to have type
   "PreservesImageLimit" (cannot unify "Cone (RMod_Forget_Ab R ◯ K)" and
   "IsLimitCone N")": the two types quantify over a cone and over a
   limit in different positions.  Consumers of [RMod_Complete] meet this
   at the application. *)
Fail Definition p449_f3 (R : RingObject) :
  @PreservesImageLimit (RMod R) Ab (RMod_Forget_Ab R) :=
  RMod_Forget_Ab_creates_continuous R.

Example p449_f3_repair (R : RingObject) :
  @PreservesImageLimit (RMod R) Ab (RMod_Forget_Ab R) :=
  Continuous_PreservesImageLimit (RMod_Forget_Ab_creates_continuous R).

(* F4 -- CONVERSION, the boundary of R13: componentwise computation of
   the action is a fact about the CHOSEN limit, not about the lifted
   action in general.  At an arbitrary [L] the defining triangle holds
   only up to [≈]: "The term "eq_refl" has type "mlim_leg K L j
   (mlim_smul K L r a) = mlim_leg K L j (mlim_smul K L r a)" while it is
   expected to have type "mlim_leg K L j (mlim_smul K L r a) = rm_smul
   (fobj[K] j) r (mlim_leg K L j a)" (cannot unify "mlim_leg K L j
   (mlim_smul K L r a)" and "rm_smul (fobj[K] j) r (mlim_leg K L j a)")"
   -- the action being a mediator of the abstract limit there.  The
   available strength is the [≈] of [mlim_smul_triangle], next. *)
Fail Definition p449_f4 {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) (r : R) (j : J) (a : vertex_obj[L]) :
  mlim_leg K L j (mlim_smul K L r a) = rm_smul (K j) r (mlim_leg K L j a)
  := eq_refl.

Example p449_f4_weak {R : RingObject} {J : Category} (K : J ⟶ RMod R)
  (L : Limit (RMod_Forget_Ab R ◯ K)) (r : R) (j : J) (a : vertex_obj[L]) :
  mlim_leg K L j (mlim_smul K L r a) ≈ rm_smul (K j) r (mlim_leg K L j a)
  := mlim_smul_triangle K L r j a.
