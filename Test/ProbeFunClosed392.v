Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Cartesian.
Require Import Category.Instance.Fun.Terminal.
Require Import Category.Instance.Omega.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Skeleton.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Monoidal.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

Require Import Category.Instance.Fun.Closed.

Generalizable All Variables.

(** * Probe for Instance/Fun/Closed.v (issue #392) *)

(* Mac Lane §IV.6 Exercise 5 ([maclane:IV.6:ex5]) and Awodey §8.7
   ([awodey:8.7:remark-pointwise-exponential-fails]).  Everything the
   target MEASURES and does not itself state is pinned here, from
   OUTSIDE that file, so that renaming a target constant breaks this
   probe rather than silently turning a guard green.  The [Require] list
   above mirrors the target's exactly, plus the target itself.

   SEVEN negatives of THREE kinds, told apart by the error text:

     1  FORMABILITY  the universe binders on [TwoFun] are load-bearing:
                     the same body without them is not an object of
                     [Omega, FinSet] at levels where the annotated one is
     2  FORMABILITY  [_2^op, Sets] elaborates only at a [Sets] whose
                     carrier universe IS [Set]
     3  CONVERSION   the presheaf P and the presheaf Q take different
                     values at [TwoY]
     4  CONVERSION   the objectwise candidate at [TwoY] is not the
                     two-element setoid, which is the value the naive
                     reading of the formula would want
     5  TYPING       the headline is about [Omega, FinSet]; it does not
                     apply to a cartesian structure on another category
     6  CONVERSION   [alpha_fam] separates exactly at its own stage
     7  TYPING       the engine's second half is about the TERMINAL
                     object of the functor category, not an arbitrary
                     source

   TWO formability, THREE conversion, TWO typing.  Each was stripped one
   at a time (its [Fail] removed, the file compiled alone) and the whole
   error read, since a passing [Fail] prints nothing.  The two
   formability ones end "universe inconsistency: Cannot enforce Set =
   ..."; the three conversion ones end "cannot unify" between two terms
   of ONE type; the two typing ones are a plain "has type ... while it
   is expected to have type ..." with NO "cannot unify" and no universe
   clause.  Every constant named inside a [Fail] is also named in a
   passing command outside every [Fail], below.

   ONE instrument check comes first, on a name that exists nowhere, so
   that [Fail] is known to be live in this file. *)

(** ** Instrument *)

Fail Check p392_this_name_exists_nowhere.

(** ** Controls: every target constant, named outside any negative *)

Check @ccc_point.
Check @ccc_point_inj.
Check @fun_const_point.
Check @fun_const_point_inj.
Check @fun_hom_point.
Check @fun_hom_point_inj.
Check @nodup_map_inj.
Check @fin_no_nat_injection.
Check @FinSet_is_cartesian_closed.
Check @two_map.
Check @TwoFun.
Check @alpha_fam.
Check @alpha_fam_F1.
Check @Alpha.
Check @Alpha_distinct.
Check @finset_point_eq.
Check @exp_card.
Check @alpha_index.
Check @alpha_index_inj.
Check @fun_not_cartesian_closed.
Check @fun_pointwise_not_cartesian_closed.
Check @TwoOpInitial.
Check @PObj.
Check @PMap.
Check @PresheafP.
Check @two_elt.
Check @PresheafQ.
Check @PQNat.
Check @PQNat_distinct.
Check @pq_point.
Check @pq_point_distinct.
Check @objectwise_candidate.
Check @objectwise_candidate_subsingleton.
Check @awodey_pointwise_not_exponential.

(* Donor constants a negative names, guarded outside every negative. *)
Check @Omega.
Check @FinSet.
Check @Sets.
Check @_2.
Check @Opposite.
Check @Functor_Category_Cartesian.
Check @Functor_Category_Terminal.
Check @FinSet_Cartesian.
Check @FinSet_Terminal.
Check @Sets_Cartesian.
Check @Sets_Closed.
Check @Omega_Initial.
Check @exponent_obj.
Check @le_t.
Check TwoY.

(** ** Positive readbacks the negatives are measured against *)

(* The two presheaves agree at [TwoX] on the nose: [PresheafQ] is a
   constant functor, and [PresheafP] takes [TwoX] to the terminal
   setoid, which is NOT the two-element one -- see negative 3 for the
   value at [TwoY], where they part company for the reason that drives
   the theorem. *)
Example p392_Q_at_TwoX : fobj[PresheafQ] TwoX = two_elt := eq_refl.

(* Away from their own stages, two members of the family agree by
   computation; negative 6 is the same statement AT a stage. *)
Example p392_alpha_off_stage : alpha_fam 0 3 = alpha_fam 1 3 := eq_refl.

(* The initial object of [_2^op] IS [Two_Terminal], with no transport:
   [Initial C] is notation for [@Terminal (C^op)]. *)
Example p392_TwoOpInitial : TwoOpInitial = Two_Terminal := eq_refl.

(** ** Negative 1 (FORMABILITY): the binders on [TwoFun] are
       load-bearing *)

(* The same body as the target's, written WITHOUT universe binders.
   Universe minimization then pins [Omega]'s hom and proof universes to
   the literal [Set]. *)
Program Definition TwoFunUnann : Omega ⟶ FinSet := {|
  fobj := fun _ => 2%nat;
  fmap := fun _ _ f => two_map f
|}.
Next Obligation. now destruct f. Qed.

Section P392Binders.

Universes p392o p392h p392p.
Constraint Set < p392h.

(* Control: the shipped, annotated constant elaborates at levels where
   [Omega]'s hom universe is declared strictly above [Set]. *)
Check (TwoFun : @Functor Omega@{p392o p392h p392p} FinSet).

(* Negative 1. *)
Fail Check (TwoFunUnann : @Functor Omega@{p392o p392h p392p} FinSet).

End P392Binders.

(** ** Negative 2 (FORMABILITY): the [Set] pin on the presheaf ambient *)

Section P392SetsPin.

Universes p392co p392so.
Constraint Set < p392co.
Constraint p392co < p392so.

(* Controls: both factors exist separately at these levels. *)
Check (Sets@{p392co p392so}).
Check (_2^op).

(* Negative 2: but they cannot be assembled into a functor category,
   because [_2]'s homs are the literal [Set], [Fun] identifies its
   source and target hom universes, and [Sets]'s hom universe IS its
   carrier universe. *)
Fail Check ([_2^op, Sets@{p392co p392so}]).

(* Discriminating control: with the polymorphic [Omega] in place of
   [_2^op] the same [Sets] instance IS admissible, so [_2] is a
   NECESSARY donor.  This control varies only [_2], so it establishes
   nothing about [Fun], and [Fun] is in fact a SECOND necessary donor:
   measured out of tree and NOT pinned here, the bare functor TYPE
   [@Functor (_2^op) Sets] is formable at these very levels while the
   CATEGORY [[_2^op, Sets]] is not, so the two are co-necessary and
   neither alone suffices.  [Sets] is measured NOT to be a donor. *)
Check ([Omega@{p392co p392co p392co}, Sets@{p392co p392so}]).

End P392SetsPin.

(** ** Negative 3 (CONVERSION): the two presheaves differ at [TwoY] *)

Fail Definition p392_n3
  : fobj[PresheafP] TwoY = fobj[PresheafQ] TwoY := eq_refl.

(** ** Negative 4 (CONVERSION): the objectwise candidate is not the
       two-element setoid *)

(* The objectwise formula would read the exponential at [TwoY] as
   Q(TwoY)^{P(TwoY)}.  That object is computable in tree, and it is NOT
   [two_elt]; the target proves separately, at [~], that all of its
   points coincide, whereas the true value has two distinct ones. *)
Fail Definition p392_n4
  : @exponent_obj Sets Sets_Cartesian Sets_Closed
      (fobj[PresheafP] TwoY) (fobj[PresheafQ] TwoY) = two_elt := eq_refl.

(** ** Negative 5 (TYPING): the headline is about [Omega, FinSet] *)

(* Control: the headline accepts the pointwise cartesian structure on
   its own functor category. *)
Check (fun_not_cartesian_closed
         (Functor_Category_Cartesian Omega FinSet FinSet_Cartesian)).

(* Negative 5: and not one on a different functor category. *)
Fail Check (fun_not_cartesian_closed
              (Functor_Category_Cartesian (_2^op) Sets Sets_Cartesian)).

(** ** Negative 6 (CONVERSION): [alpha_fam] separates at its stage *)

Fail Definition p392_n6 : alpha_fam 0 1 = alpha_fam 1 1 := eq_refl.

(** ** Negative 7 (TYPING): the engine's second half is about the
       terminal object *)

(* Control: the constant exists and is applicable at these arguments. *)
Check (@fun_const_point Omega FinSet Omega_Initial FinSet_Terminal).

(* Negative 7: its argument must be a transformation OUT OF the
   pointwise terminal functor; an endotransformation of [TwoFun] is not
   one. *)
Fail Check (@fun_const_point Omega FinSet Omega_Initial FinSet_Terminal
              TwoFun (Alpha 0)).
