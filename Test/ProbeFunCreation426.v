(** * Probe for Instance/Fun/Creation.v (issue #426)

    Pins the measured boundaries of the creation development: three
    CONVERSION refusals (N1 the lifted cone's record against the given
    cone; N2 a restricted functor against the discrete functor on its
    object map; N3 Riehl's strict clause, an [eq] between functor records)
    beside their accepted apex and leg controls, and three UNIVERSE
    refusals (N4 #425's [Functor_Category_Complete]; N5 the type
    [[Pw, Xw] ⟶ Xw]; N6 #424's [Eval]) at a shape whose objects sit
    strictly above its homs, beside the accepted [ObjCat], [Res] and
    [[Pw, Xw] ⟶ [Pw, Xw]] — the restriction functor is more
    universe-general than the theorem it serves, and the bound [jo <= jh]
    enters through [Functor] over [Fun], not through this development.
    Each refutation was stripped one at a time in a copy of the whole
    file; the import list mirrors the target's.  Section D's readbacks and
    the guard block are positive controls. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Fun.Limit.
Require Import Category.Instance.Fun.Creation.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe426_absent_name.

(** ** A: the lifted cone's image is the given cone in apex and legs, not
       as a record *)

Section JointLift.

Context {J P X : Category} (D : J ⟶ [P, X])
  (N : ∀ p : obj[P], Cone (Eval p ◯ D)) (HN : ∀ p : obj[P], IsLimitCone (N p)).

(* controls: apex and every leg convert *)
Check (fun p : obj[P] => ev_lift_apex D N HN p).
Check (fun (p : obj[P]) (x : J) => ev_lift_leg D N HN p x).

(* N1 CONVERSION: the whole cone record does not — its coherence field is a
   rebuilt opaque proof *)
Fail Example p426_ev_lift_record (p : obj[P]) :
  FCone (Eval p) (ev_lift D N HN) = N p := eq_refl.

(* readback: the family of evaluations jointly creates *)
Check (Fun_Eval_JointlyCreateLimit D).

End JointLift.

(** ** B: strictness — the restriction is the identity on objects but not
       a rebuild of functor records *)

Section Strict.

Context {P X : Category}.

(* control: object action of the restriction *)
Example p426_res_obj_at (H : [P, X]) (p : P) :
  fobj[fobj[@Res P X] H] p = fobj[H] p := eq_refl.

(* N2 CONVERSION: the restricted functor is not the discrete functor on the
   same object map — the arrow fields differ *)
Fail Example p426_res_is_disc (H : [P, X]) :
  fobj[@Res P X] H = DiscreteCat_Functor' (fobj[H]) := eq_refl.

Section StrictLimit.

Context {J : Category} (D : J ⟶ [P, X]) (L : ∀ p : P, Limit (Eval p ◯ D)).

(* control: the canonical lift's image has the pointwise apexes on the nose *)
Example p426_strict_obj_ok (p : P) :
  fobj[fobj[@Res P X] (PointwiseLimit D L)] p = plim_obj D L p := eq_refl.

(* N3 CONVERSION: Riehl's strict clause — the image of the canonical lift
   EQUAL to a given cone's apex downstairs — is an [eq] between functor
   records and is refused *)
Fail Example p426_strict_record (N : Cone (@Res P X ◯ D)) :
  fobj[@Res P X] (PointwiseLimit D L) = vertex_obj[N] := eq_refl.

(* control: cones already in the image lift strictly *)
Check (fun M : Cone D => strict_self D M).

End StrictLimit.

End Strict.

(** ** C: the restriction functor is more universe-general than the theorem
       it serves *)

Section Wide.

Universe bigo smallh.
Constraint smallh < bigo.

(* a shape whose OBJECT universe sits strictly ABOVE its hom universe *)
Context (Pw : Category@{bigo smallh smallh}).
Context (Xw : Category@{bigo smallh smallh}).

(* controls: the functor category, the discrete category on the objects,
   the restriction functor and the type of an endofunctor of [Pw, Xw] all
   form here — [DiscreteCat]'s homs are Prop-valued equalities, so the shape
   imposes no object ≤ hom, and a functor BETWEEN functor categories
   identifies two hom universes that both sit above [bigo] *)
Check ([Pw, Xw]).
Check (@ObjCat Pw).
Check (@Res Pw Xw).
Check ([Pw, Xw] ⟶ [Pw, Xw]).

(* N4 UNIVERSE: #425's corollary carries [jo <= jh] and is refused *)
Fail Check (fun HX : @Complete Xw => @Functor_Category_Complete Pw Xw HX).

(* N5 UNIVERSE: the TYPE of an evaluation functor is refused — [Fun]'s hom
   universe (natural transformations quantify over P's objects) sits above
   [bigo], and [Functor] identifies it with [Xw]'s hom universe [smallh].
   This, not anything in Instance/Fun/Creation.v, is where [jo <= jh]
   enters: every constant below that mentions [Eval] inherits it *)
Fail Check ([Pw, Xw] ⟶ Xw).

(* N6 UNIVERSE: hence #424's [Eval] itself, and with it the hypothesis
   [∀ p, Limit (Eval p ◯ D)] of [Res_CreatesLimit], cannot be stated at
   this shape, while [Res] can (control above) *)
Fail Check (@Eval Pw Xw).

End Wide.

(** ** D: readbacks *)

Check (@res_obj).
Check (@res_obj_at).
Check (@res_map).
Check (@eval_res_obj).
Check (@eval_res_map).
Check (@ptw_apex_readback).
Check (@ptw_leg_readback).
Check (@creation_apex).
Check (@creation_leg).
Check (@Res_Complete).
Check (@Res_continuous).

(** ** Guard block *)

Check @ObjCat.
Check @DiscInc.
Check @Res.
Check @ev_lift.
Check @ev_lift_apex.
Check @ev_lift_leg.
Check @Fun_pointwise_reflect.
Check @Fun_Eval_JointlyCreateLimit.
Check @Res_preserves.
Check @Res_CreatesLimit.
Check @Res_CreatesAllLimits.
Check @res_obj_at.
Check @strict_self.
Check @self_lift.
Check @PointwiseLimit.
Check @plim_obj.
Check @Functor_Category_Complete.
Check @DiscreteCat_Functor'.
Check @FCone.
Check @Cone.
Check @Complete.
Check @Limit.
Check @Eval.
Check @vertex_obj.
Check @fobj.
