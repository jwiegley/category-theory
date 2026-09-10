(** * Probe for Instance/Cat/Creation.v (issue #439)

    Pins the measured boundaries of Mac Lane §V.6 Exercises 3 and 4 as they
    are actually delivered — over the tree's FIBRE PRODUCT of categories,
    not over a pullback square in [Cat], which `Instance/Cat/Pullback.v`
    refutes for this object.  Negatives of two kinds, kept lexically apart.

    CONVERSION: n1, the composite [FP_snd ◯ Comma_to_FP] has the same object
    and arrow action as [comma_proj2] — both accepted, at [eq_refl] — but is
    not the same functor RECORD, which is exactly why
    [CreatesLimit_transport] is needed to get from one to the other; n2, the
    comma category is not the fibre product on the nose either, so
    [Comma_FP_iso] is doing real work.

    TYPING: n3, an object of a fibre product stores a LEIBNIZ equality
    between the two images, and an isomorphism does not ascribe there — this
    is the measured reason the bottom functor must create limits STRICTLY
    rather than up to isomorphism, and the accepted control beside it builds
    the same object from an equality.

    The [eq_refl] readbacks are positive controls: the strict lift's apex
    and legs lie over the given cone downstairs, the fibre-product square
    commutes definitionally at every index, and the two Verification-block
    aliases are the constants they name.  Each refutation was stripped one
    at a time in a copy of the whole file; the import list mirrors the
    target's. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Theory.Equivalence.Creation.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Slice.Adjunction.
Require Import Category.Construction.Slice.Creation.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Pullback.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Instance.Cat.Creation.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe439_absent_name.

(** ** A: CONVERSION — the transported projection against [comma_proj2] *)

Section Transported.

Context {C D : Category}.
Context (U : C ⟶ D).
Context (d : D).

(* controls: object and arrow actions agree on the nose *)

Example p439_fobj (x : (=(d) ↓ U)) :
  fobj[FP_snd (@Coslice_Proj D d) U ◯ Comma_to_FP U d] x
    = fobj[@comma_proj2 _1 C D (=(d)) U] x := eq_refl.

Example p439_fmap {x y : (=(d) ↓ U)} (f : x ~> y) :
  fmap[FP_snd (@Coslice_Proj D d) U ◯ Comma_to_FP U d] f
    = fmap[@comma_proj2 _1 C D (=(d)) U] f := eq_refl.

(* n1 CONVERSION: the two FUNCTORS are nevertheless different records *)
Fail Example p439_same_functor :
  (FP_snd (@Coslice_Proj D d) U ◯ Comma_to_FP U d)
    = (@comma_proj2 _1 C D (=(d)) U) := eq_refl.

(* n2 CONVERSION: and the comma category is not the fibre product on the
   nose, so the isomorphism is doing real work *)
Fail Example p439_same_category :
  (=(d) ↓ U) = FibreProduct (@Coslice_Proj D d) U := eq_refl.

End Transported.

(** ** B: TYPING — why the bottom functor must create limits STRICTLY *)

Section Strictness.

Context {A B C : Category}.
Context (F : A ⟶ C) (G : B ⟶ C).

(* control: an object of the fibre product is a pair plus a LEIBNIZ
   equality between the two images *)
Example p439_fp_obj (a : A) (b : B) (e : F a = G b) : FibreProduct F G :=
  ((a, b); e).

(* n3 TYPING: an isomorphism does not ascribe in that slot, which is why the
   created apex needs [slift_eq] and not a [ConeIso] *)
Fail Example p439_fp_obj_iso (a : A) (b : B) (i : F a ≅ G b) :
  FibreProduct F G := ((a, b); i).

End Strictness.

(** ** C: readbacks *)

Section Readbacks.

Context {A B C : Category}.
Context (F : A ⟶ C) (G : B ⟶ C).
Context {J : Category}.
Context (K : J ⟶ FibreProduct F G).
Context (SC : StrictlyCreatesLimit (FP_fst F G ◯ K) F).
Context (HG : PreservesLimitCone (FP_snd F G ◯ K) G).

(* the square commutes definitionally at every index *)
Example p439_square (j : J) :
  fp_square_obj F G K j = `2 (K j) := eq_refl.

(* the strict lift lies over the GIVEN cone, apex and legs *)

Example p439_lift_apex (N : Cone (FP_snd F G ◯ K)) (HN : IsLimitCone N) :
  fobj[FP_snd F G]
    (vertex_obj[slift_cone
       (screates (StrictlyCreatesLimit := fp_snd_StrictlyCreatesLimit F G K SC HG)
          N HN)])
    = vertex_obj[N] := eq_refl.

Example p439_lift_legs (N : Cone (FP_snd F G ◯ K)) (HN : IsLimitCone N)
  (j : J) :
  fmap[FP_snd F G]
    (cone_leg (slift_cone
       (screates (StrictlyCreatesLimit := fp_snd_StrictlyCreatesLimit F G K SC HG)
          N HN)) j)
    = cone_leg N j := eq_refl.

(* the issue's Verification-block name IS the constant it aliases *)
Example p439_alias_ex3 :
  creation_pullback_stable F G K SC HG = fp_snd_StrictlyCreatesLimit F G K SC HG
  := eq_refl.

End Readbacks.

Example p439_alias_ex4 {C D : Category} (U : C ⟶ D) (d : D)
  (HU : ContinuousFunctor U) {J : Category} (K : J ⟶ (=(d) ↓ U)) :
  comma_creates_limits_second_proof U d HU K
    = comma_proj2_creates_second U d HU K := eq_refl.

(** ** D: guard block *)

Check @cast_solve.
Check @cast_from_rew.
Check @cast_shuffle.
Check @cast_unit_cod.
Check @cast_unit_dom.
Check @cast_transfer.
Check @islimitcone_dtransport.
Check @islimitcone_dtransport_inv.
Check @fun_equiv_whisker_r.
Check @ctr_lift.
Check @ctr_over.
Check @ctr_fcone_iso.
Check @ctr_reflect.
Check @CreatesLimit_transport.
Check @fp_square_obj.
Check @fp_square_hom.
Check @fp_square_iso.
Check @fp_F_image_coneiso.
Check @fp_F_image_limiting.
Check @fp_med_cast.
Check @fp_med.
Check @fp_islimitcone.
Check @fp_image_cone.
Check @fp_image_limiting_at.
Check @fp_upstairs_lift.
Check @fp_lift_apex.
Check @fp_lift_leg.
Check @fp_lift_coh.
Check @fp_lift_cone.
Check @fp_strict_lift.
Check @fp_lift_limiting.
Check @fp_reflect.
Check @fp_snd_StrictlyCreatesLimit.
Check @fp_snd_CreatesLimit.
Check @fp_snd_CreatesAllLimits.
Check @creation_pullback_stable.
Check @Comma_to_FP.
Check @FP_to_Comma.
Check @FP_round_to.
Check @FP_round_from.
Check @FP_round_iso.
Check @FP_round.
Check @Comma_round_to.
Check @Comma_round_from.
Check @Comma_round_iso.
Check @Comma_round.
Check @Comma_FP_iso.
Check @Comma_FP_Equivalence.
Check @ex4_functor_iso.
Check @ex4_fp_creates.
Check @ex4_composite.
Check @comma_proj2_creates_second.
Check @comma_proj2_CreatesAllLimits_via_pullback.
Check @comma_Complete_via_pullback.
Check @comma_creates_limits_second_proof.
Check @Id_ContinuousFunctor.
Check @coslice_comma_proj2_creates_via_pullback.
Check @coslice_comma_Complete_via_pullback.
Check @FibreProduct.
Check @FP_fst.
Check @FP_snd.
Check @FibreProduct_not_Cat_pullback.
Check @FibreProduct_IsPullback.
Check @Coslice_Proj_StrictlyCreatesLimit.
Check @comma_CreatesAllLimits.
