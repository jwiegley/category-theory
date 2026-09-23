Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Structure.WellPowered.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Epi.

Generalizable All Variables.

(** * Grp is well-powered one universe up *)

(* nLab:      https://ncatlab.org/nlab/show/well-powered+category
   Wikipedia: https://en.wikipedia.org/wiki/Subgroup

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.8, book p. 130 (PDF p. 139): a category is well-powered when the
   subobjects of each object form a small set.  In [Grp] a subobject is a
   subgroup up to isomorphism, so the classical index is the set of
   subgroups.  This file states that at Structure/WellPowered.v's per-object
   record: [Grp_WellPoweredAt_up G : WellPoweredAt G], with index
   [Subgroup G] (Instance/Grp/Quotient.v).  The [Sets] witnesses are
   Instance/Sets/WellPowered.v.

   WHAT IS BUILT.  [wp_to] sends a subgroup to its inclusion
   ([grp_sub_of_subgroup], from Instance/Grp/Quotient.v's [SubgroupGrp],
   [sub_incl] and [sub_incl_monic]); [wp_from] sends a subobject to the
   image of its mono ([grp_image_subgroup], whose membership is Instance/
   Grp/Epi.v's [Type]-valued [GrpImage] and whose closure laws are that
   file's [GrpImage_respects], [GrpImage_unit], [GrpImage_mul] and
   [GrpImage_inv]).  The domain isomorphism [grp_image_iso] projects the
   carried preimage one way and pairs an element with itself the other.
   Nothing is assumed.

   A TRAP, recorded.  The [GrpImage_*] closure lemmas are [Qed], so the
   preimages they build cannot be computed with.  The homomorphism laws of
   the forward map [grp_image_fwd] are therefore proved through
   injectivity of the mono (Instance/Grp.v's [Grp_injectivity_is_monic])
   and [projT2] of the opaque witnesses, never by unfolding them.

   WHY ONE UNIVERSE UP, measured.  [Subgroup G] has a [Type]-valued
   membership predicate on the carrier, so it sits one universe above the
   carrier, which is [Grp]'s hom universe:

     Grp_WellPoweredAt_up@{u u0 u1} :
       ∀ G : obj[Grp@{u0 u1}], WellPoweredAt@{u u0 u0 u1 u} G
       (* Set < u0, u1 < u, u1 < u0 *)

   ([WellPoweredAt]'s first slot is the index universe, its fourth the hom
   universe.)  At Structure/WellPowered.v's pin the witness is refused, in
   a copy of this whole file with the one command appended:
   [WellPowered@{o h h o o} Grp@{o h}] with [h < o] gives "The term
   "Grp_WellPoweredAt_up G" has type "WellPoweredAt@{R5.4103 o o h
   R5.4103} G" while it is expected to have type "WellPoweredAt@{h o o h o}
   G" (universe inconsistency: Cannot enforce o = h because h < o)", and
   the control [Grp_WellPoweredAt_up@{o o h} G] is accepted.  [Set < u0]
   and [u1 < u0] are inherited, not introduced here: [About Grp] reads
   [Grp@{u p} : Category@{u p p}] with [Set < u] and [p < u], the [Set+1]
   that the [PropEquiv] field puts in [GrpObject]'s sort (CLAUDE.md's
   universe section).

   MEASUREMENTS.  7 [.glob] heads ('^(def|prf|thm|ind|constr|proj|rec) ')
   and 6 [Program] obligations ([grp_image_fwd_obligation_1] to [_3] and
   [grp_image_bwd_obligation_1] to [_3], found by [strings] on the .vo):
   all 13 report "Closed under the global context" by their fully
   qualified names.  [grp_image_iso] and [grp_image_to_from] are
   [Defined] (an isomorphism and a ≈ of subobjects, both data); the six
   obligations are [Qed].

   NOT DELIVERED.  [Grp] well-powered at the pin, unconditionally or under
   any hypothesis: a [Prop]-valued membership would sit at the carrier
   universe but meets the refusal Instance/Sets/WellPowered.v quotes for
   [Sets], and nothing is attempted here.  [Grp] co-well-powered: Instance/
   Grp/QuotObj.v's header records that its surjectivity leg takes the
   double-negation stability of image membership as a hypothesis, and no
   index of quotients is built.  No [Ab] or [RMod R] analogue. *)

(* The image of a homomorphism as a [Subgroup]; its membership is
   Instance/Grp/Epi.v's [GrpImage], a [Type]-valued "has a preimage". *)
Definition grp_image_subgroup {G H : Grp} (f : G ~{Grp}~> H) : Subgroup H :=
  {| sub_mem  := GrpImage f ;
     sub_resp := GrpImage_respects f ;
     sub_unit := GrpImage_unit f ;
     sub_mul  := GrpImage_mul f ;
     sub_inv  := GrpImage_inv f |}.

(* The subobject a subgroup names: its inclusion. *)
Definition grp_sub_of_subgroup (G : Grp) (S : Subgroup G) : SubObj G :=
  @Build_SubObj Grp G (SubgroupGrp S) (sub_incl S) (sub_incl_monic S).

Section GrpToFrom.

Context (G : Grp) (u : SubObj G).

(* The domain isomorphism between the image of the mono and its domain.
   The closure lemmas of Instance/Grp/Epi.v are [Qed], so the homomorphism
   laws of the forward map are proved through injectivity of the mono, never
   by computing the opaque witnesses. *)
Program Definition grp_image_fwd :
  SubgroupGrp (grp_image_subgroup (sub_mono u)) ~{Grp}~> sub_dom u := {|
  grp_map := {| morphism := fun p => `1 (`2 p) |}
|}.
Next Obligation.
  intros [b [a Ha]] [b' [a' Ha']] H; simpl in *.
  apply (snd (Grp_injectivity_is_monic (sub_mono u)) (sub_is_monic u)).
  rewrite Ha, Ha'. exact H.
Qed.
Next Obligation.
  apply (snd (Grp_injectivity_is_monic (sub_mono u)) (sub_is_monic u)).
  rewrite (projT2 (GrpImage_unit (sub_mono u))).
  symmetry. apply (grp_map_unit (sub_mono u)).
Qed.
Next Obligation.
  apply (snd (Grp_injectivity_is_monic (sub_mono u)) (sub_is_monic u)).
  rewrite (grp_map_mul (sub_mono u)).
  rewrite (projT2 (GrpImage_mul (sub_mono u) _ _ (projT2 a) (projT2 b))).
  destruct a as [b1 [x Hx]], b as [b2 [y Hy]]; simpl.
  rewrite Hx, Hy. reflexivity.
Qed.

Program Definition grp_image_bwd :
  sub_dom u ~{Grp}~> SubgroupGrp (grp_image_subgroup (sub_mono u)) := {|
  grp_map := {| morphism := fun a =>
      existT (fun b => GrpImage (sub_mono u) b) (sub_mono u a)
             (existT (fun a' => @equiv _ (is_setoid (grp_setoid G))
                                        (sub_mono u a') (sub_mono u a)) a
                     (@Equivalence_Reflexive _ _
                        (@setoid_equiv _ (is_setoid (grp_setoid G)))
                        (sub_mono u a))) |}
|}.
Next Obligation. intros a a' H; simpl. apply proper_morphism; exact H. Qed.
Next Obligation. apply (grp_map_unit (sub_mono u)). Qed.
Next Obligation. apply (grp_map_mul (sub_mono u)). Qed.

Definition grp_image_iso :
  @Isomorphism Grp (SubgroupGrp (grp_image_subgroup (sub_mono u))) (sub_dom u).
Proof.
  unshelve refine (@Build_Isomorphism Grp _ _ grp_image_fwd grp_image_bwd _ _).
  - intro a; simpl; reflexivity.
  - intros [b [a Ha]]; simpl. exact Ha.
Defined.

Definition grp_image_to_from :
  grp_sub_of_subgroup G (grp_image_subgroup (sub_mono u)) ≈ u.
Proof.
  exists grp_image_iso.
  intros [b [a Ha]]; simpl. exact Ha.
Defined.

End GrpToFrom.

Definition Grp_WellPoweredAt_up (G : Grp) : WellPoweredAt G :=
  {| wp_index   := Subgroup G ;
     wp_to      := grp_sub_of_subgroup G ;
     wp_from    := fun u => grp_image_subgroup (sub_mono u) ;
     wp_to_from := grp_image_to_from G |}.
