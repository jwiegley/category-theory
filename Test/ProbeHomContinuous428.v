(** * Probe for Functor/Hom/Continuous.v (issue #428)

    Pins the measured boundaries of the isomorphism form of hom-functor
    continuity: one CONVERSION refusal (N1: the two presentations of the
    hom-diagram, [HomFrom c ◯ F] and [HomDiagram c F], agree on objects and
    on the action of [fmap] but not at the [fmap] field, an opaque
    [Program] obligation) and two UNIVERSE refusals (N2: the carrier and
    relation levels of every set in the target are pinned to the hom level
    of the source, so the hom-functor of a fixed category cannot be read
    into a strictly larger universe of sets — only the level of the universe
    holding Sets' objects is free; Mac Lane's Remark 1 as far as it holds;
    N3: the [Sets] limit of the hom-diagram needs the
    shape's object level at or below that carrier level, while #331's
    preservation theorem does not — Riehl's large-diagram footnote).  Each
    refutation was stripped one at a time in a copy of the whole file; the
    import list mirrors the target's.  Section D's readbacks and the guard
    block are positive controls. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Structure.Limit.Weighted.
Require Import Category.Structure.Wedge.
Require Import Category.Structure.End.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.End.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Functor.Hom.Continuous.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe428_absent_name.

(** ** A: the two presentations of the hom-diagram agree on objects and on
       the action of [fmap], not at the [fmap] field *)

Section Presentations.

Context {J C : Category} (c : C) (F : J ⟶ C).

(* controls: objects, and the action on an element, both convert *)
Example p428_fobj : fobj[@HomFrom C c ◯ F] = fobj[HomDiagram c F] := eq_refl.

Example p428_fmap_value {j j' : J} (g : j ~{J}~> j') (h : c ~{C}~> F j) :
  fmap[@HomFrom C c ◯ F] g h = fmap[HomDiagram c F] g h := eq_refl.

(* N1 CONVERSION: the whole [fmap] field does not — the setoid morphism's
   respectfulness proof is an opaque [Program] obligation:
   [Curried_Hom_obligation_1], auto-discharged in Functor/Hom.v, against
   [HomDiagram]'s written-out one in Structure/Limit/Weighted.v *)
Fail Example p428_fmap_field {j j' : J} (g : j ~{J}~> j') :
  fmap[@HomFrom C c ◯ F] g = fmap[HomDiagram c F] g := eq_refl.

(* controls: the carriers Remark 2 and the Riehl items compute with *)
Example p428_image_apex (N : Cone F) :
  carrier (vertex_obj[FCone (@HomFrom C c) N]) = (c ~{C}~> vertex_obj[N])
  := eq_refl.

Example p428_limit_carrier :
  carrier (Sets_limit_obj (HomDiagram c F)) = Sets_limit_carrier (HomDiagram c F)
  := eq_refl.

Example p428_cone_carrier :
  carrier (fobj[ConePresheaf F] c) = @ACone J C c F := eq_refl.

End Presentations.

(** ** B: Remark 1 — which universe of sets *)

Section Universes.

Universe o1 h1 hbig sbig.
Constraint h1 < hbig.
Constraint hbig < sbig.

Context (Cw : Category@{o1 h1 h1}) (cw : Cw).

(* control: the level of the universe HOLDING Sets' objects is free above
   the carrier level ([Sets@{o so} : Category@{so o o}], Instance/Sets.v) *)
Check (@HomFrom Cw cw : Cw ⟶ Sets@{h1 sbig}).
Check (@hom_continuous_at Cw cw
       : ContinuousFunctor (@HomFrom_at Cw cw : Cw ⟶ Sets@{h1 sbig})).

(* N2 UNIVERSE: the CARRIER level — and with it, [SetoidObject@{o o}], the
   relation level — is pinned to the hom level of the source: the
   hom-functor of a FIXED category cannot be read into a strictly larger
   universe of sets *)
Fail Check (@HomFrom Cw cw : Cw ⟶ Sets@{hbig sbig}).

End Universes.

(** ** C: smallness — Remark 2's [Sets]-side limit needs the shape's objects
       at or below the carrier level; #331's theorem does not *)

Section Smallness.

Universe jo h.
Constraint h < jo.

Context (Jw : Category@{jo h h}) (Cw : Category@{h h h}) (cw : Cw).

(* controls: the hom-diagram forms and #331's preservation applies *)
Check (fun F : Jw ⟶ Cw => @HomFrom Cw cw ◯ F).
Check (fun F : Jw ⟶ Cw => hom_PreservesLimitCone cw F).

(* N3 UNIVERSE: the [Sets] limit of the hom-diagram is refused —
   [Sets_Limit] needs the shape's object level at or below [Sets]' carrier
   level, here [h] *)
Fail Check (fun F : Jw ⟶ Cw => Sets_Limit (@HomFrom Cw cw ◯ F)).

End Smallness.

(** ** D: readbacks *)

Section Readbacks.

Context {J C : Category} {F : J ⟶ C} (L : Limit F) (c : C).

Check (remark2_iso L c).
Check (remark2_natural L).
Check (remark2_comparison_iso L c).
Check (end_Limit c F).
Check (cone_nat_iso (F:=F) c).
Check (limtuple_cone_iso (F:=F) c).

(* the alias names the issue asks to audit *)
Check (hom_preserves_limits c).
Check (@cohom_carries_colimits_to_limits C c).

End Readbacks.

(** ** Guard block *)

Check @HomFrom.
Check @HomTo.
Check @HomDiagram.
Check @Sets_Limit.
Check @Sets_limit_obj.
Check @Sets_limit_carrier.
Check @ConePresheaf.
Check @ACone.
Check @FCone.
Check @Cone.
Check @Limit.
Check @hom_PreservesLimitCone.
Check @hom_ContinuousFunctor.
Check @hom_continuous_at.
Check @HomFrom_at.
Check @PreservesLimitCone_transport.
Check @ContinuousFunctor_transport.
Check @remark2_iso.
Check @remark3_iso.
Check @hom_iprod_iso.
Check @cohom_icoprod_iso.
Check @end_Limit.
Check @fmap.
Check @fobj.
Check @carrier.
Check @vertex_obj.
