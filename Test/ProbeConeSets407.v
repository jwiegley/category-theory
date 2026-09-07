Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Diagram.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Sets.Cone.
Require Import Category.Instance.Sets.Karoubi.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

(** * Probe for issue #407: Mac Lane SV.1, completeness of Sets *)

(* The boundary of Instance/Sets/Complete.v's cone-set section and of
   Instance/Sets/Cone.v.  Eleven refutation commands, plus one instrument
   check on a name that does not exist.  Each was stripped ONE AT A TIME,
   compiled alone, and its WHOLE error read; the classification below is by
   the error TEXT, not by expectation:

     FORMABILITY  the error ends in a universe clause
     CONVERSION   "cannot unify", no universe clause
     TYPING       a plain has-type mismatch, neither of the above
     RESOLUTION   "Cannot infer the implicit parameter ..."

   Count by kind: 7 CONVERSION, 1 TYPING, 2 FORMABILITY, 1 RESOLUTION.

   Every constant any refutation command names is also named OUTSIDE every
   such command, in a [Check] below, so that renaming it in its own library
   file breaks this file at a [Check] rather than turning a guard silently
   green.

   The [Require] list is the UNION of the two new library files' own, plus
   Category.Theory.Universal.Element, which this issue also extends and
   whose new constant is guarded below though no refutation names it.

   ONE TRAP, MEASURED AND WORKED AROUND.  Negative 2 must be a
   [Definition], not a [Check]: a bare [Check] of the same expression is
   ACCEPTED, printing an open evar for the missing [Setoid] instance, so a
   refutation command against it would be a FALSE PASS. *)

(** ** Guard block: every constant the refutations name, named outside them *)

Check @Sets_limit_obj.
Check @Sets_limit_leg.
Check @Sets_limit_compatible.
Check @cone_apex.
Check @cone_leg_at.
Check @cone_set_IsALimit.
Check @cone_set_Limit.
Check @cone_set_med.
Check @ConeSet_Complete.
Check @discrete_limit.
Check @discrete_iprod_iso.
Check @Sets_iprod_proj.
Check @iprod_proj.
Check @DiscreteCat.
Check @DiscreteCat_Functor.
Check @IsALimit.
Check @Cone.
Check @ACone.
Check @cone_apex_iso.
Check @cone_transpose.
Check @cone_untranspose.
Check @ConeSet_Natural_Iso.
Check @ConeSet_Representable.
Check @ConeSet_HasLimitsOfShape.
Check @ConeSet_Diagonal_Limit_Adjunction.
Check @Sets_Diagonal_Limit_Adjunction.
Check @Sets_HasLimitsOfShape.
Check @Cone_Natural_Transform.
Check @adj.
Check @Isomorphism.
Check @sets_eq_obj.
Check @sets_eq_incl.
Check @sets_IsEqualizer.
Check @concrete_vs_existing.
Check @existing_IsEqualizer.
Check @Sets_HasEqualizers.
Check @APair.
Check @karoubi_IsEqualizer.
Check @sets_split_obj.
Check @tuple_obj.
Check @tuple_compat.
Check @tuple_iso.
Check @tuple_proj.
Check @FunctorOfDiagram.
Check @Diagram.
Check @Quiver.
Check @Srestr.
Check @pres_iso.
Check @PresentedQuiver.
Check @PathRel.
Check @global_elements_natural.
Check @SetoidObject.
Check @fst.
Check @snd.
Check @from.
Check @to.

(** ** Instrument check *)

(* If a refutation command can pass on a name that does not exist, none of
   the ones below measures anything.  This one must pass. *)
Fail Check @coneset_probe_instrument_absent.

(** ** (1) The two apexes are not equal -- CONVERSION *)

(* One is a sigma of a dependent function with a compatibility witness, the
   other an [ACone] record.  Whole error tail:
     (cannot unify "Sets_limit_obj F" and "cone_apex F"). *)
Fail Example neg_apex_strict {D : Category} (F : D ⟶ Sets) :
  Sets_limit_obj F = cone_apex F := eq_refl.

(** ** (2) There is no [≈] grade on objects -- RESOLUTION *)

(* Objects of [Sets] carry no setoid.  Whole error:
     The following term contains unresolved implicit arguments ...
     ?Setoid: Cannot infer the implicit parameter Setoid of equiv whose
     type is "Setoid SetoidObject" (no type class instance found).
   A [Check] here is ACCEPTED (open evar), so this is a [Definition]. *)
Fail Definition neg_apex_equiv {D : Category} (F : D ⟶ Sets) : Type :=
  (Sets_limit_obj F ≈ cone_apex F).

(** ** (3) The discrete leg equation is [≈], not [eq_refl] -- CONVERSION *)

(* [∘] in [Sets] rebuilds a [SetoidMorphism] record.  The [≈] form is
   [discrete_iprod_iso_leg], which holds. *)
Fail Example neg_discrete_leg {A : Set} (f : A → obj[Sets]) (a : A) :
  Sets_iprod_proj f a ∘ to (discrete_iprod_iso f)
  = iprod_proj f (discrete_limit f) a := eq_refl.

(** ** (4) Which limit oracle the adjunction is fed -- TYPING *)

(* Fed the PRE-EXISTING [Sets_HasLimitsOfShape], the transposition does not
   land at the cone set, and not even at the same TYPE: a plain has-type
   mismatch, no "cannot unify" and no universe clause.  The accepted
   control below is the SAME statement at the cone-set oracle, which is
   what makes this negative discriminate between the two oracles rather
   than merely record that something failed. *)
Fail Definition neg_wrong_oracle {J : Category} (F : J ⟶ Sets)
  (X : obj[Sets]) :
  @Isomorphism Sets
     {| carrier := @hom ([J, Sets]) (Δ[J](X)) F |}
     {| carrier := X ~{Sets}~> cone_apex F |}
  := @adj _ _ _ _ (Sets_Diagonal_Limit_Adjunction J) X F.

Definition ctrl_right_oracle {J : Category} (F : J ⟶ Sets)
  (X : obj[Sets]) :
  @Isomorphism Sets
     {| carrier := @hom ([J, Sets]) (Δ[J](X)) F |}
     {| carrier := X ~{Sets}~> cone_apex F |}
  := @adj _ _ _ _ (ConeSet_Diagonal_Limit_Adjunction J) X F.

(** ** (5) and (6) The [Set] pin of the discrete shape -- FORMABILITY *)

(* Instance/Sets/Complete.v's discrete section is stated with [{A : Set}]
   and not [{A : Type}].  That is forced, and it takes TWO donors.  Both
   are pinned here, and [Cone] is the discriminating control: it is
   ACCEPTED at hom levels declared strictly above [Set], so the pin is not
   "the cone vocabulary". *)

Section SetPin.

Universes io co ch cp.
Constraint Set < ch.
Context (A : Type@{io}).
Context (C : Category@{co ch cp}).
Context (f : A → obj[C]).

(* Controls, all accepted at these very levels. *)
Check (DiscreteCat@{io ch cp} A).
Check (DiscreteCat_Functor f).
Check (Cone (DiscreteCat_Functor f)).
Check (@ACone (DiscreteCat A) C).

(* Donor 1: [DiscreteCat_Functor] pins its own SOURCE at
   [DiscreteCat@{_ Set Set}].  Whole error tail:
     (universe inconsistency: Cannot enforce Set = ch). *)
Fail Check (DiscreteCat_Functor f : DiscreteCat@{io ch cp} A ⟶ C).

(* Donor 2: [IsALimit] identifies the shape's hom-and-proof universes with
   the ambient category's, so once the shape is at [Set] the ambient must
   be too.  Same error tail, fired at a different place. *)
Fail Check (IsALimit (DiscreteCat_Functor f)).

End SetPin.

(** ** (7) The forward transposition is [≈], not [eq_refl] -- CONVERSION *)

(* NO CAUSE IS ISOLATED, and the obvious localization is refuted.  The
   [ACone] round trip of [Cone_Natural_Transform] does return the leg
   family on the nose (measured, accepted) while rebuilding the whole
   record, whose [cone_coherence] proof is [abstract]ed at
   Structure/Cone/Const.v:58 -- but these two sides differ ALREADY at a
   point [x : X], and again at the produced cone's leg at [d], both
   measured, so the refusal is not confined to that law field.  The [≈]
   form is [coneset_adj_to_is_transpose], which holds. *)
Fail Example neg_adj_to_strict {J : Category} (F : J ⟶ Sets)
  (X : obj[Sets]) (p : ACone X F) :
  to (@adj _ _ _ _ (ConeSet_Diagonal_Limit_Adjunction J) X F)
     (snd (Cone_Natural_Transform F X) p)
  = cone_transpose F X p := eq_refl.

(** ** (8) ... and so is the backward one, at whole-record level *)

(* Same donor, same cause.  What DOES hold on the nose is the LEG-BY-LEG
   form, [coneset_adj_from_is_untranspose]. -- CONVERSION *)
Fail Example neg_adj_from_strict {J : Category} (F : J ⟶ Sets)
  (X : obj[Sets]) (h : X ~{Sets}~> cone_apex F) :
  fst (Cone_Natural_Transform F X)
      (from (@adj _ _ _ _ (ConeSet_Diagonal_Limit_Adjunction J) X F) h)
  = cone_untranspose F X h := eq_refl.

(** ** (9) Awodey's subset is not the existing apex -- CONVERSION *)

(* The existing [HasEqualizers Sets] apex is the compatible-family setoid
   over the walking parallel pair.  The bridge is [concrete_vs_existing],
   an isomorphism and nothing stronger. *)
Fail Example neg_awodey_strict {X Y : SetoidObject} (f g : X ~{Sets}~> Y) :
  sets_eq_obj f g = Sets_limit_obj (APair f g) := eq_refl.

(** ** (10) The tuple form is an isomorphism, not an equality -- CONVERSION *)

(* The two compatibility predicates quantify over paths and over generating
   edges respectively.  The bridge is [tuple_iso]. *)
Fail Example neg_tuple_strict {G : Quiver} (D : Diagram G Sets) :
  Sets_limit_obj (FunctorOfDiagram D) = tuple_obj D := eq_refl.

(** ** (11) Presentation-independence, at object level -- CONVERSION *)

(* The CARRIER is Leibniz-equal and so is the compatibility predicate --
   both are [Example]s in Instance/Sets/Cone.v -- so the obstruction is
   confined to the [is_setoid] field, whose [setoid_equiv] is
   [Sets_limit_obj_obligation_1] applied to two functors that [Compose]
   rebuilds.  The three accepted Examples beside this refusal are what
   locate it there. *)
Fail Example neg_pres_strict (G : Quiver) (R : PathRel G)
  (S : PresentedQuiver G R ⟶ Sets) :
  Sets_limit_obj S = Sets_limit_obj (Srestr G R S) := eq_refl.

(** ** Controls for the three grades that DO hold *)

Example ctrl_pres_carrier (G : Quiver) (R : PathRel G)
  (S : PresentedQuiver G R ⟶ Sets) :
  Sets_limit_carrier S = Sets_limit_carrier (Srestr G R S) := eq_refl.

Example ctrl_apex_is_conepresheaf {D : Category} (F : D ⟶ Sets) :
  carrier (cone_apex F)
  = @ACone D Sets (@terminal_obj Sets Sets_Terminal) F := eq_refl.

Example ctrl_iso_to_is_med {D : Category} (F : D ⟶ Sets) :
  to (cone_apex_iso F)
  = cone_set_med F (alimit_cone (limit_is_alimit (Sets_Limit F)))
  := eq_refl.
