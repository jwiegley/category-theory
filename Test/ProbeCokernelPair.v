Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Morphisms.CokernelPair.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.CokernelPair.

Generalizable All Variables.

(** * Probes guarding Theory/Morphisms/CokernelPair.v and
      Instance/Sets/CokernelPair.v *)

(* This file exists so that the strength claims in those two headers break
   LOUDLY rather than silently.  Every [Fail] below was stripped once and
   the failure KIND confirmed at the message, and every negative is paired
   with a positive control that must SUCCEED, so a rename or a record
   change cannot turn a [Fail] vacuously green.

   The import list is the union of the two targets' own import lists, in
   target order — a shortened prefix is exactly what makes a probe pass
   for the wrong reason.

   The two kinds of negative are kept LEXICALLY APART:

     - CONVERSION negatives, [Fail Definition … := eq_refl], asserting
       that two well-typed terms are NOT definitionally equal;
     - FORMABILITY negatives, [Fail Check], asserting that an expression
       does not elaborate at all.

   Instrument sanity: in batch mode a [Fail] that succeeds prints nothing
   and a [Fail] that does not fail aborts the file with "The command has
   not failed!", so a green build is genuine evidence. *)

(** ** Positive controls: what IS definitional *)

Section Controls.

Context {C : Category}.
Context {x y z : C} (f : x ~> y) (g : x ~> z).

(* The bundled/pinned round trip is a field repackaging both ways, so it
   closes on the whole record.  Control for the header's claim that both
   conversions cost nothing. *)
Definition ctl_roundtrip (P : IsPushout f g) :
  is_pushout_square_pushout (pushout_is_pushout_square f g P) = P := eq_refl.

(* [IsCokernelPair] IS [IsPushoutSquare] at a repeated leg. *)
Definition ctl_ckp_is_square (P : C) (u v : y ~> P) :
  IsCokernelPair f P u v = IsPushoutSquare f f P u v := eq_refl.

(* Controls for negative 2 below.  Without these, renaming either leg of
   the round trip would make that [Fail] pass VACUOUSLY, which the header's
   blanket guarantee forbids; an audit found exactly that gap. *)
Definition ctl_epic_pushout_square (E : Epic f) := epic_pushout_square f E.
Definition ctl_pushout_square_epic (S : IsPushoutSquare f f y id id) :=
  pushout_square_epic f S.

(* The duality collapse that carries every [Monic] statement of the target
   file.  Control for [op_collapse_pushout_square]. *)
Definition ctl_op_collapse :
  @IsPushoutSquare (C^op) y x x f f x id id
    = @IsPullback C x x y f f x id id := eq_refl.

(* The chosen cokernel pair's legs ARE the chosen pushout's injections. *)
Definition ctl_ckp_left `{H : @HasPushouts C} :
  ckp_left (cokernel_pair f) = pushout_in1 (pushout f f) := eq_refl.

(* Control for formability negative 4: the pinned form DOES take an apex
   and two legs, and the bundled form IS formable on the span alone. *)
Check (IsPushoutSquare f f y id id).
Check (IsPushout f f).

(* Control for conversion negative 1: the two [IsIsomorphism] readings are
   inter-derivable, so what negative 1 refutes is CONVERTIBILITY and not
   the mathematics. *)
Check (@IsIsomorphism_of_op C x y).
Check (@op_IsIsomorphism_of C x y).

End Controls.

Section SetsControls.

Context {A B Q : SetoidObject}.
Context (f : A ~{Sets}~> B) (q1 q2 : B ~{Sets}~> Q).
Context (Hc : q1 ∘[Sets] f ≈ q2 ∘[Sets] f).

(* Control for conversion negative 3, and the sharp diagnosis: the two
   sides of the left triangle agree POINTWISE at Leibniz equality.  So
   what negative 3 refutes is the equality of [SetoidMorphism] RECORDS —
   the composite rebuilds its [proper_morphism] certificate — and not any
   disagreement of the underlying functions. *)
Definition ctl_sets_triangle_pointwise (b : carrier B) :
  (sets_ck_med f q1 q2 Hc ∘[Sets] ck_left f) b = q1 b := eq_refl.

Definition ctl_sets_triangle_pointwise_r (b : carrier B) :
  (sets_ck_med f q1 q2 Hc ∘[Sets] ck_right f) b = q2 b := eq_refl.

End SetsControls.

(* Control for formability negatives 5-7: a category whose hom universe is
   STRICTLY below its proof universe is itself perfectly formable, and its
   hom-sets can be named.  So the rejections below are attributable to the
   named constants and not to the section's own declarations. *)
Section SeparatedUniverseControl.

Universes uo uh up.
Constraint uh < up.

Context (C : Category@{uo uh up}).
Context (x y : C) (f : x ~> y).

Check (x ~> y).
Check f.

End SeparatedUniverseControl.

(** ** CONVERSION negatives *)

Section ConversionNegatives.

Context {C : Category}.
Context {x y : C} (f : x ~> y).
Context (a b : C) (h : b ~> a).

(* 1. [IsIsomorphism] at C^op is NOT the C reading on the nose.  Both
      records carry the same inverse, but their two law fields are
      SWAPPED, so the conversion is a field permutation and the header
      says so rather than claiming [eq_refl].
      Stripped: "cannot unify @IsIsomorphism C^op a b h and
      @IsIsomorphism C b a h" — a conversion failure. *)
Fail Definition neg_iso_op :
  @IsIsomorphism (C^op) a b h = @IsIsomorphism C b a h := eq_refl.

(* 2. The [Epic] ↔ pushout-square passage does NOT round-trip on the nose.
      [pushout_square_epic] rebuilds the cancellation field out of the
      mediator's [unique_property], so the recovered [Epic] is a different
      term even though [Epic] has primitive projections with eta.
      Stripped: "cannot unify pushout_square_epic f (epic_pushout_square f
      E) and E" — a conversion failure. *)
Fail Definition neg_epi_roundtrip (E : Epic f) :
  pushout_square_epic f (epic_pushout_square f E) = E := eq_refl.

End ConversionNegatives.

Section SetsConversionNegatives.

Context {A B Q : SetoidObject}.
Context (f : A ~{Sets}~> B) (q1 q2 : B ~{Sets}~> Q).
Context (Hc : q1 ∘[Sets] f ≈ q2 ∘[Sets] f).

(* 3. The left triangle of the [Sets] cokernel pair is NOT a Leibniz
      equality of MORPHISMS, though it is one pointwise on the underlying
      functions (control above).  The composite rebuilds the
      [proper_morphism] certificate.
      Stripped: "cannot unify sets_ck_med f q1 q2 Hc ∘ ck_left f and q1" —
      a conversion failure. *)
Fail Definition neg_sets_triangle :
  sets_ck_med f q1 q2 Hc ∘[Sets] ck_left f = q1 := eq_refl.

End SetsConversionNegatives.

(** ** FORMABILITY negatives *)

Section FormabilityNegatives.

Context {C : Category}.
Context {x y : C} (f : x ~> y).

(* 4. THE HEADER'S CENTRAL STRUCTURAL CLAIM.  Structure/Pushout.v's
      [IsPushout] is BUNDLED despite the [Is] prefix: it carries its apex
      as data and takes only the two span legs, so it cannot be applied to
      a GIVEN apex and a GIVEN pair of cocone legs.  That is why the
      epimorphism characterization — a statement about ONE square — was
      not expressible before [IsPushoutSquare], and why the issue's
      suggested spelling could not be used.
      Stripped: "Illegal application (Non-functional construction): the
      expression IsPushout f f of type Type cannot be applied to the term
      y" — a typing error, not a universe inconsistency. *)
Fail Check (IsPushout f f y id id).

End FormabilityNegatives.

(* Negatives 5-9 measure a DONOR universe pin and attribute it PER DONOR
   rather than to the family as a whole.  The category below has its hom
   universe STRICTLY below its proof universe; the control section above
   shows such a category is perfectly formable and its hom-sets nameable,
   so the rejections are attributable to the named constants.

   Each of [Epic] (Theory/Morphisms.v), [Pullback] (Structure/Pullback.v),
   [IsPullback] (Theory/Morphisms/Stability.v) and [IsPushout]
   (Structure/Pushout.v) INDEPENDENTLY identifies hom with proof, and
   [IsPushoutSquare] inherits the identification — it introduces none of
   its own.  Every one was stripped and reports
   "universe inconsistency: Cannot enforce vp = vh because vh < vp",
   a genuine universe inconsistency and not a typing error (contrast
   negative 4, which IS a typing error). *)

Section UniverseNegatives.

Universes vo vh vp.
Constraint vh < vp.

Context (C : Category@{vo vh vp}).
Context (x y : C) (f : x ~> y).

(* 5. the [Epic] donor, Theory/Morphisms.v *)
Fail Check (@Epic C x y f).

(* 6. the [Pullback] donor, Structure/Pullback.v *)
Fail Check (@Pullback C x x y f f).

(* 7. the [IsPullback] donor, Theory/Morphisms/Stability.v *)
Fail Check (@IsPullback C x x y f f x id id).

(* 8. the [IsPushout] donor, Structure/Pushout.v *)
Fail Check (@IsPushout C x y y f f).

(* 9. inherited by the pinned pushout square *)
Fail Check (@IsPushoutSquare C x y y f f y id id).

End UniverseNegatives.
