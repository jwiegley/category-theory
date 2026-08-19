(** * Boundary probes for the two-variable Yoneda isomorphism

    Companion to Functor/Hom/Yoneda/Natural.v (issue #316; Mac Lane §III.2
    Lemma 2, Riehl §2.2 and §E.1, Awodey §8.3 Lemma 8.2).  That file makes
    strength claims of two DIFFERENT kinds, and this file pins both.  **If
    the [Fail] commands below stop failing, this file breaks the build.**

    THE TWO KINDS ARE NOT THE SAME AND ARE NOT DESCRIBED WITH ONE WORD.

    (1) FORMABILITY.  [Covariant_Yoneda_Lemma] and [Yoneda_Lemma]
    (Functor/Hom/Yoneda.v:206 and :157) are stated over
    [C : Category@{u u u}] — object, hom and proof universes IDENTIFIED —
    so nothing built over them can be applied to a category whose objects
    live strictly below its homs.  [yoneda_natural] inherits exactly that,
    and the rejections below are UNIVERSE INCONSISTENCIES: the term is not
    formable at all, not merely non-convertible.  The two bifunctors
    [YoEval] and [YoNat] — and [YoEvalAt] — are over [Category@{u u0 u0}]
    with the object universe FREE below the hom universe (measured: their
    constraint sets carry [u <= u0] and no [u = u0]), and all three ARE
    formable there; so is the THEOREM'S OWN TYPE, [YoNat C ≅ YoEval C],
    which an audit checked elaborates in this very section — so the
    rejection is attributable to the donor TERM, not to the statement or to
    the [Isomorphism]-in-[[X, Sets]] packaging.  So is an identity
    isomorphism between the bifunctors in
    the very functor category the theorem lives in, which is what makes the
    rejection attributable to the donor rather than to the packaging.  The
    boundary runs exactly where [Covariant_Yoneda_Lemma] is consumed:
    [YoEvalAt] does not consume it and is free, while
    [YoEvalAt_Representable] does and carries [u = u0].

    (2) CONVERSION.  Four claims of Leibniz equality are rejected because
    the two sides carry different opaque proof terms, while the corresponding
    claims one or two applications further in DO hold.  These are [Fail
    Definition ... := eq_refl] and not [Fail Example ... : T.]: a failing
    type ascription would guard only the statement, whereas what is claimed
    is convertibility of the two terms.

    COUNTS.  Eight negatives — four in each group — and seven positive
    controls, which is not a one-to-one pairing: the four controls of group
    (1) serve all four of its negatives jointly, and in group (2) the [to]
    control serves two negatives.  Every negative is accompanied by at least
    one control that must SUCCEED.  The instrument itself was checked —
    wrapping [Fail] around a succeeding command reports "The command has not
    failed!" and aborts compilation — and every negative was compiled once
    with the [Fail] stripped, to confirm the error is the intended one: four
    reports of "universe inconsistency: Cannot enforce uh = uo because
    uo < uh" naming the declared universes for group (1), and four "cannot
    unify" conversion errors for group (2).  The import list is the target
    file's own, in the target file's order, plus the target file itself. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Sheaf.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Deloop.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Construction.Product.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Hom.Yoneda.Natural.

Generalizable All Variables.

(** ** (1) The inherited universe restriction

    A category whose object universe is declared STRICTLY BELOW its hom
    universe.  The two bifunctors reach it; the theorem does not. *)

Section ObjectsBelowHoms.

Universes uo uh.
Constraint uo < uh.

Context (C : Category@{uo uh uh}).

(* Positive controls: both bifunctors are formable here, and so is the
   partially applied evaluation functor... *)
Check (YoEval C).
Check (YoNat C).
Check (fun c : C => @YoEvalAt C c).

(* ...and so is an isomorphism between them in the functor category the
   theorem is stated in, so the packaging is not what is rejected. *)
Definition probe_iso_id_control :
  @Isomorphism ([([C, Sets] ∏ C), Sets]) (YoEval C) (YoEval C) := iso_id.

(* Negative 1: the theorem itself is not formable at this category. *)
Fail Check (yoneda_natural C).

(* Negatives 2 and 3: neither is its donor, in either variance — so the
   restriction is inherited and not introduced by this development. *)
Fail Check (fun (F : C ⟶ Sets) (A : C) => Covariant_Yoneda_Lemma C F A).
Fail Check (fun (F : C^op ⟶ Sets) (A : C) => Yoneda_Lemma C F A).

(* Negative 4: the representability instance is restricted too, though the
   functor it represents is not — the boundary runs exactly where
   [Covariant_Yoneda_Lemma] is consumed, and [YoEvalAt] above does not
   consume it. *)
Fail Check (fun c : C => YoEvalAt_Representable C c).

End ObjectsBelowHoms.

(** ** (2) The conversion boundaries *)

Section Conversion.

Context (C : Category).
Context (x y : [C, Sets] ∏ C).
Context (tf : x ~> y).
Context (F : C^op ⟶ Sets).
Context (A : C).
Context (yv : F A).
Context (z : C).
Context (phi : z ~{C}~> A).

(* Negative 5.  The assembled [YoNat]'s arrow action and the hand-written
   [yo_nat_map] are not the same [SetoidMorphism] RECORD: their
   [proper_morphism] fields are different proof terms, one a fresh
   obligation of the target file and one assembled from [Hom]'s and
   [Swap]'s.  Control: pointwise they ARE the same term. *)
Fail Definition probe_nat_map_record :
  @fmap _ _ (YoNat C) x y tf = yo_nat_map tf := eq_refl.

Definition probe_nat_map_pointwise_control (a : fobj[YoNat C] x) :
  @fmap _ _ (YoNat C) x y tf a = yo_nat_map tf a := eq_refl.

(* Negative 6.  The derived contravariant lemma and the in-tree one are not
   the same [Isomorphism] record: all four fields differ as proof terms.
   Control: the forward legs agree once applied. *)
Fail Definition probe_derived_iso_record :
  Yoneda_Lemma_derived C F A = Yoneda_Lemma C F A := eq_refl.

Definition probe_derived_to_control (w : Presheaves [Hom ─,A] F) :
  to (Yoneda_Lemma_derived C F A) w = to (Yoneda_Lemma C F A) w := eq_refl.

(* Negative 7.  Nor are the two forward MORPHISMS equal as records, though
   they agree on every argument — the [proper_morphism] fields differ. *)
Fail Definition probe_derived_to_record :
  to (Yoneda_Lemma_derived C F A) = to (Yoneda_Lemma C F A) := eq_refl.

(* Negative 8.  The backward legs do not even agree on an argument: the
   VALUE is a whole [Transform] record whose [naturality] and
   [naturality_sym] fields are different opaque constants.  Control: the
   agreement holds one level further in, at the components. *)
Fail Definition probe_derived_from_value :
  from (Yoneda_Lemma_derived C F A) yv = from (Yoneda_Lemma C F A) yv
  := eq_refl.

Definition probe_derived_from_component_control :
  transform[from (Yoneda_Lemma_derived C F A) yv] z phi
    = transform[from (Yoneda_Lemma C F A) yv] z phi := eq_refl.

End Conversion.
