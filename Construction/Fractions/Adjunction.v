Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Groupoid.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Fractions.
Require Import Category.Construction.Fractions.Weak.
Require Import Category.Construction.Groupoid.Core.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Grpd.

Generalizable All Variables.

(** * Riehl 4.1.15: the adjoint triple [Fractions ⊣ Incl ⊣ Core]

    nLab:      https://ncatlab.org/nlab/show/core
    nLab:      https://ncatlab.org/nlab/show/localization
    Wikipedia: https://en.wikipedia.org/wiki/Groupoid
    Book: Riehl, Category Theory in Context, 2nd ed., §4.1, Example 4.1.15,
          printed p. 137 (PDF pp. 157-158) — the inclusion of groupoids
          into categories has adjoints on both sides, the left one the
          category of fractions and the right one the core
    Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
          GTM 5, §IV.1 — adjunctions from universal arrows
    Paper: Brown, From groups to groupoids: a brief survey, Bulletin of the
           London Mathematical Society 19, 1987

    WHAT IS DELIVERED.  Both halves of Riehl's example, over ONE ambient
    category, as two [Adjunction] records bundled into one statement:

      [Fractions_Incl_Adjunction : Adjunction FractionsF Grpd_Incl]
      [Incl_Core_Adjunction      : Adjunction Grpd_Incl  Core]
      [riehl_4_1_15              : AdjointTriple FractionsF Grpd_Incl Core]

    The right-hand half is [Construction/Groupoid/Core.v]'s, unchanged and
    unmoved; only the left-hand half is new, and the ambient is [Cat] for
    both, so no strictification and no comparison functor stands between
    them.  [Instance/Grpd.v]'s header said the left half "remains prose",
    and [Construction/Fractions.v]'s said the triple "is NOT assembled over
    one ambient here".  Both are superseded by this file, and both have been
    corrected in place in those headers — Instance/Grpd.v's sentence now
    points here, and Construction/Fractions.v keeps its account of the gap
    as the record of what closing it cost, since its strict statements
    remain the sharper reading and are not weakened.

    HOW THE LEFT HALF IS BUILT, AND WHAT THE GAP WAS.  The route is the
    library's standard one — a universal arrow at every object, then
    [Theory/Universal/Arrow.v]'s [AdjunctionFromUniversalArrows], which
    builds a LEFT adjoint and is therefore the RIGHT direction for this
    half (it is the wrong direction for [Incl ⊣ Core], which is why
    [Construction/Groupoid/Core.v] took the hom-setoid route instead).  The
    single obstruction was the strength of the `∃!` clause:
    [universal_arrow_from_UMP] wants it at the ambient's hom-setoid, [Grpd]
    inherits [Cat]'s [Functor_Setoid], and [Fractions_UMP_groupoid] supplied
    it at [Functor_StrictEq_Setoid].  Existence transferred along
    [strict_equiv_implies_fun_equiv]; uniqueness did not, and
    [Construction/Fractions/Weak.v] reproves it against natural isomorphism.
    With [Fractions_UMP_weak] in hand this file is assembly: the universal
    arrow is [FractionsProj C] with the weak [Unique] record handed straight
    across, the sigma of [Grpd]'s homs contributing a [(L; I)] on the way in
    and a destructuring on the way out, since [Grpd]'s [shom] is [True].

    THE LEFT ADJOINT IS THE LOCALIZATION, ON THE NOSE AND ON MORPHISMS.
    [FractionsF : Cat ⟶ Grpd] is the functor
    [AdjunctionFromUniversalArrows] generates, and it is not merely
    isomorphic to the category of fractions: [FractionsF_obj] checks
    [fobj[FractionsF] C = (Fractions C; Fractions_IsGroupoid C)] at
    [eq_refl].  On morphisms the identification is up to `≈` and cannot be
    better, since the localization of a functor is itself only determined up
    to natural isomorphism: [FractionsF_fmap] identifies [fmap[FractionsF] F]
    with [FractionsMap F], the lift of [FractionsProj D ◯ F] along the
    projection.  [Fractions_unit_is_proj] reads the unit off as
    [FractionsProj C], which is what makes the adjunction the localization
    rather than some other left adjoint.

    FUNCTORIALITY OF [Fractions] IN [C] was listed as not delivered by
    [Construction/Fractions.v] and is delivered here, twice over: as
    [FractionsF]'s own functor laws, and — read back through
    [FractionsF_fmap] — as [FractionsMap_id] and [FractionsMap_comp] on the
    hand-written lift.  Naturality of the hom-set bijection in [C] and in
    [D], also listed as not delivered there, is the [Adjunction] record's
    [to_adj_nat_l] and [to_adj_nat_r].

    WHAT IS NOT DELIVERED.  The triple is not shown to make [Grpd]
    reflective and coreflective in [Cat] in the sense of
    [Construction/Reflective.v]; that file's [Reflective] is stated over an
    inclusion of its own and connecting it to [Grpd_Incl] is separate work.
    Nothing here computes [Fractions C] for any concrete [C], so the
    left adjoint is exhibited but no localization is evaluated; and the
    monad [Grpd_Incl ◯ FractionsF] and comonad [Grpd_Incl ◯ Core] the two
    adjunctions generate are not named. *)

(** ** The object map: a localization is a groupoid *)

(* [Construction/Fractions.v]'s [Fractions_IsGroupoid] is exactly the
   membership proof [Grpd] asks for, so the object map needs no work.  Note
   that this is a PAIR, per [Instance/Grpd.v]: the chosen inverse-assigning
   function is data. *)

Definition frac_grpd (C : Category) : Grpd :=
  (Fractions C; Fractions_IsGroupoid C).

(** ** The universal arrow

    [FractionsProj C : C ~{Cat}~> Grpd_Incl (frac_grpd C)] is universal from
    [C] to the inclusion.  The `∃!` is [Fractions_UMP_weak] at the target's
    own groupoid witness; the only manipulation is the sigma of [Grpd]'s
    homs, whose second component is [True]. *)

Definition Fractions_universal_arrow (C : Cat) : UniversalArrow C Grpd_Incl.
Proof.
  unshelve eapply (universal_arrow_from_UMP C Grpd_Incl (frac_grpd C)
                     (FractionsProj C)).
  intros d' f.
  unshelve eapply Build_Unique.
  - exact (unique_obj (Fractions_UMP_weak (`2 d') f); I).
  - exact (unique_property (Fractions_UMP_weak (`2 d') f)).
  - intros [L HL] HF.
    exact (uniqueness (Fractions_UMP_weak (`2 d') f) L HF).
Defined.

(** ** The left adjoint, and the adjunction *)

Definition FractionsF : Cat ⟶ Grpd :=
  LeftAdjointFunctorFromUniversalArrows Grpd_Incl Fractions_universal_arrow.

(* The generated functor's object map is the category of fractions itself,
   not a copy of it. *)

Example FractionsF_obj (C : Cat) : fobj[FractionsF] C = frac_grpd C := eq_refl.

Definition Fractions_Incl_Adjunction : Adjunction FractionsF Grpd_Incl :=
  AdjunctionFromUniversalArrows Grpd_Incl Fractions_universal_arrow.

(* The unit is the projection, up to `≈` -- the two differ only by the
   [Id] that [AdjunctionFromUniversalArrows] leaves in front of the
   universal arrow.  This is the counterpart of
   [Construction/Groupoid/Core.v]'s [core_counit_is_ForgetCore]. *)

Example Fractions_unit_is_proj (C : Cat) :
  @equiv _ (@Functor_Setoid C (Fractions C))
    (@unit Grpd Cat FractionsF Grpd_Incl Fractions_Incl_Adjunction C)
    (FractionsProj C).
Proof. apply fun_equiv_id_left. Qed.

(** ** Functoriality of the localization, read on the hand-written lift

    [FractionsMap F] is the functor a reader would write down: lift
    [FractionsProj D ◯ F] along the projection out of [C], which is legal
    because [Fractions D] is a groupoid.  It agrees with the generated
    [fmap[FractionsF]] up to `≈`, and that is the sharpest available reading
    — [Cat]'s hom-setoid identifies functors only up to natural isomorphism,
    so no [eq_refl] is on offer here, unlike on objects. *)

Definition FractionsMap {C D : Category} (F : C ⟶ D) : Fractions C ⟶ Fractions D :=
  FractionsLift (FractionsProj D ◯ F)
    (fun x y f => Fractions_IsGroupoid D _ _ (fmap[FractionsProj D ◯ F] f)).

Lemma FractionsF_fmap {C D : Cat} (F : C ~{Cat}~> D) :
  @equiv _ (@Functor_Setoid (Fractions C) (Fractions D))
    (`1 (fmap[FractionsF] F)) (FractionsMap F).
Proof.
  apply (uniqueness (ump_universal_arrows (Fractions_universal_arrow C)
                      (d:=frac_grpd D) (FractionsProj D ◯ F))
           (FractionsMap F; I)).
  exact (FractionsLift_factors_weak (Fractions_IsGroupoid D)
           (FractionsProj D ◯ F)).
Qed.

(* The two functor laws, transported onto [FractionsMap].  These are the
   "functoriality of [Fractions] in [C]" that [Construction/Fractions.v]
   listed as not delivered. *)

Corollary FractionsMap_id (C : Cat) :
  @equiv _ (@Functor_Setoid (Fractions C) (Fractions C))
    (FractionsMap (Id[C])) (Id[Fractions C]).
Proof.
  rewrite <- (FractionsF_fmap (Id[C])).
  exact (@fmap_id Cat Grpd FractionsF C).
Qed.

Corollary FractionsMap_comp {C D E : Cat} (G : D ~{Cat}~> E) (F : C ~{Cat}~> D) :
  @equiv _ (@Functor_Setoid (Fractions C) (Fractions E))
    (FractionsMap (G ◯ F)) (FractionsMap G ◯ FractionsMap F).
Proof.
  rewrite <- (FractionsF_fmap (G ◯ F)).
  rewrite <- (FractionsF_fmap G), <- (FractionsF_fmap F).
  exact (@fmap_comp Cat Grpd FractionsF C D E G F).
Qed.

(** ** The triple

    A bundling record: an adjoint triple is a pair of adjunctions sharing
    their middle functor.  It is defined here because this is its first use
    in the tree — [Instance/Top/Forgetful.v]'s
    [discrete_forget_indiscrete_triple] is a tuple of transposition
    isomorphisms rather than of [Adjunction] records, because the universe
    stratification there makes the records unformable, so it cannot use
    this shape. *)

Record AdjointTriple {A B : Category}
  (L : A ⟶ B) (M : B ⟶ A) (R : A ⟶ B) : Type := {
  triple_left  : Adjunction L M;
  triple_right : Adjunction M R
}.

(* Riehl §4.1, Example 4.1.15, in one statement and over one ambient. *)

Definition riehl_4_1_15 : AdjointTriple FractionsF Grpd_Incl Core :=
  {| triple_left  := Fractions_Incl_Adjunction;
     triple_right := Incl_Core_Adjunction |}.
