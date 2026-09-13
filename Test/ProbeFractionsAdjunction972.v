Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Groupoid.
Require Import Category.Construction.Groupoid.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Fractions.
Require Import Category.Construction.Fractions.Weak.
Require Import Category.Construction.Fractions.Adjunction.
Require Import Category.Construction.Groupoid.Core.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Grpd.

Generalizable All Variables.

(** * Probe for Construction/Fractions/Weak.v and
      Construction/Fractions/Adjunction.v

    Riehl, Category Theory in Context, 2nd ed., §4.1, Example 4.1.15,
    printed p. 137.  Issue #972.

    The import list above is the UNION of the two target files' own import
    lists, unabbreviated.  A short prefix is what makes a probe pass
    vacuously, so nothing is trimmed even where a require is redundant.

    This file guards the strength claims of those two files.  Every
    statement asserted to be refuted below has been STRIPPED of its refutation keyword
    in a copy of this WHOLE file, compiled alone, and its complete error
    read; a refutation that holds prints nothing under this repo's coqc, so a
    whole-file rc=0 would establish only THAT each command does not
    typecheck and never WHY.  Each negative is classified by the error
    TEXT:

      TYPING      - "The term T has type X while it is expected to have
                    type Y", with NO trailing "cannot unify" clause and no
                    universe clause.
      CONVERSION  - the same, with a trailing "(cannot unify A and B)".

    ** TALLY

    Seven positive controls and eleven negatives: NINE typing (N1-N7, N10,
    N11) and TWO conversion (N8, N9).  No negative here is a universe
    inconsistency, and that was checked rather than assumed -- see the note
    on N1 and N2 below.

    ** THE PRINTED FORM OF N1 AND N2 HIDES WHAT SEPARATES THEM

    N1 and N2 are the two cross-transfers between the strict universal
    property ([Construction/Fractions.v]'s [Fractions_UMP_groupoid]) and the
    weak one ([Construction/Fractions/Weak.v]'s [Fractions_UMP_weak]).  Both
    are [Unique] records, and the `∃!` notation hides the [Setoid] instance,
    so with default printing the two types in each message print
    identically and Coq falls back to disambiguating them by UNIVERSE
    INSTANCE.  That display invites the reading that these two negatives
    measure a universe clash rather than a strength difference, and they do
    not: re-run under [Set Printing All] each message reads

      "@Unique (@Functor (Fractions C) D) (@Functor_Setoid (Fractions C) D) …"
      versus
      "@Unique (@Functor (Fractions C) D)
         (@Functor_StrictEq_Setoid (Fractions C) D) …"

    with the two setoid arguments differing and no universe clause
    anywhere.  Both are therefore TYPING, and the thing they separate is
    the hom-setoid.

    ** WHAT THE NEGATIVES PIN

    N1  the weak universal property is NOT the strict one -- it cannot be
        read at [Functor_StrictEq_Setoid].  This is the whole point of the
        weak file: the statement it proves is genuinely weaker, and nothing
        in the tree should be able to launder it back.
    N2  the strict universal property is NOT the weak one either.  Its
        EXISTENCE half transfers along [strict_equiv_implies_fun_equiv],
        but the packaged [Unique] record does not, because its uniqueness
        clause quantifies over the wrong setoid.  This is the measured
        obstruction issue #972 was left open on.
    N3  [Fractions_proj_epic_weak]'s conclusion is at [Functor_Setoid] and
        cannot be read as [Construction/Fractions.v]'s [Fractions_proj_epic].
    N4  the original refusal, reproduced: feeding [Fractions_UMP_groupoid]
        straight to [universal_arrow_from_UMP].  The head of this message is
        quoted in [Construction/Fractions.v]'s header (there with the older
        spelling [frac_obj C] for what is now [frac_grpd C]).
    N5  [Incl_Core_Adjunction] is [Grpd_Incl ⊣ Core] and not its converse.
    N6  [Fractions_Incl_Adjunction] is [FractionsF ⊣ Grpd_Incl] and not its
        converse.
    N7  the triple does not survive exchanging its two ends: the left
        adjoint of the inclusion is the localization and the right adjoint
        is the core, not the other way round.
    N8  [FractionsF]'s action on MORPHISMS agrees with the hand-written
        [FractionsMap] only up to `≈`.  Unlike the object agreement (P3),
        this one is not [eq_refl], and the header of the adjunction file
        says so.
    N9  the unit of [Fractions_Incl_Adjunction] is [FractionsProj] only up
        to `≈` (P7 is the positive form).  In this message Coq prints the
        adjunction's [unit] projection bare, as "unit", which reads like
        the type of the same name; the environment line above it
        disambiguates.
    N10 the strict uniqueness lemma [FractionsLift_unique] does NOT accept a
        [Functor_Setoid] hypothesis.  This is the guard against the one
        shortcut the issue forbids -- restating the strict result under a
        weaker-sounding name by strengthening its hypothesis back to object
        equality.
    N11 [strict_equiv_implies_fun_equiv] runs strict-to-weak only; the
        reverse reading of it is refused.  This is why uniqueness had to be
        reproved rather than transported. *)

(** ** Positive controls *)

(* The objects of the localization ARE the objects of the source, and the
   projection is the identity on them -- the two conversions the weak
   uniqueness argument rests on. *)

Example P1 (C : Category) : @obj (Fractions C) = @obj C := eq_refl.

Example P2 (C : Category) (x : C) : fobj[FractionsProj C] x = x := eq_refl.

(* The generated left adjoint's object map is the category of fractions on
   the nose. *)

Example P3 (C : Cat) : fobj[FractionsF] C = frac_grpd C := eq_refl.

(* The two adjunctions in the directions that ARE proved, and the triple. *)

Example P4 : Adjunction FractionsF Grpd_Incl := Fractions_Incl_Adjunction.

Example P5 : Adjunction Grpd_Incl Core := Incl_Core_Adjunction.

Example P6 : AdjointTriple FractionsF Grpd_Incl Core := riehl_4_1_15.

(* The unit is the projection up to `≈`; N9 is the same statement at
   [eq_refl] and is refused. *)

Example P7 (C : Cat) :
  @equiv _ (@Functor_Setoid C (Fractions C))
    (@unit Grpd Cat FractionsF Grpd_Incl Fractions_Incl_Adjunction C)
    (FractionsProj C)
  := Fractions_unit_is_proj C.

(** ** Negatives, at an abstract source, target and functor *)

Section Negatives.

Context {C D : Category}.
Variable Dg : IsGroupoid D.
Variable F : C ⟶ D.

(* Both universal properties exist at their own strength; only the transfers
   are refused. *)

Example P8 :
  @Unique _ (@Functor_Setoid (Fractions C) D)
    (fun L => @equiv _ (@Functor_Setoid C D) F (L ◯ FractionsProj C))
  := Fractions_UMP_weak Dg F.

Example P9 :
  @Unique _ (@Functor_StrictEq_Setoid (Fractions C) D)
    (fun L => @equiv _ (@Functor_StrictEq_Setoid C D)
                F (L ◯ FractionsProj C))
  := Fractions_UMP_groupoid Dg F.

(* N1 *)
Fail Definition N1 :
  @Unique _ (@Functor_StrictEq_Setoid (Fractions C) D)
    (fun L => @equiv _ (@Functor_StrictEq_Setoid C D)
                F (L ◯ FractionsProj C)) :=
  Fractions_UMP_weak Dg F.

(* N2 *)
Fail Definition N2 :
  @Unique _ (@Functor_Setoid (Fractions C) D)
    (fun L => @equiv _ (@Functor_Setoid C D) F (L ◯ FractionsProj C)) :=
  Fractions_UMP_groupoid Dg F.

(* N3 *)
Fail Definition N3 (L L' : Fractions C ⟶ D)
  (E : @equiv _ (@Functor_Setoid C D)
         (L ◯ FractionsProj C) (L' ◯ FractionsProj C)) :
  @equiv _ (@Functor_StrictEq_Setoid (Fractions C) D) L L' :=
  Fractions_proj_epic_weak L L' E.

(* N10 *)
Fail Definition N10 (L : Fractions C ⟶ D)
  (E : @equiv _ (@Functor_Setoid C D) F (L ◯ FractionsProj C)) :
  @equiv _ (@Functor_StrictEq_Setoid (Fractions C) D)
    (FractionsLift F (fun x y f => Dg (F x) (F y) (fmap[F] f))) L :=
  FractionsLift_unique F (fun x y f => Dg (F x) (F y) (fmap[F] f)) L E.

(* N11 *)
Fail Definition N11 (G H : C ⟶ D)
  (E : @equiv _ (@Functor_Setoid C D) G H) :
  @equiv _ (@Functor_StrictEq_Setoid C D) G H :=
  strict_equiv_implies_fun_equiv G H E.

End Negatives.

(** ** Negatives about the adjunction itself *)

(* N4 *)
Fail Definition N4 (C : Cat) : UniversalArrow C Grpd_Incl :=
  universal_arrow_from_UMP C Grpd_Incl (frac_grpd C) (FractionsProj C)
    (fun d' f => Fractions_UMP_groupoid (`2 d') f).

(* N5 *)
Fail Definition N5 : Adjunction Core Grpd_Incl := Incl_Core_Adjunction.

(* N6 *)
Fail Definition N6 : Adjunction Grpd_Incl FractionsF := Fractions_Incl_Adjunction.

(* N7 *)
Fail Definition N7 : AdjointTriple Core Grpd_Incl FractionsF :=
  {| triple_left  := Fractions_Incl_Adjunction;
     triple_right := Incl_Core_Adjunction |}.

(* N8 *)
Fail Example N8 (C D : Cat) (F : C ~{Cat}~> D) :
  `1 (fmap[FractionsF] F) = FractionsMap F := eq_refl.

(* N9 *)
Fail Example N9 (C : Cat) :
  @unit Grpd Cat FractionsF Grpd_Incl Fractions_Incl_Adjunction C
    = FractionsProj C := eq_refl.
