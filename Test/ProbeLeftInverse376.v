Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Skeleton.
Require Import Category.Adjunction.Compose.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Theory.Shapes.
Require Import Category.Adjunction.LeftInverse.

Generalizable All Variables.

(** * Boundary probes for Adjunction/LeftInverse.v (Mac Lane SS IV.4)

    Each [Fail] below was stripped ONE AT A TIME -- the others left in
    place -- the file recompiled, and the whole error message read, so
    that the KIND of every rejection is measured rather than guessed.
    The kinds are kept lexically apart:

      TYPING       a plain "has type ... while it is expected to have
                   type ...", with NO "cannot unify" and no universe
                   clause;
      CONVERSION   two terms of ONE type that do not convert
                   ("Unable to unify" / "cannot unify");
      FORMABILITY  "universe inconsistency: Cannot enforce ...".

    Every constant a negative names also appears OUTSIDE a [Fail], so a
    rename cannot leave a guard vacuously green.  The negatives that
    compare terms compare TERMS OF A FIXED TYPE (an [eq] between two
    explicitly typed sides, or a [Check] of a proposition), never an
    ascription of a term to a type where a coercion -- Coq's
    [reverse_coercion] in particular -- could silently repair the
    mismatch and turn the guard into a false pass. *)

(** ** Instrument check: [Fail] itself must be able to fail. *)

Fail Check probe376_no_such_constant_anywhere.

(** ** Controls: the names the negatives below depend on. *)

Check @LeftAdjointLeftInverse.
Check @lali_characterization.
Check @LeftAdjointFFInjective.
Check @ReflectiveIsoPresentation.
Check @ri_lali_implies_lali.
Check @ri_sub.
Check @lali_implies_ri.
Check @lali_image_insertion.
Check @lali_cycle.
Check @lali_obj.
Check @lali_counit.
Check @LaliImageSub.
Check @ImageTo.
Check @ImageFrom.
Check @image_to_from_obj.
Check @lali_implies_ffi.
Check @ffi_left.
Check @lali_left.
Check @PointAt.
Check @terminal_LALI.
Check @Point.
Check @Incl.
Check @Reflective.
Check @reflective_adj.
Check @reflector.
Check @reflective_counit_iso.
Check @counit.
Check @id_cast.
Check @Functor_StrictEq_Setoid.
Check @lali_along_right_strict.
Check @ffi_implies_ri.
Check @Sub.
Check @Isomorphism.
Check StrictCat.

(** ** 1. TYPING: "the counit is the identity" is not a well-typed
       equation.

    For an arbitrary adjunction the counit at [a] runs [F (G a) ~> a],
    while [id[a]] runs [a ~> a]; the two are the same hom-set only when
    [F (G a)] and [a] are the same object at LEIBNIZ equality.  This is
    exactly why [LeftAdjointLeftInverse] carries the object equation as
    DATA and compares the counit with the identity transported along it,
    and why the issue's suggested "counit ~ nat_id" reading is not
    statable.  The control is the [id_cast] form actually used. *)

Section CounitIsNotIdentity.

Context {A X : Category}.
Context {F : X ⟶ A}.
Context {G : A ⟶ X}.
Context (Adj : F ⊣ G).
Context (a : A).

Fail Check (@counit A X F G Adj a ≈ id[a]).

Context (P : LeftAdjointLeftInverse G).

Check (@counit A X (lali_left P) G (lali_adj P) a ≈ id_cast (lali_obj P a)).
Check (lali_counit P a).

End CounitIsNotIdentity.

(** ** 2. TYPING: the same failure at a reflection, which is why clause
       (c) alone does not give clause (a).

    The counit of a reflection runs [reflector R (Incl y) ~> y] and is an
    ISOMORPHISM ([reflective_counit_iso], the control), never an identity:
    a reflector need not fix the objects of the subcategory on the nose.
    Mac Lane re-chooses the reflector on Y by a case distinction on
    membership; here membership [sobj] is proof-relevant, a reflector
    fixing the subcategory on the nose forces membership-proof
    uniqueness, and the unconditional passage is refutable (the target's
    header records the out-of-tree countermodel), so
    [ri_lali_implies_lali] takes the corrected reflector as an explicit
    hypothesis. *)

Section ReflectionCounit.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).
Context (y : Sub C S).

Fail Check (@counit (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) y
              ≈ id[y]).

Check (@counit (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) y
         ≈ to (reflective_counit_iso R y)).

End ReflectionCounit.

(** ** 3. TYPING: the third leg is CONDITIONAL, and the unconditional
       form is not what is proved.

    [ri_lali_implies_lali] wants the presentation AND a
    left-adjoint-left-inverse of the insertion; applied to the
    presentation alone it is still a function, so the ascription is
    rejected.  The control supplies the second argument. *)

Section ThirdLegIsConditional.

Context {A X : Category}.
Context {G : A ⟶ X}.
Context (Pres : ReflectiveIsoPresentation G).
Context (L : LeftAdjointLeftInverse (Incl X (ri_sub Pres))).

Fail Definition unconditional_third_leg : LeftAdjointLeftInverse G :=
  ri_lali_implies_lali Pres.

Definition conditional_third_leg : LeftAdjointLeftInverse G :=
  ri_lali_implies_lali Pres L.

End ThirdLegIsConditional.

(** ** 4. CONVERSION: going round the cycle does not return the datum.

    [lali_cycle] rebuilds the adjunction through the image subcategory,
    so its left adjoint is [ImageFrom o ImageTo o F] and its transposes
    are rebuilt; the two sides are terms of ONE type that do not
    convert.  The controls are the two identifications that DO hold on
    the nose. *)

Section CycleIsNotIdentity.

Context {A X : Category}.
Context {G : A ⟶ X}.
Context (P : LeftAdjointLeftInverse G).

Fail Example cycle_is_identity : lali_cycle P = P := eq_refl.

Example ffi_left_strict : ffi_left (lali_implies_ffi P) = lali_left P :=
  eq_refl.

Example ri_sub_strict : ri_sub (lali_implies_ri P) = @LaliImageSub A X G :=
  eq_refl.

End CycleIsNotIdentity.

(** ** 5. CONVERSION: the [ImageTo o ImageFrom] object equality is not
       [eq_refl] at a variable object.

    It is built by eliminating the membership witness, so it reduces only
    once that witness is a constructor -- which is what the control at an
    object in the image of [ImageTo] exhibits. *)

Section ImageRoundTripObj.

Context {A X : Category}.
Context {G : A ⟶ X}.
Context (B : LeftAdjointFFInjective G).
Context (y : Sub X (@LaliImageSub A X G)).
Context (a : A).

Fail Example image_obj_refl : image_to_from_obj B y = eq_refl := eq_refl.

Example image_obj_refl_at_image :
  image_to_from_obj B (@ImageTo A X G a) = eq_refl := eq_refl.

End ImageRoundTripObj.

(** ** 6. FORMABILITY: a strict functor equality identifies the two
       categories' hom-and-proof universes.

    [Functor_StrictEq_Setoid] (Theory/Functor.v:606) is declared over
    [Category@{u1 u4 u4}] and [Category@{u2 u4 u4}] -- ONE hom level for
    source and target -- so every statement below that mentions a strict
    equality between a functor [A ⟶ X] and another inherits the
    identification.  [LeftAdjointLeftInverse] is rejected at the same
    levels, but that rejection does NOT discriminate: its field
    [lali_left : X ⟶ A] is a functor in the REVERSE direction, and the
    functor type alone in that direction is already rejected here --
    [Au ⟶ Xu] is accepted while [Xu ⟶ Au] is not, since [Functor] bounds
    the source hom universe by the target's and the two directions
    together identify them -- so the record's identification is forced
    before its [Adjunction] field (Theory/Adjunction.v:133, whose own
    block carries [h1 = p1], [h1 = h2], [h1 = p2]) is consulted.  Only
    [Functor_StrictEq_Setoid] is probed in isolation below. *)

Section UniverseProbe.

Universes ao ah xo xh.
Constraint ah < xh.

Context (Au : Category@{ao ah ah}).
Context (Xu : Category@{xo xh xh}).
Context (Gu : Au ⟶ Xu).

(* control: the functor type, and a functor, at levels declared apart *)
Check (Au ⟶ Xu).
Check Gu.
Check (InjectiveOnObjects Gu).

Fail Check (Xu ⟶ Au).
Fail Check (@Functor_StrictEq_Setoid Au Xu).
Fail Check (LeftAdjointLeftInverse Gu).
Fail Check (@lali_along_right_strict Au Xu Gu Gu).
Fail Check (@ffi_implies_ri Au Xu Gu).

End UniverseProbe.

(** ** 7. FORMABILITY: clause (c) identifies the two categories' OBJECT
       universes, and clause (a) does not.

    [ri_iso] compares [A] with [Sub X ri_sub] in [StrictCat], whose
    objects are [Category] at ONE universe instance, so the two must live
    at the same levels -- which is why the packaged
    [lali_characterization] displays [A X : Category@{u6 u13 u13}] where
    [LeftAdjointLeftInverse] alone leaves both object universes free.  The
    controls below are exactly that contrast: at object levels declared
    apart, the functor type and clause (a) are accepted while the
    [StrictCat] isomorphism and (b) => (c) are rejected. *)

Section StrictCatObjectProbe.

Universes bo bh co.
Constraint bo < co.

Context (Bu : Category@{bo bh bh}).
Context (Cu2 : Category@{co bh bh}).
Context (Gu2 : Bu ⟶ Cu2).

(* controls: accepted at object levels declared apart *)
Check (Bu ⟶ Cu2).
Check (LeftAdjointLeftInverse Gu2).
Check (@LeftAdjointFFInjective Bu Cu2 Gu2).

Fail Check (@Isomorphism StrictCat Bu Cu2).
Fail Check (@ffi_implies_ri Bu Cu2 Gu2).

End StrictCatObjectProbe.

(** ** 8. FORMABILITY: [Theory/Shapes.v]'s [Point] pins the terminal
       category's hom and proof universes at [Set].

    This is the measured reason the six-line [PointAt] is rebuilt in the
    target instead of consuming [Point]: over a category whose homs are
    declared strictly above [Set], [Point] is not formable while [PointAt]
    is.  The rejection is the donor's minimization, not a restriction on
    the terminal category itself ([_1@{o h p}] has all three levels free);
    it is NOT claimed unavoidable. *)

Section PointProbe.

Universes po ph.
Constraint Set < ph.

Context (Cu : Category@{po ph ph}).
Context (c : Cu).

Check (_1@{po ph ph}).
Check (PointAt (C:=Cu) c : _1@{po ph ph} ⟶ Cu).
Check (@terminal_LALI).

Fail Check (Point (C:=Cu) c : _1@{po ph ph} ⟶ Cu).

End PointProbe.

(** ** Non-vacuity of the third leg's hypothesis.

    [lali_image_insertion] inhabits it for every presentation arising
    from a left-adjoint-left-inverse -- Mac Lane's own sentence that the
    insertion has a left-adjoint-left-inverse -- so the conditional leg
    is not an empty statement. *)

Check @lali_ri_insertion.
Check @two_LALI.
Check @two_lali_moves_TwoX.
