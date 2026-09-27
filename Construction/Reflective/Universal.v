Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Coreflective.

Generalizable All Variables.

(** * Reflective subcategories from universal arrows *)

(* nLab:  https://ncatlab.org/nlab/show/reflective+subcategory
   nLab:  https://ncatlab.org/nlab/show/universal+morphism
   Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          GTM 5, §IV.3, printed p. 91 (PDF p. 100), and the examples of
          printed p. 92 (PDF p. 101) that issue #370 collects
   Book:  Riehl, "Category Theory in Context", Dover 2016, §4.6,
          Definition 4.6.12, printed p. 169 (PDF p. 189)

   Mac Lane defines the notion on p. 91 and, in the same paragraph,
   reads it through universal arrows.  Quoted from the page image:

     "A subcategory A of B is called reflective in B when the inclusion
      functor K: A → B has a left adjoint F: B → A. ... A reflection may
      be described in terms of universal arrows: A ⊂ B is reflective if
      and only if to each b ∈ B there is an object Rb of the subcategory
      A and an arrow η_b: b → Rb such that every arrow g: b → a ∈ A has
      the form g = f ∘ η_b for a unique arrow f: Rb → a of A.  As usual,
      R is then (the object function of) a functor B → B (with values in
      A)."

   Riehl's Definition 4.6.12 is the same notion, a full subcategory
   whose inclusion has a left adjoint, which she calls the reflector or
   localization; her Example 4.6.13 is the roster of examples whose
   clauses (ii) and (iv) issue #370 also collects.

   Every concrete reflection is found that way in practice: one
   constructs the completion, the abelianization, the extension of
   scalars, one object at a time, proves its universal property, and
   only then speaks of a functor.  The general theorem that turns the
   pointwise data into an adjunction is already in the tree, as
   Theory/Universal/Arrow.v's [LeftAdjointFunctorFromUniversalArrows]
   and [AdjunctionFromUniversalArrows]; what is missing is the step from
   there into Construction/Reflective.v's record, and that step is this
   file, together with its dual into the coreflective record.  It is a
   satellite rather than part of Construction/Reflective.v because it
   needs Theory/Universal/Arrow.v, which that file does not require: the
   transitive closure of [coqdep -R . Category] over the [_CoqProject]
   files, the file itself excluded, counts 18 modules under
   Construction/Reflective.v and 31 under this file.

   WHAT IS DELIVERED.

   - [Reflective_of_UniversalArrows]: Mac Lane's "if" direction.  A full
     subcategory with a universal arrow to its inclusion at every object
     is reflective; the reflector and the adjunction are the two
     constructions of Theory/Universal/Arrow.v, unchanged.
   - [Reflective_of_UniversalArrows_obj]: the reflector sends x to the
     universal object [arrow_obj], at [eq_refl].
   - [Reflective_of_UniversalArrows_unit]: the unit at x is the
     universal arrow, up to [≈].
   - [Coreflective_of_CouniversalArrows]: the dual, Mac Lane's
     "dually" of the same page.  A full subcategory with a couniversal
     arrow from its inclusion at every object is coreflective; Theory/
     Universal/Arrow/Dual.v's [RightAdjointFunctorFromCouniversalArrows]
     and [AdjunctionFromCouniversalArrows] are fed, unchanged, to
     Construction/Reflective/Coreflective.v's covariant bridge
     [Coreflective_of_adjunction], which builds the op-typed record.
   - [Coreflective_of_CouniversalArrows_obj]: the coreflector, read back
     covariantly, sends x to the couniversal object [coarrow_obj], at
     [eq_refl]; [Coreflective_of_CouniversalArrows_counit]: the
     covariant counit at x is the couniversal arrow, up to [≈].

   STRENGTHS, MEASURED STRICT FIRST.  The object readback is [eq_refl].
   The unit is not: the adjunction's unit at x is its transpose of the
   identity, [fmap[Incl C S] id ∘ arrow], and over an abstract category
   the composite with an identity does not reduce.  An [Example] stating
   the unit [=] the arrow by [eq_refl] is refused with "cannot unify
   "unit" and "arrow"", pinned in Test/ProbeReflective370.v rather than
   here, where a negative probe line would add to [make todo].  Over a
   concrete category the composite does reduce POINTWISE, and
   Instance/Met/Uniform.v's [completionU_unit_pointwise] records that
   case at [eq_refl].  The dual is the same: the coreflector's object is
   [eq_refl], and the counit arrives as [coarrow ∘ fmap[Incl C S] id],
   the shape Dual.v's [counit_couniversal] closes up to [≈].

   UNIVERSES.  Read by [About] under [Set Printing Universes], the three
   reflective constants carry twelve universes each, the first two the
   binder's:

     Reflective_of_UniversalArrows@{o h u u0 u1 u2 u3 u4 u5 u6 u7 u8} :
       ∀ {C : Category@{o h h}} {S : Subcategory@{o h u8 h} C}, ...
         → Reflective@{u u0 u1 u2 o u8 h} S
       (* ... |= h < u0, and non-strict bounds only *)

   The one strict bound, [h < u0], is [Reflective]'s own: [About
   Reflective] prints [u5 < u0] for its hom level [u5] and its second
   universe [u0], and the constant instantiates that record at
   [@{u u0 u1 u2 o u8 h}].  The three coreflective constants carry
   fifteen, fifteen and sixteen ([Coreflective_of_CouniversalArrows],
   its [_obj] and its [_counit]), with the same binder:

     Coreflective_of_CouniversalArrows@{o h u u0 … u11} :
       ∀ {C : Category@{o h h}} {S : Subcategory@{o h u11 h} C}, ...
         → Coreflective@{u u0 u1 u2 u3 u11 o h} S
       (* ... |= h < u1, and non-strict bounds only *)

   and their one strict bound is [Coreflective]'s own: [About
   Coreflective] prints [u6 < u1] for its hom level [u6].  This file
   adds no bound, and no [Set] appears.

   NOT DELIVERED.

   - Mac Lane's "only if".  It holds, and it is one line over
     Adjunction/Representability.v's [adj_unit_universal]:
     [fun x => adj_unit_universal (reflective_adj R) x] is a universal
     arrow at every x, and feeding it back to
     [Reflective_of_UniversalArrows] returns R's reflector on objects at
     [eq_refl] (both measured in a scratch file, closed under the global
     context).  It is not stated here because that import adds 12
     modules to this file's closure (by the same [coqdep] count), among
     them the Yoneda development.
   - The "only if" of the coreflective dual: not stated either.
   - A couniversal readback of the arrow part of the coreflector: like
     the reflector's, it is [unique_obj] of Theory/Universal/Arrow.v's
     [Qed]-closed [ump_universal_arrows], read in the opposite
     categories. *)

(* Mac Lane §IV.3, printed p. 91: reflective when every object has a
   universal arrow to the inclusion. *)
Definition Reflective_of_UniversalArrows@{o h +} {C : Category@{o h h}}
  {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (UA : ∀ x : C, UniversalArrow x (Incl C S)) : Reflective S :=
  @Build_Reflective C S full
    (LeftAdjointFunctorFromUniversalArrows (Incl C S) UA)
    (AdjunctionFromUniversalArrows (Incl C S) UA).

(* The reflection of x is the universal object, on the nose. *)
Example Reflective_of_UniversalArrows_obj@{o h +} {C : Category@{o h h}}
  {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (UA : ∀ x : C, UniversalArrow x (Incl C S)) (x : C) :
  fobj[reflector (Reflective_of_UniversalArrows full UA)] x
    = @arrow_obj C (Sub C S) x (Incl C S) (UA x) := eq_refl.

(* The unit is the universal arrow, up to [≈]: it arrives as the
   transpose of the identity, [fmap[Incl C S] id ∘ arrow]. *)
Lemma Reflective_of_UniversalArrows_unit@{o h +} {C : Category@{o h h}}
  {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (UA : ∀ x : C, UniversalArrow x (Incl C S)) (x : C) :
  @unit _ _ _ _ (reflective_adj (Reflective_of_UniversalArrows full UA)) x
    ≈ @arrow C (Sub C S) x (Incl C S) (UA x).
Proof. simpl. apply id_left. Qed.

(** ** The dual: coreflective subcategories from couniversal arrows *)

(* Mac Lane §IV.3, printed p. 91, dually: coreflective when every object
   has a couniversal arrow from the inclusion.  Theory/Universal/Arrow/
   Dual.v assembles the right adjoint and the adjunction, and
   Construction/Reflective/Coreflective.v's covariant bridge packages
   them as the op-typed record. *)
Definition Coreflective_of_CouniversalArrows@{o h +} {C : Category@{o h h}}
  {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (CA : ∀ x : C, CouniversalArrow x (Incl C S)) : Coreflective S :=
  Coreflective_of_adjunction full
    (RightAdjointFunctorFromCouniversalArrows (Incl C S) CA)
    (AdjunctionFromCouniversalArrows (Incl C S) CA).

(* The coreflection of x is the couniversal object, on the nose. *)
Example Coreflective_of_CouniversalArrows_obj@{o h +}
  {C : Category@{o h h}} {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (CA : ∀ x : C, CouniversalArrow x (Incl C S)) (x : C) :
  fobj[coreflector (Coreflective_of_CouniversalArrows full CA)] x
    = @coarrow_obj C (Sub C S) x (Incl C S) (CA x) := eq_refl.

(* The covariant counit is the couniversal arrow, up to [≈]: it arrives
   as [coarrow ∘ fmap[Incl C S] id], Dual.v's [counit_couniversal]. *)
Lemma Coreflective_of_CouniversalArrows_counit@{o h +}
  {C : Category@{o h h}} {S : Subcategory C}
  (full : Construction.Subcategory.Full C S)
  (CA : ∀ x : C, CouniversalArrow x (Incl C S)) (x : C) :
  @counit _ _ _ _
    (coreflective_adj (Coreflective_of_CouniversalArrows full CA)) x
    ≈ @coarrow C (Sub C S) x (Incl C S) (CA x).
Proof. exact (counit_couniversal (Incl C S) CA x). Qed.
