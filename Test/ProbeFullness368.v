Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.Universal.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Adjunction.Fullness.

Generalizable All Variables.

(** * Boundary probe for Adjunction/Fullness.v (issue #368). *)

(* Why this file exists.  Every rejection recorded in the target's header
   is pinned here as a [Fail] command, from OUTSIDE the target: a [Fail]
   written inside the file it guards is renamed in lockstep with the
   constant it guards, so it cannot detect a rename.  The target's own
   [Require] list is mirrored above, plus what the instance section needs.

   Eleven negatives of THREE kinds, kept lexically apart, plus a scope-free
   instrument check (twelve [Fail] commands in all):

     - FORMABILITY (4): universe rejections localising the two
       identifications the target's headlines carry.  Error text ends in
       `universe inconsistency: Cannot enforce ...`.
     - TYPING (2): the whiskered transformations cannot be ascribed at the
       type the target's isomorphism is stated at.  Error text is a plain
       `has type ... while it is expected to have type ...` with no
       `cannot unify` and no universe clause.
     - CONVERSION (5): the inverse the target produces is not the donor's
       inverse on the nose, and the three record-level whisker-padding
       facts of the target's correction 4.  Error text ends in
       `cannot unify`.

   Each negative was stripped ONE AT A TIME, with the others left as
   [Fail], and compiled alone, and the WHOLE error read to confirm it
   fires at its own command.  This repo's [coqc] prints nothing for a
   [Fail] that succeeds, which is why stripping is the only check.

   Every constant a negative names appears in a succeeding positive
   control below it. *)

(* ** Instrument check: a [Fail] that must fire for a reason having
   nothing to do with universes, typing or conversion. *)

Fail Check probe368_no_such_constant_anywhere.

(* ** FORMABILITY

   The target's headlines are over [C : Category@{u u0 u0}] and
   [D : Category@{u1 u2 u2}] -- hom identified with proof in both, by
   REUSE OF THE LEVEL VARIABLE IN THE BINDER, the constraint blocks
   carrying no such equation -- and their blocks additionally carry the
   equation [u0 = u2], identifying the two hom-and-proof levels.  Neither
   identification is introduced by the target; both are inherited, and
   neither is claimed unavoidable.

   Negatives 1 and 2 localise hom = proof: [Section] and [Monic] are each
   rejected ALONE at levels declared strictly apart, while a hom and an
   identity at those very levels are accepted.  [Retraction] is rejected
   too and is shown as a third rejection in the same section.  Note that
   [Functor] is NOT a donor for this equation -- see the positive control
   in section [P_hom_proof_control] -- so "the functor vocabulary" would
   be the wrong attribution. *)

Section P_hom_proof.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (x y : Cu).
Context (f : x ~{Cu}~> y).

(* Controls: the hom-set and the identity ARE formable at these levels. *)
Check (@id Cu x).
Check f.

(* Negative 1 (FORMABILITY). *)
Fail Check (@Section Cu x y f).

(* Negative 2 (FORMABILITY). *)
Fail Check (@Monic Cu x y f).

(* Negative 3 (FORMABILITY): same cause, third donor. *)
Fail Check (@Retraction Cu x y f).

End P_hom_proof.

Section P_hom_proof_control.

Universes co ch cp do dh dp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (Du : Category@{do dh dp}).

(* [Functor] does NOT force hom = proof: this is accepted at exactly the
   levels where [Section], [Monic] and [Retraction] are rejected. *)
Check (Du ⟶ Cu).

End P_hom_proof_control.

Section P_hom_hom.

Universes co ch cp do dh dp.
Constraint dh < ch.

Context (Cu : Category@{co ch ch}).
Context (Du : Category@{do dh dh}).

(* Control: one direction is formable. *)
Check (Du ⟶ Cu).

(* Negative 4 (FORMABILITY): the OTHER direction is not, so the presence
   of functors both ways -- which every statement about an adjunction has
   -- is already sufficient for [u0 = u2].  No [Compose], no [Adjunction]
   and no [Full] is needed to force it. *)
Fail Check (Cu ⟶ Du).

End P_hom_hom.

(* ** TYPING

   [Transform] is a class applied to two FUNCTOR RECORDS.  `U ◯ (F ◯ U)`
   and `(U ◯ F) ◯ U` agree on [fobj] and on [fmap] but differ in their
   three law fields, and `U ◯ Id` is not `U`.  So the whiskered forms live
   at types the target's isomorphism cannot be stated at, and the
   components -- not the records -- are what the target identifies. *)

Section P_whisker.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

Definition PT : F ∹ U := @Adjunction_to_Transform C D F U A.

(* Controls: both whiskered transformations exist, at their own types,
   and both of the target's hand-built transformations exist at the type
   the isomorphism needs. *)
Check (U ⊳ (@counit _ _ _ _ PT)).
Check ((@unit _ _ _ _ PT) ⊲ U).
Check (@whiskered_counit C D F U A : U ◯ F ◯ U ⟹ U).
Check (@whiskered_unit C D F U A : U ⟹ U ◯ F ◯ U).

(* Negative 5 (TYPING). *)
Fail Check ((U ⊳ (@counit _ _ _ _ PT)) : U ◯ F ◯ U ⟹ U).

(* Negative 6 (TYPING). *)
Fail Check (((@unit _ _ _ _ PT) ⊲ U) : U ⟹ U ◯ F ◯ U).

(* The identification that DOES hold, componentwise and at [eq_refl],
   is the target's [whiskered_counit_is_whisker_left] and
   [whiskered_unit_is_whisker_right]; both are cited here so a rename of
   either breaks this file. *)
Check (@whiskered_counit_is_whisker_left C D F U A).
Check (@whiskered_unit_is_whisker_right C D F U A).

End P_whisker.

(* ** CONVERSION

   The target derives the componentwise invertibility of [fmap[U] ε] at
   the two in-tree adjunctions the issue names, and the inverse it
   produces is the unit component on the nose.  Neither donor's own
   inverse is that term. *)

Section P_reflective.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).
Context (x : Sub C S).

(* Controls: both isomorphisms exist, and the target's inverse is the
   unit component at [eq_refl] (this is the target's own [Example],
   restated here so a rename breaks the probe). *)
Check (reflective_counit_iso R x).
Check (reflective_fmap_counit_IsIsomorphism R x).
Check (@reflective_fmap_counit_inverse C S R x).
Check (fmap[Incl C S] (from (reflective_counit_iso R x))).

(* Negative 7 (CONVERSION).  [reflective_counit_iso] is closed with
   [Qed], so neither leg of the isomorphism it produces reduces: the two
   terms are of the same type and are NOT convertible.  The cause is
   donor opacity, not a difference of value -- nothing is claimed about
   what the donor's [from] would reduce to were it transparent, and the
   donor is not modified. *)
Fail Definition probe_reflective_inverse_strict :
  two_sided_inverse
    (IsIsomorphism := reflective_fmap_counit_IsIsomorphism R x)
  = fmap[Incl C S] (from (reflective_counit_iso R x)) := eq_refl.

End P_reflective.

Section P_equiv.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context (E : @EquivalenceOfCategories C D F).
Context (d : D).

(* Controls. *)
Check (equiv_adjunction E).
Check (equiv_adjunction_counit_iso E d).
Check (equiv_fmap_counit_IsIsomorphism E d).
Check (@equiv_fmap_counit_inverse C D F E d).
Check (@equiv_fmap_counit_inverse_agrees C D F E d).

(* Negative 8 (CONVERSION).  Here the `≈` form IS available and is
   delivered by the target as [equiv_fmap_counit_inverse_agrees]
   (control above); it is the strict form that fails. *)
Fail Definition probe_equiv_inverse_strict :
  two_sided_inverse (IsIsomorphism := equiv_fmap_counit_IsIsomorphism E d)
  = fmap[@quasi_inverse C D F E]
      (two_sided_inverse
         (IsIsomorphism := equiv_adjunction_counit_iso E d)) := eq_refl.

End P_equiv.

(* ** CONVERSION, the whisker padding itself

   Correction 4 of the target rests on three record-level facts beneath
   the two TYPING negatives above: the two parenthesizations of the
   triple composite are not convertible, and neither identity padding is
   convertible with the bare functor.  Each is pinned here as a CONVERSION
   negative; the controls show that [fobj] and [fmap] DO agree at
   [eq_refl] in every case, so what differs is confined to the three law
   fields.  Every statement below is an equation between two inhabitants
   of ONE type ([C ⟶ D]), which is what separates this kind from the
   TYPING pair, where the ascription itself is rejected. *)

Section P_padding.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

(* Controls: the data fields agree on the nose. *)
Example probe_padding_assoc_fobj :
  fobj[U ◯ (F ◯ U)] = fobj[(U ◯ F) ◯ U] := eq_refl.
Example probe_padding_assoc_fmap :
  @fmap _ _ (U ◯ (F ◯ U)) = @fmap _ _ ((U ◯ F) ◯ U) := eq_refl.
Example probe_padding_unit_r_fobj : fobj[U ◯ Id[C]] = fobj[U] := eq_refl.
Example probe_padding_unit_r_fmap :
  @fmap _ _ (U ◯ Id[C]) = @fmap _ _ U := eq_refl.
Example probe_padding_unit_l_fobj : fobj[Id[D] ◯ U] = fobj[U] := eq_refl.
Example probe_padding_unit_l_fmap :
  @fmap _ _ (Id[D] ◯ U) = @fmap _ _ U := eq_refl.

(* Negative 9 (CONVERSION): the two parenthesizations. *)
Fail Definition probe_padding_assoc : U ◯ (F ◯ U) = (U ◯ F) ◯ U := eq_refl.

(* Negative 10 (CONVERSION): the right identity padding. *)
Fail Definition probe_padding_unit_r : U ◯ Id[C] = U := eq_refl.

(* Negative 11 (CONVERSION): the left identity padding. *)
Fail Definition probe_padding_unit_l : Id[D] ◯ U = U := eq_refl.

End P_padding.

(* ** Positive controls for the remaining headline names

   So that a rename of any name a negative or the target's header depends
   on breaks this file rather than turning a guard vacuously green. *)

Section P_names.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

Check (@counit_split_mono_of_full_right C D F U A).
Check (@unit_split_epi_of_full_left C D F U A).
Check (@counit_inv_of_full_right C D F U A).
Check (@unit_inv_of_full_left C D F U A).
Check (@unit_fmap_counit_of_full_right C D F U A).
Check (@unit_fmap_counit_of_full_left C D F U A).
Check (@unit_fmap_counit C D F U A).
Check (@fmap_counit_IsIsomorphism_of_full C D F U A).
Check (@fmap_unit_counit_of_full_left C D F U A).
Check (@fmap_unit_counit_of_full_right C D F U A).
Check (@fmap_unit_counit C D F U A).
Check (@counit_at_F_IsIsomorphism_of_full C D F U A).
Check (@whiskered_counit_iso_of_full C D F U A).
Check (@whiskered_counit_iso_of_full_left C D F U A).
Check (@whiskered_counit_iso_of_full_right C D F U A).
Check (@whiskered_unit_F C D F U A).
Check (@whiskered_counit_F C D F U A).
Check (@whiskered_unit_iso_of_full C D F U A).
Check (@whiskered_unit_iso_of_full_left C D F U A).
Check (@whiskered_unit_iso_of_full_right C D F U A).
Check (@unit_at_UF_of_full_right C D F U A).
Check (@unit_epic_of_full_monic C D F U A).
Check (@unit_epic_of_full_left C D F U A).
Check (@unit_iso_of_full_monic C D F U A).
Check (@unit_at_U_IsIsomorphism_of_full C D F U A).
Check (@split_inverses_agree C).

End P_names.

Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.One.
Require Import Category.Instance.Sets.Pointed.

Check (@Full_Erase_of_ZeroObject).
Check (@zero_erase_adjunction).
Check (@zero_erase_fmap_counit_IsIsomorphism).
Check Erase_PointedSets_not_Faithful.
Check pointed_counit_not_IsIsomorphism.
