Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Construction.Quotient.
Require Import Category.Adjunction.LeftInverse.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Theory.Equivalence.Strict.

(** * Boundary probe for Theory/Equivalence/Strict.v (Mac Lane IV.4.3)

    Every rejection the target's header records is pinned here, from
    OUTSIDE the target, so that a rename breaks the probe loudly instead
    of turning a guard vacuously green.  The import list is the target's
    own, plus the target.

    Twelve negatives in THREE kinds, told apart by the error TEXT rather
    than by label:

      TYPING       (3) -- a plain "has type ... while it is expected to
                          have type ...", with no "cannot unify" clause;
                          negatives 1, 2 and 5.
      CONVERSION   (5) -- "cannot unify" between two terms of ONE type,
                          or a tactic script that does not close;
                          negatives 3, 4, 6, 7 and 8.
      FORMABILITY  (4) -- "universe inconsistency: Cannot enforce ...";
                          negatives 9 to 12.

    Negative 5 was expected to be a conversion rejection and is NOT: the
    two adjunctions have different TYPES, because their left adjoints are
    two non-convertible functors, so the error carries no "cannot unify"
    clause at all.  It is counted as typing.

    plus a scope-free instrument check.  Each was stripped ONE AT A TIME,
    the others left in place, the file compiled alone, and the whole error
    message read.  Every constant a negative names also appears in a
    command outside any guarded position. *)

Generalizable All Variables.

(** ** Instrument check *)

(* If a guarded command could succeed for want of a name, this one would
   too.  It must be rejected. *)
Fail Check probe377_no_such_constant_anywhere.

(** ** Controls: every constant the negatives name, named outside a guard *)

Check @unit.
Check @counit.
Check @id_cast.
Check @id_cast_iso.
Check @iso_id.
Check @eso_iso.
Check @LeftAdjointRightInverse.
Check @lari_left.
Check @lari_adj.
Check @lari_obj.
Check @lari_unit.
Check @surjective_ESO.
Check @SurjectiveOnObjects.
Check @SurjectiveOnObjects_Id.
Check @ff_surjective_left.
Check @ff_surj_eq.
Check @ff_surj_adj.
Check @ff_surj_eso.
Check @ff_surj_eso_adjoint_equivalence.
Check @ff_surjective_adjoint_equivalence.
Check @ff_surjective_counit_iso.
Check @ff_eso_inverse.
Check @adj_equivalence.
Check @Adjunction.
Check IndT.
Check indiscrete_LARI.
Check Indiscrete.
Check @Erase.
Check erase_pt.

(** ** TYPING negatives: the two identity readings that are not statable *)

Section UnitAndCounitTyping.

Context {A C : Category}.
Context {S : A ⟶ C}.
Context (P : LeftAdjointRightInverse S).
Context (c : C).

(* Control: the delivered form of "unit the identity", against the
   identity TRANSPORTED along the object equation. *)
Check (@unit A C (lari_left P) S (lari_adj P) c
         ≈ id_cast (eq_sym (lari_obj P c))).

(* Control: both sides of the negative are individually well-formed. *)
Check (@unit A C (lari_left P) S (lari_adj P) c).
Check (@id C c).

(* NEGATIVE 1 (TYPING).  The unit runs [c ~> S (lari_left c)] and the
   identity runs [c ~> c]; the two lie in one hom-set only when the two
   objects coincide at Leibniz equality, which is exactly what
   [lari_obj] supplies and what [≈] cannot. *)
Fail Check (@unit A C (lari_left P) S (lari_adj P) c ≈ @id C c).

End UnitAndCounitTyping.

Section CounitTyping.

Context {A C : Category}.
Context {S : A ⟶ C}.
Context `{@Category.Theory.Functor.Full A C S}.
Context `{@Faithful A C S}.
Context (surj : SurjectiveOnObjects S).
Context (a : A).

(* Control: the counit is well-formed, and is an isomorphism -- which is
   the strength Mac Lane's epsilon actually has. *)
Check (@counit A C (ff_surjective_left surj) S (ff_surj_adj surj) a).
Check (ff_surjective_counit_iso surj a).
Check (@id A a).

(* NEGATIVE 2 (TYPING).  The counit runs
   [ff_surjective_left (S a) ~> a], and the chosen preimage of [S a] need
   not be [a]: the exercise gives an isomorphism, not an identity. *)
Fail Check (@counit A C (ff_surjective_left surj) S (ff_surj_adj surj) a
            ≈ @id A a).

End CounitTyping.

(* Control: the counit of the delivered adjoint equivalence at the
   non-degenerate witness is well-formed, and is an isomorphism. *)
Check (@counit (Indiscrete bool) _1 (lari_left indiscrete_LARI)
         (Erase (Indiscrete bool)) (lari_adj indiscrete_LARI) false).

Check (@adj_equiv_counit_iso _1 (Indiscrete bool) IndT
         (Erase (Indiscrete bool)) indiscrete_adjoint_equivalence false).

(* A trap worth recording rather than hiding.  At the [Indiscrete bool]
   witness the comparison of that counit with the identity IS well-typed,
   and indeed holds: [Indiscrete]'s hom family ignores its endpoints, so
   [true ~> false] and [false ~> false] are one and the same type, whose
   sole inhabitant is [tt].  The endpoints still differ
   ([indiscrete_counit_endpoints_differ]).  So the typing obstruction is
   stated at an abstract [A] above, where nothing collapses the two
   hom-sets, and NOT at this witness. *)
Check (@counit (Indiscrete bool) _1 (lari_left indiscrete_LARI)
         (Erase (Indiscrete bool)) (lari_adj indiscrete_LARI) false
       ≈ @id (Indiscrete bool) false).

(* And it holds: both sides are the one inhabitant of [unit]. *)
Example p377_indiscrete_counit_is_id :
  @counit (Indiscrete bool) _1 (lari_left indiscrete_LARI)
    (Erase (Indiscrete bool)) (lari_adj indiscrete_LARI) false
  ≈ @id (Indiscrete bool) false.
Proof. cbn; reflexivity. Qed.

(** ** CONVERSION negatives *)

Section StrictReadbacks.

Context {A C : Category}.
Context {S : A ⟶ C}.
Context `{@Category.Theory.Functor.Full A C S}.
Context `{@Faithful A C S}.
Context (surj : SurjectiveOnObjects S).
Context (c : C).

(* Control: the residue is exhibited at Leibniz equality -- the unit IS
   [fmap[S] id] composed with the transported identity. *)
Check (ff_surj_unit_residue surj c).

(* Control: the [≈] form does hold. *)
Check (ff_surj_unit_is surj c).

(* NEGATIVE 3 (CONVERSION).  [unit] is [⌊id⌋], so it carries an
   [fmap[S] id] that conversion cannot remove at an abstract [S]. *)
Fail Example p377_n3 :
  @unit A C (ff_surjective_left surj) S (ff_surj_adj surj) c
    = id_cast (eq_sym (ff_surj_eq surj c)) := eq_refl.

(* Controls: both actions of the two left adjoints agree on the nose. *)
Check (ff_surj_eso_inverse_obj surj c).
Check (ff_surj_eso_inverse_strict surj).

(* NEGATIVE 4 (CONVERSION).  The whole functor RECORDS are not
   Leibniz-equal: the three law fields are rebuilt. *)
Fail Example p377_n4 :
  @ff_eso_inverse A C S _ _ (ff_surj_eso surj) = ff_surjective_left surj
  := eq_refl.

(* Control: the adjunction extracted from the delivered adjoint
   equivalence IS the directly built one. *)
Check (ff_surj_equiv_adj surj).

(* NEGATIVE 5 (TYPING).  The adjunction the alternative route produces is
   not the directly built one -- and the two do not even have the same
   type, the left adjoints being non-convertible functors. *)
Fail Example p377_n5 :
  @adj_equivalence C A _ S (ff_surj_eso_adjoint_equivalence surj)
    = ff_surj_adj surj := eq_refl.

(* NEGATIVE 6 (CONVERSION).  The alternative route's unit is not the
   transported identity on the nose either.  Note that this error prints
   exactly like negative 3's, both sides displaying as [unit] with the
   implicit arguments hidden; what separates the two routes is negative 7
   below, not this one. *)
Fail Example p377_n6 :
  @unit A C (@ff_eso_inverse A C S _ _ (ff_surj_eso surj)) S
    (@adj_equivalence C A _ S (ff_surj_eso_adjoint_equivalence surj)) c
    = id_cast (eq_sym (ff_surj_eq surj c)) := eq_refl.

(* Control: on the DIRECT route the [≈] form is reached by unfolding the
   unit and computing -- the residue is one [fmap_id]. *)
Definition p377_route_control :
  @unit A C (ff_surjective_left surj) S (ff_surj_adj surj) c
    ≈ id_cast (eq_sym (ff_surj_eq surj c))
  := ltac:(unfold unit; simpl; rewrite fmap_id, id_left; reflexivity).

(* NEGATIVE 7 (CONVERSION).  The same script on the ALTERNATIVE route does
   not close, and the error names where it stops: the goal is
   [equiv_adj_to EquivalenceOfCategories_sym id], i.e. the [symmetry]
   taken on [Functor_Setoid], whose [Equivalence] obligation is closed
   opaquely at Theory/Functor.v:193.  This is the measurement that decides
   which route is shipped. *)
Fail Definition p377_n7 :
  @unit A C (@ff_eso_inverse A C S _ _ (ff_surj_eso surj)) S
    (@adj_equivalence C A _ S (ff_surj_eso_adjoint_equivalence surj)) c
    ≈ id_cast (eq_sym (ff_surj_eq surj c))
  := ltac:(unfold unit; simpl; reflexivity).

End StrictReadbacks.

(* Controls: at an [eq_refl] witness both legs of the repackaged
   isomorphism are [id] on the nose. *)
Check @surjective_ESO_refl_to.
Check @surjective_ESO_refl_from.

(* NEGATIVE 8 (CONVERSION).  The whole isomorphism RECORD is nevertheless
   not [iso_id]: the two inverse-law fields are different proofs. *)
Fail Example p377_n8 {C : Category} (c : C) :
  @eso_iso C C Id[C] (surjective_ESO (@SurjectiveOnObjects_Id C)) c
    = @iso_id C c := eq_refl.

(** ** FORMABILITY negatives *)

(* The two categories' hom universes are identified in every delivered
   constant.  The cause is measured rather than attributed: the mere
   presence of functors in BOTH directions already forces it, before any
   adjunction is formed. *)

Section HomLevelBoundary.

Universes uo uh vo vh.
Constraint uh < vh.

Context (Au : Category@{uo uh uh}).
Context (Xu : Category@{vo vh vh}).

(* Controls: both categories are formable at these declared levels, and a
   functor in the DIRECTION the bound permits elaborates. *)
Check Au.
Check Xu.
Check (Au ⟶ Xu).

(* NEGATIVE 9 (FORMABILITY).  The other direction does not: [Functor]
   forces the source's hom level below the target's. *)
Fail Check (Xu ⟶ Au).

(* NEGATIVE 10 (FORMABILITY).  Hence neither does the record, whose
   [lari_left] field is a functor the other way. *)
Fail Check (∀ S : Au ⟶ Xu, LeftAdjointRightInverse S).

End HomLevelBoundary.

(* Hom is identified with proof as well, and that is a second, separate
   donor: it is already forced by [Adjunction], whose hom-set isomorphism
   lives in [Sets], where a setoid's carrier and relation universes
   coincide. *)

Section HomProofBoundary.

Universes wo wh wp.
Constraint wh < wp.

Context (Bu : Category@{wo wh wp}).

(* Controls: the category, its homs, and functors on it are all formable
   with hom declared strictly below proof. *)
Check Bu.
Check (∀ x y : Bu, x ~{Bu}~> y).
Check (Bu ⟶ Bu).

(* NEGATIVE 11 (FORMABILITY).  The adjunction is not. *)
Fail Check (∀ F G : Bu ⟶ Bu, F ⊣ G).

(* NEGATIVE 12 (FORMABILITY).  Nor, therefore, is the record. *)
Fail Check (∀ S : Bu ⟶ Bu, LeftAdjointRightInverse S).

End HomProofBoundary.
