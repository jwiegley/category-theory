Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Free.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * The underlying-set functor of R-modules is represented by R

    Book: Riehl, "Category Theory in Context", 2nd ed., §2.1
          Example 2.1.5(iv), printed p. 56 (PDF pp. 76-77) —
          riehl:2.1:example5
    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          §III.1, printed p. 56 — maclane:III.1:remark2
    Book: Riehl, "Category Theory in Context", 2nd ed., §4.1
          Exercise 4.1.v, printed p. 138 —
          riehl:4.1:exv, which asks for a proof that the free R-module
          construction is FUNCTORIAL in the generating set.  That
          exercise needs no work here and none is done: packaging the
          free module as a [UniversalArrow] and feeding it to
          Theory/Universal/Arrow.v's [AdjunctionFromUniversalArrows]
          delivers the functoriality as the [fmap] of the constructed
          left adjoint, and Instance/Mod/Free.v does exactly that
          ([FreeMod], :513, with [free_module_adjunction], :517, and
          [free_module_fmap_generators] recording that the induced action
          relabels basis vectors).  The citation is recorded here because
          this is the file the exercise's other half — the pointwise
          representability criterion — would be read against.
    nLab:      https://ncatlab.org/nlab/show/representable+functor
    nLab:      https://ncatlab.org/nlab/show/free+module
    Wikipedia: https://en.wikipedia.org/wiki/Representable_functor

    WHAT RIEHL ADDS TO THE FREE-MODULE CONSTRUCTION.  Instance/Mod/Free.v
    already proves that the free module on a generating setoid solves a
    universal mapping problem, and packages that as a [UniversalArrow]
    and an adjunction.  Riehl's Example 2.1.5(iv) says something that
    LOOKS like a corollary and is worth separating: the forgetful functor
    [RMod_Forget R] is REPRESENTABLE, and its representing object is R
    itself, the free module on ONE generator.  Two things are being
    claimed at once — that the ∃!-factorization property upgrades to a
    natural isomorphism of functors

        [Hom R,─]  ≅  RMod_Forget R      (in [RMod R, Sets])

    and that the representing object can be named on the nose as
    Instance/Mod.v's [Ring_RMod R], with no formal-sum carrier in sight.

    HOW IT IS PROVED, AND WHY NOT BY CITING THE FREE MODULE.  The route
    taken is the direct one: [ring_universal_element] exhibits [rig_one R]
    as a universal element of [RMod_Forget R] at [Ring_RMod R], because a
    module map out of R is determined by its value at 1 (h r ≈ h (r·1) ≈
    r · h 1) and every element m of every module is the value at 1 of the
    map r ↦ r·m.  That is four lines of module algebra and no formal sums.
    Routing through Instance/Mod/Free.v instead would have produced the
    representation at the object [FreeModObject SetsOne] — correct, but
    naming a quotient of formal expressions where Riehl names R.  What
    the free module then contributes is the COMPARISON, and it comes for
    free from the generic uniqueness machinery: [free_one_generator_iso]
    below is Theory/Universal/Element.v's [universal_element_iso] applied
    to the two universal elements, so "the free module on one generator
    is R" is a theorem here rather than a slogan, and it is proved
    without ever computing a normal form.

    WHAT IS DELIVERED.

      - [ring_universal_element], and its bundled form; the
        representation [rmod_representation] as a natural isomorphism in
        the functor category, and [rmod_representable] as an inhabitant
        of Functor/Representable.v's class;
      - the two Theory/Universal/Arrow.v encodings of the same content as
        a universal arrow from the one-point setoid;
      - [free_one_generator_iso], the canonical isomorphism between the
        free module on the singleton setoid and R, together with
        [free_one_generator_iso_unique] — the uniqueness clause, which is
        the part a bare [≅] would drop;
      - the witness at ℤ, where the represented set is the integers.

    WHAT IS NOT DELIVERED.  No claim that the representing object is
    unique on the nose (it is unique up to the unique isomorphism
    compatible with the universal elements, which is exactly what
    [universal_element_unique] gives and no more); no contravariant or
    enriched version; and no statement about [RMod_Forget_Ab], to which
    Functor/Representable.v's class does not even apply — that functor
    lands in [Ab], not in [Sets]. *)

Section RingRepresents.

Context (R : RingObject).

(** ** The module map determined by an element *)

(** For m in a module W, the map r ↦ r·m.  Each of the four obligations
    is a module law of W: respectfulness is [rm_smul_respects],
    preservation of zero is [rm_smul_zero_l], of sums
    [rm_smul_distr_r], and of the action [rm_smul_assoc] — the action of
    [Ring_RMod R] on itself BEING the multiplication of R. *)
Program Definition rmod_by_element (W : RModObject R)
  (m : carrier (cmon_setoid W)) : Ring_RMod R ~{RMod R}~> W := {|
  rm_hom := {| cmon_map := {| morphism := fun r => rm_smul W r m |} |}
|}.
Next Obligation.
  intros W m a b Hab; exact (rm_smul_respects W _ _ Hab _ _ (reflexivity m)).
Qed.
Next Obligation. intros W m; simpl; apply rm_smul_zero_l. Qed.
Next Obligation. intros W m a b; simpl; apply rm_smul_distr_r. Qed.
Next Obligation. intros W m r a; simpl; apply rm_smul_assoc. Qed.

(** A module map out of R is determined by its value at 1. *)
Lemma rmod_out_of_ring (W : RModObject R) (g : Ring_RMod R ~{RMod R}~> W)
  (r : carrier (rig_setoid R)) :
  cmon_map (rm_hom g) r
    ≈ rm_smul W r (cmon_map (rm_hom g) (rig_one R)).
Proof.
  transitivity (cmon_map (rm_hom g) (rig_mul R r (rig_one R))).
  - apply (proper_morphism (cmon_map (rm_hom g))).
    symmetry; apply rig_mul_one_r.
  - exact (rm_map_smul g r (rig_one R)).
Qed.

(** ** Riehl's Example 2.1.5(iv) *)

(** The unit of R is a universal element of the underlying-set functor.
    The factorization is [rmod_by_element], the commutation is
    [rm_smul_one], and the uniqueness is [rmod_out_of_ring]. *)
Definition ring_universal_element
  : AUniversalElement (RMod_Forget R) (Ring_RMod R).
Proof.
  unshelve econstructor.
  - exact (rig_one R).
  - intros W m.
    unshelve econstructor.
    + exact (rmod_by_element W m).
    + simpl; apply rm_smul_one.
    + intros g Hg r; simpl.
      symmetry.
      transitivity (rm_smul W r (cmon_map (rm_hom g) (rig_one R))).
      * exact (rmod_out_of_ring W g r).
      * exact (rm_smul_respects W _ _ (reflexivity r) _ _ Hg).
Defined.

Definition ring_universal_element_bundled : UniversalElement (RMod_Forget R) :=
  UniversalElement_of_AUniversalElement ring_universal_element.

(** The representation as a NATURAL isomorphism in [[RMod R, Sets]] —
    Riehl's packaging, not merely the ∃! factorization property. *)
Definition rmod_representation
  : @Curried_Hom (RMod R) (Ring_RMod R) ≅[[RMod R, Sets]] RMod_Forget R :=
  ue_representation (RMod_Forget R) (Ring_RMod R) ring_universal_element.

Definition rmod_representable : Representable (RMod_Forget R) :=
  Representable_of_UniversalElement ring_universal_element_bundled.

(** The same content as a universal arrow from the one-point setoid, in
    both of Theory/Universal/Arrow.v's encodings. *)
Definition ring_auniversal_arrow
  : AUniversalArrow SetsOne (RMod_Forget R) (Ring_RMod R) :=
  AUniversalArrow_of_AUniversalElement (RMod_Forget R) (Ring_RMod R)
    ring_universal_element.

Definition ring_universal_arrow : UniversalArrow SetsOne (RMod_Forget R).
Proof.
  unshelve eapply
    (universal_arrow_from_UMP SetsOne (RMod_Forget R) (Ring_RMod R)).
  - exact (@universal_arrow _ _ _ _ _ ring_auniversal_arrow).
  - intros W f.
    unshelve econstructor.
    + exact (unique_obj (@universal_arrow_universal _ _ _ _ _
                           ring_auniversal_arrow W f)).
    + symmetry.
      exact (unique_property (@universal_arrow_universal _ _ _ _ _
                                ring_auniversal_arrow W f)).
    + intros v Hv.
      exact (uniqueness (@universal_arrow_universal _ _ _ _ _
                           ring_auniversal_arrow W f) v (symmetry Hv)).
Defined.

(** ** The free module on one generator IS R

    Instance/Mod/Free.v's universal arrow at the singleton setoid is a
    universal element of the same functor, so the two representing
    objects are canonically isomorphic.  Nothing is computed: this is
    [universal_element_iso], and the uniqueness clause below is
    [universal_element_unique]. *)

Definition free_one_universal_element
  : AUniversalElement (RMod_Forget R) (@FreeModObject R SetsOne) :=
  AUniversalElement_of_AUniversalArrow (RMod_Forget R)
    (@FreeModObject R SetsOne)
    (free_module_AUniversalArrow R SetsOne).

Definition free_one_generator_iso
  : @FreeModObject R SetsOne ≅[RMod R] Ring_RMod R :=
  universal_element_iso free_one_universal_element ring_universal_element.

(** The isomorphism carrying the basis vector to 1 is the ONLY one: a
    bare [≅] would leave the free module's automorphisms in play. *)
Definition free_one_generator_iso_unique
  : Unique (fun i : @FreeModObject R SetsOne ≅[RMod R] Ring_RMod R =>
              fmap[RMod_Forget R] (to i)
                (@aue_elem _ (RMod_Forget R) _ free_one_universal_element)
                ≈ rig_one R) :=
  universal_element_unique free_one_universal_element ring_universal_element.

(** The universal element of the free-module side is the basis vector at
    the unique point, definitionally. *)
Example free_one_universal_elem_is_generator :
  @aue_elem _ (RMod_Forget R) _ free_one_universal_element
    = @fv_gen R SetsOne ttt := eq_refl.

End RingRepresents.

(** ** The witness at ℤ

    The represented set of the ℤ-module ℤ is the integers, and the
    mediating map is multiplication by the chosen integer, which
    computes. *)

Example int_universal_elem : @aue_elem _ (RMod_Forget Int_Ring) _
  (ring_universal_element Int_Ring) = 1%Z := eq_refl.

Example int_mediator_computes :
  cmon_map (rm_hom (rmod_by_element Int_Ring Int_RMod 5%Z)) 3%Z = 15%Z
  := eq_refl.
