Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.

Generalizable All Variables.

(** * The discrete topology as a universal arrow

    nLab:      https://ncatlab.org/nlab/show/discrete+space
    nLab:      https://ncatlab.org/nlab/show/universal+morphism
    Wikipedia: https://en.wikipedia.org/wiki/Discrete_space

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          GTM 5, Springer 1998, §III.1, Exercise 3, printed p. 59 —
          item maclane:III.1:ex3.  The exercise asks for a universal
          arrow to each of four forgetful functors; this file is its
          THIRD row, the discrete topology on a set.  Riehl, "Category
          Theory in Context" 2nd ed., §4.1 Example 4.1.10 lists the same
          adjunction (riehl:4.1:example10).

    The content is Seven Sketches' Exercise 7.29 read as a universal
    property: a map out of a discrete space is continuous for ANY
    topology on the target, so the underlying-set map IS the continuous
    map, and the extension is unique because a continuous map is
    determined by its action on points.

    WHY THIS FILE DOES NOT PACKAGE AN [Adjunction], AND WHY THAT IS NOT A
    DEFECT OF THIS FILE.  Instance/Top/Forgetful.v:70-83 records a
    pre-existing universe obstruction, in its own words: a functor out of
    [Top@{h o}] lands in [Sets@{h so}] while a functor INTO [Top@{h o}]
    must come from [Sets@{o so}], so "[a]n [Adjunction] record between the
    two would need both functors to share ONE Sets, at levels o and h
    simultaneously, with o < h: the packaged triple is unformable at every
    universe assignment."  That file calls it "the library's familiar
    classifier phenomenon ... not a defect of the mathematics", the same
    stratification Instance/Sets/Classifier.v lives with.  Accordingly it
    delivers the adjunction as the cross-universe transposition
    isomorphism [discrete_adj] (:191) with its four naturality lemmas,
    rather than as an [Adjunction].

    So the honest statement of #312's third row is NOT a packaged
    [UniversalArrow] — [Theory/Universal/Arrow.v]'s record would inherit
    exactly the same obstruction, since it mentions the forgetful functor
    applied to an object of the OTHER category.  What IS formable, and is
    delivered here, is the universal property itself, written out:

      - [disc_extend] : the extension of a setoid map to a continuous map
        out of the discrete space.
      - [discrete_universal] : the FULL universal property as a Type-valued
        [∃!] — every setoid map from A into the points of Y extends to one
        and only one continuous map out of [Discrete_Top A].  This is the
        elementary content that a [UniversalArrow] record would package,
        and nothing about it is conditional or cross-universe.
      - [disc_unit] : Mac Lane's unit X → U(X_disc), which the exercise
        names explicitly.

    THE UNIT IS THE IDENTITY, AND THAT IS STRICT.  [Top_Forget]'s object
    action is [Setoid_Lift (top_carrier X)] and [Top_Discrete]'s is
    [Discrete_Top A], whose carrier is A itself, so the composite is
    [Setoid_Lift A] ON THE NOSE — [disc_unit_target_strict] is [eq_refl],
    and it is NOT new: Instance/Top/Forgetful.v:615 already ships
    [forget_discrete_on_objects], the same proposition with the same
    proof.  It is restated here only so the unit below can be read
    without leaving the file —
    and the unit is literally [id] of the lifted setoid.  That is the
    right mathematical statement rather than a degeneracy: the discrete
    topology adds nothing to the underlying set.  (That is the usual
    reason one expects this left adjoint to be fully faithful, but NEITHER
    [Full Top_Discrete] NOR [Faithful Top_Discrete] is proved here or
    anywhere in tree, and neither is claimed — see NOT DELIVERED.)  Note the
    unit
    must be stated on the LIFTED setoid: [A] itself lives in
    [Sets@{o so}] while [Top_Forget]'s values live in [Sets@{h so}], and
    those are different categories — the same stratification again.

    A MEASUREMENT WORTH RECORDING.  Writing [disc_extend] with the record
    literal [{| continuous_map := g; ... |}] is REJECTED even though the
    donor [discrete_adj] fills that very field the same way: the checker
    must solve [top_carrier ?X = A] for [?X], which is higher-order, and
    the ascription on the result type does not determine it in time.
    Applying the constructor explicitly, [@Build_ContinuousMorphism
    (Discrete_Top A) Y g _], fixes [?X] and elaborates.  The donor escapes
    because there the field sits inside a [Program Definition] whose
    expected type is already known.

    NOT DELIVERED: [Full Top_Discrete] and [Faithful Top_Discrete] are
    not proved, so the full faithfulness remarked on above is an
    expectation and not a result of this file.  No [Adjunction] and no
    [UniversalArrow] record either, for the reason above — and no claim that
    either is unformable for a reason
    OTHER than the donor's stratification, which is not re-derived here.
    Nothing is said about the indiscrete side beyond what Forgetful.v
    already proves, and no comparison with [Instance/Discrete.v]'s
    [DiscreteCat] (a different construction on a different subject) is
    made. *)

(** ** The extension of a setoid map to the discrete space *)

(* A map out of a discrete space is continuous for every topology on the
   target ([out_of_discrete_continuous]), so the underlying setoid map is
   already the continuous map.  The constructor is applied explicitly; see
   the header for why the record literal is rejected here. *)
Definition disc_extend (A : SetoidObject) (Y : TopSpace)
  (g : SetoidMorphism A (top_carrier Y))
  : Discrete_Top A ~{Top}~> Y :=
  @Build_ContinuousMorphism (Discrete_Top A) Y g
    (out_of_discrete_continuous A Y g).

Example disc_extend_map (A : SetoidObject) (Y : TopSpace)
  (g : SetoidMorphism A (top_carrier Y)) (a : carrier A) :
  disc_extend A Y g a = g a := eq_refl.

(** ** The universal property (Mac Lane §III.1 Exercise 3, row three) *)

Theorem discrete_universal (A : SetoidObject) (Y : TopSpace)
  (g : SetoidMorphism A (top_carrier Y)) :
  ∃! f : Discrete_Top A ~{Top}~> Y, ∀ a, f a ≈ g a.
Proof.
  exists (disc_extend A Y g).
  - intro a; reflexivity.
  - intros f' Hf' a; simpl; symmetry; exact (Hf' a).
Qed.

(** ** The unit X → U(X_disc), and that it is the identity *)

Example disc_unit_target_strict (A : SetoidObject) :
  fobj[Top_Forget] (fobj[Top_Discrete] A) = Setoid_Lift A := eq_refl.

Definition disc_unit (A : SetoidObject)
  : Setoid_Lift A ~{Sets}~> fobj[Top_Forget] (fobj[Top_Discrete] A) := id.

Example disc_unit_is_id (A : SetoidObject) (a : carrier A) :
  disc_unit A a = a := eq_refl.

(** ** Agreement with the pre-existing transposition isomorphism *)

(* [discrete_adj]'s forward leg strips a continuous map to its underlying
   setoid map; on an extension it returns the map it started from. *)
Example disc_extend_is_adj_from (A : SetoidObject) (Y : TopSpace)
  (g : SetoidMorphism A (top_carrier Y)) :
  to (discrete_adj A Y) (disc_extend A Y g) = g := eq_refl.

(** ** Non-vacuity

    The witness must exercise a target whose topology is NOT discrete,
    or the universal property would say nothing: with both sides discrete
    every map is continuous for trivial reasons on both ends.  The
    two-point indiscrete space is the in-tree witness that separates. *)

Example disc_universal_at_indiscrete
  (g : SetoidMorphism bool_setoid_object
         (top_carrier TwoPoint_Indiscrete)) :
  ∃! f : Discrete_Top bool_setoid_object ~{Top}~> TwoPoint_Indiscrete,
    ∀ a, f a ≈ g a :=
  discrete_universal bool_setoid_object TwoPoint_Indiscrete g.

(* And the extension really is the identity on points, so the universal
   property is not collapsing anything. *)
Example disc_extend_indiscrete_computes
  (g : SetoidMorphism bool_setoid_object
         (top_carrier TwoPoint_Indiscrete)) (b : bool) :
  disc_extend bool_setoid_object TwoPoint_Indiscrete g b = g b := eq_refl.
