(** * Probe for #372(a): the boundaries of Instance/Ord.v and
      Instance/Ord/Poset.v

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          §IV.3, printed p. 92, Exercise 4(a).  Catalog id:
          maclane:IV.3:ex4.

    This file exists so that every rejection the two library files
    MEASURE is also GUARDED.  It restates them from OUTSIDE those files,
    because an in-file [Fail] renames in lockstep with the constant it
    guards and so cannot detect a rename; and it mirrors the FULL
    [Require] list of both, because a short prefix is what makes a probe
    fail for a reason it never measured.

    Six negatives of THREE kinds, plus one scope-free instrument check.
    Each was stripped ONE AT A TIME into its own file and compiled alone,
    and its WHOLE error was read; the kind recorded below is read off that
    error rather than assumed.

    CONVERSION (four; each ends "cannot unify" between two terms of one
    type):

    1. [neg_posets_round_strict] -- the [Pos]/[Posets] round trip is not
       [eq_refl] on the nose.  Error: cannot unify
       "fobj[Pos_to_Posets] (fobj[Posets_to_Pos] x)" and "x".  Cause: an
       object of [Posets] is a stdlib [sigT], which Lib.v:10's [Set
       Primitive Projections] does not cover, so [(`1 x; `2 x) = x] holds
       only after a [destruct].  Control: [ctrl_posets_round], the SAME
       statement discharged by [posets_pos_posets_obj] -- so the negative
       measures the missing eta and nothing else.
    2. [neg_unit_record] -- the adjunction's unit is not the projection as
       a RECORD.  Error: cannot unify "poset_unit P" and
       "reflection_proj P".  Control: [ctrl_unit_pointwise], the same
       identification applied to a point, which IS [eq_refl].
    3. [neg_natle_reflection_eq] -- the reflection of a partial order is
       not equal to it.  Error: cannot unify "PosetReflection NatLe" and
       "NatLe".  Control: [ctrl_natle_reflection_order], which shows the
       two agree in the ORDER field, so the difference is the setoid.
    5. [neg_ord_obj_is_not_points] -- the reviewer's distinction.  Error:
       cannot unify "obj[Ord]" and "obj[OrdAsCategory Chaos2]".  Controls:
       [ctrl_ord_obj] and [ctrl_thin_obj] name both sides positively.

    TYPING (one; a plain mismatch, with NO "cannot unify" and no universe
    clause):

    4. [neg_adj_is_not_reflective] -- the adjunction is strictly less than
       the [Reflective] record.  Error: The term "Poset_adj" has type
       "Poset_reflector ⊣ Incl Ord Pos_Sub" while it is expected to have
       type "Reflective Pos_Sub".  Control: [ctrl_reflective_adj].

    FORMABILITY (one; "universe inconsistency: Cannot enforce up = uh"):

    6. [Subcategory C] is refused at a category whose hom and proof
       universes are declared strictly apart, while [x ~> y] and [id{C}]
       at those very levels are ACCEPTED -- so the rejection is the
       donor's identification and not an artifact of naming a hom.  Only
       ONE such negative is stated: [Reflective] takes a [Subcategory] and
       cannot be tested apart from it (the trap
       Test/ProbeRingLattice340.v records for [MonoidObject]), so a second
       negative naming [Reflective] would fire at its argument and measure
       nothing new.

    A SEVENTH negative was drafted and WITHDRAWN as a false pass:
    [Fail Example : obj[Ord] := OrdAsCategory P] SUCCEEDS, because Coq
    inserts [@reverse_coercion (obj[Ord]) Category P (OrdAsCategory P)].
    Negative 5 replaces it at the level of the two object TYPES, where no
    coercion can intervene.  The episode is recorded rather than quietly
    fixed.

    Every constant a negative names also appears OUTSIDE a [Fail], in the
    control block below or in a control beside the negative itself. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Pos.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Ord.
Require Import Category.Instance.Ord.Poset.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(** ** Instrument check *)

Fail Definition probe_ord372_instrument : nat := true.

(** ** Controls *)

Check @Poset_Reflective_in_Ord.
Check @Poset_reflector.
Check @Poset_adj.
Check @Pos_Sub.
Check @Pos_Sub_Full.
Check @Posets.
Check @Ord.
Check @OrdObject.
Check @OrdAntisymmetric.
Check @PosetReflection.
Check @PosetReflectionObj.
Check @reflection_proj.
Check @poset_unit.
Check @NatLe.
Check @NatLePos.
Check @Chaos2.
Check @MixOrd.
Check @Pos_to_Posets.
Check @Posets_to_Pos.
Check @Pos_Posets_strict_iso.
Check @posets_pos_posets_obj.
Check @OrdAsCategory.
Check @OrdHomAsFunctor.
Check @Subcategory.
Check @Reflective.
Check @Incl.
Check @Proset.
Check @PosetObject.

(** ** Negative 1 (CONVERSION) *)

Example ctrl_posets_round (x : Posets) :
  fobj[Pos_to_Posets] (fobj[Posets_to_Pos] x) = x
  := posets_pos_posets_obj x.

Fail Example neg_posets_round_strict (x : Posets) :
  fobj[Pos_to_Posets] (fobj[Posets_to_Pos] x) = x := eq_refl.

(** ** Negative 2 (CONVERSION) *)

Example ctrl_unit_pointwise (P : OrdObject)
    (x : carrier (ord_setoid P)) :
  ord_fn (poset_unit P) x = ord_fn (reflection_proj P) x := eq_refl.

Fail Example neg_unit_record (P : OrdObject) :
  poset_unit P = reflection_proj P := eq_refl.

(** ** Negative 3 (CONVERSION) *)

Example ctrl_natle_reflection_order :
  ord_le (PosetReflection NatLe) = ord_le NatLe := eq_refl.

Fail Example neg_natle_reflection_eq :
  PosetReflection NatLe = NatLe := eq_refl.

(** ** Negative 4 (TYPING) *)

Example ctrl_reflective_adj :
  Poset_reflector ⊣ Incl Ord Pos_Sub := Poset_adj.

Fail Example neg_adj_is_not_reflective :
  Reflective Pos_Sub := Poset_adj.

(** ** Negative 5 (CONVERSION): the reviewer's distinction.

    The objects of [Ord] are PREORDERS; the objects of [OrdAsCategory P]
    are the POINTS of one preorder.  Both readings are pinned positively
    just below, and their identification is refuted. *)

Example ctrl_ord_obj : obj[Ord] = OrdObject := eq_refl.

Example ctrl_thin_obj :
  obj[OrdAsCategory Chaos2] = carrier (ord_setoid Chaos2) := eq_refl.

Fail Example neg_ord_obj_is_not_points :
  obj[Ord] = obj[OrdAsCategory Chaos2] := eq_refl.

(** ** Negative 6 (FORMABILITY) *)

Section ProbeUniverses.
  Universes uo uh up.
  Constraint uh < up.
  Context (C : Category@{uo uh up}) (x y : C).

  Check (x ~> y).
  Check (@id C x).

  Fail Check (Subcategory C).
End ProbeUniverses.
