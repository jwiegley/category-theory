Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * Regression test for the [Poset] category construction (issue #124)

    nLab:      https://ncatlab.org/nlab/show/poset
    Wikipedia: https://en.wikipedia.org/wiki/Partially_ordered_set

    Issue #124 reported two defects in [Instance/Poset.v] (fixed in PR
    #136 / commit e2bcc89):

      1. the carrier [C] was typed as a [Category] rather than a plain
         [Type] (the morphism structure is unused); and
      2. the order relation was required [Asymmetric] instead of
         [Antisymmetric].  Because [PreOrder] is reflexive ([R x x]), an
         [Asymmetric] relation ([R x y -> ~ R y x]) forces [~ R x x],
         contradicting reflexivity — so under the old definition the only
         possible carrier was empty ([there_is_no_poset : Poset P -> False]).

    This file locks in the corrected definition.  Every [Definition],
    [Example], and [Lemma] below type-checks only against the fixed
    signature [Poset {C : Type} `{R : relation C} (P : PreOrder R)
    `{@Antisymmetric C eq eq_equiv R}], so a successful build IS the
    assertion.  The accompanying comments record why each item would have
    been ill-typed or unprovable under the old broken definition.

    NB on name resolution: [Instance/Proset.v] ALSO exports a
    [LessThanEqualTo_Category] (the proset over [(ℕ, ≤)]).  To make the
    [nat] block below a genuine regression guard rather than silently
    falling through to the proset's definition, every reference to the
    poset's example is fully qualified as
    [Category.Instance.Poset.LessThanEqualTo_Category]; under the old
    definition that name does not exist (no example could be built), so the
    reference fails outright. *)

(** ** The canonical example [(ℕ, ≤)]

    [Category.Instance.Poset.LessThanEqualTo_Category] is exported from
    [Instance/Poset.v] and is built as [@Poset nat le le_preorder
    (partial_order_antisym le_partialorder)].  It exists ONLY because the
    carrier is now a plain [Type] ([nat]) and the constraint is
    [Antisymmetric] (discharged by [partial_order_antisym]).  It is the
    concrete witness that a poset over a non-empty carrier is constructible
    — the exact opposite of the old [there_is_no_poset]. *)

Definition Poset_nat : Category :=
  Category.Instance.Poset.LessThanEqualTo_Category.

(** *** Inhabitation: the carrier is a plain, non-empty [Type]

    Under the old [{C : Category}] / [Asymmetric] signature the carrier was
    forced empty (reflexivity + asymmetry yields [False] for any element),
    so no object term could exist; moreover [obj] would be [obj[C]] for some
    [Category C], never definitionally the bare [Type nat]. *)

Definition poset_nat_has_object : obj[Poset_nat] := 0%nat.

Example poset_nat_obj_is_nat : obj[Poset_nat] = nat := eq_refl.

Theorem poset_nat_is_inhabited : inhabited obj[Poset_nat].
Proof. exact (inhabits 0%nat). Qed.

(** *** Morphisms: identities from reflexivity, arrows from [≤],
        composition from transitivity

    In [Proset] the hom-type [x ~> y] is definitionally [R x y], here
    [(x <= y)%nat].  The object arguments to [@id]/[@compose] parse in
    [object_scope], so the numeric indices carry explicit [%nat]. *)

Definition poset_nat_id0 : (0 ~{Poset_nat}~> 0)%nat := @id Poset_nat 0%nat.

Definition poset_nat_hom_0_1 : (0 ~{Poset_nat}~> 1)%nat := le_S 0 0 (le_n 0).

Definition poset_nat_hom_1_2 : (1 ~{Poset_nat}~> 2)%nat := le_S 1 1 (le_n 1).

Definition poset_nat_comp_0_2 : (0 ~{Poset_nat}~> 2)%nat :=
  @compose Poset_nat 0%nat 1%nat 2%nat poset_nat_hom_1_2 poset_nat_hom_0_1.

(** *** Antisymmetry / skeletality

    This is the exact witness the fixed [Poset] relies on.  Its type is
    [Antisymmetric ... eq ...]; it CANNOT be coerced to [Asymmetric], the
    type the old definition demanded — a direct type mismatch. *)

Definition poset_nat_antisym : Antisymmetric nat eq PeanoNat.Nat.le :=
  partial_order_antisym PeanoNat.Nat.le_partialorder.

Lemma poset_nat_skeletal :
  forall x y : obj[Poset_nat],
    (x ~{Poset_nat}~> y)%nat -> (y ~{Poset_nat}~> x)%nat -> x = y.
Proof. intros x y Hxy Hyx; exact (poset_nat_antisym x y Hxy Hyx). Qed.

Lemma poset_nat_le_antisym :
  forall x y : nat, (x <= y)%nat -> (y <= x)%nat -> x = y.
Proof. intros x y; apply (antisymmetry (R:=PeanoNat.Nat.le)). Qed.

(** ** A bespoke 2-element poset over a [Type] with no categorical structure

    This decisively exercises defect 1: the carrier [two] is an ordinary
    inductive [Type] that is NOT a [Category], so [@Poset two ...] is
    unbuildable under the old [{C : Category}] signature.  It also exercises
    defect 2: the fourth argument is an [Antisymmetric] instance, exactly
    where the old definition demanded an [Asymmetric] one.  A self-contained
    custom order is used (Rocq 9.1 ships [Bool.le] but no bundled
    [PreOrder]/[Antisymmetric] instances for it). *)

Inductive two : Type := lo | hi.

Definition two_le (x y : two) : Prop :=
  match x, y with
  | lo, _   => True
  | hi, hi  => True
  | hi, lo  => False
  end.

#[local] Instance two_le_preorder : PreOrder two_le.
Proof.
  constructor.
  - intros [|]; constructor.
  - intros [|] [|] [|]; simpl; auto.
Qed.

#[local] Instance two_le_antisym : @Antisymmetric two eq eq_equiv two_le.
Proof.
  intros [|] [|]; simpl; intros H1 H2;
    solve [ reflexivity | contradiction ].
Qed.

Definition Poset_two : Category := @Poset two two_le two_le_preorder two_le_antisym.

Definition poset_two_has_object : obj[Poset_two] := lo.

Example poset_two_obj_is_two : obj[Poset_two] = two := eq_refl.

Definition poset_two_hom : (lo ~{Poset_two}~> hi) := I.

Theorem poset_two_is_inhabited : inhabited obj[Poset_two].
Proof. exact (inhabits lo). Qed.

Lemma poset_two_skeletal :
  forall x y : obj[Poset_two],
    (x ~{Poset_two}~> y) -> (y ~{Poset_two}~> x) -> x = y.
Proof. intros x y Hxy Hyx; exact (two_le_antisym x y Hxy Hyx). Qed.

(** ** Why the OLD definition forced an empty carrier (documentation)

    This standalone lemma captures, in categorical-free vocabulary, the
    precise contradiction the fix repaired: any inhabitant of a carrier
    bearing both a [PreOrder] and an [Asymmetric] relation yields [False].
    It does not mention [Poset] and is valid regardless of its definition;
    it is here purely as explanatory contrast for issue #124. *)

Lemma asym_preorder_forces_empty :
  forall (C : Type) (R : relation C),
    PreOrder R -> Asymmetric R -> C -> False.
Proof.
  intros C R P A x.
  pose proof (@reflexivity C R (@PreOrder_Reflexive C R P) x) as Hrefl.
  exact (A x x Hrefl Hrefl).
Qed.
