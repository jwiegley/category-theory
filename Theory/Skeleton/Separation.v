Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Bundled.
Require Import Category.Theory.Skeleton.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Instance.StrictCat.

Generalizable All Variables.

(** * Skeletality separates equivalence from isomorphism of categories *)

(* nLab: https://ncatlab.org/nlab/show/skeleton
   nLab: https://ncatlab.org/nlab/show/principle+of+equivalence

   Awodey asks (Category Theory, 1st ed., §7.10, Exercise 11, p. 188) which
   properties of categories respect equivalence, and for one that is
   invariant under isomorphism of categories but not under equivalence.
   Skeletality is the canonical answer, and this file supplies the negative
   half as a theorem: [skeletality_is_not_equivalence_invariant] exhibits
   the terminal category [1], which is skeletal, equivalent to the
   indiscrete category on [bool], which is not.  The positive half —
   skeletality IS carried along an isomorphism of categories — is
   [Skeletal_StrictCat_invariant] in Theory/Skeleton.v, where it belongs
   because it needs no witnesses.  Together they turn the prose of
   Theory/Equivalence.v ("skeletality is not equivalence-invariant") into a
   pair of proofs.

   The same pair does double duty for Awodey's Exercise 12 (p. 188), which
   asks for a skeletal subcategory equivalent to a given category:
   [Indiscrete_bool_Skeleton] supplies a genuine, non-trivial [Skeleton]
   datum for a category that is NOT skeletal, and
   [Indiscrete_bool_skeleton_is_One] then identifies its skeleton with [1]
   on the nose — an isomorphism in [StrictCat], not merely an equivalence,
   obtained by feeding two equivalences to
   [skeletal_equivalence_is_isomorphism].  This is the in-tree witness
   docs/INHABITATION.md records for the [Skeleton] record: the chosen
   representative is named outright ([true]), so nothing here smuggles a
   choice principle, and no existence claim is made for an arbitrary
   category.

   [One_Skeletal] and [Two_Skeletal] round out the small witnesses;
   [Two_Skeletal] in particular gives Instance/Two.v's header, which calls a
   Boolean algebra "a skeletal thin finitely-cocomplete star-autonomous"
   category, a companion theorem about [_2] itself.

   WHY A SEPARATE FILE.  Theory/Skeleton.v is already a heavyweight Theory
   module (see its header); the witnesses here additionally need
   Instance/Discrete/Reconstruct.v for [Indiscrete] and Instance/Two.v for
   [_2], neither of which any consumer of the core theory has reason to
   pull in.  This is the split rationale Instance/Discrete/Reconstruct.v
   records for itself. *)

(** ** Small skeletal categories *)

Lemma One_Skeletal : Skeletal _1.
Proof. intros x y _; now destruct x, y. Qed.

(* [_2] has no arrow [TwoY ~> TwoX], so its only isomorphisms are the
   identities. *)

Lemma Two_Skeletal : Skeletal _2.
Proof.
  intros [] [] i; try reflexivity.
  - destruct (TwoHom_Y_X_absurd (from i)).
  - destruct (TwoHom_Y_X_absurd (to i)).
Qed.

(** ** The indiscrete category on [bool] is not skeletal *)

Program Definition Indiscrete_iso {A : Type} (x y : A) :
  @Isomorphism (Indiscrete A) x y := {| to := tt; from := tt |}.

Lemma Indiscrete_bool_not_Skeletal : Skeletal (Indiscrete bool) → False.
Proof.
  intro SK.
  pose proof (SK true false (Indiscrete_iso true false)) as H.
  discriminate.
Qed.

(** ** ... yet it is equivalent to the terminal category *)

Program Definition Pick : _1 ⟶ Indiscrete bool := {|
  fobj := fun _ => true;
  fmap := fun _ _ _ => tt
|}.

(* [poly_unit] has no definitional eta, so the unit component is given by a
   [match] rather than by [fun _ => iso_id].  Both obligations end in
   [Defined] to keep the equivalence transparent; unlike
   [skeleton_inclusion_is_equivalence], whose [Defined] is what makes
   [skel_reflect_obj] hold by [reflexivity], nothing here depends on it. *)

Program Definition One_Indiscrete_Equivalence :
  EquivalenceOfCategories Pick := {| quasi_inverse := Erase (Indiscrete bool) |}.
Next Obligation.
  exists (fun x => Indiscrete_iso true x).
  intros x y f; now destruct f.
Defined.
Next Obligation.
  exists (fun x => match x as u return (Isomorphism (C:=_1) u ttt) with
                   | ttt => iso_id end).
  intros x y f; now destruct x, y, f.
Defined.

(* Awodey §7.10 Exercise 11, negative half.  The statement mentions neither
   [Cat] nor [StrictCat] on purpose: phrasing it as an isomorphism in [Cat]
   would bump a universe level for no gain. *)

Theorem skeletality_is_not_equivalence_invariant :
  { C : Category & { D : Category &
      ((C ≃ D) * Skeletal C * (Skeletal D → False))%type } }.
Proof.
  exists _1, (Indiscrete bool).
  split; [split|].
  - exact (Pick; One_Indiscrete_Equivalence).
  - exact One_Skeletal.
  - exact Indiscrete_bool_not_Skeletal.
Defined.

(** ** Awodey §7.10 Exercise 12: a skeleton of a non-skeletal category *)

Program Definition Indiscrete_bool_Sub : Subcategory (Indiscrete bool) := {|
  sobj := fun x => x = true;
  shom := fun x y ox oy f => True
|}.

Section IndiscreteWitness.
#[local] Obligation Tactic := idtac.

(* The uniqueness obligation needs no decidability of [bool] equality: the
   based path space [y = true] is contractible, so [destruct] on the
   membership proof closes it. *)

Program Definition Indiscrete_bool_Skeleton : Skeleton (Indiscrete bool) := {|
  skel_sub  := Indiscrete_bool_Sub;
  skel_full := fun x y ox oy f => I;
  skel_rep  := fun _ => (true; @eq_refl bool true);
  skel_iso  := fun x => Indiscrete_iso x true;
  skel_uniq := _
|}.
Next Obligation.
  intros x a i; destruct a as [y b]; simpl in *; now destruct b.
Qed.

End IndiscreteWitness.

Example Indiscrete_bool_skeleton_has_one_object :
  ∀ X Y : skel_cat Indiscrete_bool_Skeleton, X = Y.
Proof. intros [x a] [y b]; simpl in *; destruct a, b; reflexivity. Qed.

(* The capstone: the skeleton of the indiscrete category on [bool] IS the
   point, on the nose — an isomorphism of categories, not merely an
   equivalence. *)

Definition Indiscrete_bool_skeleton_is_One :
  skel_cat Indiscrete_bool_Skeleton ≅[StrictCat] _1 :=
  let e : skel_cat Indiscrete_bool_Skeleton ≃ _1 :=
    Equivalence_trans (skeleton_equivalence Indiscrete_bool_Skeleton)
      (Equivalence_sym (Pick; One_Indiscrete_Equivalence)) in
  skeletal_equivalence_is_isomorphism
    (skeleton_is_skeletal Indiscrete_bool_Skeleton) One_Skeletal (`1 e) (`2 e).
