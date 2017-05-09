Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Construction.Product.
Require Export Category.Instance.Nat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Monoidal.

Context `{C : Category}.

Reserved Infix "⨂" (at level 30, right associativity).

Class Monoidal := {
  tensor : C ∏ C ⟶ C
    where "x ⨂ y" := (tensor (x, y));

  I : C;

  tensor_assoc {X Y Z} : (X ⨂ Y) ⨂ Z ≅ X ⨂ (Y ⨂ Z); (* alpha *)

  unit_left  {X} : I ⨂ X ≅ X;   (* lambda *)
  unit_right {X} : X ⨂ I ≅ X;   (* rho *)

  (* jww (2017-05-09): This should be provable *)
  unit_identity : to (@unit_left I) ≈ to (@unit_right I);

  triangle_identity {X Y} :
    bimap (to unit_right) id
      ≈ bimap id (to unit_left) ∘ to (@tensor_assoc X I Y);

  pentagon_identity {X Y Z W} :
    bimap (id[W]) (to (@tensor_assoc X Y Z))
      ∘ to (@tensor_assoc W (X ⨂ Y) Z)
      ∘ bimap (to (@tensor_assoc W X Y)) (id[Z])
      ≈ to (@tensor_assoc W X (Y ⨂ Z)) ∘ to (@tensor_assoc (W ⨂ X) Y Z)
}.

Notation "X ⨂ Y" := (tensor (X, Y)) (at level 30, right associativity).

Theorem left_quadrangle_commutes `{Monoidal} {X Y Z} :
  bimap (to unit_right) id ∘ to (@tensor_assoc _ (X ⨂ I) Y Z)
    ≈ to (@tensor_assoc _ X Y Z) ∘ bimap (bimap (to unit_right) id) id.
Proof.
  pose proof (@pentagon_identity _ I Y Z X).
Abort.

Theorem right_quadrangle_commutes `{Monoidal} {X Y Z} :
  bimap id (bimap (to unit_left) id) ∘ to (@tensor_assoc _ X (I ⨂ Y) Z)
    ≈ to (@tensor_assoc _ X Y Z) ∘ bimap (bimap id (to unit_left)) id.
Proof.
Abort.

Theorem triangle_upper `{Monoidal} {X Y Z : C} :
  @bimap C C C tensor _ _ _ _ (bimap (to unit_right) id) (id[Z])
    ≈ bimap (bimap id (to unit_left)) (id[Z])
        ∘ bimap (to (@tensor_assoc _ X I Y)) (id[Z]).
Proof.
  rewrite (@triangle_identity _ X Y).
  rewrite <- bimap_comp.
  rewrite id_left.
  reflexivity.
Qed.

Definition triangle_lower_left `{Monoidal} {X Y Z} :
  bimap (to unit_right) id
    ≈ bimap id (to unit_left) ∘ to (@tensor_assoc _ X I (Y ⨂ Z)) :=
  triangle_identity.

Theorem triangle_lower_right `{Monoidal} {X Y Z} :
  @bimap C C C tensor _ _ _ _ id (bimap (to unit_left) id)
    ≈ bimap id (to unit_left) ∘ bimap (id[X]) (to (@tensor_assoc _ I Y Z)).
Proof.
  rewrite <- bimap_comp.
  rewrite id_left.
  apply bimap_respects; [reflexivity|].
Abort.

Theorem triangle_right `{Monoidal} {X Y} :
  to unit_right
    ≈ bimap id (to unit_right) ∘ to (@tensor_assoc _ X Y I).
Proof.
  pose proof (@triangle_identity _).
Abort.

Theorem triangle_left `{Monoidal} {X Y} :
  bimap (to unit_left) id
    ≈ to unit_left ∘ to (@tensor_assoc _ I X Y).
Proof.
Abort.

Class SymmetricMonoidal `{Monoidal} := {
  sym_swap {X Y} : X ⨂ Y ≅ Y ⨂ X;

  sym_swap_swap_to   {X Y} :
    to (@sym_swap Y X) ∘ to (@sym_swap X Y) ≈ id;
  sym_swap_swap_from {X Y} :
    from (@sym_swap X Y) ∘ from (@sym_swap Y X) ≈ id
}.

End Monoidal.

Notation "(⨂)" := (@tensor _ _) : functor_scope.
Notation "X ⨂ Y" := (@tensor _ _ (X%object, Y%object))
  (at level 30, right associativity) : object_scope.

Local Obligation Tactic := program_simpl.

(* This reflects the fact that categories are themselves "monoidoids", or
   monoidal with respect to identity and composition.  *)

Program Definition Composition_Monoidal `{C : Category} :
  @Monoidal ([C, C]) := {|
  tensor :=
    {| fobj := fun p => Compose (fst p) (snd p)
     ; fmap := fun F G N =>
         {| transform := fun x =>
              transform[fst N] (snd G x) ∘ fmap[fst F] (transform[snd N] x) |}
     |};
  I := Id
|}.
Next Obligation.
  simpl in *.
  rewrite <- naturality.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- naturality.
  rewrite <- !comp_assoc.
  rewrite <- naturality.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- naturality.
  reflexivity.
Qed.
Next Obligation.
  proper; simplify; simpl in *.
  rewrite a, b.
  reflexivity.
Qed.
Next Obligation.
  simplify; simpl in *.
  rewrite !fmap_id; cat.
Qed.
Next Obligation.
  simplify; simpl in *.
  rewrite <- !comp_assoc.
  apply compose_respects.
    reflexivity.
  rewrite <- !naturality.
  rewrite fmap_comp.
  rewrite comp_assoc.
  reflexivity.
Qed.
Next Obligation. constructive; cat. Defined.
Next Obligation. constructive; cat. Defined.
Next Obligation. constructive; cat. Defined.
Next Obligation. cat. Defined.
Next Obligation. cat. Defined.
Next Obligation. cat. Defined.

(* Every cartesian category with terminal objects gives rise to a monoidal
   category taking the terminal object as unit, and the tensor as product. *)

Require Import Category.Functor.Product.Internal.

(* Any cartesian category with terminal objects is monoidal with respect to
   its internal product functor. *)

Program Definition InternalProduct_Monoidal
        `{C : Category} `{@Cartesian C} `{@Terminal C} : @Monoidal C := {|
  tensor := InternalProductFunctor C;
  I := One
|}.
Next Obligation. apply one_unique. Qed.
Next Obligation.
  cat.
  rewrite <- fork_comp; cat.
  rewrite <- comp_assoc; cat.
Qed.
Next Obligation.
  cat.
  rewrite <- !fork_comp; cat.
  rewrite <- !comp_assoc; cat.
  rewrite <- !fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

Require Import Category.Functor.Bifunctor.

Local Obligation Tactic := simpl; intros.

(* Any product of monoidal categories is monoidal. *)

Program Instance Product_Monoidal
        `{C : Category} `{@Monoidal C} `{D : Category} `{@Monoidal D} :
  @Monoidal (C ∏ D) := {
  tensor :=
    {| fobj := fun x => (fst (fst x) ⨂ fst (snd x),
                         snd (fst x) ⨂ snd (snd x))
     ; fmap := fun _ _ f => (bimap (fst (fst f)) (fst (snd f)),
                             bimap (snd (fst f)) (snd (snd f))) |};
  I := (@I C _, @I D _)
}.
Next Obligation.
  exact H.
Defined.
Next Obligation.
  exact H0.
Defined.
Next Obligation.
  simplify; simpl in *.
  proper; simplify; simpl in *.
    rewrite a0, a.
    reflexivity.
  rewrite b0, b1.
  reflexivity.
Qed.
Next Obligation.
  simplify; simpl in *;
  rewrite <- fmap_id;
  apply fmap_respects; cat.
Qed.
Next Obligation.
  simplify; simpl in *;
  rewrite bimap_comp;
  reflexivity.
Qed.
Next Obligation.
  isomorphism; simpl; simplify; simpl.
  - apply (to tensor_assoc).
  - apply (to tensor_assoc).
  - apply (from tensor_assoc).
  - apply (from tensor_assoc).
  - apply iso_to_from.
  - apply iso_to_from.
  - apply iso_from_to.
  - apply iso_from_to.
Defined.
Next Obligation.
  isomorphism; simpl; simplify.
  - apply (to unit_left).
  - apply (to unit_left).
  - apply (from unit_left).
  - apply (from unit_left).
  - apply iso_to_from.
  - apply iso_to_from.
  - apply iso_from_to.
  - apply iso_from_to.
Defined.
Next Obligation.
  isomorphism; simpl; simplify; simpl.
  - apply (to unit_right).
  - apply (to unit_right).
  - apply (from unit_right).
  - apply (from unit_right).
  - apply iso_to_from.
  - apply iso_to_from.
  - apply iso_from_to.
  - apply iso_from_to.
Defined.
Next Obligation.
  split; apply unit_identity.
Qed.
Next Obligation.
  destruct X, Y; simpl; split;
  apply triangle_identity.
Qed.
Next Obligation.
  destruct X, Y, Z, W; simpl; split;
  apply pentagon_identity.
Qed.
