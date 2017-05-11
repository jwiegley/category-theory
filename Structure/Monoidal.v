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
  to unit_right ≈ bimap id (to unit_right) ∘ to (@tensor_assoc _ X Y I).
Proof.
  pose proof (@triangle_identity _).
Abort.

Theorem triangle_left `{Monoidal} {X Y} :
  bimap (to unit_left) id ≈ to unit_left ∘ to (@tensor_assoc _ I X Y).
Proof.
Abort.

Class SymmetricMonoidal `{Monoidal} := {
  sym_swap {X Y} : X ⨂ Y ≅ Y ⨂ X;

  sym_swap_swap_to   {X Y} :
    to (@sym_swap Y X) ∘ to (@sym_swap X Y) ≈ id;
  sym_swap_swap_from {X Y} :
    from (@sym_swap X Y) ∘ from (@sym_swap Y X) ≈ id
}.

Class RelevanceMonoidal `{Monoidal} := {
  comultiply {X} : X ~> X ⨂ X
}.

(* Wikipedia: "Cartesian monoidal categories have a number of special and
   important properties, such as the existence of diagonal maps (Δ) x : x → x
   ⊗ x and augmentations (e) x : x → I for any object x. In applications to
   computer science we can think of (Δ) as 'duplicating data' and (e) as
   'deleting' data. These maps make any object into a comonoid. In fact, any
   object in a cartesian monoidal category becomes a comonoid in a unique way.

   Moreover, one can show (e.g. Heunen-Vicary 12, p. 84) that any symmetric
   monoidal category equipped with suitably well-behaved diagonals and
   augmentations must in fact be cartesian monoidal." *)

(* jww (2017-05-10): Given the statement above about symmetric monoidal,
   perhaps some of the properties below can be derived. *)

Class CartesianMonoidal `{Monoidal} := {
  diagonal  {X} : X ~> X ⨂ X;
  eliminate {X} : X ~> I;

  unit_terminal {X} (f g : X ~> I) : f ≈ g;

  eliminate_left  {X Y} (f : X ~> Y) :
    to unit_left  ∘ bimap eliminate f ∘ diagonal ≈ f;
  eliminate_right {X Y} (f : X ~> Y) :
    to unit_right ∘ bimap f eliminate ∘ diagonal ≈ f;

  eliminate_diagonal {X Y Z W} (f : X ~> Y) (g : Z ~> W) :
    bimap (to unit_right ∘ bimap f eliminate)
          (to unit_left  ∘ bimap eliminate g) ∘ diagonal ≈ bimap f g;

  diagonal_natural {X Y} (f : X ~> Y) :
      bimap f f ∘ diagonal ≈ diagonal ∘ f
}.

Corollary eliminate_comp `{Monoidal} `{@CartesianMonoidal _} `{f : A ~> B} :
  eliminate ∘ f ≈ eliminate.
Proof. intros; apply unit_terminal. Qed.

Global Program Definition SymmetricCartesianMonoidal_Cartesian
       `{@Monoidal} (* `{@SymmetricMonoidal _} *) `{@CartesianMonoidal _} :
  @Cartesian C := {|
  Prod := fun X Y => tensor (X, Y);
  fork := fun _ _ _ f g => bimap f g ∘ diagonal;
  exl  := fun _ _ => to unit_right ∘ bimap id eliminate;
  exr  := fun _ _ => to unit_left  ∘ bimap eliminate id
|}.
Next Obligation.
  proper.
  rewrite X0, X1.
  reflexivity.
Qed.
Next Obligation.
  split; intros.
    split; rewrite X0; clear X0;
    rewrite <- !comp_assoc;
    rewrite (comp_assoc (bimap _ _));
    rewrite <- bimap_comp;
    rewrite id_left;
    rewrite eliminate_comp;
    rewrite comp_assoc.
      apply eliminate_right.
    apply eliminate_left.
  destruct X0.
  rewrite <- e, <- e0; clear e e0.
  rewrite bimap_comp.
  rewrite <- comp_assoc.
  rewrite diagonal_natural.
  rewrite comp_assoc.
  rewrite <- id_left at 1.
  apply compose_respects; [|reflexivity].
  symmetry.
  rewrite eliminate_diagonal.
  apply bimap_id_id.
Qed.

End Monoidal.

Notation "(⨂)" := (@tensor _ _) : functor_scope.
Notation "X ⨂ Y" := (@tensor _ _ (X%object, Y%object))
  (at level 30, right associativity) : object_scope.
Notation "X ⨂[ M ] Y" := (fobj[@tensor _ M] (X, Y))
  (at level 9, only parsing) : object_scope.

Local Obligation Tactic := program_simpl; simpl in *.

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
  proper; simpl in *.
  rewrite x0, y0.
  reflexivity.
Qed.
Next Obligation.
  rewrite !fmap_id; cat.
Qed.
Next Obligation.
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
  rewrite <- fork_comp; cat.
  rewrite <- comp_assoc; cat.
Qed.
Next Obligation.
  rewrite <- !fork_comp; cat.
  rewrite <- !comp_assoc; cat.
  rewrite <- !fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

Program Definition InternalProduct_SymmetricMonoidal
        `{C : Category} `{@Cartesian C} `{@Terminal C} :
  @SymmetricMonoidal C InternalProduct_Monoidal := {|
  sym_swap  := fun X Y =>
    {| to   := @swap C _ X Y
     ; from := @swap C _ Y X
     ; iso_to_from := swap_invol
     ; iso_from_to := swap_invol
    |}
|}.
Next Obligation. apply swap_invol. Qed.
Next Obligation. apply swap_invol. Qed.

Program Definition InternalProduct_CartesianMonoidal
        `{C : Category} `{@Cartesian C} `{@Terminal C} :
  @CartesianMonoidal C InternalProduct_Monoidal := {|
  diagonal  := fun _ => id △ id;
  eliminate := fun _ => one
|}.
Next Obligation. apply one_unique. Qed.
Next Obligation. cat; rewrite <- comp_assoc; cat. Qed.
Next Obligation. cat; rewrite <- comp_assoc; cat. Qed.
Next Obligation.
  rewrite <- fork_comp; cat.
  rewrite <- comp_assoc; cat.
  rewrite <- comp_assoc; cat.
Qed.
Next Obligation.
  rewrite <- fork_comp; cat.
  rewrite <- comp_assoc; cat.
  rewrite <- fork_comp; cat.
  rewrite <- comp_assoc; cat.
Qed.

Require Import Category.Functor.Bifunctor.

Local Obligation Tactic := intros; simplify; simpl in *.

(* Any product of monoidal categories is monoidal. *)

Program Instance Product_Monoidal
        `{C : Category} `{@Monoidal C} `{D : Category} `{@Monoidal D} :
  @Monoidal (C ∏ D) := {
  tensor :=
    {| fobj := fun p => (fst (fst p) ⨂ fst (snd p),
                         snd (fst p) ⨂ snd (snd p))
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
  proper; simplify; simpl in *.
    rewrite x1, x2.
    reflexivity.
  rewrite y0, y1.
  reflexivity.
Qed.
Next Obligation.
  split; rewrite bimap_id_id; reflexivity.
Qed.
Next Obligation.
  split; rewrite bimap_comp; reflexivity.
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
  isomorphism; simpl; simplify; simpl.
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
