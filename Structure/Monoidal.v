Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Naturality.
Require Export Category.Functor.Bifunctor.
Require Export Category.Construction.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Monoidal.

Context `{C : Category}.

Reserved Infix "⨂" (at level 30, right associativity).

Class Monoidal := {
  I : C;
  tensor : C ∏ C ⟶ C where "x ⨂ y" := (tensor (x, y));

  unit_left  {X} : I ⨂ X ≅ X;  (* lambda *)
  unit_right {X} : X ⨂ I ≅ X;  (* rho *)

  tensor_assoc {X Y Z} : (X ⨂ Y) ⨂ Z ≅ X ⨂ (Y ⨂ Z);  (* alpha *)

  (* alpha, lambda and rho are all natural isomorphisms. *)

  to_unit_left_natural {X Y} (g : X ~> Y) :
    g ∘ unit_left << I ⨂ X ~~> Y >> unit_left ∘ bimap id g;
  from_unit_left_natural {X Y} (g : X ~> Y) :
    bimap id g ∘ unit_left⁻¹ << X ~~> I ⨂ Y >> unit_left⁻¹ ∘ g;

  to_unit_right_natural {X Y} (g : X ~> Y) :
    g ∘ unit_right << X ⨂ I ~~> Y >> unit_right ∘ bimap g id;
  from_unit_right_natural {X Y} (g : X ~> Y) :
    bimap g id ∘ unit_right⁻¹ << X ~~> Y ⨂ I >> unit_right⁻¹ ∘ g;

  to_tensor_assoc_natural
    {X Y Z W V U} (g : X ~> Y) (h : Z ~> W) (i : V ~> U) :
    bimap g (bimap h i) ∘ tensor_assoc
      << (X ⨂ Z) ⨂ V ~~> Y ⨂ W ⨂ U >>
    tensor_assoc ∘ bimap (bimap g h) i;

  from_tensor_assoc_natural
    {X Y Z W V U} (g : X ~> Y) (h : Z ~> W) (i : V ~> U) :
    bimap (bimap g h) i ∘ tensor_assoc⁻¹
      << X ⨂ Z ⨂ V ~~> (Y ⨂ W) ⨂ U >>
    tensor_assoc⁻¹ ∘ bimap g (bimap h i);

  (* The above observe the following coherence conditions *)

  triangle_identity {X Y} :
    bimap unit_right id
      << (X ⨂ I) ⨂ Y ~~> X ⨂ Y >>
    bimap id unit_left ∘ tensor_assoc;

  pentagon_identity {X Y Z W} :
    bimap id tensor_assoc ∘ tensor_assoc ∘ bimap tensor_assoc id
      << ((X ⨂ Y) ⨂ Z) ⨂ W ~~> X ⨂ (Y ⨂ (Z ⨂ W)) >>
    tensor_assoc ∘ tensor_assoc
}.

Notation "(⨂)" := (@tensor _) : functor_scope.
Notation "X ⨂ Y" := (tensor (X, Y))
  (at level 30, right associativity) : object_scope.
Notation "f ⨂ g" := (bimap[(⨂)] f g)
  (at level 30, right associativity) : morphism_scope.

(* Define functors over the left and right objects of the tensor. *)

Global Program Definition Tensor_Left `{Monoidal}
        `{F : C ⟶ C} {Y : C} : C ⟶ C := {|
  fobj := fun X => (F X ⨂ Y)%object;
  fmap := fun _ _ f => fmap[F] f ⨂ id
|}.
Next Obligation.
  proper.
  apply bimap_respects.
    rewrite X0; reflexivity.
  reflexivity.
Qed.
Next Obligation. normal; reflexivity. Qed.

Global Program Instance Tensor_Left_Map `{Monoidal}
        `{@CanonicalMap C P} {Y : C} :
  @CanonicalMap C (fun X => P X ⨂ Y)%object := {
  map := fun _ _ f => map f ⨂ id;
  is_functor := @Tensor_Left _ is_functor _
}.
Next Obligation.
  unfold Tensor_Left_Map_obligation_1.
  apply bifunctor_respects; simpl; split.
    apply fobj_related.
  reflexivity.
Defined.
Next Obligation.
  unfold Tensor_Left_Map_obligation_1;
  unfold Tensor_Left_Map_obligation_2; simpl.
  rewrite fmap_related.
  normal; reflexivity.
Qed.

Global Program Instance Tensor_Right `{Monoidal}
        `{F : C ⟶ C} {X : C} : Functor := {
  fobj := fun Y => (X ⨂ F Y)%object;
  fmap := fun _ _ f => id ⨂ fmap[F] f
}.
Next Obligation.
  proper.
  apply bimap_respects.
    reflexivity.
  rewrite X1; reflexivity.
Qed.
Next Obligation. normal; reflexivity. Qed.

Global Program Instance Tensor_Right_Map `{Monoidal}
        `{@CanonicalMap C P} {X : C} :
  @CanonicalMap C (fun Y => X ⨂ P Y)%object := {
  map := fun _ _ f => id ⨂ map f;
  is_functor := @Tensor_Right _ is_functor _
}.
Next Obligation.
  unfold Tensor_Left_Map_obligation_1.
  apply bifunctor_respects; simpl; split.
    reflexivity.
  apply fobj_related.
Defined.
Next Obligation.
  unfold Tensor_Left_Map_obligation_1;
  unfold Tensor_Left_Map_obligation_2; simpl.
  rewrite fmap_related.
  normal; reflexivity.
Qed.

Global Program Definition Tensor_Both `{Monoidal} `{F : C ⟶ C} : C ⟶ C := {|
  fobj := fun X => (F X ⨂ F X)%object;
  fmap := fun _ _ f => fmap[F] f ⨂ fmap[F] f
|}.
Next Obligation.
  proper.
  apply bimap_respects;
  rewrite X0; reflexivity.
Qed.
Next Obligation. normal; reflexivity. Qed.

Global Program Instance Tensor_Both_Map `{Monoidal} `{@CanonicalMap C P} :
  @CanonicalMap C (fun X => P X ⨂ P X)%object := {
  map := fun _ _ f => map f ⨂ map f;
  is_functor := @Tensor_Both _ is_functor
}.
Next Obligation.
  apply bifunctor_respects; simpl; split;
  apply fobj_related.
Defined.
Next Obligation.
  rewrite fmap_related.
  normal; reflexivity.
Qed.

Theorem monoidal_naturality `{M : Monoidal} :
  natural (@unit_left M) *
  natural (@unit_right M) *
  natural (@tensor_assoc M).
Proof. prove_naturality M normal. Qed.

Lemma tensor_id_left_inj `{Monoidal} {X Y} (f g : X ~> Y) :
  id[I] ⨂ f ≈ id[I] ⨂ g -> f ≈ g.
Proof.
  intros.
  rewrite <- id_right; symmetry;
  rewrite <- id_right; symmetry.
  rewrite <- (iso_to_from unit_left).
  rewrite !comp_assoc.
  rewrite !to_unit_left_natural.
  rewrite X0.
  reflexivity.
Qed.

Lemma tensor_id_right_inj `{Monoidal} {X Y} (f g : X ~> Y) :
  f ⨂ id[I] ≈ g ⨂ id[I] -> f ≈ g.
Proof.
  intros.
  rewrite <- id_right; symmetry;
  rewrite <- id_right; symmetry.
  rewrite <- (iso_to_from unit_right).
  rewrite !comp_assoc.
  rewrite !to_unit_right_natural.
  rewrite X0.
  reflexivity.
Qed.

(* The following proofs are from the book "Tensor Categories", by Pavel
   Etingof, Shlomo Gelaki, Dmitri Nikshych, and Victor Ostrik. *)

(* Proposition 2.2.2 *)

Proposition id_unit_left `{Monoidal} {X} :
  id ⨂ unit_left ≈ @unit_left _ (I ⨂ X).
Proof.
  (* "It follows from naturality of the left unit constraint l that the
     following diagram commutes..." *)
  assert (unit_left ∘ id ⨂ unit_left
            << I ⨂ (I ⨂ X) ~~> X >>
          unit_left ∘ unit_left).
    rewrite to_unit_left_natural; reflexivity.

  (* "Since lX is an isomorphism, the first identity follows." *)
  symmetry.
  do 2 (rewrite <- id_left; symmetry).
  rewrite <- (iso_from_to unit_left).
  rewrite <- !comp_assoc.
  rewrite X0; reflexivity.
Qed.

Proposition id_unit_right `{Monoidal} {X} :
  unit_right ⨂ id ≈ @unit_right _ (X ⨂ I).
Proof.
  (* "It follows from naturality of the left unit constraint l that the
     following diagram commutes..." *)
  assert (unit_right ∘ unit_right ⨂ id
            << (X ⨂ I) ⨂ I ~~> X >>
          unit_right ∘ unit_right).
    rewrite to_unit_right_natural; reflexivity.

  (* "The second one follows similarly from naturality of r." *)
  symmetry.
  do 2 (rewrite <- id_left; symmetry).
  rewrite <- (iso_from_to unit_right).
  rewrite <- !comp_assoc.
  rewrite X0; reflexivity.
Qed.

(* Proposition 2.2.4 *)

Lemma bimap_id_unit_left `{Monoidal} {X Y Z} :
  id ⨂ (unit_left ⨂ id)
    << X ⨂ ((I ⨂ Y) ⨂ Z) ~~> X ⨂ (Y ⨂ Z) >>
  id ⨂ unit_left ∘ id ⨂ tensor_assoc.
Proof.
  (* "Consequently, the lower right triangle commutes as well." *)
  pose proof (to_tensor_assoc_natural (id[X]) (@unit_left _ Y) (id[Z])) as X0.
  assert (X1 : ∀ X Y Z W (f g : (X ⨂ Y) ⨂ Z ~> W),
             f ≈ g -> f ∘ tensor_assoc⁻¹ ≈ g ∘ tensor_assoc⁻¹).
    intros; rewrite X2; reflexivity.
  apply X1 in X0.
  rewrite <- !comp_assoc in X0.
  rewrite iso_to_from, id_right in X0.
  rewrite X0; clear X0.
  rewrite comp_assoc; normal.

  pose proof (to_tensor_assoc_natural
                (@unit_right _ X) (id[Y]) (id[Z])) as X0.
  rewrite bimap_id_id in X0.
  rewrite triangle_identity in X0.
  rewrite triangle_identity in X0.
  rewrite <- comp_assoc in X0.
  rewrite <- pentagon_identity in X0.
  rewrite !comp_assoc in X0.
  normal.
  symmetry in X0.
  rewrite bimap_comp_id_right in X0.
  rewrite comp_assoc in X0.

  assert (X2 : ∀ (f g : (X ⨂ I ⨂ Y) ⨂ Z ~{ C }~> X ⨂ Y ⨂ Z),
             f ∘ tensor_assoc ⨂ id ≈ g ∘ tensor_assoc ⨂ id
             -> f ≈ g).
    intros.
    assert (∀ X Y Z W V (f g : ((X ⨂ Y) ⨂ Z) ⨂ V ~> W),
               f ≈ g -> f ∘ (tensor_assoc⁻¹ ⨂ id[V]) ≈
                        g ∘ (tensor_assoc⁻¹ ⨂ id[V])).
      intros; rewrite X4; reflexivity.
    apply X3 in X2.
    normal.
    rewrite !iso_to_from in X2.
    rewrite !bimap_id_id, !id_right in X2.
    assumption.
  apply X2 in X0; clear X2.
  rewrite X0; clear X0.

  rewrite <- comp_assoc.
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

Theorem triangle_identity_left `{Monoidal} {X Y} :
  unit_left ⨂ id
    << (I ⨂ X) ⨂ Y ~~> X ⨂ Y >>
  unit_left ∘ tensor_assoc.
Proof.
  (* "Setting X = 1 and applying the functor L−1 to the lower right triangle,
     1 we obtain commutativity of the triangle (2.12)." *)
  pose proof (@bimap_id_unit_left _ I X Y).
  normal.
  apply tensor_id_left_inj in X0.
  assumption.
Qed.

Theorem inverse_triangle_identity `{Monoidal} {X Y} :
  id ⨂ unit_left
    << X ⨂ (I ⨂ Y) ~~> X ⨂ Y >>
  unit_right ⨂ id ∘ tensor_assoc⁻¹.
Proof.
  rewrite triangle_identity.
  rewrite <- comp_assoc.
  rewrite iso_to_from; cat.
Qed.

Theorem inverse_pentagon_identity `{Monoidal} {X Y Z W} :
  tensor_assoc⁻¹ ⨂ id[W] ∘ tensor_assoc⁻¹ ∘ id[X] ⨂ tensor_assoc⁻¹
      << X ⨂ (Y ⨂ (Z ⨂ W)) ~~> ((X ⨂ Y) ⨂ Z) ⨂ W >>
  tensor_assoc⁻¹ ∘ tensor_assoc⁻¹.
Proof.
  apply (iso_epic tensor_assoc).
  rewrite <- !comp_assoc.
  rewrite iso_from_to, id_right.
  apply (iso_epic tensor_assoc).
  rewrite iso_from_to.
  rewrite <- !comp_assoc.
  rewrite <- pentagon_identity.
  normal.
  rewrite iso_from_to; normal.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (tensor_assoc⁻¹)).
  rewrite iso_from_to; normal.
  rewrite iso_from_to; normal.
  reflexivity.
Qed.

Lemma bimap_unit_right_id `{Monoidal} {X Y Z} :
  (id ⨂ unit_right) ⨂ id
    << (X ⨂ (Y ⨂ I)) ⨂ Z ~~> (X ⨂ Y) ⨂ Z >>
  unit_right ⨂ id ∘ tensor_assoc⁻¹ ⨂ id.
Proof.
  (* "Consequently, the lower right triangle commutes as well." *)
  pose proof (from_tensor_assoc_natural (id[X]) (@unit_right _ Y) (id[Z])) as X0.
  assert (X1 : ∀ X Y Z W (f g : X ⨂ (Y ⨂ Z) ~> W),
             f ≈ g -> f ∘ tensor_assoc ≈ g ∘ tensor_assoc).
    intros; rewrite X2; reflexivity.
  apply X1 in X0.
  rewrite <- !comp_assoc in X0.
  rewrite iso_from_to, id_right in X0.
  rewrite X0; clear X0.
  rewrite comp_assoc; normal.

  pose proof (from_tensor_assoc_natural
                (id[X]) (id[Y]) (@unit_left _ Z)) as X0.
  rewrite bimap_id_id in X0.
  rewrite inverse_triangle_identity in X0.
  rewrite inverse_triangle_identity in X0.
  rewrite <- comp_assoc in X0.
  rewrite <- inverse_pentagon_identity in X0.
  rewrite !comp_assoc in X0.
  normal.
  symmetry in X0.
  rewrite bimap_comp_id_left in X0.
  rewrite comp_assoc in X0.

  assert (X2 : ∀ (f g : X ⨂ ((Y ⨂ I) ⨂ Z) ~{ C }~> (X ⨂ Y) ⨂ Z),
             f ∘ id ⨂ tensor_assoc⁻¹ ≈ g ∘ id ⨂ tensor_assoc⁻¹
             -> f ≈ g).
    intros.
    assert (∀ X Y Z W V (f g : X ⨂ (Y ⨂ (Z ⨂ V)) ~> W),
               f ≈ g -> f ∘ (id[X] ⨂ tensor_assoc) ≈
                        g ∘ (id[X] ⨂ tensor_assoc)).
      intros; rewrite X4; reflexivity.
    apply X3 in X2.
    normal.
    rewrite !iso_from_to in X2.
    rewrite !bimap_id_id, !id_right in X2.
    assumption.
  apply X2 in X0; clear X2.
  rewrite X0; clear X0.

  rewrite <- comp_assoc.
  rewrite iso_from_to, id_right.
  reflexivity.
Qed.

Theorem triangle_identity_right `{Monoidal} {X Y} :
  id ⨂ unit_right
    << X ⨂ (Y ⨂ I) ~~> X ⨂ Y >>
  unit_right ∘ tensor_assoc⁻¹.
Proof.
  pose proof (@bimap_unit_right_id _ X Y I).
  normal.
  apply tensor_id_right_inj in X0.
  assumption.
Qed.

Theorem bimap_triangle_right `{Monoidal} {X Y} :
  unit_right
    << (X ⨂ Y) ⨂ I ~~> X ⨂ Y >>
  bimap id unit_right ∘ to tensor_assoc.
Proof.
  rewrite triangle_identity_right.
  rewrite <- comp_assoc.
  rewrite iso_from_to; cat.
Qed.

Theorem bimap_triangle_left `{Monoidal} {X Y} :
  unit_left
    << I ⨂ (X ⨂ Y) ~~> X ⨂ Y >>
  bimap unit_left id ∘ tensor_assoc⁻¹.
Proof.
  rewrite triangle_identity_left.
  rewrite <- comp_assoc.
  rewrite iso_to_from; cat.
Qed.

Corollary unit_identity `{Monoidal} :
  to (@unit_left _ I) ≈ to (@unit_right _ I).
Proof.
  pose proof (@bimap_id_unit_left _ I I I).
  pose proof (@triangle_identity _ I I).
  normal.
  rewrite id_unit_left in X0.
  rewrite <- X0 in X; clear X0.
  apply tensor_id_left_inj in X.
  apply tensor_id_right_inj in X.
  apply X.
Qed.

End Monoidal.

Notation "(⨂)" := (@tensor _ _) : functor_scope.
Notation "X ⨂ Y" := (@tensor _ _ (X%object, Y%object))
  (at level 30, right associativity) : object_scope.
Notation "X ⨂[ M ] Y" := (fobj[@tensor _ M] (X, Y))
  (at level 9, only parsing, right associativity) : object_scope.
Notation "f ⨂ g" := (bimap[(⨂)] f g)
  (at level 30, right associativity) : morphism_scope.
Notation "f ⨂[ M ] g" := (bimap[@tensor _ M] f g)
  (at level 9, only parsing, right associativity) : morphism_scope.
