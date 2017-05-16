Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Morphisms.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Construction.Product.
Require Export Category.Instance.Nat.

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

(* "The commutativity of the triangle (2.13) is proved similarly."

     Theorem triangle_right `{Monoidal} {X Y} :
       unit_right
         << (X ⨂ Y) ⨂ I ~~> X ⨂ Y >>
       bimap id unit_right ∘ to tensor_assoc.

   This will require repeating most of the above, but for a commuting
   pentagram ((X ⨂ Y) ⨂ Z) ⨂ I ~~> X ⨂ (Y ⨂ (Z ⨂ I)). *)

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

Class SymmetricMonoidal `{Monoidal} := {
  twist {X Y} : X ⨂ Y ≅ Y ⨂ X;
  twist_natural : natural (@twist);

  twist_invol {X Y} : twist ∘ twist ≈ id[X ⨂ Y];

  hexagon_identity {X Y Z} :
    tensor_assoc ∘ twist ∘ tensor_assoc
      << (X ⨂ Y) ⨂ Z ~~> Y ⨂ (Z ⨂ X) >>
    id ⨂ twist ∘ tensor_assoc ∘ twist ⨂ id
}.

(* A semi-cartesian monoidal category is basically an assertion that the unit
   is terminal. *)

Class SemiCartesianMonoidal `{Monoidal} := {
  eliminate {X} : X ~> I;

  unit_terminal {X} (f g : X ~> I) : f ≈ g;

  proj_left  {X Y} : X ⨂ Y ~> X := unit_right ∘ id ⨂ eliminate;
  proj_right {X Y} : X ⨂ Y ~> Y := unit_left  ∘ eliminate ⨂ id;

  proj_left_tensor_id {X Y Z} :
    proj_left ⨂ id ≈ id[X] ⨂ @proj_right Y Z ∘ tensor_assoc;
  proj_right_tensor_id {X Y Z} :
    id ⨂ proj_right ≈ @proj_left X Y ⨂ id[Z] ∘ tensor_assoc⁻¹;

  proj_left_left {X Y Z} :
    proj_left ∘ proj_left ≈ @proj_left X (Y ⨂ Z) ∘ tensor_assoc;
  proj_right_right {X Y Z} :
    proj_right ∘ proj_right ≈ @proj_right (X ⨂ Y) Z ∘ tensor_assoc⁻¹
}.

Class RelevanceMonoidal `{Monoidal} := {
  is_symmetric :> SymmetricMonoidal;

  diagonal {X} : X ~> X ⨂ X;
  diagonal_natural : natural (@diagonal);

  (* These properties are given by Kosta Došen and Zoran Petrić in their 2007
     publication, "Relevant Categories and Partial Functions". *)

  diagonal_unit : @diagonal I ≈ unit_left⁻¹;

  diagonal_tensor_assoc {X} :
   id ⨂ diagonal ∘ diagonal ≈ tensor_assoc ∘ diagonal ⨂ id ∘ @diagonal X;

  twist_diagonal {X} :
    twist ∘ diagonal ≈ @diagonal X;

  twist2 {X Y Z W} : (X ⨂ Y) ⨂ (Z ⨂ W) ~> (X ⨂ Z) ⨂ (Y ⨂ W) :=
    tensor_assoc⁻¹
      ∘ id ⨂ (tensor_assoc ∘ twist ⨂ id ∘ tensor_assoc⁻¹)
      ∘ tensor_assoc;

  diagonal_twist2 {X Y} :
    @diagonal (X ⨂ Y) ≈ twist2 ∘ diagonal ⨂ diagonal
}.

Lemma twist2_natural `{Monoidal} `{@RelevanceMonoidal _} :
  natural (@twist2 _ _).
Proof.
  unfold twist2; simpl; intros; normal.
  rewrite from_tensor_assoc_natural.
  rewrite <- !comp_assoc.
  rewrite <- to_tensor_assoc_natural.
  normal.
  apply compose_respects; [|reflexivity].
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  normal.
  apply bimap_respects; [reflexivity|].
  rewrite to_tensor_assoc_natural.
  rewrite <- !comp_assoc.
  rewrite <- from_tensor_assoc_natural.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  normal.
  apply bimap_respects; [|reflexivity].
  pose proof (fst twist_natural _ _ h _ _ i); simpl in X0.
  normal; assumption.
Qed.

(* Wikipedia: "Cartesian monoidal categories have a number of special and
   important properties, such as the existence of diagonal maps (Δ) x : x → x
   ⨂ x and augmentations (e) x : x → I for any object x. In applications to
   computer science we can think of (Δ) as 'duplicating data' and (e) as
   'deleting' data. These maps make any object into a comonoid. In fact, any
   object in a cartesian monoidal category becomes a comonoid in a unique way.

   Moreover, one can show (e.g. Heunen-Vicary 12, p. 84) that any symmetric
   monoidal category equipped with suitably well-behaved diagonals and
   augmentations must in fact be cartesian monoidal." *)

Class CartesianMonoidal `{Monoidal} := {
  is_semicartesian :> @SemiCartesianMonoidal _;
  is_relevance     :> @RelevanceMonoidal _;

  proj_left_diagonal  {X} : proj_left  ∘ diagonal ≈ id[X];
  proj_right_diagonal {X} : proj_right ∘ diagonal ≈ id[X];

  unit_left_twist  {X} : unit_left  ∘ @twist _ _ X I ≈ unit_right;
  unit_right_twist {X} : unit_right ∘ @twist _ _ I X ≈ unit_left
}.

Notation "∆ X" := (@diagonal _ _ X) (at level 9, format "∆ X") : morphism_scope.

Corollary eliminate_comp `{Monoidal} `{@CartesianMonoidal _} `{f : A ~> B} :
  eliminate ∘ f ≈ eliminate.
Proof. intros; apply unit_terminal. Qed.

Corollary unit_left_eliminate `{Monoidal} `{@CartesianMonoidal _}
          {X Y} (f : X ~> Y) :
  unit_left ∘ eliminate ⨂ f ∘ ∆X ≈ f.
Proof.
  symmetry.
  rewrite <- id_left at 1.
  rewrite <- proj_right_diagonal.
  unfold proj_right.
  rewrite <- !comp_assoc.
  pose proof diagonal_natural; simpl in X0.
  rewrite <- X0; clear X0.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

Corollary unit_right_eliminate `{Monoidal} `{@CartesianMonoidal _}
          {X Y} (f : X ~> Y) :
  unit_right ∘ f ⨂ eliminate ∘ ∆X ≈ f.
Proof.
  symmetry.
  rewrite <- id_left at 1.
  rewrite <- proj_left_diagonal.
  unfold proj_left.
  rewrite <- !comp_assoc.
  pose proof diagonal_natural; simpl in X0.
  rewrite <- X0; clear X0.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

Lemma eliminate_right_diagonal `{Monoidal} `{@CartesianMonoidal _} {X} :
  id[X] ⨂ eliminate ∘ ∆X ≈ unit_right⁻¹.
Proof.
  apply (iso_monic unit_right).
  rewrite comp_assoc.
  rewrite unit_right_eliminate.
  rewrite iso_to_from.
  reflexivity.
Qed.

Lemma eliminate_left_diagonal `{Monoidal} `{@CartesianMonoidal _} {X} :
  eliminate ⨂ id[X] ∘ ∆X ≈ unit_left⁻¹.
Proof.
  apply (iso_monic unit_left).
  rewrite comp_assoc.
  rewrite unit_left_eliminate.
  rewrite iso_to_from.
  reflexivity.
Qed.

Lemma proj_left_id_diagonal `{Monoidal} `{@CartesianMonoidal _} {X Y} :
  proj_left ⨂ id ∘ @diagonal _ _ (X ⨂ Y) ≈ tensor_assoc ∘ diagonal ⨂ id.
Proof.
  rewrite diagonal_twist2.
  remember (_ ∘ _ ∘ tensor_assoc) as p.
  pose proof (@twist2_natural _ _ X _ id X _ id Y _ eliminate Y _ id); simpl in X0.
  rewrite !bimap_id_id in X0.
  rewrite !id_left, !id_right in X0.
  unfold proj_left.
  normal.
  rewrite bimap_comp_id_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc ((_ ⨂ _) ⨂ _)).
  unfold twist2 in X0.
  rewrite Heqp; clear Heqp p.
  rewrite X0; clear X0.
  normal.
  rewrite eliminate_left_diagonal.
  rewrite triangle_identity.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc tensor_assoc).
  rewrite iso_to_from.
  normal.
  rewrite <- triangle_identity_left.
  normal.
  rewrite unit_left_twist.
  rewrite triangle_identity.
  rewrite <- !comp_assoc.
  rewrite iso_to_from.
  normal.
  rewrite to_tensor_assoc_natural.
  normal.
  rewrite iso_to_from.
  reflexivity.
Qed.

Lemma proj_right_id_diagonal `{Monoidal} `{@CartesianMonoidal _} {X Y} :
  proj_right ⨂ id ∘ @diagonal _ _ (X ⨂ Y)
    ≈ tensor_assoc ∘ twist ⨂ id ∘ tensor_assoc⁻¹ ∘ id ⨂ diagonal.
Proof.
  rewrite diagonal_twist2.
  remember (_ ∘ _ ∘ tensor_assoc) as p.
  pose proof (@twist2_natural _ _ X _ eliminate X _ id Y _ id Y _ id);
  simpl in X0.
  rewrite !bimap_id_id in X0.
  rewrite !id_right in X0.
  unfold twist2 in X0.
  unfold proj_right.
  normal.
  rewrite bimap_comp_id_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc ((_ ⨂ _) ⨂ _)).
  rewrite Heqp; clear Heqp p.
  rewrite X0; clear X0.
  normal.
  rewrite eliminate_left_diagonal.
  rewrite triangle_identity_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc tensor_assoc).
  rewrite iso_to_from.
  normal.
  rewrite <- to_unit_left_natural.
  rewrite <- !comp_assoc.
  repeat (apply compose_respects; [reflexivity|]).
  rewrite comp_assoc.
  rewrite <- triangle_identity_left.
  normal.
  rewrite iso_to_from.
  reflexivity.
Qed.

Corollary proj_right_left_diagonal `{Monoidal} `{@CartesianMonoidal _} {X Y} :
  proj_right ⨂ proj_left ∘ ∆(X ⨂ Y) ≈ twist.
Proof.
  rewrite <- bimap_id_left_right.
  rewrite <- comp_assoc.
  rewrite proj_right_id_diagonal.
  unfold proj_left, proj_right.
  normal.
  rewrite bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ tensor_assoc).
  rewrite to_tensor_assoc_natural.
  normal.
  rewrite <- comp_assoc.
  rewrite triangle_identity_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (tensor_assoc⁻¹)).
  rewrite iso_from_to.
  normal.
  rewrite <- bimap_id_right_left.
  rewrite !comp_assoc.
  rewrite <- to_unit_right_natural.
  symmetry.
  rewrite <- id_right at 1.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  symmetry.
  normal.
  pose proof (@from_tensor_assoc_natural _ X _ Y _ Y _ id id eliminate).
  rewrite bimap_id_id in X0.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (bimap _ _)).
  rewrite X0; clear X0.
  normal.
  rewrite eliminate_right_diagonal.
  rewrite <- triangle_identity_right.
  normal.
  rewrite iso_to_from.
  normal; reflexivity.
Qed.

Corollary proj_left_natural `{Monoidal} `{@CartesianMonoidal _} {X Y Z W}
          (f : X ~> Y) (g : Z ~> W) :
  proj_left ∘ f ⨂ g ≈ f ∘ proj_left.
Proof.
  unfold proj_left.
  rewrite comp_assoc.
  rewrite to_unit_right_natural.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

Corollary proj_right_natural `{Monoidal} `{@CartesianMonoidal _} {X Y Z W}
          (f : X ~> Y) (g : Z ~> W) :
  proj_right ∘ f ⨂ g ≈ g ∘ proj_right.
Proof.
  unfold proj_right.
  rewrite comp_assoc.
  rewrite to_unit_left_natural.
  normal.
  rewrite eliminate_comp.
  reflexivity.
Qed.

Corollary proj_left_right_diagonal
          `{Monoidal} `{@CartesianMonoidal _} {X Y} :
  proj_left ⨂ proj_right ∘ ∆(X ⨂ Y) ≈ id[X ⨂ Y].
Proof.
  rewrite <- bimap_id_left_right.
  rewrite <- comp_assoc.
  rewrite proj_left_id_diagonal.
  rewrite comp_assoc.
  unfold proj_right.
  rewrite bimap_comp_id_left.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ tensor_assoc).
  rewrite to_tensor_assoc_natural.
  normal.
  rewrite <- comp_assoc.
  rewrite eliminate_right_diagonal.
  normal.
  rewrite <- triangle_identity.
  normal.
  rewrite iso_to_from.
  normal; reflexivity.
Qed.

Local Obligation Tactic := intros; simplify; simpl in *; intros; normal.

Program Instance diagonal_monic `{Monoidal} `{@CartesianMonoidal _} {X} :
  Monic ∆X.
Next Obligation.
  rewrite <- unit_left_eliminate.
  rewrite <- (unit_left_eliminate g2).
  rewrite <- (@eliminate_comp _ _ _ _ g1) at 1.
  rewrite <- (@eliminate_comp _ _ _ _ g2) at 1.
  rewrite <- (id_left g1) at 2.
  rewrite <- (id_left g2) at 2.
  rewrite !bimap_comp.
  rewrite <- !comp_assoc.
  srewrite diagonal_natural.
  rewrite X0.
  srewrite diagonal_natural.
  reflexivity.
Qed.

Corollary proj_left_twist `{Monoidal} `{@CartesianMonoidal _} {X Y} :
  proj_left ∘ twist ≈ @proj_right _ _ X Y.
Proof.
  unfold proj_left, proj_right.
  rewrite <- proj_right_left_diagonal.
  normal.
  rewrite eliminate_comp.
  rewrite unit_right_eliminate.
  reflexivity.
Qed.

Corollary proj_right_twist `{Monoidal} `{@CartesianMonoidal _} {X Y} :
  proj_right ∘ twist ≈ @proj_left _ _ X Y.
Proof.
  unfold proj_left, proj_right.
  rewrite <- proj_right_left_diagonal.
  normal.
  rewrite eliminate_comp.
  rewrite unit_left_eliminate.
  reflexivity.
Qed.

Corollary bimap_twist `{Monoidal} `{@CartesianMonoidal _}
          {X Y Z W} (f : X ~> Z) (g : Y ~> W) :
  twist ∘ g ⨂ f ∘ twist ≈ f ⨂ g.
Proof.
  pose proof (fst twist_natural _ _ f _ _ g); simpl in X0.
  normal.
  rewrite <- comp_assoc.
  rewrite X0.
  rewrite comp_assoc.
  rewrite twist_invol; cat.
Qed.

Bind Scope object_scope with C.

Global Program Definition SymmetricCartesianMonoidal_Cartesian
       `{Monoidal} `{@CartesianMonoidal _} :
  @Cartesian C := {|
  Prod := fun X Y => (X ⨂ Y)%object;
  fork := fun X _ _ f g => f ⨂ g ∘ ∆X;
  exl  := fun _ _ => proj_left;
  exr  := fun _ _ => proj_right
|}.
Next Obligation.
  apply is_relevance.
Defined.
Next Obligation.
  proper.
  rewrite X0, X1.
  reflexivity.
Qed.
Next Obligation.
  - rewrite X0; clear X0;
    rewrite comp_assoc.
    rewrite proj_left_natural.
    rewrite <- comp_assoc.
    rewrite proj_left_diagonal; cat.
  - rewrite X0; clear X0;
    rewrite comp_assoc.
    rewrite proj_right_natural.
    rewrite <- comp_assoc.
    rewrite proj_right_diagonal; cat.
  - rewrite <- x, <- y.
    rewrite bimap_comp.
    rewrite <- !comp_assoc.
    srewrite diagonal_natural.
    rewrite comp_assoc.
    rewrite proj_left_right_diagonal; cat.
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
Notation "∆ X" := (@diagonal _ _ _ X)
  (at level 9, format "∆ X") : morphism_scope.

Local Obligation Tactic := intros; simplify; simpl in *; intros; normal.

(* This reflects the fact that categories are themselves "monoidoids", or
   monoidal with respect to identity and composition.  *)

Program Definition Composition_Monoidal `{C : Category} :
  @Monoidal ([C, C]) := {|
  tensor :=
    {| fobj := fun p => Compose (fst p) (snd p)
     ; fmap := fun F G N =>
         {| transform := fun x =>
              fst N (snd G x) ∘ fmap[fst F] (snd N x) |}
     |};
  I := Id
|}.
Next Obligation.
  rewrite <- naturality.
  rewrite <- !comp_assoc.
  rewrite <- naturality.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- naturality.
  rewrite comp_assoc.
  normal.
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
Next Obligation. cat. Defined.
Next Obligation.
  normal.
  rewrite <- !comp_assoc.
  rewrite fmap_comp.
  reflexivity.
Qed.
Next Obligation.
  normal.
  rewrite <- !comp_assoc.
  rewrite fmap_comp.
  reflexivity.
Qed.
Next Obligation. normal; reflexivity. Qed.
Next Obligation. normal; rewrite !fmap_id; reflexivity. Qed.

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
Next Obligation. cat. Qed.
Next Obligation.
  rewrite <- fork_comp; cat.
  rewrite <- comp_assoc; cat.
  rewrite <- fork_comp; cat.
Qed.
Next Obligation. cat. Qed.
Next Obligation.
  repeat (rewrite <- !fork_comp; cat;
          rewrite <- !comp_assoc; cat).
Qed.
Next Obligation.
  repeat (rewrite <- !fork_comp; cat;
          rewrite <- !comp_assoc; cat).
Qed.
Next Obligation.
  repeat (rewrite <- !fork_comp; cat;
          rewrite <- !comp_assoc; cat).
Qed.
Next Obligation.
  repeat (rewrite <- !fork_comp; cat;
          rewrite <- !comp_assoc; cat).
Qed.
Next Obligation.
  repeat (rewrite <- !fork_comp; cat;
          rewrite <- !comp_assoc; cat).
Qed.

Program Definition InternalProduct_SymmetricMonoidal
        `{C : Category} `{@Cartesian C} `{@Terminal C} :
  @SymmetricMonoidal C InternalProduct_Monoidal := {|
  twist := fun X Y =>
    {| to   := @swap C _ X Y
     ; from := @swap C _ Y X
     ; iso_to_from := swap_invol
     ; iso_from_to := swap_invol
    |}
|}.
Next Obligation.
  unfold swap; split; intros;
  repeat (rewrite <- !fork_comp; cat;
          rewrite <- !comp_assoc; cat).
Qed.
Next Obligation.
  unfold swap.
  repeat (rewrite <- !fork_comp; cat;
          rewrite <- !comp_assoc; cat).
Qed.
Next Obligation.
  unfold swap.
  repeat (rewrite <- !fork_comp; cat;
          rewrite <- !comp_assoc; cat).
Qed.

Program Definition InternalProduct_CartesianMonoidal
        `{C : Category} `{@Cartesian C} `{@Terminal C} :
  @CartesianMonoidal C InternalProduct_Monoidal := {|
  is_semicartesian := {| eliminate := fun _ => one |};
  is_relevance := {| diagonal  := fun _ => id △ id |}
|}.
Next Obligation. cat. Qed.
Next Obligation.
  rewrite <- !fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.
Next Obligation.
  rewrite <- !fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.
Next Obligation.
  rewrite <- !comp_assoc; cat.
  rewrite <- !fork_comp; cat.
Qed.
Next Obligation.
  rewrite <- !comp_assoc; cat.
  rewrite <- !fork_comp; cat.
Qed.
Next Obligation.
  apply InternalProduct_SymmetricMonoidal.
Defined.
Next Obligation.
  rewrite <- !fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.
Next Obligation.
  apply fork_respects.
    apply one_unique.
  reflexivity.
Qed.
Next Obligation.
  rewrite <- !fork_comp; cat.
  rewrite <- !comp_assoc; cat.
  rewrite <- !fork_comp; cat.
Qed.
Next Obligation.
  apply swap_fork.
Qed.
Next Obligation.
  unfold swap.
  repeat (rewrite <- !fork_comp; cat;
          rewrite <- !comp_assoc; cat).
Qed.
Next Obligation.
  unfold proj_left; simpl.
  rewrite <- !comp_assoc; cat.
  rewrite <- !fork_comp; cat.
Qed.
Next Obligation.
  unfold proj_right; simpl.
  rewrite <- !comp_assoc; cat.
  rewrite <- !fork_comp; cat.
Qed.
Next Obligation.
  unfold proj_left; simpl.
  repeat (rewrite <- !fork_comp; cat;
          rewrite <- !comp_assoc; cat).
Qed.
Next Obligation.
  unfold proj_right, proj_left, swap; simpl.
  repeat (rewrite <- !fork_comp; cat;
          rewrite <- !comp_assoc; cat).
Qed.

Require Import Category.Functor.Bifunctor.

(* Any product of monoidal categories is monoidal. *)

Program Instance Product_Monoidal
        `{C : Category} `{@Monoidal C} `{D : Category} `{@Monoidal D} :
  @Monoidal (C ∏ D) := {
  tensor :=
    {| fobj := fun p => (fst (fst p) ⨂ fst (snd p),
                         snd (fst p) ⨂ snd (snd p))%object
     ; fmap := fun _ _ f => (fst (fst f) ⨂ fst (snd f),
                             snd (fst f) ⨂ snd (snd f)) |};
  I := (@I C _, @I D _)
}.
Next Obligation. exact H. Defined.
Next Obligation. exact H0. Defined.
Next Obligation.
  proper; simplify; simpl in *.
    rewrite x1, x2.
    reflexivity.
  rewrite y0, y1.
  reflexivity.
Qed.
Next Obligation. split; normal; reflexivity. Qed.
Next Obligation. split; normal; reflexivity. Qed.
Next Obligation.
  isomorphism; simpl; simplify; simpl.
  - apply unit_left.
  - apply unit_left.
  - apply (unit_left⁻¹).
  - apply (unit_left⁻¹).
  - apply iso_to_from.
  - apply iso_to_from.
  - apply iso_from_to.
  - apply iso_from_to.
Defined.
Next Obligation.
  isomorphism; simpl; simplify; simpl.
  - apply unit_right.
  - apply unit_right.
  - apply (unit_right⁻¹).
  - apply (unit_right⁻¹).
  - apply iso_to_from.
  - apply iso_to_from.
  - apply iso_from_to.
  - apply iso_from_to.
Defined.
Next Obligation.
  isomorphism; simpl; simplify; simpl.
  - apply tensor_assoc.
  - apply tensor_assoc.
  - apply (tensor_assoc⁻¹).
  - apply (tensor_assoc⁻¹).
  - apply iso_to_from.
  - apply iso_to_from.
  - apply iso_from_to.
  - apply iso_from_to.
Defined.
Next Obligation.
  simplify; simpl in *;
  apply to_unit_left_natural.
Qed.
Next Obligation.
  simplify; simpl in *;
  apply from_unit_left_natural.
Qed.
Next Obligation.
  simplify; simpl in *;
  apply to_unit_right_natural.
Qed.
Next Obligation.
  simplify; simpl in *;
  apply from_unit_right_natural.
Qed.
Next Obligation.
  simplify; simpl in *;
  apply to_tensor_assoc_natural.
Qed.
Next Obligation.
  simplify; simpl in *;
  apply from_tensor_assoc_natural.
Qed.
Next Obligation.
  simplify; simpl in *;
  apply triangle_identity.
Qed.
Next Obligation.
  simplify; simpl in *;
  apply pentagon_identity.
Qed.
