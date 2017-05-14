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

Section Monoidal.

Context `{C : Category}.

Reserved Infix "⨂" (at level 30, right associativity).

Class Monoidal := {
  I : C;
  tensor : C ∏ C ⟶ C
    where "x ⨂ y" := (tensor (x, y));

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
Notation "X ⨂ Y" := (tensor (X, Y)) (at level 30, right associativity).

Global Program Instance Tensor_LeftMapF `{Monoidal}
        `{F : C ⟶ C} {Y : C} : Functor := {
  fobj := fun X => F X ⨂ Y;
  fmap := fun _ _ f => bimap (fmap[F] f) id
}.
Next Obligation.
  proper.
  apply bimap_respects.
    rewrite X0; reflexivity.
  reflexivity.
Qed.
Next Obligation.
  rewrite fmap_id, bimap_id_id; reflexivity.
Qed.
Next Obligation.
  normal; reflexivity.
Qed.

Program Instance tensor_respects `{Monoidal} :
  Proper ((fun p q => Isomorphism (fst p) (fst q) * Isomorphism (snd p) (snd q))
            ==> Isomorphism) tensor.
Next Obligation.
  proper; simpl in *.
  isomorphism.
  - exact (bimap x0 y0).
  - exact (bimap (x0⁻¹) (y0⁻¹)).
  - normal.
    rewrite !iso_to_from.
    rewrite bimap_id_id.
    reflexivity.
  - normal.
    rewrite !iso_from_to.
    rewrite bimap_id_id.
    reflexivity.
Defined.

Global Program Instance Tensor_LeftMap `{Monoidal}
        `{@CanonicalMap C P} {Y : C} :
  @CanonicalMap C (fun X => P X ⨂ Y) := {
  map := fun _ _ f => @bimap C C C (⨂) _ _ _ _ (@map _ _ _ _ _ f) (id[Y]);
  is_functor := @Tensor_LeftMapF _ is_functor _
}.
Next Obligation.
  unfold Tensor_LeftMap_obligation_1.
  apply tensor_respects; simpl; split.
    apply fobj_related.
  reflexivity.
Defined.
Next Obligation.
  unfold Tensor_LeftMap_obligation_1.
  unfold Tensor_LeftMap_obligation_2; simpl.
  rewrite fmap_related.
  normal.
  reflexivity.
Qed.

Global Program Instance Tensor_RightMapF `{Monoidal}
        `{F : C ⟶ C} {X : C} : Functor := {
  fobj := fun Y => X ⨂ F Y;
  fmap := fun _ _ f => bimap id (fmap[F] f)
}.
Next Obligation.
  proper.
  apply bimap_respects.
    reflexivity.
  rewrite X1; reflexivity.
Qed.
Next Obligation.
  rewrite fmap_id, bimap_id_id; reflexivity.
Qed.
Next Obligation.
  normal; reflexivity.
Qed.

Global Program Instance Tensor_RightMap `{Monoidal}
        `{@CanonicalMap C P} {X : C} :
  @CanonicalMap C (fun Y => X ⨂ P Y) := {
  map := fun _ _ f => @bimap C C C (⨂) _ _ _ _ (id[X]) (@map _ _ _ _ _ f);
  is_functor := @Tensor_RightMapF _ is_functor _
}.
Next Obligation.
  unfold Tensor_LeftMap_obligation_1.
  apply tensor_respects; simpl; split.
    reflexivity.
  apply fobj_related.
Defined.
Next Obligation.
  unfold Tensor_LeftMap_obligation_1.
  unfold Tensor_LeftMap_obligation_2; simpl.
  rewrite fmap_related.
  normal.
  reflexivity.
Qed.

(* The following proofs are from the book "Tensor Categories", by Pavel
   Etingof, Shlomo Gelaki, Dmitri Nikshych, and Victor Ostrik. *)

(* Proposition 2.2.2 *)

Proposition id_unit_left `{Monoidal} {X} :
  unit_left ≈ bimap (id[I]) (@unit_left _ X).
Proof.
  (* "It follows from naturality of the left unit constraint l that the
     following diagram commutes..." *)
  assert (unit_left ∘ bimap id unit_left
            << I ⨂ (I ⨂ X) ~~> X >>
          unit_left ∘ unit_left).
    rewrite to_unit_left_natural; reflexivity.

  (* "Since lX is an isomorphism, the first identity follows." *)
  do 2 (rewrite <- id_left; symmetry).
  rewrite <- (iso_from_to unit_left).
  rewrite <- !comp_assoc.
  rewrite X0; reflexivity.
Qed.

Proposition id_unit_right `{Monoidal} {X} :
  unit_right ≈ bimap (@unit_right _ X) (id[I]).
Proof.
  (* "It follows from naturality of the left unit constraint l that the
     following diagram commutes..." *)
  assert (unit_right ∘ bimap unit_right id
            << (X ⨂ I) ⨂ I ~~> X >>
          unit_right ∘ unit_right).
    rewrite to_unit_right_natural; reflexivity.

  (* "The second one follows similarly from naturality of r." *)
  do 2 (rewrite <- id_left; symmetry).
  rewrite <- (iso_from_to unit_right).
  rewrite <- !comp_assoc.
  rewrite X0; reflexivity.
Qed.

(* Proposition 2.2.3 is the triangle idenity. *)

(* Proposition 2.2.4 *)

Corollary outside_pentagon `{Monoidal} {X Y Z} :
  bimap id tensor_assoc ∘ tensor_assoc ∘ bimap tensor_assoc id
    << ((X ⨂ I) ⨂ Y) ⨂ Z ~~> X ⨂ (I ⨂ (Y ⨂ Z)) >>
  tensor_assoc ∘ tensor_assoc.
Proof.
  (* "The outside pentagon commutes by the pentagon axiom." *)
  apply pentagon_identity.
Qed.

Corollary left_quadrangle `{Monoidal} {X Y Z} :
  bimap unit_right id ∘ tensor_assoc
    << ((X ⨂ I) ⨂ Y) ⨂ Z ~~> X ⨂ (Y ⨂ Z) >>
  tensor_assoc ∘ bimap (bimap unit_right id) id.
Proof.
  (* "The functoriality of a implies the commutativity of the two middle
     quadrangles." *)
  rewrite <- to_tensor_assoc_natural.
  normal; reflexivity.
Qed.

Corollary right_quadrangle `{Monoidal} {X Y Z} :
  bimap id (bimap unit_left id) ∘ tensor_assoc
    << (X ⨂ (I ⨂ Y)) ⨂ Z ~~> X ⨂ (Y ⨂ Z) >>
  tensor_assoc ∘ bimap (bimap id unit_left) id.
Proof.
  rewrite <- to_tensor_assoc_natural.
  reflexivity.
Qed.

Corollary upper_triangle `{Monoidal} {X Y Z : C} :
  bimap (bimap unit_right id) id
    << ((X ⨂ I) ⨂ Y) ⨂ Z ~~> (X ⨂ Y) ⨂ Z >>
  bimap (bimap id unit_left) id ∘ bimap tensor_assoc id.
Proof.
  (* "The triangle axiom implies the commutativity of the upper triangle..." *)
  rewrite triangle_identity.
  normal; reflexivity.
Qed.

Corollary lower_left_triangle `{Monoidal} {X Y Z} :
  bimap unit_right id
    << (X ⨂ I) ⨂ (Y ⨂ Z) ~~> X ⨂ (Y ⨂ Z) >>
  bimap id unit_left ∘ tensor_assoc.
Proof.
  (* "... and the lower left triangle." *)
  apply triangle_identity.
Qed.

Corollary lower_right_triangle `{Monoidal} {X Y Z} :
  bimap id (bimap unit_left id)
    << X ⨂ ((I ⨂ Y) ⨂ Z) ~~> X ⨂ (Y ⨂ Z) >>
  bimap id unit_left ∘ bimap id tensor_assoc.
Proof.
  (* "Consequently, the lower right triangle commutes as well." *)
  pose proof (@outside_pentagon _ X Y Z).
  pose proof (@right_quadrangle _ X Y Z).
  assert (∀ X Y Z W (f g : (X ⨂ Y) ⨂ Z ~> W),
             f ≈ g -> f ∘ tensor_assoc⁻¹ ≈ g ∘ tensor_assoc⁻¹).
    intros.
    rewrite X3.
    reflexivity.
  apply X2 in X1.
  rewrite <- !comp_assoc in X1.
  rewrite iso_to_from, id_right in X1.
  rewrite X1; clear X1.
  rewrite comp_assoc.
  normal.
  pose proof (@left_quadrangle _ X Y Z).
  rewrite triangle_identity in X1.
  rewrite triangle_identity in X1.
  rewrite <- comp_assoc in X1.
  rewrite <- X0 in X1; clear X0.
  rewrite !comp_assoc in X1.
  normal.
  symmetry in X1.
  rewrite bimap_comp_id_right in X1.
  rewrite comp_assoc in X1.
  assert (∀ (f g : (X ⨂ I ⨂ Y) ⨂ Z ~{ C }~> X ⨂ Y ⨂ Z),
             f ∘ bimap[(⨂)] tensor_assoc (id[Z])
               ≈ g ∘ bimap[(⨂)] tensor_assoc (id[Z])
             -> f ≈ g).
    intros.
    assert (∀ X Y Z W V (f g : ((X ⨂ Y) ⨂ Z) ⨂ V ~> W),
               f ≈ g -> f ∘ bimap[(⨂)] (tensor_assoc⁻¹) (id[V]) ≈
                        g ∘ bimap[(⨂)] (tensor_assoc⁻¹) (id[V])).
      intros.
      rewrite X4.
      reflexivity.
    apply X3 in X0.
    normal.
    rewrite !iso_to_from in X0.
    rewrite !bimap_id_id, !id_right in X0.
    assumption.
  apply X0 in X1; clear X0.
  rewrite X1; clear X1.
  rewrite <- comp_assoc.
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

Lemma tensor_id_left_inj `{Monoidal} {X Y} (f g : X ~> Y) :
  bimap[(⨂)] (id[I]) f ≈ bimap[(⨂)] (id[I]) g -> f ≈ g.
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
  bimap[(⨂)] f (id[I]) ≈ bimap[(⨂)] g (id[I]) -> f ≈ g.
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

Theorem triangle_left `{Monoidal} {X Y} :
  bimap unit_left id
    << (I ⨂ X) ⨂ Y ~~> X ⨂ Y >>
  unit_left ∘ tensor_assoc.
Proof.
  (* "Setting X = 1 and applying the functor L−1 to the lower right triangle,
     1 we obtain commutativity of the triangle (2.12)." *)
  pose proof (@lower_right_triangle _ I X Y).
  normal.
  apply tensor_id_left_inj in X0.
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
  pose proof (@lower_right_triangle _ I I I).
  pose proof (@triangle_identity _ I I).
  normal.
  rewrite <- id_unit_left in X0.
  rewrite <- X0 in X; clear X0.
  apply tensor_id_left_inj in X.
  apply tensor_id_right_inj in X.
  apply X.
Qed.

Class SymmetricMonoidal `{Monoidal} := {
  braid {X Y} : X ⨂ Y ≅ Y ⨂ X;
  braid_natural : natural (@braid);

  braid_invol {X Y} : braid ∘ braid ≈ id[X ⨂ Y];

  hexagon_identity {X Y Z} :
    tensor_assoc ∘ braid ∘ tensor_assoc
      << (X ⨂ Y) ⨂ Z ~~> Y ⨂ (Z ⨂ X) >>
    bimap id braid ∘ tensor_assoc ∘ bimap braid id
}.

Class RelevanceMonoidal `{Monoidal} := {
  comultiply {X} : X ~> X ⨂ X
}.

(* Wikipedia: "Cartesian monoidal categories have a number of special and
   important properties, such as the existence of diagonal maps (Δ) x : x → x
   ⨂ x and augmentations (e) x : x → I for any object x. In applications to
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
    unit_left  ∘ bimap eliminate f ∘ diagonal ≈ f;
  eliminate_right {X Y} (f : X ~> Y) :
    unit_right ∘ bimap f eliminate ∘ diagonal ≈ f;

  eliminate_diagonal {X Y Z W} (f : X ~> Y) (g : Z ~> W) :
    bimap (unit_right ∘ bimap f eliminate)
          (unit_left  ∘ bimap eliminate g) ∘ diagonal ≈ bimap f g;

  diagonal_natural {X Y} (f : X ~> Y) :
      bimap f f ∘ diagonal ≈ diagonal ∘ f
}.

Corollary foo `{Monoidal} `{@CartesianMonoidal _}
          {X Y Z W} (f : X ~> Y) (g : Z ~> W) :
    bimap (unit_right ∘ bimap f eliminate)
          (unit_left  ∘ bimap eliminate g) ∘ diagonal ≈ bimap f g.
Proof.
  intros.
  symmetry.
  rewrite <- (eliminate_right f) at 1.
  rewrite <- (eliminate_left g) at 1.
  rewrite !bimap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
Abort.

Corollary eliminate_comp `{Monoidal} `{@CartesianMonoidal _} `{f : A ~> B} :
  eliminate ∘ f ≈ eliminate.
Proof. intros; apply unit_terminal. Qed.

Global Program Definition SymmetricCartesianMonoidal_Cartesian
       `{Monoidal} (* `{@SymmetricMonoidal _} *) `{@CartesianMonoidal _} :
  @Cartesian C := {|
  Prod := fun X Y => tensor (X, Y);
  fork := fun _ _ _ f g => bimap f g ∘ diagonal;
  exl  := fun _ _ => unit_right ∘ bimap id eliminate;
  exr  := fun _ _ => unit_left  ∘ bimap eliminate id
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

(* jww (2017-05-13): 
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
*)

(* Every cartesian category with terminal objects gives rise to a monoidal
   category taking the terminal object as unit, and the tensor as product. *)

Require Import Category.Functor.Product.Internal.

(* Any cartesian category with terminal objects is monoidal with respect to
   its internal product functor. *)

(* jww (2017-05-13): TODO
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
*)

(* jww (2017-05-13): TODO
Program Definition InternalProduct_SymmetricMonoidal
        `{C : Category} `{@Cartesian C} `{@Terminal C} :
  @SymmetricMonoidal C InternalProduct_Monoidal := {|
  braid := fun X Y =>
    {| to   := @swap C _ X Y
     ; from := @swap C _ Y X
     ; iso_to_from := swap_invol
     ; iso_from_to := swap_invol
    |}
|}.
Next Obligation.
  unfold swap; split; intros.
  rewrite <- !fork_comp; cat.
  rewrite <- !comp_assoc; cat.
  rewrite <- !fork_comp; cat.
  rewrite <- !comp_assoc; cat.
  rewrite <- !fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.
Next Obligation. apply swap_invol. Qed.
Next Obligation.
  unfold swap.
  rewrite <- !fork_comp; cat.
  rewrite <- !comp_assoc; cat.
  rewrite <- !fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.
*)

(* jww (2017-05-13): TODO
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
*)

Require Import Category.Functor.Bifunctor.

Local Obligation Tactic := intros; simplify; simpl in *.

(* Any product of monoidal categories is monoidal. *)

(* jww (2017-05-13): TODO
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
*)