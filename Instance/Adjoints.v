Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Export Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

#[global]
Program Instance adj_id {C : Category} : Id ⊣ Id := {
  adj := fun _ _ =>
    {| to   := {| morphism := _ |}
     ; from := {| morphism := _ |} |}
}.

Program Definition adj_comp
        {C : Category} {D : Category} {E : Category}
        (F : D ⟶ C) (U : C ⟶ D) (F' : E ⟶ D) (U' : D ⟶ E)
        (X : F ⊣ U) (Y : F' ⊣ U') :
  F ◯ F' ⊣ U' ◯ U := {|
  adj := fun a b =>
    {| to   := {| morphism := fun (f : F (F' a) ~> b) => to adj (to adj f) |}
     ; from := {| morphism := fun (f : a ~> U' (U b)) => adj⁻¹ (adj⁻¹ f) |} |}
|}.
Next Obligation. proper. rewrites; reflexivity. Qed.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation.
  srewrite (@iso_to_from _ _ _ (@adj C D F U X (F' a) b)).
  sapply (@iso_to_from _ _ _ (@adj D E F' U' Y a (U b))).
Qed.
Next Obligation.
  srewrite (@iso_from_to _ _ _ (@adj D E F' U' Y a (U b))).
  sapply (@iso_from_to _ _ _ (@adj C D F U X (F' a) b)).
Qed.
Next Obligation. rewrite <- !to_adj_nat_l; reflexivity. Qed.
Next Obligation. rewrite <- !to_adj_nat_r; reflexivity. Qed.
Next Obligation. rewrite <- !from_adj_nat_l; reflexivity. Qed.
Next Obligation. rewrite <- !from_adj_nat_r; reflexivity. Qed.

Notation "F ⊚ G" := (@adj_comp _ _ _ _ _ _ _ F G)
  (at level 30, right associativity) : category_scope.

Record adj_morphism {C : Category} {D : Category} := {
  free_functor : D ⟶ C;
  forgetful_functor : C ⟶ D;
  adjunction : free_functor ⊣ forgetful_functor
}.

#[global]
Program Instance adj_morphism_setoid {C : Category} {D : Category} :
  Setoid (@adj_morphism C D) := {
  equiv := fun f g =>
              (free_functor f ≅[Fun] free_functor g) *
              (forgetful_functor f ≅[Fun] forgetful_functor g)
}.
Next Obligation.
  equivalence.
    transitivity (free_functor y); assumption.
  transitivity (forgetful_functor y); assumption.
Qed.

(* The category of Adjoints:

    objects                Categories
    arrows                 Adjunctions between categories
    identity               Id ⊣ Id
    composition            F ⊣ U -> F' ⊣ U' -> F ◯ F' ⊣ U' ◯ U *)

Program Definition Adjoints : Category := {|
  obj     := Category;
  hom     := @adj_morphism;
  homset  := @adj_morphism_setoid;
  id      := fun X => {| free_functor      := Id[X]
                  ; forgetful_functor := Id[X] |};
  compose := fun A B C f g =>
    {| adjunction :=
         @adj_comp A B C (free_functor g) (forgetful_functor g)
                   (free_functor f) (forgetful_functor f)
                   (adjunction g) (adjunction f) |}
|}.
Next Obligation.
  proper; simpl.
  - isomorphism; simpl.
    + transform; simpl; intros.
      * exact (fmap (transform[to X] _) ∘ transform[to X0] _).
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
    + transform; simpl; intros.
      * exact (fmap (transform[from X] _) ∘ transform[from X0] _).
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
    + simpl.
      rewrite naturality.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap (transform[to X] _))).
      rewrite <- fmap_comp.
      rewrite naturality.
      rewrite comp_assoc.
      destruct X; simpl in *.
      rewrite iso_to_from; cat.
      destruct X0; simpl in *.
      rewrite iso_to_from0; cat.
    + simpl.
      rewrite naturality.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap (transform[from X] _))).
      rewrite <- fmap_comp.
      rewrite naturality.
      rewrite comp_assoc.
      destruct X; simpl in *.
      rewrite iso_from_to; cat.
      destruct X0; simpl in *.
      rewrite iso_from_to0; cat.
  - isomorphism; simpl.
    + transform; simpl; intros.
      * exact (fmap (transform[to H] _) ∘ transform[to H0] _).
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
    + transform; simpl; intros.
      * exact (fmap (transform[from H] _) ∘ transform[from H0] _).
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
    + simpl.
      rewrite naturality.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap (transform[to H] _))).
      rewrite <- fmap_comp.
      rewrite naturality.
      rewrite comp_assoc.
      destruct H; simpl in *.
      rewrite iso_to_from; cat.
      destruct H0; simpl in *.
      rewrite iso_to_from0; cat.
    + simpl.
      rewrite naturality.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap (transform[from H] _))).
      rewrite <- fmap_comp.
      rewrite naturality.
      rewrite comp_assoc.
      destruct H; simpl in *.
      rewrite iso_from_to; cat.
      destruct H0; simpl in *.
      rewrite iso_from_to0; cat.
Qed.
Next Obligation.
  split; isomorphism;
  try (transform; simpl; intros; try exact id; cat); cat.
Qed.
Next Obligation.
  split; isomorphism;
  try (transform; simpl; intros; try exact id; cat); cat.
Qed.
Next Obligation.
  split; isomorphism;
  try (transform; simpl; intros; try exact id; cat); cat.
Qed.
Next Obligation.
  split; isomorphism;
  try (transform; simpl; intros; try exact id; cat); cat.
Qed.

(* mathoverflow: "You will have to make an arbitrary choice for the direction
   of morphisms: is the left adjoint "forward" or "backward"? To prevent that,
   you can add involutions. The resulting category [InvAdj] of involutive
   categories and adjunctions has a lot of interesting structure. It is a
   dagger category, and in fact the `mother of all dagger categories', as it
   universally embeds any dagger category. In particular, the full subcategory
   of (ortho)posets and Galois connections has dagger kernels, dagger
   biproducts, an an opclassifier. See these two papers. Now for the
   definition (from 3.1.8 of my thesis):

   A functor ∗ : C^op → C is called involutive when ∗ ∘ ∗ = Id. Define a
   category [InvAdj] as follows. Objects are pairs (C,∗) of a category with an
   involution. A morphism (C,∗) → (D,∗) is functor F : C^op → D that has a
   left adjoint, where two such functors are identified when they are
   naturally isomorphic. The identity morphism on (C,∗) is the functor ∗ :
   C^op → C ; its left adjoint is ∗^op : C → C^op. The composition of F : C^op
   → D and G : D^op → E is defined by G ∘ ∗^op ∘ F : C^op → E; its left
   adjoint is F′ ∘ ∗ ∘ G′, where F′ ⊣ F and G′ ⊣ G.

   (It is not arbitrary to require a left adjoint instead of a right one. A
   contravariant functor from C to D can be written both as a (covariant)
   functor F : C^op → D or as a (covariant) functor F^op : C → D^op. The
   latter version has a right adjoint precisely when the former version has a
   left adjoint.)" *)
