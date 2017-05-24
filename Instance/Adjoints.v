Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Export Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Program Instance adj_id {C : Category} : Id ⊣ Id := {
  unit   := {| transform := _ |};
  counit := {| transform := _ |}
}.

Program Definition adj_comp
        {C : Category} {D : Category} {E : Category}
        (F : D ⟶ C) (U : C ⟶ D) (F' : E ⟶ D) (U' : D ⟶ E)
        (X : F ⊣ U) (Y : F' ⊣ U') :
  F ○ F' ⊣ U' ○ U := {|
  unit   := {| transform := fun a =>
    fmap[U'] (transform[unit[X]] (F' a)) ∘ transform[unit[Y]] a |};
  counit := {| transform := fun a =>
    transform[counit[X]] a ∘ fmap[F] (transform[counit[Y]] (U a)) |};
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  srewrite (naturality[unit[X]]).
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  srewrite (naturality[unit[Y]]); cat.
Qed.
Next Obligation.
  symmetry.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  srewrite_r (naturality[counit[Y]]).
  rewrite fmap_comp.
  rewrite comp_assoc.
  srewrite_r (naturality[counit[X]]); cat.
Qed.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite (@fmap_comp _ _ F').
  rewrite comp_assoc.
  srewrite_r (naturality[counit[Y]]).
  rewrite !fmap_comp.
  rewrite !comp_assoc.
  srewrite (@counit_fmap_unit _ _ _ _ X); cat.
  rewrite <- fmap_comp.
  srewrite (@counit_fmap_unit _ _ _ _ Y); cat.
Qed.
Next Obligation.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite (@fmap_comp _ _ U).
  rewrite <- comp_assoc.
  srewrite (naturality[unit[X]]).
  rewrite !comp_assoc.
  srewrite (@fmap_counit_unit _ _ _ _ X); cat.
  srewrite (@fmap_counit_unit _ _ _ _ Y); cat.
Qed.

Notation "F ⊚ G" := (@adj_comp _ _ _ _ _ _ _ F G)
  (at level 40, left associativity) : category_scope.

Record adj_morphism {C : Category} {D : Category} := {
  free_functor : D ⟶ C;
  forgetful_functor : C ⟶ D;
  adjunction : free_functor ⊣ forgetful_functor
}.

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

(* Category of Adjoints:

   objects      Categories
   arrows       Adjoint functors between categories
   identity     Id ⊣ Id
   composition  F ⊣ G -> G ⊣ H -> F ⊣ H *)

Program Definition Adjoints : Category := {|
  ob := Category;
  hom := @adj_morphism;
  homset := @adj_morphism_setoid;
  id := fun X => {| free_functor      := Id[X]
                  ; forgetful_functor := Id[X] |};
  compose := fun A B C f g =>
    {| adjunction :=
             @adj_comp A B C (free_functor g) (forgetful_functor g)
                       (free_functor f) (forgetful_functor f)
                       (adjunction g) (adjunction f) |}
|}.
Next Obligation.
  proper; simpl; constructive.
  - exact (fmap (transform[to x2] _) ∘ transform[to x1] _).
  - rewrite comp_assoc.
    rewrite <- fmap_comp.
    rewrite !naturality.
    rewrite <- comp_assoc.
    rewrite <- fmap_comp.
    reflexivity.
  - exact (fmap (transform[from x2] _) ∘ transform[from x1] _).
  - rewrite comp_assoc.
    rewrite <- fmap_comp.
    rewrite !naturality.
    rewrite <- comp_assoc.
    rewrite <- fmap_comp.
    reflexivity.
  - rewrite naturality.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (fmap (transform[to x2] _))).
    rewrite <- fmap_comp.
    rewrite naturality.
    rewrite comp_assoc.
    destruct x2; simpl in *.
    rewrite iso_to_from; cat.
    destruct x1; simpl in *.
    rewrite iso_to_from0; cat.
  - rewrite naturality.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (fmap (transform[from x2] _))).
    rewrite <- fmap_comp.
    rewrite naturality.
    rewrite comp_assoc.
    destruct x2; simpl in *.
    rewrite iso_from_to; cat.
    destruct x1; simpl in *.
    rewrite iso_from_to0; cat.
  - exact (fmap (transform[to y1] _) ∘ transform[to y2] _).
  - rewrite comp_assoc.
    rewrite <- fmap_comp.
    rewrite !naturality.
    rewrite <- comp_assoc.
    rewrite <- fmap_comp.
    reflexivity.
  - exact (fmap (transform[from y1] _) ∘ transform[from y2] _).
  - rewrite comp_assoc.
    rewrite <- fmap_comp.
    rewrite !naturality.
    rewrite <- comp_assoc.
    rewrite <- fmap_comp.
    reflexivity.
  - rewrite naturality.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (fmap (transform[to y1] _))).
    rewrite <- fmap_comp.
    rewrite naturality.
    rewrite comp_assoc.
    destruct y1; simpl in *.
    rewrite iso_to_from; cat.
    destruct y2; simpl in *.
    rewrite iso_to_from0; cat.
  - rewrite naturality.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (fmap (transform[from y1] _))).
    rewrite <- fmap_comp.
    rewrite naturality.
    rewrite comp_assoc.
    destruct y1; simpl in *.
    rewrite iso_from_to; cat.
    destruct y2; simpl in *.
    rewrite iso_from_to0; cat.
Qed.
Next Obligation. split; simpl; constructive; cat. Qed.
Next Obligation. split; simpl; constructive; cat. Qed.
Next Obligation. split; simpl; constructive; cat. Qed.
Next Obligation. split; simpl; constructive; cat. Qed.

(* From mathoverflow:

   You will have to make an arbitrary choice for the direction of morphisms:
   is the left adjoint "forward" or "backward"? To prevent that, you can add
   involutions. The resulting category [InvAdj] of involutive categories and
   adjunctions has a lot of interesting structure. It is a dagger category,
   and in fact the `mother of all dagger categories', as it universally embeds
   any dagger category. In particular, the full subcategory of (ortho)posets
   and Galois connections has dagger kernels, dagger biproducts, an an
   opclassifier. See these two papers. Now for the definition (from 3.1.8 of
   my thesis):

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
   left adjoint.) *)
