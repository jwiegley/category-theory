Require Import Category.Lib.
Require Import Category.Lib.Tactics2.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.
Require Import Category.Structure.UniversalProperty.
Require Import Category.Theory.Universal.Arrow.

Section UniversalArrowUniversalProperty.
  Context (C D: Category).
  Context (U : D ⟶ C).
  Context (c : C).

  Hint Resolve fmap : cat.

  Proposition fmap_respects' (x y : D) (f g : x ~> y) :
    f ≈ g -> fmap[U] f ≈ fmap[U] g.
  Proof using Type.
    apply fmap_respects.
  Qed.
                             
  Hint Resolve fmap_respects' : cat.
  Hint Rewrite @fmap_comp : categories.
  Hint Resolve uniqueness : cat.
  
  Proposition UniversalArrowIsUniversalProperty :
    IsUniversalProperty D (fun a : D => AUniversalArrow c U a) _.
  Proof.
    exists ((Curried_Hom C c) ◯ U).
    intro a.
    repeat(unshelve econstructor; try intro).
    - simpl in *. destruct X. auto with cat.
    - abstract(auto with cat).
    - abstract(auto with cat).
    - abstract(auto with cat).
    - simpl in *. destruct X. now apply universal_arrow_universal. 
    - abstract(simpl; intros; apply uniqueness;
      rewrite (unique_property universal_arrow_universal); easy).
    - abstract(simpl; intros; symmetry; apply uniqueness;
      autorewrite with categories;
               now rewrite (unique_property universal_arrow_universal)).
    - abstract(simpl; intros; destruct X; simpl; apply uniqueness;
      autorewrite with categories; apply compose_respects; [ reflexivity |];
               apply (unique_property (universal_arrow_universal _ _))).
    - abstract(simpl; intros; rewrite (unique_property universal_arrow_universal);
               auto with cat).
    - abstract(auto with cat).
    - abstract(auto with cat).
    - abstract(simpl; intros; apply uniqueness;
      simpl in X;
               now rewrite X, (unique_property (universal_arrow_universal ))).
    - exact (((to X) a) id).
    - now apply (from X d).
    - abstract(simpl; set (M := @preyoneda D^op _ d _ (to X));
      simpl in M; rewrite <- M; clear M;
      assert (K := (@iso_to_from _ _ _ X)); simpl in K; rewrite K;
               now autorewrite with categories).
    - (* This proof is only valid for Coq versions >= 8.16 
         because setoid rewriting supports polymorphism better *)
      try(
      simpl; assert (M := @preyoneda D^op _ d _ (to X));
      simpl in M; intro A; rewrite <- M in A; clear M;
      apply (proper_morphism (from X d)) in A;
      set (B := (iso_from_to X)); simpl in B; now rewrite B , id_left in A); admit.
    - abstract(simpl; intros; destruct X as [e ?]; simpl in e; apply e).
    - abstract(simpl; intro; assert (M := @preyoneda D^op _ x0 _ (to x));
               simpl in M; now rewrite <- M).
    - abstract (auto with cat).
    - abstract(auto with cat).
  Defined.

End UniversalArrowUniversalProperty.
      
      
