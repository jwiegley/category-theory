Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Structure.Cartesian.
Require Import Category.Lib.Tactics2.

Proposition fmap_respects' (C D : Category) (F : C ⟶ D) : forall (x y : C) (f g: hom x y),
    f ≈ g -> fmap[F] f ≈ fmap[F] g.
Proof. now apply fmap_respects. Defined.
#[export] Hint Resolve fmap_respects' : cat.

Proposition ump_product' (C : Category) `{@Cartesian C} (x y z: C)
  (h h': z ~> x × y) : (exl ∘ h) ≈ (exl ∘ h') -> (exr ∘ h) ≈ (exr ∘ h') -> h ≈ h'.
Proof.
  intros.
  assert (RW: h ≈ fork (exl ∘ h) (exr ∘ h)). {
  apply (snd (ump_products _ _ _)); split; reflexivity.
  }
  rewrite RW; symmetry.
  apply (snd (ump_products _ _ _)); split; symmetry; assumption. 
Qed.

Proposition ump_product_auto1 (C : Category) `{@Cartesian C} (x y z: C)
  (h : z ~> x × y) (f : z ~> x) (g : z ~> y) : (exl ∘ h) ≈ f -> (exr ∘ h) ≈ g -> h ≈ fork f g.
Proof.
  intros. apply (snd (ump_products _ _ _)); split; trivial.
Qed.

Proposition ump_product_auto2 (C : Category) `{@Cartesian C} (x y z: C)
  (h : z ~> x × y) (f : z ~> x) (g : z ~> y) : (exl ∘ h) ≈ f -> (exr ∘ h) ≈ g -> fork f g ≈ h.
Proof.
  intros. symmetry. apply (snd (ump_products _ _ _)); split; trivial.
Qed.

#[export] Hint Resolve ump_product_auto1 : cat.
#[export] Hint Resolve ump_product_auto2 : cat.
(* #[export] Hint Resolve ump_product' : cat. *)

#[export] Hint Rewrite @exl_fork_assoc  : categories.
#[export] Hint Rewrite @exl_fork_comp : categories.
#[export] Hint Rewrite @exr_fork_assoc  : categories.
#[export] Hint Rewrite @exr_fork_comp : categories.

Proposition ump_product_auto3 (C : Category) `{@Cartesian C}
 (c d p q: C) (h : c ~> d) (f : d ~> p) (g : d ~> q) (k : c ~> p × q) :
 f ∘ h ≈ exl ∘ k -> g ∘ h ≈ exr ∘ k -> (fork f g ∘ h) ≈ k.
Proof.
  intros H1 H2.
  rewrite <- fork_comp.
  apply ump_product_auto2; symmetry; assumption.
Qed.

Proposition ump_product_auto4 (C : Category) `{@Cartesian C}
 (c d p q: C) (h : c ~> d) (f : d ~> p) (g : d ~> q) (k : c ~> p × q) :
 f ∘ h ≈ exl ∘ k -> g ∘ h ≈ exr ∘ k -> k ≈ (fork f g ∘ h).
Proof.
  intros H1 H2.
  rewrite <- fork_comp.
  apply ump_product_auto1; symmetry; assumption.
Qed.

#[export] Hint Resolve ump_product_auto3 : cat.
#[export] Hint Resolve ump_product_auto4 : cat.

Ltac component_of_nat_trans :=
  match goal with
  | [ H : @Transform ?C ?D ?F ?G |- @hom ?D (fobj[?F] ?x) (fobj[?G] ?x) ] => apply H
  end.
#[export] Hint Extern 1 (hom (fobj[ _ ] ?x) (fobj[ _ ] ?x)) => component_of_nat_trans : cat.
#[local] Hint Rewrite @fmap_comp : categories.
#[local] Hint Rewrite @exl_split : categories.
#[local] Hint Rewrite @exr_split : categories.

#[export]
Instance Functor_Category_Cartesian (C D : Category) (_ : @Cartesian D) : @Cartesian (@Fun C D).
Proof.
  unshelve econstructor.
  - simpl. intros F G. unshelve econstructor.
    + exact (fun c => fobj[F] c × fobj[G] c).
    + exact (fun x y f => Cartesian.split (fmap[F] f) (fmap[G] f)).
    + abstract(intros x y; repeat(intro); apply split_respects; auto with cat).
    + abstract(intro; simpl; unfold split; auto with cat).
    + abstract(intros x y z f g; simpl; unfold split; auto with cat).
  - intros F G H σ τ. cbn in *.
    unshelve econstructor; simpl.
    + intro x. simpl. auto with cat.
    + abstract(intros x y f;
      unfold split; autorewrite with categories;
      apply ump_product_auto3; autorewrite with categories;
        destruct σ, τ; auto). 
    + abstract(intros x y f; destruct σ, τ; unfold split; auto with cat).
  - simpl. intros F G; unshelve econstructor.
    + intro a. simpl. exact exl.
    + abstract(simpl; intros; now autorewrite with categories).
    + abstract(simpl; intros; now autorewrite with categories).
  - simpl; intros F G. unshelve econstructor.
    + intro a. simpl. exact exr.
    + abstract(simpl; intros; now autorewrite with categories).
    + abstract(simpl; intros; now autorewrite with categories).
  - abstract(simpl; repeat(intro); simpl; auto with cat).
  - simpl. intros F G H s t fk. split.
    + abstract(intro l; split; intro; rewrite l; now autorewrite with categories).
    + abstract(intros [l1 l2] x; rewrite <- l1, <- l2; auto with cat).
Defined.
