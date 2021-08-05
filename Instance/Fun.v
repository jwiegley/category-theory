Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Natural.Transformation.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Fun.

Context {C : Category}.
Context {D : Category}.

Program Definition nat_equiv {F : C ⟶ D} {G : C ⟶ D} : crelation (F ⟹ G) :=
  fun n m => ∀ A, transform[n] A ≈ transform[m] A.

Hint Unfold nat_equiv : core.

Global Program Definition nat_equiv_equivalence {F : C ⟶ D} {G : C ⟶ D} :
  Equivalence (@nat_equiv F G).
Proof.
  equivalence.
  transitivity (transform[y] A).
    apply X.
  apply X0.
Qed.

Global Program Instance nat_Setoid {F : C ⟶ D} {G : C ⟶ D} :
  Setoid (F ⟹ G) := {
  equiv := nat_equiv;
  setoid_equiv := nat_equiv_equivalence
}.

Global Program Definition nat_id {F : C ⟶ D} : F ⟹ F := {|
  transform := fun X => fmap (@id C X)
|}.

Hint Unfold nat_id : core.

Global Program Definition nat_compose {F : C ⟶ D} {G : C ⟶ D} {K : C ⟶ D}
  (f : G ⟹ K) (g : F ⟹ G) : F ⟹ K := {|
  transform := fun X => transform[f] X ∘ transform[g] X
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite naturality.
  rewrite <- comp_assoc.
  rewrite naturality.
  rewrite comp_assoc.
  reflexivity.
Qed.
Next Obligation.
  symmetry.
  apply nat_compose_obligation_1.
Qed.

Hint Unfold nat_compose : core.

Global Program Definition nat_compose_respects
       {F : C ⟶ D} {G : C ⟶ D} {K : C ⟶ D} :
  Proper (equiv ==> equiv ==> equiv) (@nat_compose F G K).
Proof. proper. Qed.

(* Wikipedia: "Natural transformations also have a "horizontal composition".
   If η : F → G is a natural transformation between functors F,G : C → D and ε
   : J → K is a natural transformation between functors J,K : D → E, then the
   composition of functors allows a composition of natural transformations
   ε ∘ η : J ◯ F → K ◯ G. This operation is also associative with identity,
   and the identity coincides with that for vertical composition. The two
   operations are related by an identity which exchanges vertical composition
   with horizontal composition." *)

Global Program Definition nat_hcompose {E} {F G : C ⟶ D} {J K : D ⟶ E}
  (ε : J ⟹ K) (η : F ⟹ G) : J ◯ F ⟹ K ◯ G := {|
  transform := fun x => transform[ε] (fobj[G] x) ∘ fmap[J] (transform[η] x)
|}.
Next Obligation.
  rewrite <- naturality.
  rewrite <- comp_assoc.
  rewrite comp_assoc.
  rewrite <- !fmap_comp.
  rewrite !naturality.
  reflexivity.
Qed.
Next Obligation.
  rewrite <- !naturality.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite !naturality.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  reflexivity.
Qed.

(* Fun is the category whose morphisms are natural transformations between
   Functors from C ⟶ D. *)

Global Program Definition Fun : Category := {|
  obj     := C ⟶ D;
  hom     := @Transform C D;
  id      := @nat_id;
  compose := @nat_compose;

  compose_respects := @nat_compose_respects
|}.

End Fun.

Notation "[ C , D ]" := (@Fun C D)
  (at level 90, right associativity, format "[ C ,  D ]") : category_scope.

Notation "F ∙ G" := (@nat_compose _ _ _ _ _ F G) (at level 40, left associativity).

Hint Unfold nat_compose : core.
Hint Unfold nat_id : core.
Hint Unfold nat_equiv : core.

Arguments nat_equiv {_ _ _ _} _ _ /.

Corollary nat_id_left C D (F G : C ⟶ D) (N : F ⟹ G) :
  nat_id ∙ N ≈[Fun] N.
Proof. unfold nat_id, nat_compose; simpl; intros; cat. Qed.

Corollary nat_id_right C D (F G : C ⟶ D) (N : F ⟹ G) :
  N ∙ nat_id ≈[Fun] N.
Proof. unfold nat_id, nat_compose; simpl; intros; cat. Qed.

Corollary nat_comp_assoc C D (F G H J : C ⟶ D)
          (M : H ⟹ J) (N : G ⟹ H) (O : F ⟹ G) :
  M ∙ (N ∙ O) ≈[Fun] (M ∙ N) ∙ O.
Proof. unfold nat_compose; simpl; intros; cat. Qed.

Lemma whisker_right_id A B C (F : A ⟶ B) (G : B ⟶ C) : id{Fun} ⊲ F ≈ id{Fun}.
Proof. simpl; intros; cat. Qed.

Lemma whisker_left_id A B C (F : A ⟶ B) (G : B ⟶ C) : G ⊳ id{Fun} ≈ id{Fun}.
Proof. simpl; intros; cat. Qed.

Lemma whisker_left_dist A B C (F : A ⟶ B) (G H J : B ⟶ C)
      (η : G ⟹ H) (θ : H ⟹ J) : (θ ⊲ F) ∙ (η ⊲ F) ≈ (θ ∙ η) ⊲ F.
Proof. simpl; intros; cat. Qed.

Lemma whisker_right_dist A B C (F G H : A ⟶ B) (J : B ⟶ C)
      (η : F ⟹ G) (θ : G ⟹ H) : (J ⊳ θ) ∙ (J ⊳ η) ≈ J ⊳ (θ ∙ η).
Proof. simpl; intros; cat. now rewrite fmap_comp. Qed.

Lemma nat_λ {A B} (F : A ⟶ B) : F ◯ Id ≅[Fun] F.
Proof.
  construct; simpl.
  - construct.
    + exact id.
    + abstract cat.
    + abstract cat.
  - construct.
    + exact id.
    + abstract cat.
    + abstract cat.
  - abstract cat.
  - abstract cat.
Defined.

Lemma nat_ρ {A B} (F : A ⟶ B) : Id ◯ F ≅[Fun] F.
Proof.
  construct; simpl.
  - construct.
    + exact id.
    + abstract cat.
    + abstract cat.
  - construct.
    + exact id.
    + abstract cat.
    + abstract cat.
  - abstract cat.
  - abstract cat.
Defined.

Lemma nat_α {A B C D} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
  H ◯ (G ◯ F) ≅[Fun] (H ◯ G) ◯ F.
Proof.
  construct; simpl.
  - construct.
    + exact id.
    + abstract cat.
    + abstract cat.
  - construct.
    + exact id.
    + abstract cat.
    + abstract cat.
  - abstract cat.
  - abstract cat.
Defined.

Lemma whisker_left_right A B C (F G : A ⟶ B) (H J : B ⟶ C)
      (η : F ⟹ G) (θ : H ⟹ J) :
  (J ⊳ η) ∙ (θ ⊲ F) ≈ (θ ⊲ G) ∙ (H ⊳ η).
Proof. simpl; intros; cat; apply naturality. Qed.

Lemma whisker_flip A B C (F : A ⟶ B) (G : B ⟶ C) :
  (to (nat_λ G) ⊲ F) ∙ to (nat_α F Id G) ≈ G ⊳ (to (nat_ρ F)).
Proof. simpl; intros; cat. Qed.

Lemma nat_α_whisker_right_comp
      A B C D (F : A ⟶ B) (G : B ⟶ C) (H J : C ⟶ D) (η : H ⟹ J) :
  to (nat_α F G J) ∙ η ⊲ (G ◯ F) ≈ (η ⊲ G) ⊲ F ∙ to (nat_α F G H).
Proof. simpl; intros; cat. Qed.

Lemma nat_α_whisker_left_comp
      A B C D (F G : A ⟶ B) (H : B ⟶ C) (J : C ⟶ D) (η : F ⟹ G) :
  to (nat_α G H J) ∙ J ⊳ (H ⊳ η) ≈ (J ◯ H) ⊳ η ∙ to (nat_α F H J).
Proof. simpl; intros; cat. Qed.

Lemma nat_α_whisker_assoc
      A B C D (F : A ⟶ B) (G H : B ⟶ C) (J : C ⟶ D) (η : G ⟹ H) :
  to (nat_α F H J) ∙ J ⊳ (η ⊲ F) ≈ (J ⊳ η) ⊲ F ∙ to (nat_α F G J).
Proof. simpl; intros; cat. Qed.

Lemma nat_α_nat_α A B C D E (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) (J : D ⟶ E) :
  (to (nat_α G H J) ⊲ F ∙ to (nat_α F (H ◯ G) J)) ∙ (J ⊳ (to (nat_α F G H)))
    ≈ to (nat_α F G (J ◯ H)) ∙ to (nat_α (G ◯ F) H J).
Proof. simpl; intros; cat. Qed.

Class Pointed {C : Category} (F : C ⟶ C) := {
  point : Id ⟹ F
}.

Class WellPointed `{@Pointed C F} := {
  well_pointed :
    (F ⊳ point) ∙ from (nat_λ _) ≈ (point ⊲ F) ∙ from (nat_ρ _)
}.

Theorem Functor_Setoid_Nat_Iso `(F : C ⟶ D) (G : C ⟶ D) :
  F ≅[Fun] G ↔ F ≈ G.
Proof.
  split; intros; simpl.
    given (iso : ∀ x : C, F x ≅ G x). {
      intros; isomorphism; simpl; intros.
      - apply X.
      - apply (X⁻¹).
      - abstract (srewrite (iso_to_from X); cat).
      - abstract (srewrite (iso_from_to X); cat).
    }
    exists iso; simpl in *; intros.
    abstract
      (rewrite <- comp_assoc;
       rewrite (naturality[to X]);
       rewrite comp_assoc;
       srewrite (iso_from_to X); cat).
  destruct X.
  isomorphism; simpl; intros.
  - transform; simpl; intros.
    + apply x.
    + abstract
        (rewrite e; simpl;
         rewrite !comp_assoc;
         rewrite iso_to_from; cat).
    + abstract
        (rewrite e; simpl;
         rewrite !comp_assoc;
         rewrite iso_to_from; cat).
  - transform; simpl; intros.
    + apply x.
    + abstract
        (rewrite e; simpl;
         rewrite <- !comp_assoc;
         rewrite iso_to_from; cat).
    + abstract
        (rewrite e; simpl;
         rewrite <- !comp_assoc;
         rewrite iso_to_from; cat).
  - abstract
      (rewrite fmap_id;
       apply iso_to_from).
  - abstract
      (rewrite fmap_id;
       apply iso_from_to).
Defined.

Definition iso_equiv {C D : Category} {f g : C ⟶ D} :
  f ≅[Fun] g -> f ≈ g := fst (Functor_Setoid_Nat_Iso _ _).

Definition equiv_iso {C D : Category} {f g : C ⟶ D} :
  f ≈ g -> f ≅[Fun] g := snd (Functor_Setoid_Nat_Iso _ _).
