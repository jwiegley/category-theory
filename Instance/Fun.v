Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Instance.Sets.

Generalizable All Variables.

Section Fun.

Context {C : Category}.
Context {D : Category}.

(* Fun is the category whose morphisms are natural transformations between
   Functors from C ⟶ D. *)

Program Definition Fun : Category := {|
  obj     := C ⟶ D;
  hom     := @Transform C D;
  id      := @nat_id C D;
  compose := @nat_compose C D;

  compose_respects := @nat_compose_respects C D
|}.

End Fun.

Notation "[ C , D ]" := (@Fun C D)
  (at level 90, right associativity, format "[ C ,  D ]") : category_scope.

Notation "[[[ C , D ]]]( F , G )" := ({| carrier   := @hom (@Fun C D) F G
                                       ; is_setoid := @homset (@Fun C D) F G |})
  (at level 90, right associativity, format "[[[ C ,  D ]]]( F , G )") : homset_scope.

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

Definition nat_λ {A B} (F : A ⟶ B) : F ◯ Id ≅[Fun] F.
Proof.
  construct.
  - apply fun_id_right.
  - apply fun_id_right_sym.
  - apply fun_id_right_and_sym.
  - apply fun_id_right_sym_and.
Defined.

Definition nat_ρ {A B} (F : A ⟶ B) : Id ◯ F ≅[Fun] F.
Proof.
  construct.
  - apply fun_id_left.
  - apply fun_id_left_sym.
  - apply fun_id_left_and_sym.
  - apply fun_id_left_sym_and.
Defined.

Definition nat_α {A B C D} (F : A ⟶ B) (G : B ⟶ C) (H : C ⟶ D) :
  H ◯ (G ◯ F) ≅[Fun] (H ◯ G) ◯ F.
Proof.
  construct.
  - apply fun_comp_assoc.
  - apply fun_comp_assoc_sym.
  - apply fun_comp_assoc_and_sym.
  - apply fun_comp_assoc_sym_and.
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
  F ≅[Fun] G  ↔  F ≈ G.
Proof.
  split; intros; simpl.
  - given (iso : ∀ x : C, F x ≅ G x). {
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
  - destruct X.
    isomorphism; simpl; intros.
    + transform; simpl; intros.
      * apply x.
      * abstract
          (rewrite e; simpl;
           rewrite !comp_assoc;
           rewrite iso_to_from; cat).
      * abstract
          (rewrite e; simpl;
           rewrite !comp_assoc;
           rewrite iso_to_from; cat).
    + transform; simpl; intros.
      * apply x.
      * abstract
          (rewrite e; simpl;
           rewrite <- !comp_assoc;
           rewrite iso_to_from; cat).
      * abstract
          (rewrite e; simpl;
           rewrite <- !comp_assoc;
           rewrite iso_to_from; cat).
    + abstract
        (rewrite fmap_id;
         apply iso_to_from).
    + abstract
        (rewrite fmap_id;
         apply iso_from_to).
Defined.

Definition iso_equiv {C D : Category} {f g : C ⟶ D} :
  f ≅[Fun] g → f ≈ g := fst (Functor_Setoid_Nat_Iso _ _).

Definition equiv_iso {C D : Category} {f g : C ⟶ D} :
  f ≈ g → f ≅[Fun] g := snd (Functor_Setoid_Nat_Iso _ _).
