Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.

Generalizable All Variables.

Section Transform.

Universes o1 h1 p1 o2 h2 p2.
Context {C : Category@{o1 h1 p2}}.
Context {D : Category@{o2 h2 p2}}.
Context {F : C ⟶ D}.
Context {G : C ⟶ D}.

(* If a functor may be transformed, one must show how to transform mapped
   objects and that the mapping of morphisms is natural (i.e., transforming
   before or after introduces no change in the effect of such mappings). *)

Class Transform := {
  transform {x} : F x ~> G x;

  naturality {x y} (f : x ~> y) :
    fmap[G] f ∘ transform ≈ transform ∘ fmap[F] f;

  naturality_sym {x y} (f : x ~> y) :
    transform ∘ fmap[F] f ≈ fmap[G] f ∘ transform
}.

#[export]
Program Instance Transform_Setoid : Setoid Transform :=
  {| equiv N0 N1 := ∀ x, (@transform N0 x) ≈ (@transform N1 x); |}.
Next Obligation.
  equivalence.
  transitivity (@transform y x0); auto.
Qed.

End Transform.

Arguments transform {_ _ _ _} _ _.
Arguments naturality
  {_ _ _ _ _ _ _ _}, {_ _ _ _} _ {_ _ _}, {_ _ _ _} _ _ _ _.
Arguments naturality_sym
  {_ _ _ _ _ _ _ _}, {_ _ _ _} _ {_ _ _}, {_ _ _ _} _ _ _ _.

Declare Scope transform_scope.
Declare Scope transform_type_scope.
Bind Scope transform_scope with Transform.
Delimit Scope transform_type_scope with transform_type.
Delimit Scope transform_scope with transform.
Open Scope transform_type_scope.
Open Scope transform_scope.

Notation "F ⟹ G" := (@Transform _ _ F%functor G%functor)
  (at level 90, right associativity) : transform_type_scope.

Notation "transform[ F ]" := (@transform _ _ _ _ F%transform)
  (at level 9, only parsing) : morphism_scope.
Notation "naturality[ F ]" := (@naturality _ _ _ _ F%transform)
  (at level 9, only parsing) : morphism_scope.

Coercion transform : Transform >-> Funclass.

Ltac transform :=
  unshelve (refine {| transform := _ |}; simpl; intros).

Corollary fun_id_left {C D : Category} {F : C ⟶ D} : Id ◯ F ⟹ F.
Proof. transform; simpl; intros; cat. Defined.

Corollary fun_id_left_sym {C D : Category} {F : C ⟶ D} : F ⟹ Id ◯ F.
Proof. transform; simpl; intros; cat. Defined.

Lemma fun_id_left_and_sym `(F : C ⟶ D) (x : C) :
  fun_id_left x ∘ fun_id_left_sym x ≈ fmap[F] id.
Proof. simpl; cat. Qed.

Lemma fun_id_left_sym_and `(F : C ⟶ D) (x : C) :
  fun_id_left_sym x ∘ fun_id_left x ≈ fmap[F] id.
Proof. simpl; cat. Qed.

Corollary fun_id_right {C D : Category} {F : C ⟶ D} : F ◯ Id ⟹ F.
Proof. transform; simpl; intros; cat. Defined.

Corollary fun_id_right_sym {C D : Category} {F : C ⟶ D} : F ⟹ F ◯ Id.
Proof. transform; simpl; intros; cat. Defined.

Lemma fun_id_right_and_sym `(F : C ⟶ D) (x : C) :
  fun_id_right x ∘ fun_id_right_sym x ≈ fmap[F] id.
Proof. simpl; cat. Qed.

Lemma fun_id_right_sym_and `(F : C ⟶ D) (x : C) :
  fun_id_right_sym x ∘ fun_id_right x ≈ fmap[F] id.
Proof. simpl; cat. Qed.

Corollary fun_comp_assoc {C D E B : Category}
  {F : E ⟶ B} {G : D ⟶ E} {H : C ⟶ D} : F ◯ (G ◯ H) ⟹ (F ◯ G) ◯ H.
Proof. transform; simpl; intros; cat. Defined.

Corollary fun_comp_assoc_sym {C D E B : Category}
  {F : E ⟶ B} {G : D ⟶ E} {H : C ⟶ D} : (F ◯ G) ◯ H ⟹ F ◯ (G ◯ H).
Proof. transform; simpl; intros; cat. Defined.

Lemma fun_comp_assoc_and_sym `(F : A ⟶ B) `(G : B ⟶ C) `(H : C ⟶ D) (x : A) :
  fun_comp_assoc x ∘ fun_comp_assoc_sym x ≈ fmap[H] (fmap[G] (fmap[F] id)).
Proof. simpl; cat. Qed.

Lemma fun_comp_assoc_sym_and `(F : A ⟶ B) `(G : B ⟶ C) `(H : C ⟶ D) (x : A) :
  fun_comp_assoc_sym x ∘ fun_comp_assoc x ≈ fmap[H] (fmap[G] (fmap[F] id)).
Proof. simpl; cat. Qed.

Program Definition nat_id `{F : C ⟶ D} : F ⟹ F := {|
  transform := λ X, fmap (@id C X)
|}.

#[export] Hint Unfold nat_id : core.

Program Definition nat_compose `{F : C ⟶ D} {G : C ⟶ D} {K : C ⟶ D}
  (f : G ⟹ K) (g : F ⟹ G) : F ⟹ K := {|
  transform := λ X, transform[f] X ∘ transform[g] X
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
  now apply nat_compose_obligation_1.
Qed.

#[export] Hint Unfold nat_compose : core.

Notation "F ∙ G" := (@nat_compose _ _ _ _ _ F G) (at level 40, left associativity).

Program Definition nat_compose_respects
        `{F : C ⟶ D} {G : C ⟶ D} {K : C ⟶ D} :
  Proper (equiv ==> equiv ==> equiv) (@nat_compose C D F G K).
Proof. proper. Qed.

#[export]
Program Instance Transform_PreOrder {C E : Category} :
  PreOrder (@Transform C E).
Next Obligation.
  exact (λ _, nat_id).
Defined.
Next Obligation.
  exact (λ _ _ _ f g, nat_compose g f).
Defined.

#[export]
Program Instance Transform_respects {C D : Category} :
  Proper ((λ F G, G ⟹ F) ==> @Transform C D ==> arrow) (@Transform C D) :=
  λ _ _ F _ _ G H, nat_compose G (nat_compose H F).

(* Wikipedia: "Natural transformations also have a "horizontal composition".
   If η : F → G is a natural transformation between functors F,G : C → D and ε
   : J → K is a natural transformation between functors J,K : D → E, then the
   composition of functors allows a composition of natural transformations
   ε ∘ η : J ◯ F → K ◯ G. This operation is also associative with identity,
   and the identity coincides with that for vertical composition. The two
   operations are related by an identity which exchanges vertical composition
   with horizontal composition." *)

Program Definition nat_hcompose {C D E} {F G : C ⟶ D} {J K : D ⟶ E}
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
  symmetry.
  now apply nat_hcompose_obligation_1.
Qed.

#[export]
Program Instance Compose_respects_Transform {C D E : Category} :
  Proper (@Transform D E ==> @Transform C D ==> @Transform C E)
         (@Compose C D E) :=
  λ _ F M G _ N,
    {| transform := λ x, fmap[F] (transform[N] x) ∘ transform[M] (G x) |}.
Next Obligation.
  simpl.
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite naturality.
  rewrite naturality.
  rewrite naturality.
  rewrite fmap_comp.
  cat.
Qed.
Next Obligation.
  symmetry.
  now apply Compose_respects_Transform_obligation_1.
Qed.

Program Definition whisker_right {C D : Category} {F G : C ⟶ D} `(N : F ⟹ G)
        {E : Category} (X : E ⟶ C) : F ◯ X ⟹ G ◯ X := {|
  transform := λ x, N (X x);

  naturality     := λ _ _ _, naturality;
  naturality_sym := λ _ _ _, naturality_sym
|}.

Notation "N ⊲ F" := (whisker_right N F) (at level 10).

Program Definition whisker_left {C D : Category}
        {E : Category} (X : D ⟶ E)
        {F G : C ⟶ D} `(N : F ⟹ G) : X ◯ F ⟹ X ◯ G := {|
  transform := λ x, fmap[X] (N x)
|}.
Next Obligation.
  simpl; rewrite <- !fmap_comp;
  apply fmap_respects, naturality.
Qed.
Next Obligation.
  simpl; rewrite <- !fmap_comp;
  apply fmap_respects, naturality_sym.
Qed.

Notation "F ⊳ N" := (whisker_left F N) (at level 10).
