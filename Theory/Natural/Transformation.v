Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Naturality.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Transform.

Context {C : Category}.
Context {D : Category}.
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

Global Program Instance Transform_Setoid : Setoid Transform.

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
Proof. transform; simpl; intros; cat. Qed.

Corollary fun_id_left_sym {C D : Category} {F : C ⟶ D} : F ⟹ Id ◯ F.
Proof. transform; simpl; intros; cat. Qed.

Corollary fun_id_right {C D : Category} {F : C ⟶ D} : F ◯ Id ⟹ F.
Proof. transform; simpl; intros; cat. Qed.

Corollary fun_id_right_sym {C D : Category} {F : C ⟶ D} : F ⟹ F ◯ Id.
Proof. transform; simpl; intros; cat. Qed.

Corollary fun_comp_assoc {C D E B : Category}
      {F : E ⟶ B} {G : D ⟶ E} {H : C ⟶ D} : F ◯ (G ◯ H) ⟹ (F ◯ G) ◯ H.
Proof. transform; simpl; intros; cat. Qed.

Corollary fun_comp_assoc_sym {C D E B : Category}
          {F : E ⟶ B} {G : D ⟶ E} {H : C ⟶ D} : (F ◯ G) ◯ H ⟹ F ◯ (G ◯ H).
Proof. transform; simpl; intros; cat. Qed.

Program Definition whisker_right {C D : Category} {F G : C ⟶ D} `(N : F ⟹ G)
        {E : Category} (X : E ⟶ C) : F ◯ X ⟹ G ◯ X := {|
  transform := fun x => N (X x);

  naturality     := fun _ _ _ => naturality;
  naturality_sym := fun _ _ _ => naturality_sym
|}.

Notation "N ⊲ F" := (whisker_right N F) (at level 10).

Program Definition whisker_left {C D : Category}
        {E : Category} (X : D ⟶ E)
        {F G : C ⟶ D} `(N : F ⟹ G) : X ◯ F ⟹ X ◯ G := {|
  transform := fun x => fmap[X] (N x)
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

Global Program Definition nat_id `{F : C ⟶ D} : F ⟹ F := {|
  transform := fun X => fmap (@id C X)
|}.

Hint Unfold nat_id : core.

Program Instance Transform_reflexive {C D : Category} :
  Reflexive (@Transform C D) :=
  fun _ => nat_id.

Global Program Definition nat_compose `{F : C ⟶ D} {G : C ⟶ D} {K : C ⟶ D}
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

Program Instance Transform_transitive {C E : Category} :
  Transitive (@Transform C E) :=
  fun _ _ _ f g => nat_compose g f.

Program Instance Transform_respects {C D : Category} :
  Proper (@Transform C D --> @Transform C D ==> Basics.arrow) (@Transform C D).
Next Obligation.
  proper.
  unfold Basics.flip in X.
  transitivity x0; auto.
  transitivity x; auto.
Qed.

Program Instance Compose_Transform_respects {C D E : Category} :
  Proper (@Transform D E ==> @Transform C D ==> @Transform C E) (@Compose C D E).
Next Obligation.
  proper.
  transform; simpl; intros.
  - destruct X, X0; simpl in *.
    exact (fmap (transform1 x1) ∘ transform0 (fobj[x0] x1)).
  - simpl.
    rewrite comp_assoc.
    rewrite <- fmap_comp.
    rewrite naturality.
    rewrite naturality.
    rewrite naturality.
    rewrite fmap_comp.
    cat.
  - simpl.
    rewrite comp_assoc.
    rewrite <- fmap_comp.
    rewrite naturality.
    rewrite naturality.
    rewrite naturality.
    rewrite fmap_comp.
    cat.
Qed.

(** jww (2021-08-07): Get rewriting to work whenever there is a function F ⟶
    G, or a natural transformation F ⟹ G, treating it as an implication.
    Likewise F ≅ G should rewrite as if it were an equivalence. *)
