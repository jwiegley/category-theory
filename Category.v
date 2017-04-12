Require Import Lib.

Generalizable All Variables.

Reserved Infix "∘" (at level 30, right associativity).
Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "≈" (at level 79).

Class Category (ob : Type) := {
  uhom := Type : Type;
  hom  : ob → ob → uhom where "a ~> b" := (hom a b);

  id {A} : A ~> A;
  compose {A B C} (f: B ~> C) (g : A ~> B) : A ~> C
    where "f ∘ g" := (compose f g);

  eqv {A B : ob} : relation (A ~> B)
    where "f ≈ g" := (eqv f g);

  eqv_equivalence : ∀ A B, Equivalence (@eqv A B);
  compose_respects : ∀ A B C,
    Proper (@eqv B C ==> @eqv A B ==> @eqv A C) compose;

  id_left {X Y} (f : X ~> Y) : id ∘ f ≈ f;
  id_right {X Y} (f : X ~> Y) : f ∘ id ≈ f;

  comp_assoc {X Y Z W} (f : Z ~> W) (g : Y ~> Z) (h : X ~> Y) :
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
}.

Infix "~>" := hom : category_scope.
Infix "≈" := eqv : category_scope.
Infix "~{ C }~>" := (@hom C _) (at level 90) : category_scope.
Infix "∘" := compose : category_scope.

Notation "id[ X  ]" := (@id _ _ X)  (at level 50) : category_scope.

Hint Rewrite @id_left : categories.
Hint Rewrite @id_right : categories.

Ltac cat := autorewrite with categories; auto with category_laws.

Global Program Instance parametric_relation_eqv `{Category C} {a b : C} :
  Equivalence (@eqv C _ a b) := eqv_equivalence a b.

Global Program Instance parametric_morphism_compose `{Category C} {a b c : C} :
  Proper (eqv ==> eqv ==> eqv) (@compose C _ a b c) := compose_respects a b c.

Global Program Instance impl_eqv `{Category C} {a b : C} :
  Proper (eqv --> @eqv _ _ a b ++> Basics.impl) eqv.
Obligation 1.
  intros ???????.
  transitivity x; auto.
  transitivity x0; auto.
Qed.

Global Program Instance flip_impl_eqv `{Category C} (a b : C) :
  Proper (eqv --> @eqv _ _ a b ++> Basics.flip Basics.impl) eqv.
Obligation 1.
  intros ???????.
  unfold Basics.flip in H0.
  rewrite <- H0, H1.
  assumption.
Qed.

Hint Constructors Equivalence.

Hint Unfold Reflexive.
Hint Unfold Symmetric.
Hint Unfold Transitive.

Hint Extern 1 (Proper _ _) => unfold Proper; auto.
Hint Extern 1 (Reflexive ?X) => unfold Reflexive; auto.
Hint Extern 1 (Symmetric ?X) => unfold Symmetric; intros; auto.
Hint Extern 1 (Transitive ?X) => unfold Transitive; intros; auto.
Hint Extern 1 (Equivalence ?X) => apply Build_Equivalence.
Hint Extern 8 (respectful _ _ _ _) => unfold respectful; auto.

Hint Extern 4 (?A ≈ ?A) => reflexivity : category_laws.
Hint Extern 6 (?X ≈ ?Y) => apply Equivalence_Symmetric : category_laws.
Hint Extern 7 (?X ≈ ?Z) =>
  match goal with
    [H : ?X ≈ ?Y, H' : ?Y ≈ ?Z |- ?X ≈ ?Z] => transitivity Y
  end : category_laws.
Hint Extern 10 (?X ∘ ?Y ≈ ?Z ∘ ?Q) =>
  apply compose_respects; auto : category_laws.
