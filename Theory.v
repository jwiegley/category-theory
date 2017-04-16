Require Import Category.Lib.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Infix "≈" := equiv (at level 79) : category_scope.

Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "∘" (at level 30, right associativity).

Class Category := {
  ob : Type;

  uhom := Type : Type;
  hom : ob -> ob -> uhom where "a ~> b" := (hom a b);

  homset :> ∀ X Y, Setoid (X ~> Y);

  id {A} : A ~> A;
  compose {A B C} (f: B ~> C) (g : A ~> B) : A ~> C
    where "f ∘ g" := (compose f g);

  compose_respects (X Y Z : ob) :>
    Proper (equiv ==> equiv ==> equiv) (@compose X Y Z);

  id_left  {X Y} (f : X ~> Y) : id ∘ f ≈ f;
  id_right {X Y} (f : X ~> Y) : f ∘ id ≈ f;

  comp_assoc {X Y Z W} (f : Z ~> W) (g : Y ~> Z) (h : X ~> Y) :
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
}.

Infix "~>" := hom (at level 90, right associativity) : category_scope.
Infix "~{ C }~>" := (@hom C) (at level 90) : category_scope.
Infix "∘" := compose : category_scope.

Notation "id[ X  ]" := (@id _ X)  (at level 50) : category_scope.

Coercion ob : Category >-> Sortclass.

Hint Rewrite @id_left : categories.
Hint Rewrite @id_right : categories.

Ltac cat :=
  autorewrite with categories; auto with category_laws; try reflexivity.

Lemma eq_eqv `{C : Category} {X Y : C} (f g : X ~> Y) :
  f = g -> f ≈ g.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

(*
Program Instance impl_eqv `{C : Category} {a b : C} :
  Proper (equiv --> equiv ++> Basics.impl) equiv.
Obligation 1.
  intros ???????.
  transitivity x; auto.
  transitivity x0; auto.
Qed.

Program Instance flip_impl_eqv `{C : Category} (a b : C) :
  Proper (eqv --> @eqv C a b ++> Basics.flip Basics.impl) eqv.
Obligation 1.
  intros ???????.
  unfold Basics.flip in H.
  rewrite <- H, H0.
  assumption.
Qed.
*)

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
