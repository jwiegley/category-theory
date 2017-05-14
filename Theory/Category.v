Set Warnings "-notation-overridden".

Require Import Category.Lib.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "∘" (at level 40, left associativity).

Notation "f ≈ g" := (equiv f g)
  (at level 79, only parsing) : category_theory_scope.

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

  dom {A B} (f: A ~> B) := A;
  cod {A B} (f: A ~> B) := B;

  id_left  {X Y} (f : X ~> Y) : id ∘ f ≈ f;
  id_right {X Y} (f : X ~> Y) : f ∘ id ≈ f;

  comp_assoc {X Y Z W} (f : Z ~> W) (g : Y ~> Z) (h : X ~> Y) :
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h;

  comp_assoc_sym {X Y Z W} (f : Z ~> W) (g : Y ~> Z) (h : X ~> Y) :
    (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
}.

Bind Scope category_scope with Category.
Bind Scope homset_scope with hom.
Bind Scope object_scope with ob.

Delimit Scope category_scope with category.
Delimit Scope object_scope with object.
Delimit Scope homset_scope with homset.
Delimit Scope morphism_scope with morphism.

Arguments dom {_%category _%object _%object} _%morphism.
Arguments cod {_%category _%object _%object} _%morphism.

Notation "ob[ C ]" := (@ob C%category)
  (at level 0, format "ob[ C ]") : object_scope.

Notation "X ~> Y" := (@hom _%category X%object Y%object)
  (at level 90, right associativity) : homset_scope.
Notation "X ~{ C }~> Y" := (@hom C%category X%object Y%object)
  (at level 90) : homset_scope.

Notation "X <~ Y" := (@hom _%category Y%object X%object)
  (at level 90, right associativity, only parsing) : homset_scope.
Notation "X <~{ C }~ Y" := (@hom C%category Y%object X%object)
  (at level 90, only parsing) : homset_scope.

Notation "id[ X ]" := (@id _%category X%object)
  (at level 50, format "id[ X ]") : morphism_scope.

Notation "f ∘ g" :=
  (@compose _%category _%object _%object _%object f%morphism g%morphism)
  : morphism_scope.
Notation "f ∘[ C ] g" :=
  (@compose C%category _%object _%object _%object _%morphism _%morphism)
  (at level 40, only parsing) : morphism_scope.

Notation "f ≈ g" :=
  (@equiv _ (@homset _%category _%object _%object) f%morphism g%morphism)
  (at level 79) : category_theory_scope.
Notation "f ≈[ C ] g" :=
  (@equiv _ (@homset C%category _%object _%object) f%morphism g%morphism)
  (at level 79, only parsing) : category_theory_scope.
Notation "f ≈[ C ] g" :=
  (@equiv _ (@homset C%category _%object _%object) f%morphism g%morphism)
  (at level 79, only parsing) : category_theory_scope.

Notation "f << A ~~> B >> g" :=
  (@equiv (A%object ~> B%object)%homset _ f%morphism g%morphism)
  (at level 99, A at next level, B at next level, only parsing,
   format "'[v' f '/'   <<  A  ~~>  B  >> '//' g ']'") : category_theory_scope.

Coercion ob : Category >-> Sortclass.

Hint Rewrite @id_left : categories.
Hint Rewrite @id_right : categories.

Open Scope category_scope.
Open Scope object_scope.
Open Scope homset_scope.
Open Scope morphism_scope.

Section Category.

Context `{C : Category}.

Corollary dom_id {X : C} : dom (@id C X) = X.
Proof. auto. Qed.

Corollary cod_id {X : C} : dom (@id C X) = X.
Proof. auto. Qed.

Corollary dom_comp {X Y Z : C} (g : Y ~> Z) (f : X ~> Y) :
  dom g = cod f <-> dom (g ∘ f) = dom f.
Proof. split; auto. Qed.

Corollary cod_comp {X Y Z : C} (g : Y ~> Z) (f : X ~> Y) :
  dom g = cod f <-> cod (g ∘ f) = cod g.
Proof. split; auto. Qed.

End Category.

Arguments dom {_ _ _} _.
Arguments cod {_ _ _} _.
Arguments id_left {_ _ _} _.
Arguments id_right {_ _ _} _.
Arguments comp_assoc {_ _ _ _ _} _ _ _.

Program Instance hom_preorder `{C : Category} : PreOrder (@hom C) := {
  PreOrder_Reflexive  := fun _ => id;
  PreOrder_Transitive := fun _ _ _ f g => g ∘ f
}.

Ltac reassoc f :=
  repeat match goal with
    | [ |- context[(?F ∘ f) ∘ ?G] ] => rewrite <- (comp_assoc F f G)
    | [ |- context[f ∘ (?G ∘ ?H)] ] => rewrite (comp_assoc f G H)
    end.

Ltac reassoc_before f g :=
  repeat match goal with
    | [ |- context[(?F ∘ f) ∘ g] ] => rewrite <- (comp_assoc F f g)
    | [ |- context[f ∘ (g ∘ ?H)] ] => rewrite (comp_assoc f g H)
    end.

Ltac reassoc_after g f :=
  repeat match goal with
    | [ |- context[(?F ∘ g) ∘ f] ] => rewrite <- (comp_assoc F g f)
    | [ |- context[g ∘ (f ∘ ?H)] ] => rewrite (comp_assoc g f H)
    end.

Ltac equiv :=
  repeat match goal with
  | [ H : equiv (?F ∘ ?G) _
    |- context[(_ ∘ ?F) ∘ (?G ∘ _)] ] => reassoc F; rewrite H
  | [ H : equiv (?F ∘ ?G) _
    |- context[?F ∘ (?G ∘ _)] ] => reassoc F; rewrite H
  | [ H : equiv (?F ∘ ?G) _
    |- context[(_ ∘ ?F) ∘ ?G] ] => reassoc F; rewrite H
  | [ H : equiv (?F ∘ ?G) _
    |- context[?F ∘ ?G] ] => rewrite H
  | [ |- equiv ?F ?F ] => reflexivity
  | [ |- context[id ∘ ?F] ] => rewrite (id_left F)
  | [ |- context[?F ∘ id] ] => rewrite (id_right F)
  end.

Hint Extern 10 (?X ∘ ?Y ≈ ?Z ∘ ?Q) =>
  apply compose_respects; auto : category_laws.
Hint Extern 10 (?X ∘ (?Y ∘ ?Z) ≈ ?W) =>
  rewrite <- comp_assoc; cat : category_laws.
Hint Extern 10 ((?X ∘ ?Y) ∘ ?Z ≈ ?W) =>
  rewrite comp_assoc; cat : category_laws.
