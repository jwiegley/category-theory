Require Import Category.Lib.

Generalizable All Variables.

Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "∘" (at level 40, left associativity).

(* nLab: https://ncatlab.org/nlab/show/category
   Wikipedia: https://en.wikipedia.org/wiki/Category_(mathematics)

   A category C consists of a collection of objects, a hom `x ~> y` of
   morphisms for each pair of objects, an identity `id : x ~> x` for each
   object, and a composition `f ∘ g : x ~> z` for `g : x ~> y` and
   `f : y ~> z`, subject to the unit laws `id ∘ f ≈ f` and `f ∘ id ≈ f` and
   the associativity law `f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h`. Here the hom is a
   setoid (a hom-setoid) rather than a bare set, so morphism equality is the
   chosen equivalence `≈` rather than Coq's `=`.

   The objects of a category are all of some `Type`.

  Morphisms, or arrows, are also of type `Type`, but always in a universe
  above objects. All of the library has `Universe Polymorphism` enabled,
  allowing categories whose objects are categories, etc.

  The morphisms identified by `A ~> B` form a hom-set, except that in this
  library it is a hom-setoid, requiring the meaning of (computationally
  relevant) equivalence between morphisms to be given. This makes it a
  quotient category C/R over the equivalence relation R, but since this is
  almost always needed (since equality is very restrictive in Coq's type
  theory), we call it a [Category] here, and assume the existence of some
  other category using only equality, with a functor from that category to
  this.

  Categories (as distinct from Category/~) are identified by [homset :=
  Morphism_equality]. *)

Class Category@{o h p | h <= p} : Type@{max(o+1,h+1,p+1)} := {
  obj : Type@{o};                       (* collection of objects *)

  uhom := Type@{h} : Type@{h+1};        (* universe of hom-setoids *)
  hom : obj → obj → uhom where "a ~> b" := (hom a b);  (* morphisms x ~> y *)
  homset : ∀ X Y, Setoid@{h p} (X ~> Y);  (* hom is a setoid; equality is ≈ *)

  id {x} : x ~> x;                      (* identity morphism on x *)
  compose {x y z} (f: y ~> z) (g : x ~> y) : x ~> z
    where "f ∘ g" := (compose f g);     (* composition f ∘ g *)

  compose_respects {x y z} :            (* compose respects ≈ (bifunctorial Proper) *)
    Proper@{h p} (respectful@{h p h p h p} equiv
                    (respectful@{h p h p h p} equiv equiv))
      (@compose x y z);

  dom {x y} (f : x ~> y) := x;          (* domain (source) of a morphism *)
  cod {x y} (f : x ~> y) := y;          (* codomain (target) of a morphism *)

  id_left  {x y} (f : x ~> y) : id ∘ f ≈ f;  (* left unit law *)
  id_right {x y} (f : x ~> y) : f ∘ id ≈ f;  (* right unit law *)

  comp_assoc {x y z w} (f : z ~> w) (g : y ~> z) (h : x ~> y) :
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h;         (* associativity *)
  comp_assoc_sym {x y z w} (f : z ~> w) (g : y ~> z) (h : x ~> y) :
    (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)          (* associativity, dual form (built-in duality) *)
}.
#[export] Existing Instance homset.
#[export] Existing Instance compose_respects.

Declare Scope category_scope.
Declare Scope object_scope.
Declare Scope homset_scope.
Declare Scope morphism_scope.

Bind Scope category_scope with Category.
Bind Scope object_scope with obj.
Bind Scope homset_scope with hom.

Delimit Scope category_scope with category.
Delimit Scope object_scope with object.
Delimit Scope homset_scope with homset.
Delimit Scope morphism_scope with morphism.

Arguments dom {_%_category _%_object _%_object} _%_morphism.
Arguments cod {_%_category _%_object _%_object} _%_morphism.

Notation "obj[ C ]" := (@obj C%category)
  (at level 0, format "obj[ C ]") : type_scope.
Notation "hom[ C ]" := (@hom C%category)
  (at level 0, format "hom[ C ]") : type_scope.

Notation "x ~> y" := (@hom _%category x%object y%object)
  (at level 90, right associativity) : homset_scope.
Notation "x ~{ C }~> y" := (@hom C%category x%object y%object)
  (at level 90) : homset_scope.

Notation "x <~ y" := (@hom _%category y%object x%object)
  (at level 90, right associativity, only parsing) : homset_scope.
Notation "x <~{ C }~ y" := (@hom C%category y%object x%object)
  (at level 90, only parsing) : homset_scope.

Notation "id[ x ]" := (@id _%category x%object)
  (at level 9, format "id[ x ]") : morphism_scope.

Notation "id{ C }" := (@id C%category _%object)
  (at level 9, format "id{ C }") : morphism_scope.

Notation "f ∘ g" :=
  (@compose _%category _%object _%object _%object f%morphism g%morphism)
  : morphism_scope.
Notation "f ∘[ C ] g" :=
  (@compose C%category _%object _%object _%object f%morphism g%morphism)
  (at level 40, only parsing) : morphism_scope.

Notation "f ≈[ C ] g" :=
  (@equiv _ (@homset C%category _%object _%object) f%morphism g%morphism)
  (at level 79, only parsing) : category_theory_scope.
Notation "f ≈[ C ] g" :=
  (@equiv _ (@homset C%category _%object _%object) f%morphism g%morphism)
  (at level 79, only parsing) : category_theory_scope.

Notation "f << A ~~> B >> g" :=
  (@equiv (A%object ~> B%object)%homset _ f%morphism g%morphism)
  (at level 99, A at next level, B at next level, only parsing) : category_theory_scope.

Coercion obj : Category >-> Sortclass.

#[export] Hint Rewrite @id_left : categories.
#[export] Hint Rewrite @id_right : categories.

(* [Build_Category'] is a custom constructor that automatically provides the
   definition of [comp_assoc_sym] from [comp_assoc] by symmetry. It is intended
   to be used with the [refine] tactic, such as in the example below. *)
Definition Build_Category'
           {obj} hom {homset} id compose
           {compose_respects}
           {id_left id_right comp_assoc} :=
  {| obj              := obj;
     hom              := hom;
     homset           := homset;
     id               := id;
     compose          := compose;
     compose_respects := compose_respects;
     id_left          := id_left;
     id_right         := id_right;
     comp_assoc       := comp_assoc;
     comp_assoc_sym   :=
       fun _ _ _ _ _ _ _ => symmetry (@comp_assoc _ _ _ _ _ _ _);
  |}.

Example Build_Category'_Coq : Category.
Proof.
  unshelve refine (Build_Category' (@Basics.arrow)
                                   (@Datatypes.id) (@Basics.compose));
  intros; try reflexivity.
  - refine {| equiv := fun f g => ∀ x, f x = g x |}.
    equivalence.
    now transitivity (y x0).
  - proper.
    now rewrite X, X0.
Defined.

Open Scope category_scope.
Open Scope object_scope.
Open Scope homset_scope.
Open Scope morphism_scope.

(* The hom-setoid whose equivalence is Coq's strict equality `eq`. Equipping a
   hom with this `Setoid` recovers the classical (non-quotient) notion of a
   category, where two morphisms are equal only when definitionally equal. *)
Program Definition Morphism_equality@{o h p}
  {ob : Type@{o}} {hom : ob → ob → Type@{h}}
  (x y : ob) : Setoid@{h p} (hom x y) := {|
  equiv := eq
|}.
Arguments Morphism_equality {_ _} _ _ /.

Section Category.

Context {C : Category}.

Corollary dom_id {x : C} : dom (@id C x) = x.
Proof. auto. Qed.

Corollary cod_id {x : C} : cod (@id C x) = x.
Proof. auto. Qed.

Corollary dom_comp {x y z : C} (g : y ~> z) (f : x ~> y) :
  dom g = cod f ↔ dom (g ∘ f) = dom f.
Proof. split; auto. Qed.

Corollary cod_comp {x y z : C} (g : y ~> z) (f : x ~> y) :
  dom g = cod f ↔ cod (g ∘ f) = cod g.
Proof. split; auto. Qed.

End Category.

Arguments dom {_%_category _%_object _%_object} _%_morphism.
Arguments cod {_%_category _%_object _%_object} _%_morphism.
Arguments id_left {_%_category _%_object _%_object} _%_morphism.
Arguments id_right {_%_category _%_object _%_object} _%_morphism.
Arguments comp_assoc {_%_category _%_object _%_object _%_object _%_object}
  _%_morphism _%_morphism _%_morphism.

(* The hom relation of any category is a preorder on objects: reflexivity is
   witnessed by `id` and transitivity by composition (note the order: `g ∘ f`
   for `f : x ~> y` and `g : y ~> z`). This is the standard observation that a
   category has an underlying preorder of objects (a preorder is exactly a thin
   category). *)
#[export]
Program Instance hom_preorder {C : Category} : PreOrder (@hom C) := {
  PreOrder_Reflexive  := fun _ => id;
  PreOrder_Transitive := fun _ _ _ f g => g ∘ f
}.

Ltac comp_left :=
  try rewrite <- !comp_assoc;
  apply compose_respects; [reflexivity|].

Ltac comp_right :=
  try rewrite !comp_assoc;
  apply compose_respects; [|reflexivity].

#[export] Hint Extern 10 (?X ∘ ?Y ≈ ?Z ∘ ?Q) =>
  apply compose_respects; auto : category_laws.
#[export] Hint Extern 10 (?X ∘ (?Y ∘ ?Z) ≈ ?W) =>
  apply comp_assoc : category_laws.

Ltac rewrites :=
  repeat match goal with
  | [ H : ?X ≈ ?Y                      |- context[?X] ] => rewrite !H; clear H
  | [ H : ?X ≈ ?Y                      |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _, ?X ≈ ?Y                 |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _, ?X ≈ ?Y                 |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _, ?X _ ≈ ?Y _             |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _, ?X _ ≈ ?Y _             |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _, ?X ≈ ?Y               |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _, ?X ≈ ?Y               |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _, ?X _ ≈ ?Y _           |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _, ?X _ ≈ ?Y _           |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _, ?X _ _ ≈ ?Y _ _       |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _, ?X _ _ ≈ ?Y _ _       |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _ _, ?X ≈ ?Y             |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _ _, ?X ≈ ?Y             |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _ _, ?X _ ≈ ?Y _         |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _ _, ?X _ ≈ ?Y _         |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _ _, ?X _ _ ≈ ?Y _ _     |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _ _, ?X _ _ ≈ ?Y _ _     |- context[?X] ] => srewrite H; clear H
  | [ H : ∀ _ _ _, ?X _ _ _ ≈ ?Y _ _ _ |- context[?X] ] => rewrite !H; clear H
  | [ H : ∀ _ _ _, ?X _ _ _ ≈ ?Y _ _ _ |- context[?X] ] => srewrite H; clear H

  | [ H : ?X ≈ ?Y                      |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ?X ≈ ?Y                      |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _, ?X ≈ ?Y                 |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _, ?X ≈ ?Y                 |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _, ?X _ ≈ ?Y _             |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _, ?X _ ≈ ?Y _             |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _ _, ?X ≈ ?Y               |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _, ?X ≈ ?Y               |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _ _, ?X _ ≈ ?Y _           |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _, ?X _ ≈ ?Y _           |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _ _, ?X _ _ ≈ ?Y _ _       |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _, ?X _ _ ≈ ?Y _ _       |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _ _ _, ?X ≈ ?Y             |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _ _, ?X ≈ ?Y             |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _ _ _, ?X _ ≈ ?Y _         |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _ _, ?X _ ≈ ?Y _         |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _ _ _, ?X _ _ ≈ ?Y _ _     |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _ _, ?X _ _ ≈ ?Y _ _     |- context[?Y] ] => srewrite_r H; clear H
  | [ H : ∀ _ _ _, ?X _ _ _ ≈ ?Y _ _ _ |- context[?Y] ] => rewrite <- !H; clear H
  | [ H : ∀ _ _ _, ?X _ _ _ ≈ ?Y _ _ _ |- context[?Y] ] => srewrite_r H; clear H
  end.
