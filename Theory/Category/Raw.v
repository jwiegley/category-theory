Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Reserved Infix "~>⁻" (at level 90, right associativity).
Reserved Infix "∘⁻" (at level 40, left associativity).

Class RawCategory := {
  r_obj : Type;

  r_uhom := Type : Type;
  r_hom : r_obj -> r_obj -> r_uhom where "a ~>⁻ b" := (r_hom a b);

  r_id {x} : r_hom x x;
  r_compose {x y z} (f: r_hom y z) (g : r_hom x y) : r_hom x z
    where "f ∘⁻ g" := (r_compose f g);
}.

Declare Scope raw_category_scope.
Declare Scope raw_object_scope.
Declare Scope raw_morphism_scope.

Bind Scope raw_category_scope with RawCategory.
Bind Scope raw_object_scope with r_obj.

Delimit Scope raw_category_scope with raw_category.
Delimit Scope raw_object_scope with raw_object.
Delimit Scope raw_morphism_scope with raw_morphism.

Notation "x ~>⁻ y" := (@r_hom _%raw_category x%raw_object y%raw_object)
  (at level 90, right associativity) : type_scope.
Notation "f ∘⁻ g" :=
  (@r_compose _%raw_category _%raw_object _%raw_object _%raw_object f%raw_morphism g%raw_morphism)
  : raw_morphism_scope.

Coercion r_obj : RawCategory >-> Sortclass.

Definition From_RawCategory
           (raw : RawCategory)
           {homset} {compose_respects}
           {id_left id_right comp_assoc} : Category :=
  {| obj              := r_obj;
     hom              := r_hom;
     homset           := homset;
     id               := @r_id raw;
     compose          := @r_compose raw;
     compose_respects := compose_respects;
     id_left          := id_left;
     id_right         := id_right;
     comp_assoc       := comp_assoc;
     comp_assoc_sym   :=
       fun _ _ _ _ _ _ _ => symmetry (@comp_assoc _ _ _ _ _ _ _) |}.

Open Scope raw_morphism_scope.

(** A [Denotation] is a Functor from a lawless "category" to a lawful
    category. This is enough to establish the laws of the source category via
    the homomorphisms [h_id] and [h_compose], so long as the equivalences of
    the source category are defined in terms of the [denote] function. See
    [DerivedEquivalence] below. *)
Class Denotation {C : RawCategory} {D : Category} := {
  dobj : C -> D;
  denote {x y : C} (f : x ~>⁻ y) : dobj x ~> dobj y;

  h_id (x : C) : @denote x x r_id ≈ id;
  h_compose (x y z : C) (f : y ~>⁻ z) (g : x ~>⁻ y) :
    denote (f ∘⁻ g) ≈ denote f ∘ denote g
}.

Coercion dobj : Denotation >-> Funclass.

Notation "C ⟶⁻ D" := (@Denotation C%raw_category D%category)
  (at level 90, right associativity) : type_scope.

Program Definition DerivedEquivalence
        `(F : C ⟶⁻ D) : ∀ X Y, Setoid (X ~>⁻ Y) := fun X Y =>
  {| equiv := fun f g => denote f ≈ denote g
   ; setoid_equiv := _ |}.

(** Given a lawless "category", a lawful category, and a denotation from the
    former to the latter, return a re-definition of the source as a lawful
    category, by way of that denotation. *)
Program Definition LawfulCategory `{F : C ⟶⁻ D} : Category :=
  @From_RawCategory C (DerivedEquivalence F) _ _ _ _.
Next Obligation. proper; now rewrite !h_compose, X, X0. Qed.
Next Obligation. rewrite h_compose, h_id; now cat. Qed.
Next Obligation. rewrite h_compose, h_id; now cat. Qed.
Next Obligation. rewrite !h_compose; now cat. Qed.
