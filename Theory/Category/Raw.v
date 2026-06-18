Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

Reserved Infix "~>⁻" (at level 90, right associativity).
Reserved Infix "∘⁻" (at level 40, left associativity).

(* nLab: https://ncatlab.org/nlab/show/category
   Wikipedia: https://en.wikipedia.org/wiki/Category_(mathematics)

   A [RawCategory] is the bare data of a category -- objects, a hom for each
   pair of objects, an identity for each object, and a composition -- WITHOUT
   any of the structure that [Category] (Theory/Category.v) adds on top:

     - there is no [homset] field, so the hom `a ~>⁻ b` is a plain [Type]
       rather than a setoid, and there is no chosen equivalence `≈` on
       morphisms; and
     - there are no unit or associativity laws.

   So a [RawCategory] is a "lawless category": the signature of a category
   stripped of both the hom-setoid quotient and the categorical axioms. This
   is the "other category using only equality, with a functor from that
   category to this" that Theory/Category.v anticipates: rather than discharge
   the laws directly (often awkward under Coq's restrictive `=`), one defines
   the raw data here and recovers a lawful [Category] through a [Denotation]
   (a functor into a lawful category, see below). The decorated notations
   `~>⁻` and `∘⁻` mirror `~>` and `∘` from Theory/Category.v. *)
Class RawCategory := {
  r_obj : Type;                         (* collection of objects *)

  r_uhom := Type : Type;                (* universe of homs (bare Types) *)
  r_hom : r_obj → r_obj → r_uhom where "a ~>⁻ b" := (r_hom a b);  (* morphisms x ~>⁻ y *)

  r_id {x} : r_hom x x;                 (* identity morphism on x *)
  r_compose {x y z} (f: r_hom y z) (g : r_hom x y) : r_hom x z
    where "f ∘⁻ g" := (r_compose f g);  (* composition f ∘⁻ g *)
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

(* Assemble a lawful [Category] from raw data once the missing setoid
   ([homset]), the [Proper] respectfulness of composition, and the unit and
   associativity laws are supplied externally. The dual associativity law
   [comp_assoc_sym] (present for the built-in duality of Theory/Category.v) is
   filled in here by symmetry of [comp_assoc], so it need not be given. *)
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

(* nLab: https://ncatlab.org/nlab/show/functor
   Wikipedia: https://en.wikipedia.org/wiki/Functor

   A [Denotation] is a functor from a lawless [RawCategory] C to a lawful
   [Category] D: an object map [dobj], a morphism map [denote], and the two
   functoriality laws preserving identities ([h_id]) and composition
   ([h_compose]). Because D is lawful and equality of source morphisms is
   defined by their image under [denote] (see [DerivedEquivalence] below),
   these two laws are enough to transport D's unit and associativity laws back
   onto C, recovering a lawful [Category] (see [LawfulCategory] below). *)
Class Denotation {C : RawCategory} {D : Category} := {
  dobj : C → D;                                   (* object map  C₀ → D₀ *)
  denote {x y : C} (f : x ~>⁻ y) : dobj x ~> dobj y;  (* morphism map on homs *)

  h_id (x : C) : @denote x x r_id ≈ id;           (* preserves identities *)
  h_compose (x y z : C) (f : y ~>⁻ z) (g : x ~>⁻ y) :
    denote (f ∘⁻ g) ≈ denote f ∘ denote g         (* preserves composition *)
}.

Coercion dobj : Denotation >-> Funclass.

Notation "C ⟶⁻ D" := (@Denotation C%raw_category D%category)
  (at level 90, right associativity) : type_scope.

(* The hom-setoid on the raw category induced by a denotation: two raw
   morphisms are equivalent exactly when their images under [denote] are
   equivalent in the lawful target. This is the pullback of D's `≈` along
   [denote], and it is an equivalence relation because `≈` on D is. *)
Program Definition DerivedEquivalence
        `(F : C ⟶⁻ D) : ∀ X Y, Setoid (X ~>⁻ Y) := fun X Y =>
  {| equiv := fun f g => denote f ≈ denote g
   ; setoid_equiv := _ |}.

(* Given a lawless [RawCategory], a lawful [Category], and a denotation from
   the former to the latter, re-present the source as a lawful [Category] by
   way of that denotation: take the derived hom-setoid above, then discharge
   the unit and associativity laws by rewriting with [h_id] and [h_compose]
   and appealing to the corresponding laws of the lawful target. *)
Program Definition LawfulCategory `{F : C ⟶⁻ D} : Category :=
  @From_RawCategory C (DerivedEquivalence F) _ _ _ _.
Next Obligation. proper; now rewrite !h_compose, X, X0. Qed.
Next Obligation. rewrite h_compose, h_id; now cat. Qed.
Next Obligation. rewrite h_compose, h_id; now cat. Qed.
Next Obligation. rewrite !h_compose; now cat. Qed.
