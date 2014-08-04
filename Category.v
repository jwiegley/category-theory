Require Export Coq.Classes.Equivalence.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Setoids.Setoid.
Require Export Coq.Unicode.Utf8.
Require        Setoid.
Require Export CpdtTactics.

Open Scope type_scope.

(* Proof General seems to add an extra two columns of overhead *)

Set Printing Width 130.
Generalizable All Variables.

(* ~> is used to describe morphisms.

   Unicode ≈ means equivalence, while ≅ is isomorphism and = is identity.

   Unicode ∘ is composition of morphisms.

   ~{ C }~> specifically types a morphisms in C.
*)
Reserved Notation "a ~> b" (at level 90, right associativity).
Reserved Notation "f ≈ g" (at level 54).
Reserved Notation "f ∘ g" (at level 45).

(* A Category is defined by objects and morphisms between objects, plus the
   following structure:

   - Every object has an identity morphism.
   - Morphisms compose.

   - Composition respect a monoidal structure: left and right identity with
     identity morphisms, and associativity.

   - There is a notion of equivalence of morphsims in the category.
   - Composition must respect equivalence.
*)
Class Category (Ob : Type) (Hom : Ob -> Ob -> Type) :=
{ hom := Hom where "a ~> b" := (hom a b)
; ob  := Ob

; id : forall {A}, A ~> A
; compose : forall {A B C}, (B ~> C) -> (A ~> B) -> (A ~> C)
    where "f ∘ g" := (compose f g)
; eqv : forall {A B}, (A ~> B) -> (A ~> B) -> Prop where "f ≈ g" := (eqv f g)

; eqv_equivalence : forall {A B}, Equivalence (@eqv A B)
; compose_respects : forall {A B C},
    Proper (@eqv B C ==> @eqv A B ==> @eqv A C) compose

; right_identity : forall {A B} (f : A ~> B), f ∘ id ≈ f
; left_identity : forall {A B} (f : A ~> B), id ∘ f ≈ f
; comp_assoc : forall {A B C D} (f : C ~> D) (g : B ~> C) (h : A ~> B),
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
}.

Coercion ob : Category >-> Sortclass.

Notation "ob/ a" := (ob a) (at level 100) : category_scope.
Notation "a ~> b" := (hom a b) : category_scope.
Notation "f ≈ g" := (eqv f g) : category_scope.
Notation "f ∘ g" := (compose f g) : category_scope.
Notation "a ~{ C }~> b" := (@hom _ _ C a b) (at level 100) : category_scope.

Open Scope category_scope.

Hint Extern 3 => apply compose_respects.
Hint Extern 1 => apply left_identity.
Hint Extern 1 => apply right_identity.

Add Parametric Relation (Ob : Type) (Hom : Ob -> Ob -> Type)
  `(C : Category Ob Hom) (a b : Ob) : (hom a b) (@eqv _ _ C a b)

  reflexivity proved by  (@Equivalence_Reflexive  _ _ eqv_equivalence)
  symmetry proved by     (@Equivalence_Symmetric  _ _ eqv_equivalence)
  transitivity proved by (@Equivalence_Transitive _ _ eqv_equivalence)
    as parametric_relation_eqv.

  Add Parametric Morphism `(c : Category Ob Hom) (a b c : Ob)
    : (@compose _ _ _ a b c)
    with signature (eqv ==> eqv ==> eqv) as parametric_morphism_comp.
    auto.
  Defined.

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

Hint Extern 4 (?A ≈ ?A) => reflexivity.
Hint Extern 6 (?X ≈ ?Y) => apply Equivalence_Symmetric.
Hint Extern 7 (?X ≈ ?Z) => match goal
  with [H : ?X ≈ ?Y, H' : ?Y ≈ ?Z |- ?X ≈ ?Z] => transitivity Y end.
Hint Extern 10 (?X ∘ ?Y ≈ ?Z ∘ ?Q) => apply compose_respects; auto.

(* The following are handy for rewriting. *)

Lemma juggle1
  : forall `{C : Category} `(f : d ~> e) `(g : c ~> d) `(h : b ~> c) `(k : a ~> b),
  ((f ∘ g) ∘ h) ∘ k ≈ f ∘ (g ∘ h) ∘ k.
  intros; repeat setoid_rewrite <- comp_assoc. reflexivity.
  Defined.

Lemma juggle2
  : forall `{C : Category} `(f : d ~> e) `(g : c ~> d) `(h : b ~> c) `(k : a ~> b),
  f ∘ (g ∘ (h ∘ k)) ≈ f ∘ (g ∘ h) ∘ k.
  intros; repeat setoid_rewrite <- comp_assoc. reflexivity.
  Defined.

Lemma juggle3
  : forall `{C : Category} `(f : d ~> e) `(g : c ~> d) `(h : b ~> c) `(k : a ~> b),
  (f ∘ g) ∘ (h ∘ k) ≈ f ∘ (g ∘ h) ∘ k.
  intros; repeat setoid_rewrite <- comp_assoc. reflexivity.
  Defined.

Definition homomorphisms A := A -> A -> Type.

Record category := mkCat
{ objs : Type
; homs : homomorphisms objs
; cat  : Category objs homs
}.

(* Coq is the category of Coq types and functions. *)

Program Instance Coq : Category Type (fun X Y => X -> Y) :=
{ id      := fun _ x => x
; compose := fun _ _ _ f g x => f (g x)
; eqv     := fun X Y f g => forall {x : X}, f x = g x
}.
Obligation 1. crush. Defined.
Obligation 2. crush. Defined.

Definition Sets := Coq.