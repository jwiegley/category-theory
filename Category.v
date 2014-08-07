Require Export Utils.

Generalizable All Variables.

(* X ~> Y is used to indicate morphisms from X to Y in some category.
   X ~{ C }~> Y specifically indicates morphisms in C.

   f ∘ g is composition of morphisms f and g in some category. *)

Reserved Notation "a ~> b" (at level 90, right associativity).
Reserved Notation "f ∘ g" (at level 45).

(* A Category is defined by objects and morphisms between objects, plus the
   following structure:

   - Every object has an identity morphism.
   - Morphisms compose.

   - Composition respect a monoidal structure: left and right identity using
     the identity morphisms, and associativity. *)

Class Category :=
{ ob  : Type
; hom : ob → ob → Type where "a ~> b" := (hom a b)

; id : ∀ {A}, A ~> A
; compose : ∀ {A B C}, (B ~> C) → (A ~> B) → (A ~> C)
    where "f ∘ g" := (compose f g)

; right_identity : ∀ A B (f : A ~> B), f ∘ id = f
; left_identity : ∀ A B (f : A ~> B), id ∘ f = f
; comp_assoc : ∀ A B C D (f : C ~> D) (g : B ~> C) (h : A ~> B),
    f ∘ (g ∘ h) = (f ∘ g) ∘ h
}.

(* Using a Category in a context requiring a Type DTRT with this coercion. *)
Coercion ob : Category >-> Sortclass.

Notation "a ~> b" := (hom a b) : category_scope.
Notation "a ~{ C }~> b" := (@hom C a b) (at level 100) : category_scope.
Notation "f ∘ g" := (compose f g) : category_scope.
Notation "ob/ C" := (@ob C) (at level 44).

Open Scope category_scope.

Hint Resolve left_identity.
Hint Resolve right_identity.
Hint Resolve comp_assoc.

(* The opposite category, C^op. *)

Definition Opposite `(C : Category) : Category.
  apply Build_Category with
    (hom     := fun x y => hom y x)
    (id      := @id C)
    (compose := fun a b c f g => g ∘ f).

  intros; apply (@left_identity C).
  intros; apply (@right_identity C).
  intros. symmetry; apply comp_assoc.
Defined.

Notation "C ^op" := (Opposite C) (at level 90) : category_scope.

Definition Yoneda := Opposite.

Definition op `{C : Category} : forall {X Y}, (X ~{C^op}~> Y) -> (Y ~{C}~> X).
Proof. intros. auto. Defined.

Definition unop `{C : Category} : forall {X Y}, (Y ~{C}~> X) -> (X ~{C^op}~> Y).
Proof. intros. auto. Defined.

(* Coq is the category of Coq types and functions.  *)

Program Instance Arr : Category :=
{ ob      := Type
; hom     := fun X Y => X → Y
; id      := fun _ x => x
; compose := fun _ _ _ f g x => f (g x)
}.

Definition coq  := Arr.
Definition Sets := Arr.
