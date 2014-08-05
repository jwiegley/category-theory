Require Export Coq.Unicode.Utf8.
Require Export CpdtTactics.

Open Scope type_scope.

Generalizable All Variables.

(* Proof General seems to add an extra two columns of overhead *)

Set Printing Width 130.

(* jww (2014-08-05): Assume functional extensionality for now, until I switch
   to using higher inductive types. Setoids are just too cumbersome and slow
   for the flexibility they offer.
*)
Axiom ext_eq : forall {T1 T2 : Type} (f1 f2 : T1 -> T2),
  (forall x, f1 x = f2 x) -> f1 = f2.

Theorem ext_eqS : forall (T1 T2 : Type) (f1 f2 : T1 -> T2),
  (forall x, f1 x = f2 x) -> f1 = f2.
Proof.
  intros; rewrite (ext_eq f1 f2); auto.
Qed.

Hint Resolve ext_eq.
Hint Resolve ext_eqS.

Ltac ext_eq := (apply ext_eq || apply ext_eqS); intro.

(* ~> is used to describe morphisms.

   Unicode = means equivalence, while ≅ is isomorphism and = is identity.

   Unicode ∘ is composition of morphisms.

   ~{ C }~> specifically types a morphisms in C.
*)
Reserved Notation "a ~> b" (at level 90, right associativity).
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
Class Category :=
{ ob  : Type
; hom : ob → ob → Type
    where "a ~> b" := (hom a b)

; id : ∀ {A}, A ~> A
; compose : ∀ {A B C}, (B ~> C) → (A ~> B) → (A ~> C)
    where "f ∘ g" := (compose f g)

; right_identity : ∀ A B (f : A ~> B), f ∘ id = f
; left_identity : ∀ A B (f : A ~> B), id ∘ f = f
; comp_assoc : ∀ A B C D (f : C ~> D) (g : B ~> C) (h : A ~> B),
    f ∘ (g ∘ h) = (f ∘ g) ∘ h
}.

Coercion ob : Category >-> Sortclass.

Notation "a ~> b" := (hom a b) : category_scope.
Notation "f ∘ g" := (compose f g) : category_scope.
Notation "a ~{ C }~> b" := (@hom C a b) (at level 100) : category_scope.

Open Scope category_scope.

Hint Extern 1 => apply left_identity.
Hint Extern 1 => apply right_identity.
Hint Extern 1 => apply comp_assoc.

Hint Extern 4 (?A = ?A) => reflexivity.
Hint Extern 7 (?X = ?Z) => match goal
  with [H : ?X = ?Y, H' : ?Y = ?Z |- ?X = ?Z] => transitivity Y end.

(* Coq is the category of Coq types and functions.  *)

Program Instance Coq : Category :=
{ ob      := Type
; hom     := fun X Y => X → Y
; id      := fun _ x => x
; compose := fun _ _ _ f g x => f (g x)
}.

Definition Sets := Coq.
