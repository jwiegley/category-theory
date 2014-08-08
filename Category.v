(**
Welcome to the Coq development of Edward Kmett's hask library, which expresses
many of the theories used by Haskell in the context of curried monoidal
bifunctors.

This is a specialized treatment of category theory, in that we narrowing our
focus to closed monoidal categories equipped with enriched internal homs.  We
do not attempt to formalize all of category theory, but only those aspects
touching on this specific sub-domain.  We do this because it is directly
applicable to the universe of Haskell types and functions, and gives us useful
results there.

Another deviation from convention is that we name categories after their
morphisms, rather than their objects.  Thus, operations always name
categories, which Coq coerces implicitly to the morphisms of that category.

For example, the notation [F ⟹ G] refers to natural transformations from [F]
to [G]; it also a name for the category [Nat] ([F ⟹ G] is just sugar for [Nat
F G]): the category of functors from some implied [C] to [D].  We can normally
let the particular cateries be inferred from context, or they can be named
using [@Nat C D F G].

Reference: _Categories for the Working Mathematician_ %\cite{Categories}%, by
Saunders Mac Lane.
*)

Require Export Hask.Utils.

Set Universe Polymorphism.
Generalizable All Variables.

(**
[X ~> Y] is used to indicate morphisms from [X] to [Y] in some category.

[X ~{ C }~> Y] specifically indicates morphisms in [C].

[f ∘ g] is composition of morphisms [f] and [g] in some category.
*)

Reserved Notation "a ~> b" (at level 90, right associativity).
Reserved Notation "f ∘ g" (at level 45).

(**
A [Category] is defined by objects and morphisms between objects, plus the
following structure:

- Every object has an identity morphism.
- Morphisms compose.

- Composition respect a monoidal structure: left and right identity using
  the identity morphisms, and associativity.
*)

Class Category :=
{ (** The universe of types of homomorphisms must be higher than the universe
      of types of objects.  This will allow us to define the category of all
      (locally small) categories. *)
  uhom := Type : Type

; ob  : Type
; hom : ob → ob → uhom where "a ~> b" := (hom a b)

; id : ∀ {A}, A ~> A
; compose : ∀ {A B C}, (B ~> C) → (A ~> B) → (A ~> C)
    where "f ∘ g" := (compose f g)

; right_identity : ∀ A B (f : A ~> B), f ∘ id = f
; left_identity : ∀ A B (f : A ~> B), id ∘ f = f
; comp_assoc : ∀ A B C D (f : C ~> D) (g : B ~> C) (h : A ~> B),
    f ∘ (g ∘ h) = (f ∘ g) ∘ h
}.

(* begin hide *)
(** Using a [Category] in a context requiring a [Type] will do what is
    expected using this coercion. *)
Coercion ob : Category >-> Sortclass.

Notation "a ~> b" := (hom a b) : category_scope.
Notation "a ~{ C }~> b" := (@hom C a b) (at level 100) : category_scope.
Notation "f ∘ g" := (compose f g) : category_scope.
Notation "ob/ C" := (@ob C) (at level 44) : category_scope.
Notation "id/ X" := (@id _ X) (at level 44).

Open Scope category_scope.

Hint Resolve left_identity.
Hint Resolve right_identity.
Hint Resolve comp_assoc.

Lemma cat_irrelevance `(C : Category) `(D : Category)
  : forall (m n : ∀ {A}, A ~> A)
           (p q : ∀ {A B C}, (B ~> C) → (A ~> B) → (A ~> C))
           l l' r r' c c',
  @m = @n ->
  @p = @q ->
  {| ob             := C
   ; hom            := @hom C
   ; id             := @m
   ; compose        := @p
   ; left_identity  := l
   ; right_identity := r
   ; comp_assoc     := c
 |} =
  {| ob             := C
   ; hom            := @hom C
   ; id             := @n
   ; compose        := @q
   ; left_identity  := l'
   ; right_identity := r'
   ; comp_assoc     := c'
 |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.
(* end hide *)

(** The opposite, or categorical dual, of any category is expressed as
    [C^op]. *)

Program Instance Opposite `(C : Category) : Category :=
{ ob      := @ob C
; hom     := fun x y => @hom C y x
; id      := @id C
; compose := fun _ _ _ f g => @compose C _ _ _ g f
}.

Notation "C ^op" := (Opposite C) (at level 90) : category_scope.

Definition op `{C : Category} : forall {X Y}, (X ~{C^op}~> Y) -> (Y ~{C}~> X).
Proof. intros. auto. Defined.

Definition unop `{C : Category} : forall {X Y}, (Y ~{C}~> X) -> (X ~{C^op}~> Y).
Proof. intros. auto. Defined.

Lemma op_involutive (C : Category) : (C^op)^op = C.
Proof.
  unfold Opposite.
  induction C.
  apply f_equal3.
  unfold Opposite_obligation_1.
  repeat (extensionality e; simpl; crush).
  unfold Opposite_obligation_2.
  repeat (extensionality e; simpl; crush).
  unfold Opposite_obligation_3.
  repeat (extensionality e; simpl; crush).
  extensionality f.
  extensionality g.
  extensionality h.
  extensionality i.
  extensionality j.
  extensionality k. crush.
Defined.

(** [Sets] is the category of Coq types and functions.  *)

Program Instance Sets : Category :=
{ ob      := Type
; hom     := fun X Y => X → Y
; id      := fun _ x => x
; compose := fun _ _ _ f g x => f (g x)
}.
