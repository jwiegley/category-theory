Generalizable All Variables.

Reserved Notation "a → b" (at level 70, right associativity).
Reserved Notation "f ≈ g" (at level 54).
Reserved Notation "f ∘ g" (at level 45).
Reserved Notation "a {C}-> b" (at level 100).

(* I am not interested in general categories here, but just sub-categories
   within Coq, the category of Coq types and functions. *)

Class Category Ob (Hom : Ob -> Ob -> Type) :=
{ hom := Hom where "a → b" := (hom a b)
; ob  := Ob

; id : forall {X}, X → X
; compose : forall {A B C}, (B → C) -> (A → B) -> (A → C)
  where "f ∘ g" := (compose f g)

; eqv : forall A B, (A → B) -> (A → B) -> Prop
  where "f ≈ g" := (eqv _ _ f g)
(* ; eqv_equivalence : forall a b, (eqv a b (eqv a b) (eqv a b)) *)
(* ; comp_respects : forall a b c, *)
(*   Proper (eqv a b ==> eqv b c ==> eqv a c) (comp _ _ _) *)

; right_identity : forall {A B} (f : A → B), f ∘ id ≈ f
; left_identity : forall {A B} (f : A → B), id ∘ f ≈ f
; comp_assoc : forall {A B C D} (f : C → D) (g : B → C) (h : A → B) ,
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
}.
Coercion ob : Category >-> Sortclass.

Notation "a → b" := (hom a b).
Notation "f ≈ g" := (eqv _ _ f g).
Notation "f ∘ g" := (compose f g).
Notation "a -{ C }-> b" := (@hom _ _ C a b) (at level 100).

Global Instance Coq : Category Type (fun X Y => X -> Y) :=
{ id      := fun _ x => x
; compose := fun _ _ _ f g x => f (g x)
; eqv     := fun _ _ f g => f = g
}.
Proof.
  (* right_identity *) intros. reflexivity.
  (* left_identity *)  intros. reflexivity.
  (* comp_assoc *)     intros. reflexivity.  Qed.

Definition homomorphisms A := A -> A -> Type.

Record category := mkCat
{ objs : Type
; homs : homomorphisms objs
; cat  : Category objs homs
}.

Class Functor `(C : Category objC homC, D : Category objD homD) :=
{ Fobj : objC -> objD
; fmap : forall {A B}, (A → B) -> (Fobj A → Fobj B)
; functor_law_1 : forall {X : objC}, fmap (@id objC homC C X) ≈ id
; functor_law_2 : forall {X Y Z} (f : Y → Z) (g : X → Y),
    compose (fmap f) (fmap g) ≈ fmap (compose f g)
}.
