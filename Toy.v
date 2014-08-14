Require Export Hask.CpdtTactics.
Require Export Coq.Unicode.Utf8.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Program.Tactics.

Set Implicit Arguments.
Set Universe Polymorphism.
Set Printing Projections.
(* Set Primitive Projection. *)
Set Automatic Introduction.
Set Asymmetric Patterns.
Generalizable All Variables.

Reserved Notation "x ~> y" (at level 90, right associativity).
Reserved Notation "f ∘ g" (at level 45).
Reserved Notation "1".
Reserved Notation "x ~{ C }~> y" (at level 90, right associativity).

Delimit Scope category_scope with category.
Delimit Scope ob_scope with ob.
Delimit Scope hom_scope with hom.
Delimit Scope path_scope with path.

Local Open Scope hom_scope.

Class Presemicategory :=
{ ob               :> Type
; uhom             := Type : Type
; hom              : ob → ob → uhom where "x ~> y" := (hom x y)
; compose          : ∀ {x y z}, (y ~> z) → (x ~> y) → (x ~> z) where "f ∘ g" := (compose f g)
; compose_assoc    : ∀ {w x y z} (f : y ~> z) (g : x ~> y) (h : w ~> x), f ∘ (g ∘ h) = (f ∘ g) ∘ h
; compose_assoc_op : ∀ {w x y z} (f : y ~> z) (g : x ~> y) (h : w ~> x), (f ∘ g) ∘ h = f ∘ (g ∘ h)
}.

Bind Scope category_scope with Presemicategory.
Bind Scope ob_scope with ob.
Bind Scope hom_scope with hom.

Create HintDb category discriminated.
Create HintDb ob discriminated.
Create HintDb hom discriminated.

Arguments ob C%category : rename.
Arguments hom !C%category x y : rename.
Arguments compose [!C%category x%ob y%ob z%ob] f%hom g%hom : rename.

Hint Resolve @compose_assoc : category morphism.

Coercion ob : Presemicategory >-> Sortclass.

Infix "~>" := hom : category_scope.
Infix "~{ C }~>" := (@hom C) (at level 90, right associativity) : category_scope.
Infix "∘" := compose : hom_scope.
Open Scope category_scope.

Class Precategory := 
{ precategory_presemicategory :> Presemicategory
; id               : ∀ {x}, x ~> x
; right_id         : ∀ {x y} (f : x ~> y), f ∘ @id x = f
; left_id          : ∀ {x y} (f : x ~> y), @id y ∘ f = f
; id_id            : ∀ {x}, @id x ∘ @id x = @id x
}.

Notation "1" := id : hom_scope.

Arguments id [!C%category] x%ob : rename.
Arguments right_id [!C%category] x%ob y%ob f%hom : rename.
Arguments left_id [!C%category] x%ob y%ob f%hom : rename.
Arguments id_id [!C%category] x%ob : rename.

Coercion precategory_presemicategory : Precategory >-> Presemicategory.

Hint Resolve @left_id @right_id @id_id : category hom.
Hint Rewrite @left_id @right_id @id_id : category.
Hint Rewrite @left_id @right_id @id_id : hom.

Class Pregroupoid :=
{ pregroupoid_precategory :> Precategory
; inverse : ∀ {x y}, (x ~> y) → (y ~> x)
}.

Coercion pregroupoid_precategory : Pregroupoid >-> Precategory. 

Program Instance Sets_Presemicategory : Presemicategory :=
{ ob      := Type
; hom     := fun x y => x → y
; compose := fun _ _ _ f g x => f (g x)
}.

Program Instance Sets_Precategory : Precategory := 
{ id      := fun _ x => x
}.

Inductive paths {A} : A → A → Type :=
  refl : ∀ (a: A), paths a a.

Bind Scope path_scope with paths.

Arguments refl {A a}, [A] a.
Hint Resolve @refl.

Notation "x ~ y" := (paths x y) (at level 90).
Notation "x ~{ A }~ y" := (@paths A x y) (at level 90).

Ltac path_induction :=
  intros; repeat progress (
     match goal with
     | [ p : _ ~ _ |- _ ] => induction p
     | _ => idtac
     end
  ); auto.

Local Obligation Tactic := path_induction.

Program Instance Paths_Presemicategory {A} : Presemicategory :=
{ ob := A
; hom := @paths A
}

Obligation 1. path_induction. Defined.
Obligation 2. path_induction. Defined.
Obligation 3. path_induction. Defined.

Program Instance Paths_Precategory {A} : Precategory := {
  precategory_presemicategory := @Paths_Presemicategory A
}.
Obligation 1. path_induction. Defined.
Obligation 2. path_induction. Defined.
Obligation 3. path_induction. Defined.
     
Program Instance Paths_Pregroupoid {A} : Pregroupoid := {
  pregroupoid_precategory := @Paths_Precategory A
}.
Obligation 1. path_induction. Defined.
 
Definition Sets  := @Sets_Precategory.
Definition Paths {A} := @Paths_Pregroupoid A.

Definition fun_compose := @compose Sets.
Definition path_compose {A} := @compose (@Paths A).

Infix "∘" := path_compose : path_scope.
Infix "∘" := fun_compose : type_scope.

Notation "! p" := (inverse p) (at level 50) : path_scope.

(* If Prop and HoTT got along, we could Add Parametric Relation (A: Type): A (@paths A) *)

(* paths between paths are homotopies *)

Definition path_left_id {A} {x y : A} (p : x ~ y) : (refl ∘ p ~ p) % path.
Proof. path_induction. Defined.

Definition path_right_id {A} {x y : A} (p : x ~ y) : (p ∘ refl ~ p) % path. 
Proof. path_induction. Defined.

Arguments path_left_id [!C%category] x%ob y%ob p%path : rename.
Arguments path_right_id [!C%category] x%ob y%ob p%path : rename.

Lemma unique_id {C : Precategory} (id0 id1 : ∀ {x : C}, x ~> x)
  (id1_left  : ∀ (x y : C) (f : x ~> y), @id1 y ∘ f = f)
  (id0_right : ∀ (x y : C) (f : x ~> y), f ∘ @id0 x = f) 
  : ∀ x, @id0 x = @id1 x.
Proof.
  intro.
  etransitivity; [ symmetry; apply id1_left | apply id0_right ].
Qed.

Definition as_left_id { C : Precategory } {x y : C} (f: x ~> y) i (H: i = 1) : i ∘ f = f.
Proof.
  rewrite -> H.
  path_induction.
  apply left_id.
Defined.

Arguments as_left_id [!C%category] x%ob y%ob f%hom i%hom H%hom : rename.

Definition as_right_id { C : Precategory } {x y : C} (f : x ~> y) i (H: i = 1) : f ∘ i = f.
Proof.    
  rewrite -> H.
  path_induction.
  apply right_id.
Defined.

Arguments as_right_id [!C%category] x%ob y%ob f%hom i%hom H%hom : rename.
