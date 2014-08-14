Require Export Hask.CpdtTactics.
Require Export Coq.Unicode.Utf8.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Program.Tactics.

Set Implicit Arguments.
Set Universe Polymorphism.
Set Printing Projections.
Set Shrink Obligations.
(* Set Primitive Projections. *)
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

(** paths *)

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

(** Presemicategory *)

Class Presemicategory :=
{ ob               :> Type
; uhom             := Type : Type
; hom              : ob → ob → uhom where "x ~> y" := (hom x y)
; compose          : ∀ {x y z}, (y ~> z) → (x ~> y) → (x ~> z) where "f ∘ g" := (compose f g)
; compose_assoc    : ∀ {w x y z} (f : y ~> z) (g : x ~> y) (h : w ~> x), f ∘ (g ∘ h) ~ (f ∘ g) ∘ h
; compose_assoc_op : ∀ {w x y z} (f : y ~> z) (g : x ~> y) (h : w ~> x), (f ∘ g) ∘ h ~ f ∘ (g ∘ h)
}.

Coercion ob : Presemicategory >-> Sortclass.

Bind Scope category_scope with Presemicategory.
Bind Scope ob_scope with ob.
Bind Scope hom_scope with hom.

(*
Create HintDb category discriminated.
Create HintDb hom discriminated.
*)
Arguments ob C%category : rename.
Arguments hom !C%category x y : rename.
Arguments compose [!C%category x%ob y%ob z%ob] f%hom g%hom : rename.

Hint Resolve @compose_assoc : category morphism.

Infix "~>" := hom : category_scope.
Infix "~{ C }~>" := (@hom C) (at level 90, right associativity) : category_scope.
Infix "∘" := compose : hom_scope.

Open Scope category_scope.

(** Precategory *)


Class Precategory := 
{ precategory_presemicategory :> Presemicategory
; id       : ∀ {x}, x ~> x
; right_id : ∀ {x y} (f : x ~> y), f ∘ @id x ~ f
; left_id  : ∀ {x y} (f : x ~> y), @id y ∘ f ~ f
; id_id    : ∀ {x}, @id x ∘ @id x ~ @id x
}.

Coercion precategory_presemicategory : Precategory >-> Presemicategory.

Notation "1" := id : hom_scope.

Arguments id [!C%category] x%ob : rename.
Arguments right_id [!C%category] x%ob y%ob f%hom : rename.
Arguments left_id [!C%category] x%ob y%ob f%hom : rename.
Arguments id_id [!C%category] x%ob : rename.

Hint Resolve @left_id @right_id @id_id : category hom.
Hint Rewrite @left_id @right_id @id_id : category.
Hint Rewrite @left_id @right_id @id_id : hom.

(** Pregroupoid *)

Class Pregroupoid :=
{ pregroupoid_precategory :> Precategory
; inverse : ∀ {x y}, (x ~> y) → (y ~> x)
; inverse_inverse : ∀ {x y} (f : x ~> y), inverse (inverse f) ~ f
; inverse_left_inverse : ∀ {x y} (f : x ~> y), inverse f ∘ f ~ id x 
; inverse_right_inverse : ∀ {x y} (f : x ~> y), f ∘ inverse f ~ id y 
}.

Coercion pregroupoid_precategory : Pregroupoid >-> Precategory. 

Notation "! p" := (inverse p) (at level 50) : hom_scope.

(** Sets *)

Program Instance Sets_Presemicategory : Presemicategory :=
{ ob      := Type
; hom     := fun x y => x → y
; compose := fun _ _ _ f g x => f (g x)
}.
Next Obligation. path_induction. Defined.
Next Obligation. path_induction. Defined.
  
Program Instance Sets_Precategory : Precategory := 
{ precategory_presemicategory := Sets_Presemicategory
}.
Next Obligation. path_induction. Defined.
Next Obligation. path_induction. Defined.
Next Obligation. path_induction. Defined.
  
Definition Sets  := @Sets_Precategory.
Definition fun_compose := @compose Sets.
Infix "∘" := fun_compose : type_scope.


(** Paths *)

Program Instance Paths_Presemicategory {A} : Presemicategory :=
{ ob := A
; hom := @paths A
}.
Next Obligation. path_induction. Defined.
Next Obligation. path_induction. Defined.
Next Obligation. path_induction. Defined.

Program Instance Paths_Precategory {A} : Precategory := {
  precategory_presemicategory := @Paths_Presemicategory A
}.
Next Obligation. path_induction. Defined.
Next Obligation. path_induction. Defined.
Next Obligation. path_induction. Defined.
Next Obligation. path_induction. Defined.


Program Instance Paths_Pregroupoid {A} : Pregroupoid := {
  pregroupoid_precategory := @Paths_Precategory A
}.
Next Obligation. path_induction. Defined.
Next Obligation. path_induction. Defined.
Next Obligation. path_induction. Defined.
Next Obligation. path_induction. Defined.
 
Definition Paths A := @Paths_Pregroupoid A.
Definition path_compose {A} := @compose (@Paths_Presemicategory A).
Definition path_inverse {A} := @inverse (@Paths_Pregroupoid A).

Infix "∘" := path_compose : path_scope.
Notation "! p" := (path_inverse p) (at level 50) : path_scope.
 
Lemma unique_id {C : Precategory} (id0 id1 : ∀ {x : C}, x ~> x)
  (id1_left  : ∀ (x y : C) (f : x ~> y), @id1 y ∘ f = f)
  (id0_right : ∀ (x y : C) (f : x ~> y), f ∘ @id0 x = f) 
  : ∀ x, @id0 x = @id1 x.
Proof.
  intro.
  etransitivity; [ symmetry; apply id1_left | apply id0_right ].
Qed.

Definition as_left_id { C : Precategory } {x y : C} (f: x ~> y) i (H: i = 1) : i ∘ f ~ f.
Proof.
  rewrite -> H.
  path_induction.
  apply left_id.
Defined.

Arguments as_left_id [!C%category] x%ob y%ob f%hom i%hom H%hom : rename.

Definition as_right_id { C : Precategory } {x y : C} (f : x ~> y) i (H: i = 1) : f ∘ i ~ f.
Proof.    
  rewrite -> H.
  path_induction.
  apply right_id.
Defined.

Arguments as_right_id [!C%category] x%ob y%ob f%hom i%hom H%hom : rename.

(* Opposite notions *)

Program Instance Op_Presemicategory (C : Presemicategory) : Presemicategory :=
{ ob := C
; hom := fun x y => @hom C y x
; compose := fun x y z f g => @compose C z y x g f
}.
Obligation 1. apply (@compose_assoc_op C). Defined.
Obligation 2. apply (@compose_assoc C). Defined.

Program Instance Op_Precategory (C : Precategory) : Precategory :=
{ precategory_presemicategory := Op_Presemicategory C
; id := @id C
}.
Obligation 1. apply (@left_id C). Defined.
Obligation 2. apply (@right_id C). Defined.
Obligation 3. apply (@id_id C). Defined.

Program Instance Op_Pregroupoid (C : Pregroupoid) : Pregroupoid :=
{ pregroupoid_precategory := Op_Precategory C
; inverse := fun x y => @inverse C y x
}.
Obligation 1. apply (@inverse_inverse C). Defined.
Obligation 2. apply (@inverse_right_inverse C). Defined.
Obligation 3. apply (@inverse_left_inverse C). Defined.

(* We need funext for these *)

Class Op (T:Type) :=
{ op : T -> T
; op_op : ∀ (x : T), op (op x) = x (* needs funext *)
}.

Program Instance Presemicategory_Op : Op Presemicategory :=
{ op := Op_Presemicategory
}.
Obligation 1. 
  unfold Op_Presemicategory. 
  unfold Op_Presemicategory_obligation_1.
  unfold Op_Presemicategory_obligation_2.
  simpl.
  admit. (* funext *)
Defined.


Program Instance Precategory_Op : Op Precategory :=
{ op := Op_Precategory
}.


Program Instance Pregroupoid_Op : Op Pregroupoid :=
{ op := Op_Pregroupoid
}.