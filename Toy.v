(* requires coq trunk newer than August 14th, 2014 *)

Require Export Hask.CpdtTactics.
Require Export Coq.Unicode.Utf8.
Require Export Coq.Classes.Morphisms.
Require Export Coq.Program.Tactics.

Set Automatic Introduction.
Set Implicit Arguments.
Set Printing Projections.
Set Primitive Projections.
Set Shrink Obligations.
Set Universe Polymorphism.
Generalizable All Variables.

Notation idmap := (fun x => x).

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

(* (∞, 1)-category *)
Class Precategory :=
{ ob               : Type
; hom              : ob → ob → Type where "x ~> y" := (hom x y)
; compose          : ∀ {x y z : ob}, (y ~> z) → (x ~> y) → (x ~> z) where "f ∘ g" := (compose f g)
; compose_assoc    : ∀ {w x y z : ob} (f : y ~> z) (g : x ~> y) (h : w ~> x), f ∘ (g ∘ h) ~ (f ∘ g) ∘ h
; compose_assoc_op : ∀ {w x y z : ob} (f : y ~> z) (g : x ~> y) (h : w ~> x), (f ∘ g) ∘ h ~ f ∘ (g ∘ h)
; id               : ∀ {x : ob}, x ~> x
; right_id         : ∀ {x y : ob} (f : x ~> y), f ∘ @id x ~ f
; left_id          : ∀ {x y : ob} (f : x ~> y), @id y ∘ f ~ f
; id_id            : ∀ {x : ob}, @id x ∘ @id x ~ @id x
}.

Coercion ob : Precategory >-> Sortclass.

Bind Scope category_scope with Precategory.
Bind Scope ob_scope with ob.
Bind Scope hom_scope with hom.

Tactic Notation "evia" open_constr(y) :=
  let R := match goal with |- ?R ?x ?z => constr:(R) end in
  let x := match goal with |- ?R ?x ?z => constr:(x) end in
  let z := match goal with |- ?R ?x ?z => constr:(z) end in
  refine (@compose _ R _ x y z _ _).

Tactic Notation "evia" := evia _.

(*
Create HintDb category discriminated.
Create HintDb hom discriminated.
*)
Arguments ob C%category : rename.
Arguments hom !C%category x y : rename.
Arguments compose [!C%category x%ob y%ob z%ob] f%hom g%hom : rename.
Arguments id [!C%category] x%ob : rename.
Arguments right_id [!C%category] x%ob y%ob f%hom : rename.
Arguments left_id [!C%category] x%ob y%ob f%hom : rename.
Arguments id_id [!C%category] x%ob : rename.

Hint Resolve @compose_assoc : category morphism.
Hint Resolve @left_id @right_id @id_id : category hom.
Hint Rewrite @left_id @right_id @id_id : category.
Hint Rewrite @left_id @right_id @id_id : hom.

Infix "~>" := hom : category_scope.
Infix "~{ C }~>" := (@hom C) (at level 90, right associativity) : category_scope.
Infix "∘" := compose : hom_scope.

Notation "1" := id : hom_scope.
Notation "1" := refl : path_scope.

Open Scope category_scope.

(* ∞-groupoid *)
Class Pregroupoid :=
{ pregroupoid_precategory :> Precategory
; inverse : ∀ {x y}, (x ~> y) → (y ~> x)
; inverse_inverse : ∀ {x y} (f : x ~> y), inverse (inverse f) ~ f
; inverse_left_inverse : ∀ {x y} (f : x ~> y), inverse f ∘ f ~ id x 
; inverse_right_inverse : ∀ {x y} (f : x ~> y), f ∘ inverse f ~ id y 
}.

Coercion pregroupoid_precategory : Pregroupoid >-> Precategory. 

Notation "! p" := (inverse p) (at level 50) : hom_scope.

Arguments inverse [!C%category] x%ob y%ob f%hom : rename.
Arguments inverse_inverse [!C%category] x%ob y%ob f%hom : rename.
Arguments inverse_left_inverse [!C%category] x%ob y%ob f%hom : rename.
Arguments inverse_right_inverse [!C%category] x%ob y%ob f%hom : rename.

Hint Resolve @inverse_inverse @inverse_left_inverse @inverse_right_inverse : category hom path.
Hint Rewrite @inverse_inverse @inverse_left_inverse @inverse_right_inverse : category.
Hint Rewrite @inverse_inverse @inverse_left_inverse @inverse_right_inverse : hom.
Hint Rewrite @inverse_inverse @inverse_left_inverse @inverse_right_inverse : path.

(** Sets *)


Program Instance Sets_Precategory : Precategory :=
{ ob      := Type
; hom     := fun x y => x → y
; compose := fun _ _ _ f g x => f (g x)
}.
Solve All Obligations with path_induction.

(*
Program Instance Sets_Category : Category :=
{ category_precategory := Sets_Precategory
}.
Next Obligation. 
  unfold isSet.
  intros.
  path_induction.
  *)
  
Definition fun_compose := @compose Sets_Precategory.
Infix "∘" := fun_compose : type_scope.

(** Paths *)

Program Instance Paths_Precategory {A} : Precategory :=
{ ob := A
; hom := @paths A
}.
Solve All Obligations with path_induction.

Program Instance Paths_Pregroupoid {A} : Pregroupoid :=
{ pregroupoid_precategory := @Paths_Precategory A
}.
Next Obligation. path_induction. Defined.
Next Obligation. path_induction. Defined.
Next Obligation. path_induction. Defined.
Next Obligation. path_induction. Defined.

 
Definition Paths A := @Paths_Pregroupoid A.
Definition path_compose {A} := @compose (@Paths_Precategory A).
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

(*
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
*)

(* Prefunctor *)

Class Prefunctor :=
{ dom : Precategory
; cod : Precategory
; fobj :> dom → cod
; fmap : ∀ {x y : dom}, (x ~> y) → (fobj x ~> fobj y)
; fmap_id : ∀ {x : dom}, fmap (@id dom x) ~ @id cod (fobj x)
; fmap_compose : ∀ {x y z : dom} (f : y ~> z) (g : x ~> y),
   fmap f ∘ fmap g = fmap (f ∘ g)
}.

Program Instance map_path `(f : A -> B) : Prefunctor := 
{ dom := Paths A
; cod := Paths B
; fobj := f
}.
Next Obligation. path_induction. Defined.
Next Obligation. path_induction. Defined.
Next Obligation. path_induction. Defined.

Definition isProp (A : Type) := ∀ (x y : A), x ~ y.
Definition isSet (A : Type) := ∀ (x y : A) (p q : x ~ y), p ~ q.

(* a category is an (∞,1)-category, where the hom-sets are actual sets. *)
Class Category :=
{ category_precategory :> Precategory
; hom_set : ∀ {x y}, isSet (x ~> y)
}.

Coercion category_precategory : Category >-> Precategory. 

Class ThinCategory :=
{ thincategory_category :> Category
; hom_prop : ∀ {x y}, isProp (x ~> y)
}.

Coercion thincategory_category : ThinCategory >-> Category. 

Class StrictCategory :=
{ strictcategory_category :> Category
; ob_set : ∀ x, isSet x
}.

Coercion strictcategory_category : StrictCategory >-> Category.

(* Opposite notions *)

Program Instance Op_Precategory (C : Precategory) : Precategory :=
{ ob := C
; hom := fun x y => @hom C y x
; compose := fun x y z f g => @compose C z y x g f
; id := @id C
}.
Next Obligation. apply (@compose_assoc_op C). Defined.
Next Obligation. apply (@compose_assoc C). Defined.
Next Obligation. apply (@left_id C). Defined.
Next Obligation. apply (@right_id C). Defined.
Next Obligation. apply (@id_id C). Defined.

Program Instance Op_Pregroupoid (C : Pregroupoid) : Pregroupoid :=
{ pregroupoid_precategory := Op_Precategory C
; inverse := fun x y => @inverse C y x
}.
Next Obligation. apply (@inverse_inverse C). Defined.
Next Obligation. apply (@inverse_right_inverse C). Defined.
Next Obligation. apply (@inverse_left_inverse C). Defined.

(* We need funext for these *)

Class Op (T:Type) :=
{ op : T -> T
; op_op : ∀ (x : T), op (op x) ~ x (* needs funext *)
}.

Program Instance Precategory_Op : Op Precategory :=
{ op := Op_Precategory
}.
Next Obligation. 
  unfold Op_Precategory. 
  unfold Op_Precategory_obligation_1.
  unfold Op_Precategory_obligation_2.
  simpl.
  admit.
Defined.

Program Instance Pregroupoid_Op : Op Pregroupoid :=
{ op := Op_Pregroupoid
}.
Obligation 1.
  unfold Op_Pregroupoid.
  unfold Op_Pregroupoid_obligation_1.
  unfold Op_Pregroupoid_obligation_2.
  unfold Op_Pregroupoid_obligation_3.
  simpl.
  admit.

(*
Definition relation (A : Type) := A -> A -> Type.

Class Reflexive {A} (R : relation A) :=
  reflexivity : ∀ (x : A), R x x.

Class Symmetric {A} (R : relation A) :=
  symmetry : ∀ (x y : A), R x y -> R y x.

Class Transitive {A} (R : relation A) :=
  transitivity : ∀ (x y z : A), R y z -> R x y -> R x z.

*)