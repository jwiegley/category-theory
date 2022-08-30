Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

Section FunctorParts.

Context {C D : Category}.

(* [FunctorParts] allows the object mapping to be stated explicitly, but not
   the morphisms mapping. *)
Record FunctorParts (p_fobj : C → D) : Type := {
  p_fmap {x y : C} (f : x ~> y) : p_fobj x ~> p_fobj y;

  p_fmap_respects {x y : C} : Proper (equiv ==> equiv) (@p_fmap x y);

  p_fmap_id {x : C} : p_fmap (@id C x) ≈ id;
  p_fmap_comp {x y z : C} (f : y ~> z) (g : x ~> y) :
    p_fmap (f ∘ g) ≈ p_fmap f ∘ p_fmap g;
}.

Definition FunctorFromParts `(P : FunctorParts p_fobj) : C ⟶ D := {|
  fobj          := λ x, p_fobj x;
  fmap          := @p_fmap p_fobj P;
  fmap_respects := @p_fmap_respects p_fobj P;
  fmap_id       := @p_fmap_id p_fobj P;
  fmap_comp     := @p_fmap_comp p_fobj P;
|}.

End FunctorParts.

Section Binoidal.

Context {C : Category}.

Reserved Infix "⋉" (at level 15, right associativity).
Reserved Infix "⋊" (at level 15, right associativity).
Reserved Infix "⊗" (at level 30, right associativity).

(* This is effectively "premagmoidal" with separate functoriality in the two
   arguments to the tensor. *)
Class Binoidal := {
  tensor (x y : C) : C where "x ⊗ y" := (tensor x y);

  (* The binoidal tensor is functorial in each argument separately, whereas
     monoidal categories, whose tensor is a functor from C ∏ C ⟶ C, is
     functorial in both arguments jointly. *)
  left_functor y' : FunctorParts (λ x, x ⊗ y');
  inj_left (y' : C) : C ⟶ C := FunctorFromParts (left_functor y')
    where "x ⋊ y" := (inj_left x y);

  right_functor x' : FunctorParts (λ y, x' ⊗ y);
  inj_right (x' : C) : C ⟶ C := FunctorFromParts (right_functor x')
    where "x ⋉ y" := (inj_right x y);
}.

Context `{Binoidal}.

Notation "x ⋉ y" := (inj_left x y) (at level 15, right associativity).
Notation "x ⋊ y" := (inj_right x y) (at level 15, right associativity).
Notation "x ⊗ y" := (tensor x y) (at level 30, right associativity).

Corollary inj_left_right {x y} : x ⋉ y = y ⋊ x.
Proof. reflexivity. Qed.

(* A morphism f:x→y in a binoidal category is central if, for every morphism
   f′:x′→y′, the following diagrams commute. *)

Definition central `(f : x ~> y) : Type :=
  ∀ x' y' (f' : x' ~> y'),
    (fmap[inj_left y'] f ∘ fmap[inj_right x] f'
       << x ⊗ x' ~~> y ⊗ y' >>
     fmap[inj_right y] f' ∘ fmap[inj_left x'] f)
  ∧ (fmap[inj_left y] f' ∘ fmap[inj_right x'] f
       << x' ⊗ x ~~> y' ⊗ y >>
     fmap[inj_right y'] f ∘ fmap[inj_left x] f').

Definition composite_ff' {x x' y y'} (f : x ~> y) (f' : x' ~> y') :
  x ⊗ x' ~> y ⊗ y' := fmap[inj_right y] f' ∘ fmap[inj_left x'] f.
  
#[export]
Program Instance composite_ff'_respects {x x' y y'} :
  Proper (equiv ==> equiv ==> equiv) (@composite_ff' x x' y y').
Next Obligation.
  unfold composite_ff'.
  proper.
  destruct H.
  simpl in *.
  destruct left_functor0, right_functor0; simpl in *.
  now rewrite X, X0.
Qed.

Definition composite_f'f {x x' y y'} (f' : x' ~> y') (f : x ~> y) :
  x' ⊗ x ~> y' ⊗ y := fmap[inj_right y'] f ∘ fmap[inj_left x] f'.
  
#[export]
Program Instance composite_f'f_respects {x x' y y'} :
  Proper (equiv ==> equiv ==> equiv) (@composite_f'f x x' y y').
Next Obligation.
  unfold composite_f'f.
  proper.
  destruct H.
  simpl in *.
  destruct left_functor0, right_functor0; simpl in *.
  now rewrite X, X0.
Qed.

End Binoidal.

Notation "x ⋉ y" := (@inj_left _ _ y x)
  (at level 15, right associativity) : object_scope.
Notation "x ⋊ y" := (@inj_right _ _ x y)
  (at level 15, right associativity) : object_scope.

Notation "f ⋉ y" := (fmap[@inj_left _ _ y] f)
  (at level 15, right associativity) : morphism_scope.
Notation "x ⋊ f" := (fmap[@inj_right _ _ x] f)
  (at level 15, right associativity) : object_scope.

Notation "(⊗)" := (@tensor _ _) : functor_scope.
Notation "x ⊗ y" := (@tensor _ _ x%object y%object)
  (at level 30, right associativity) : object_scope.
Notation "f ⊗ g" := (composite_ff' f g)
  (at level 30, right associativity) : morphism_scope.
