Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Transparent Obligations.

Section Binoidal.

Context {C : Category}.

Reserved Infix "⋉" (at level 15, right associativity).
Reserved Infix "⋊" (at level 15, right associativity).
Reserved Infix "⊗" (at level 30, right associativity).

(* nLab: https://ncatlab.org/nlab/show/binoidal+category
   Wikipedia: none (no "binoidal category" article; the notion is covered
   under https://en.wikipedia.org/wiki/Premonoidal_category)

   A binoidal category is a category C with an object x ⊗ y for each pair of
   objects that is functorial in each argument *separately* rather than
   jointly. Where a monoidal tensor is a single bifunctor C ∏ C ⟶ C, the
   binoidal tensor provides, for each fixed object, two one-argument
   tensoring functors,

       x ⋉ -  : C ⟶ C   maps z to z ⊗ x      ([inj_left x],  - ⊗ x fixed right)
       x ⋊ -  : C ⟶ C   maps z to x ⊗ z      ([inj_right x], x ⊗ - fixed left)

   These need not assemble into a bifunctor: tensoring f : a ~> b on the left
   and f' : a' ~> b' on the right may be applied in two orders, giving in
   general distinct composites a ⊗ a' ~> b ⊗ b'. This is the "premagmoidal"
   precursor to a premonoidal category, which adds a unit and central
   coherence isomorphisms. The naming here follows the rest of the library;
   the symbols ⋉ / ⋊ match the nLab convention for the right/left tensoring
   functors. *)
Class Binoidal := {
  tensor (x y : C) : C where "x ⊗ y" := (tensor x y);

  (* The binoidal tensor is functorial in each argument separately, whereas
     monoidal categories, whose tensor is a functor from C ∏ C ⟶ C, is
     functorial in both arguments jointly. *)
  left_functor y' : AFunctor (λ x, x ⊗ y');         (* - ⊗ y' (fixes right)  *)
  inj_left (y' : C) : C ⟶ C := FromAFunctor (left_functor y')
    where "x ⋉ y" := (inj_left x y);

  right_functor x' : AFunctor (λ y, x' ⊗ y);        (* x' ⊗ - (fixes left)   *)
  inj_right (x' : C) : C ⟶ C := FromAFunctor (right_functor x')
    where "x ⋊ y" := (inj_right x y);
}.

Context `{Binoidal}.

Notation "x ⋉ y" := (inj_left x y) (at level 15, right associativity).
Notation "x ⋊ y" := (inj_right x y) (at level 15, right associativity).
Notation "x ⊗ y" := (tensor x y) (at level 30, right associativity).

Corollary inj_left_right {x y} : x ⋉ y = y ⋊ x.
Proof. reflexivity. Qed.

(* A morphism f : x ~> y in a binoidal category is central if, for every
   morphism f' : x' ~> y', the two orders of tensoring f and f' agree. The
   first conjunct is the square on x ⊗ x' ~~> y ⊗ y' (f on the left, f' on the
   right); the second is the mirror square on x' ⊗ x ~~> y' ⊗ y. When f is
   central these common composites are the f ⊗ f' and f' ⊗ f below. The
   central morphisms form the centre, a monoidal subcategory of C. *)

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
  (at level 15, right associativity) : morphism_scope.

Notation "(⊗)" := (@tensor _ _) : functor_scope.
Notation "x ⊗ y" := (@tensor _ _ x%object y%object)
  (at level 30, right associativity) : object_scope.
Notation "f ⊗ g" := (composite_ff' f g)
  (at level 30, right associativity) : morphism_scope.
