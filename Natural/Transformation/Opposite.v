Set Warnings "-notation-overridden".
Set Warnings "-notation-incompatible-format".

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Opposite_Transform `{F : C ⟶ D} {G : C ⟶ D} `(N : F ⟹ G) :
  G^op ⟹ F^op :=
  @Build_Transform (C^op) (D^op) (G^op) (F^op) N
    (λ (x y : (C ^op)%category) (f : x ~{C^op}~> y),
      @naturality_sym C D F G N y x f)
    (λ (x y : (C ^op)%category) (f : x ~{C^op}~> y),
      @naturality C D F G N y x f).

Notation "N ^op" := (@Opposite_Transform _ _ _ _ N)
  (at level 7, format "N ^op", left associativity) : transform_scope.

Open Scope transform_scope.

Open Scope transform_scope.

Corollary Opposite_Transform_invol `{F : C ⟶ D} {G : C ⟶ D} `(N : F ⟹ G) :
  (N^op)^op = N.
Proof. reflexivity. Qed.
