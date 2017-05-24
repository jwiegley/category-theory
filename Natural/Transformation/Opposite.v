Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Construction.Opposite.
Require Export Category.Functor.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* jww (2017-05-24): TODO
Definition Opposite_Transform `{F : C ⟶ D} {G : C ⟶ D} `(N : F ⟹ G) :
  F^op ⟹ G^op :=
  @Build_Transform (C^op) (D^op) (F^op) (G^op) (transform[N])
    (λ (X Y : (C ^op)%category) (f : X ~{C^op}~> Y),
     _).
Next Obligation.
  rewrite naturality; reflexivity.
Defined.
Next Obligation.
Admitted.

Notation "N ^op" := (@Opposite_Transform _ _ _ _ N)
  (at level 7, format "N ^op") : transform_scope.

Corollary Opposite_Transform_invol `{F : C ⟶ D} {G : C ⟶ D} `(N : F ⟹ G) :
  (N^op)^op = N.
Proof. reflexivity. Qed.
*)
