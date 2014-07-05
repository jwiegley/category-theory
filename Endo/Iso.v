Require Export Basics.

Class Isomorphism X Y :=
{ to   : X -> Y
; from : Y -> X

; iso_to   : from ∘ to = id
; iso_from : to ∘ from = id
}.
  Arguments to       {X} {Y} {Isomorphism} x.
  Arguments from     {X} {Y} {Isomorphism} x.
  Arguments iso_to   {X} {Y} {Isomorphism}.
  Arguments iso_from {X} {Y} {Isomorphism}.

Hint Resolve id_x.
Hint Resolve compose_x.
Hint Resolve iso_to.
Hint Resolve iso_from.

Notation "X ≅ Y" := (Isomorphism X Y) (at level 50) : type_scope.
Notation "x ≡ y" := (to x = y /\ from y = x) (at level 50).

Theorem iso_from_x : forall {X Y} `{X ≅ Y} (y : Y), to (from y) = y.
Proof.
  intros.
  destruct H.
  simpl.
  rewrite <- uncompose with (f := to0).
    rewrite iso_from0.
    reflexivity.
  assumption.
Qed.

Hint Resolve iso_from_x.
