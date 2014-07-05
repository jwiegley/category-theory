Require Export Iso.

Global Instance LTuple_Isomorphism {A} : unit * A ≅ A :=
{ to   := @snd unit A
; from := pair tt
}.
Proof.
  intros.
  ext_eq. destruct x. compute. destruct u. reflexivity.
  ext_eq. compute. reflexivity.
Defined.

Global Instance RTuple_Isomorphism {A} : A * unit ≅ A :=
{ to   := @fst A unit
; from := fun x => (x, tt)
}.
Proof.
  intros.
  ext_eq. destruct x. compute. destruct u. reflexivity.
  ext_eq. compute. reflexivity.
Defined.

Definition tuple_swap_a_bc_to_ab_c {A B C} (x : A * (B * C)) : A * B * C :=
  match x with
    (a, (b, c)) => ((a, b), c)
  end.

Definition tuple_swap_ab_c_to_a_bc {A B C} (x : A * B * C) : A * (B * C) :=
  match x with
    ((a, b), c) => (a, (b, c))
  end.

Definition left_triple {A B C} (x : A) (y : B) (z : C) : A * B * C :=
  ((x, y), z).

Definition right_triple {A B C} (x : A) (y : B) (z : C) : A * (B * C) :=
  (x, (y, z)).

Global Instance Tuple_Assoc {A B C} : A * B * C ≅ A * (B * C) :=
{ to   := tuple_swap_ab_c_to_a_bc
; from := tuple_swap_a_bc_to_ab_c
}.
Proof.
  - (* iso_to *)
    intros.
    ext_eq.
    unfold compose.
    destruct x.
    destruct p.
    unfold id.
    unfold tuple_swap_a_bc_to_ab_c, tuple_swap_ab_c_to_a_bc.
    reflexivity.
  - (* iso_from *)
    intros.
    ext_eq.
    unfold compose.
    destruct x.
    destruct p.
    unfold id.
    unfold tuple_swap_a_bc_to_ab_c, tuple_swap_ab_c_to_a_bc.
    reflexivity.
Defined.

Definition uncurry {X Y Z} (f : X -> Y -> Z) (xy : X * Y) : Z :=
  match xy with (x, y) => f x y end.

Theorem uncurry_works : forall {X Y Z} (x : X) (y : Y) (f : X -> Y -> Z),
  uncurry f (x, y) = f x y.
Proof. reflexivity. Qed.
