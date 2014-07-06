Require Export Monad.

Inductive Cont (R A : Type) : Type :=
  Cont_ : ((A -> R) -> R) -> Cont R A.

Definition Cont_map {R X Y} (f : X -> Y) (x : Cont R X) : Cont R Y :=
  match x with
    Cont_ k => Cont_ R Y (fun h => k (h ∘ f))
  end.

Global Instance Cont_Functor {R} : Functor (Cont R) :=
{ fmap := @Cont_map R
}.
Proof.
  - (* fun_identity *)
    intros. ext_eq. compute. destruct x; reflexivity.
  - (* fun_composition *)
    intros. ext_eq. compute. destruct x; reflexivity.
Defined.

Definition Cont_apply {R X Y} (f : Cont R (X -> Y)) (x : Cont R X)
  : Cont R Y :=
  match f with
    Cont_ kf => Cont_ R Y (fun h => kf (fun f' =>
      match x with
        Cont_ kx => kx (fun x' => h (f' x'))
      end))
  end.

Global Instance Cont_Applicative {R} : Applicative (Cont R) :=
{ is_functor := Cont_Functor
; eta := fun A x => Cont_ R A (fun k => k x)
; apply := @Cont_apply R
}.
Proof.
  - (* app_identity *)
    intros. ext_eq. compute. destruct x; reflexivity.
  - (* app_composition *)
    intros. compute.
    destruct u.
      destruct v; reflexivity.
  - (* app_homomorphism *)
    intros. compute. reflexivity.
  - (* app_interchange *)
    intros. compute. destruct u; reflexivity.
  - (* app_fmap_unit *)
    intros. ext_eq. compute. destruct x; reflexivity.
Defined.

Definition Cont_join {R X} (x : Cont R (Cont R X)) : Cont R X :=
  match x with
    Cont_ k => Cont_ R X (fun h => k (fun m =>
      match m with
        Cont_ km => km (fun x' => h x')
      end))
  end.

Global Instance Cont_Monad {R} : Monad (Cont R) :=
{ is_applicative := Cont_Applicative
; mu := @Cont_join R
}.
Proof.
  - (* monad_law_1 *)
    intros. ext_eq. compute.
    destruct x.
    f_equal. ext_eq.
    f_equal. ext_eq.
    destruct x0.
    f_equal.
  - (* monad_law_2 *)
    intros. ext_eq. compute.
    destruct x; reflexivity.
  - (* monad_law_3 *)
    intros. ext_eq. compute.
    destruct x; reflexivity.
  - (* monad_law_4 *)
    intros. ext_eq. compute.
    destruct x.
    f_equal. ext_eq.
    f_equal. ext_eq.
    destruct x0.
    f_equal.
Defined.
