Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Cocartesian.
Require Export Category.Structure.Monoidal.Semicartesian.Terminal.
Require Export Category.Structure.Monoidal.Cartesian.
Require Export Category.Structure.Monoidal.Cartesian.Cartesian.
Require Export Category.Structure.Monoidal.Closed.
Require Export Category.Structure.Initial.
Require Export Category.Structure.Terminal.
Require Export Category.Instance.Coq.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition option_bind {A B : Type}
           (f : A → option B) (o : option A) : option B :=
  match o with
  | Some x => f x
  | None => None
  end.

Definition option_join {A : Type} (o : option (option A)) : option A :=
  match o with
  | Some x => x
  | None => None
  end.

(* The category of partial maps expressed as functions in Coq. *)

Program Definition Par : Category := {|
  obj     := Type;
  hom     := fun A B => A ~> option B;
  homset  := fun P Q =>
               {| equiv := fun f g => ∀ x, f x = g x |};
  id      := λ _, Some;
  compose := fun x y z f g => option_bind f ∘ g
|}.
Next Obligation.
  equivalence.
  now rewrite H.
Qed.
Next Obligation.
  proper.
  rewrite H0.
  now destruct (y1 x2); simpl.
Qed.
Next Obligation. now destruct (f x0); simpl. Qed.
Next Obligation. now destruct (h x0); simpl. Qed.
Next Obligation. now destruct (h x0); simpl. Qed.

#[local] Ltac crunch :=
  repeat match goal with
  | [ |- context[match ?X with _ => _ end] ] => destruct X eqn:?; subst
  | [ H : context[match ?X with _ => _ end] |- _ ] => destruct X eqn:?; subst
  | [ H : Some _ = Some _ |- _ ] => inv H
  | [ H : _ _ = Some _ |- _ ] => rewrite H in *
  end; auto; try discriminate; try tauto.

#[local] Ltac solveit :=
  try unfold option_bind;
  solve [ intuition idtac; simpl; crunch
        | intuition eauto
        | firstorder eauto
        | crunch ].

#[export] Program Instance Par_Monoidal : @Monoidal Par := {
  I := False;
  tensor := {|
    fobj := λ '(x, y), (x * y) + x + y; (* smash product *)
    fmap := λ '(x1, x2) '(y1, y2) '(f1, f2) o,
      match o with
      | Datatypes.inl (Datatypes.inl (x, y)) =>
          match f1 x, f2 y with
          | Some x', Some y' => Some (Datatypes.inl (Datatypes.inl (x', y')))
          | Some x', None => Some (Datatypes.inl (Datatypes.inr x'))
          | None, Some y' => Some (Datatypes.inr y')
          | None, None => None
          end
      | Datatypes.inl (Datatypes.inr x) =>
          match f1 x with
          | Some x' => Some (Datatypes.inl (Datatypes.inr x'))
          | None => None
          end
      | Datatypes.inr y =>
          match f2 y with
          | Some y' => Some (Datatypes.inr y')
          | None => None
          end
      end;
  |};
  unit_left := λ _, {|
    to := λ x,
      match x with
      | Datatypes.inl (Datatypes.inl (H, _)) => False_rect _ H
      | Datatypes.inl (Datatypes.inr H) => False_rect _ H
      | Datatypes.inr x => Some x
      end;
    from := λ x, Some (Datatypes.inr x)
  |};
  unit_right := λ _, {|
    to := λ x,
      match x with
      | Datatypes.inl (Datatypes.inl (_, H)) => False_rect _ H
      | Datatypes.inl (Datatypes.inr x) => Some x
      | Datatypes.inr H => False_rect _ H
      end;
    from := λ x, Some (Datatypes.inl (Datatypes.inr x))
  |};
  tensor_assoc := λ _ _ _, {|
    to   := _;
    from := _;
  |};
}.
Next Obligation.
  proper; simpl in *.
  - now rewrite (H a), (H0 b).
  - now rewrite (H b).
  - now rewrite (H0 b).
Qed.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.

#[export] Program Instance Par_BraidedMonoidal : @BraidedMonoidal Par _ := {
  braid := λ _ _, {|
    to   := λ p,
      match p with
      | Datatypes.inl (Datatypes.inl (x, y)) =>
          Some (Datatypes.inl (Datatypes.inl (y, x)))
      | Datatypes.inl (Datatypes.inr x) => Some (Datatypes.inr x)
      | Datatypes.inr y => Some (Datatypes.inl (Datatypes.inr y))
      end;
    from := λ p,
      match p with
      | Datatypes.inl (Datatypes.inl (y, x)) =>
          Some (Datatypes.inl (Datatypes.inl (x, y)))
      | Datatypes.inl (Datatypes.inr y) => Some (Datatypes.inr y)
      | Datatypes.inr x => Some (Datatypes.inl (Datatypes.inr x))
      end;
  |}
}.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.

#[export] Program Instance Par_SymmetricMonoidal : @SymmetricMonoidal Par _.
Next Obligation. solveit. Defined.

#[export] Program Instance Par_RelevantMonoidal : @RelevantMonoidal Par _ := {
  diagonal := λ _ x, Some (Datatypes.inl (Datatypes.inl (x, x)))
}.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.

#[export]
Program Instance Par_SemicartesianMonoidal : @SemicartesianMonoidal Par _ := {
  eliminate := λ _ _, None
}.
Next Obligation.
  destruct (f x0); try tauto.
  destruct (g x0); try tauto.
Defined.

#[export] Program Instance Par_CartesianMonoidal : @CartesianMonoidal Par _.
Next Obligation. solveit. Defined.
Next Obligation. solveit. Defined.

#[export] Instance Par_Terminal : @Terminal Par :=
  @SemicartesianMonoidal_Terminal _ Par_Monoidal Par_SemicartesianMonoidal.

#[export] Program Instance Par_Cartesian : @Cartesian Par :=
  @CartesianMonoidal_Cartesian _ Par_Monoidal Par_CartesianMonoidal.

(* Par is not cartesian closed, but it is monoidal closed by taking the smash
   product as the tensor. *)

#[export] Program Instance Par_Initial : Initial Par := {
  terminal_obj := False;
  one := λ _ _, False_rect _ _
}.
Next Obligation. contradiction. Qed.

#[export] Program Instance Par_Cocartesian : @Cocartesian Par := {
  product_obj := sum;
  fork := λ _ _ _ f g x,
            match x with
            | Datatypes.inl v => f v
            | Datatypes.inr v => g v
            end;
  exl  := λ _ _ p, Some (Datatypes.inl p);
  exr  := λ _ _ p, Some (Datatypes.inr p)
}.
Next Obligation.
  split; intros.
    split; intros;
    rewrite H; reflexivity.
  destruct x0; firstorder.
Qed.

Open Scope object_scope.

#[export] Program Instance Par_ClosedMonoidal : @ClosedMonoidal Par Par_Monoidal := {
  exponent_obj := λ A B, A ~{Par}~> B;
  exp_iso := λ x y z, {|
    to   := {|
      morphism := λ (f : x ⨂ y ~> z) x,
        Some (λ y, f (Datatypes.inl (Datatypes.inl (x, y))))
    |};
    from := {|
      morphism := λ (f : x ~> y ~> z) (o : x ⨂ y),
        match o with
        | Datatypes.inl (Datatypes.inl (x, y)) =>
            option_bind (λ g, g y) (f x)
        | Datatypes.inl (Datatypes.inr x) => None
        | Datatypes.inr y => None
        end;
    |}
  |}
}.
Next Obligation.
  proper.
  f_equal.
  extensionality w.
  apply H.
Qed.
Next Obligation.
  proper.
  now rewrite (H a).
Qed.
Next Obligation.
  unfold option_bind.
  crunch.
Admitted.
Next Obligation.
  crunch.
Admitted.
Next Obligation.
Admitted.
