Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Coq.
Require Import Category.Theory.Coq.Semigroup.
Require Import Category.Theory.Coq.Monoid.

Generalizable All Variables.

Section ParE.

Context {E : Type}.
Context `{Monoid E}.

Definition sum_bind {A B : Type} (f : A → E + B) (o : E + A) : E + B :=
  match o with
  | Datatypes.inl x => Datatypes.inl x
  | Datatypes.inr y => f y
  end.

Ltac bust x := destruct (x _); subst; auto; try tauto.

(* The category of partial maps yielding errors is expressed as functions in
   Coq via error irrelevance: that is, two morphisms are considered equivalent
   if, for a given input, they either yield the same output or both yield some
   error.

   jww (2022-08-19): I could say something stronger here, like error
   compatibility: There exists some error of which both errors form a part.
   However, I was unable to prove transitivity for this formulation. *)

Program Definition ParE : Category := {|
  obj     := Type;
  hom     := λ A B, A ~> E + B;
  homset  := λ _ _, {|
    equiv := λ f g, ∀ x,
      match f x, g x return Type with
      | Datatypes.inr x, Datatypes.inr y => x = y
      | Datatypes.inl _, Datatypes.inl _ => True
      | _, _ => False
      end
  |};
  id      := λ _, Datatypes.inr;
  compose := λ _ _ _ f g, sum_bind f ∘ g
|}.
Next Obligation.
  equivalence.
  - bust x.
  - specialize (X x0).
    bust y; bust x.
  - specialize (X x0).
    specialize (X0 x0).
    bust x; bust y.
Qed.
Next Obligation.
  proper.
  unfold sum_bind.
  specialize (X0 x2).
  bust x1; bust y1.
  specialize (X y3).
  bust x0; bust y0.
Qed.
Next Obligation.
  unfold sum_bind.
  bust f.
Qed.
Next Obligation.
  unfold sum_bind.
  bust f.
Qed.
Next Obligation.
  unfold sum_bind.
  bust h; bust g; bust f.
Qed.
Next Obligation.
  unfold sum_bind.
  bust h; bust g; bust f.
Qed.

#[export] Program Instance ParE_Terminal : @Terminal ParE := {
  terminal_obj := False;
  one := λ _ _, Datatypes.inl mempty
}.
Next Obligation.
  destruct (f x0), (g x0); try contradiction; auto.
Qed.

#[export] Program Instance Par_Cartesian : @Cartesian ParE := {
  product_obj := λ x y, (x * y) + x + y;
  fork := λ _ _ _ f g x,
      match f x, g x with
        | Datatypes.inr a, Datatypes.inr b =>
            Datatypes.inr (Datatypes.inl (Datatypes.inl (a, b)))
        | Datatypes.inr a, Datatypes.inl _ =>
            Datatypes.inr (Datatypes.inl (Datatypes.inr a))
        | Datatypes.inl _, Datatypes.inr b =>
            Datatypes.inr (Datatypes.inr b)
        | Datatypes.inl e, Datatypes.inl e' =>
            Datatypes.inl (e ⊗ e')
      end;
  exl  := λ _ _ p,
      match p with
      | Datatypes.inl (Datatypes.inl (a, _)) => Datatypes.inr a
      | Datatypes.inl (Datatypes.inr a) => Datatypes.inr a
      | _ => Datatypes.inl mempty
      end;
  exr  := λ _ _ p,
      match p with
      | Datatypes.inl (Datatypes.inl (_, b)) => Datatypes.inr b
      | Datatypes.inr b => Datatypes.inr b
      | _ => Datatypes.inl mempty
      end;
}.
Next Obligation. proper; congruence. Qed.
Next Obligation. proper; congruence. Qed.
Next Obligation.
  proper.
  specialize (X x2).
  specialize (X0 x2).
  bust x0; bust x1; bust y0; bust y1.
Qed.
Next Obligation.
  unfold sum_bind.
  repeat split; intros.
  - specialize (X x0).
    bust h; bust f; bust g.
  - specialize (X x0).
    bust h; bust f; bust g.
  - destruct X.
    specialize (y0 x0).
    specialize (y1 x0).
    bust h; bust f; bust g;
    destruct s; subst; auto; try tauto;
    destruct s; subst; auto; try tauto;
    destruct p; subst; auto; try tauto.
Qed.

(* Par is not cartesian closed, but it is monoidal closed by taking the smash
   product as the tensor. *)

#[export] Program Instance Par_Initial : Initial ParE := {
  terminal_obj := False;
  one := λ _ _, False_rect _ _
}.
Next Obligation. contradiction. Qed.

#[export] Program Instance Par_Cocartesian : @Cocartesian ParE := {
  product_obj := sum;
  fork := λ _ _ _ f g x,
            match x with
            | Datatypes.inl v => f v
            | Datatypes.inr v => g v
            end;
  exl  := λ _ _ p, Datatypes.inr (Datatypes.inl p);
  exr  := λ _ _ p, Datatypes.inr (Datatypes.inr p)
}.
Next Obligation.
  proper.
  - specialize (X a).
    bust x0; bust y0.
  - specialize (X0 b).
    bust x1; bust y1.
Qed.
Next Obligation.
  split; intros.
  - split; intros.
    + specialize (X (Datatypes.inl x0)).
      bust h.
    + specialize (X (Datatypes.inr x0)).
      bust h.
  - destruct x0; firstorder.
Qed.

End ParE.
