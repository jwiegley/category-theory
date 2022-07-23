Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Cocartesian.
Require Export Category.Structure.Cartesian.Closed.
Require Export Category.Structure.Initial.
Require Export Category.Structure.Terminal.
Require Export Category.Instance.Coq.
Require Export Coq.Sets.Ensembles.

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
               {| equiv := fun f g => forall x, f x = g x |};
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

Program Instance Par_Terminal : @Terminal Par := {
  terminal_obj := False;
  one := λ _ a, None
}.
Next Obligation.
  destruct (f x0), (g x0); try contradiction; auto.
Qed.

Program Instance Par_Cartesian : @Cartesian Par := {
  product_obj := λ x y, (x * y) + x + y;
  fork := λ _ _ _ f g x,
      match f x, g x with
        | Some a, Some b => Some (Datatypes.inl (Datatypes.inl (a, b)))
        | Some a, None => Some (Datatypes.inl (Datatypes.inr a))
        | None, Some b => Some (Datatypes.inr b)
        | None, None => None
      end;
  exl  := λ _ _ p,
      match p with
      | Datatypes.inl (Datatypes.inl (a, _)) => Some a
      | Datatypes.inl (Datatypes.inr a) => Some a
      | _ => None
      end;
  exr  := λ _ _ p,
      match p with
      | Datatypes.inl (Datatypes.inl (_, b)) => Some b
      | Datatypes.inr b => Some b
      | _ => None
      end;
}.
Next Obligation. proper; congruence. Qed.
Next Obligation. proper; congruence. Qed.
Next Obligation.
  proper.
  rewrite H.
  destruct (y0 x2);
  rewrite H0;
  now destruct (y1 x2).
Qed.
Next Obligation.
  repeat split; intros.
  - rewrite H; clear H.
    now destruct (f x0), (g x0).
  - rewrite H; clear H.
    now destruct (f x0), (g x0).
  - destruct H.
    rewrite <- e, <- e0.
    destruct (h x0); simpl; auto.
    destruct s; simpl; auto.
    destruct s; simpl; auto.
    now destruct p.
Qed.

(* Par is not cartesian closed, but it is monoidal closed by taking the smash
   product as the tensor. *)

Program Instance Par_Initial : Initial Par := {
  terminal_obj := False;
  one := λ _ _, False_rect _ _
}.
Next Obligation. contradiction. Qed.

Program Instance Par_Cocartesian : @Cocartesian Par := {
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
