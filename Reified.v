Require Import Lib.
Require Export BiCCC.

Generalizable All Variables.
Set Primitive Projection.
Set Universe Polymorphism.

Inductive Obj : Type :=
  | One_    : Obj
  | Prod_   : Obj -> Obj -> Obj
  | Exp_    : Obj -> Obj -> Obj
  | Zero_   : Obj
  | Coprod_ : Obj -> Obj -> Obj.

Fixpoint denote `(o : Obj) : ∀ `{BiCCC C}, C := fun _ _ _ _ _ =>
  match o with
  | One_        => One
  | Prod_ x y   => denote x × denote y
  | Exp_ x y    => denote y ^ denote x
  | Zero_       => Zero
  | Coprod_ x y => denote x + denote y
  end.

Inductive Hom : Obj -> Obj -> Type :=
  | Id      : ∀ {a}, Hom a a
  | Compose : ∀ {a b c}, Hom b c -> Hom a b -> Hom a c

  | One'    : ∀ {a}, Hom a One_

  | Exl     : ∀ {a b}, Hom (Prod_ a b) a
  | Exr     : ∀ {a b}, Hom (Prod_ a b) b
  | Fork    : ∀ {a c d}, Hom a c -> Hom a d -> Hom a (Prod_ c d)

  | Curry   : ∀ {a b c}, Hom (Prod_ a b) c -> Hom a (Exp_ b c)
  | Uncurry : ∀ {a b c}, Hom a (Exp_ b c) -> Hom (Prod_ a b) c

  | Zero'   : ∀ {a}, Hom Zero_ a

  | Inl     : ∀ {a b}, Hom a (Coprod_ a b)
  | Inr     : ∀ {a b}, Hom b (Coprod_ a b)
  | Merge   : ∀ {a c d}, Hom c a -> Hom d a -> Hom (Coprod_ c d) a.

Program Fixpoint interp `(c : Hom a b) :
  ∀ `{BiCCC C}, denote a ~{C}~> denote b := fun _ _ _ _ _ =>
  match c with
  | Id          => id
  | Compose f g => interp f ∘ interp g

  | One'        => one

  | Exl         => exl
  | Exr         => exr
  | Fork f g    => fork (interp f) (interp g)

  | Curry f     => curry (interp f)
  | Uncurry f   => uncurry (interp f)

  | Zero'       => zero

  | Inl         => inl
  | Inr         => inr
  | Merge f g   => merge (interp f) (interp g)
  end.

Local Obligation Tactic := simpl; intros; auto; cat.

Program Instance Hom_Category : Category Obj := {
  hom := Hom;
  id := @Id;
  compose := @Compose;
  eqv := fun _ _ f g =>
           forall `{BiCCC C},
             @eqv C _ _ _ (interp f) (interp g)
}.
Obligation 1.
  constructor.
  - intros ??????.
    reflexivity.
  - intros ????????.
    symmetry.
    apply H.
  - intros ??????????.
    rewrite H, H0.
    reflexivity.
Defined.
Obligation 2.
  intros ?????? ?????.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.
Obligation 5.
  rewrite comp_assoc.
  reflexivity.
Qed.

Program Instance Hom_Terminal : Terminal Obj := {
  terminal_category := Hom_Category;
  One := One_;
  one := @One'
}.

Program Instance Hom_Cartesian : Cartesian Obj := {
  cartesian_terminal := Hom_Terminal;
  Prod := Prod_;
  fork := @Fork;
  exl  := @Exl;
  exr  := @Exr
}.
Obligation 1.
  intros ?????? ?????.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.
Obligation 2.
  split; intros.
    split; intros; rewrite H; cat.
  destruct H.
  rewrite <- H, <- H4.
  rewrite fork_comp; cat.
Qed.

Program Instance Hom_Closed : Closed Obj := {
  closed_cartesian := Hom_Cartesian;
  Exp := Exp_;
  curry := @Curry;
  uncurry := @Uncurry
}.
Obligation 1.
  intros ??? ?????.
  simpl.
  rewrite H.
  reflexivity.
Qed.
Obligation 2.
  intros ??? ?????.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Program Instance Hom_Initial : Initial Obj := {
  Zero := Zero_;
  zero := @Zero'
}.

Program Instance Hom_Cocartesian : Cocartesian Obj := {
  Coprod  := Coprod_;
  merge := @Merge;
  inl  := @Inl;
  inr  := @Inr
}.
Obligation 1.
  intros ?????? ?????.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.
Obligation 2.
  split; intros.
    split; intros; rewrite H; cat.
  destruct H.
  rewrite <- H, <- H4.
  rewrite merge_comp; cat.
Qed.

Program Instance Hom_Bicartesian : @Bicartesian Obj _ _ _.

Program Instance Hom_BiCCC : @BiCCC Obj _ _ _.

Section Reified.

Context `{BiCCC C}.

Hint Rewrite (@id_left C _) : category.
Hint Rewrite (@id_right C _) : category.

Local Obligation Tactic :=
  simpl; intros; auto; autorewrite with category; try reflexivity; auto.

Global Program Instance Hom_Functor : Functor Obj C := {
  fobj := fun x => denote x;
  fmap := fun _ _ f => interp f
}.

Global Program Instance Hom_TerminalFunctor : TerminalFunctor Obj C := {
  terminal_category_functor := Hom_Functor;
  map_one := id
}.

Global Program Instance Hom_CartesianFunctor : CartesianFunctor Obj C := {
  terminal_functor := Hom_TerminalFunctor;
  fobj_prod_iso := _
}.

Global Program Instance Hom_ClosedFunctor : ClosedFunctor Obj C := {
  cartesian_functor := Hom_CartesianFunctor;
  fobj_exp_iso := _
}.

Global Program Instance Hom_InitialFunctor : InitialFunctor Obj C := {
  map_zero := id
}.

Global Program Instance Hom_CocartesianFunctor : CocartesianFunctor Obj C := {
  initial_functor := Hom_InitialFunctor;
  fobj_coprod_iso := _
}.

End Reified.
