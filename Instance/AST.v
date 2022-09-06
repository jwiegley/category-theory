Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.BiCCC.
Require Import Category.Instance.Sets.

Generalizable All Variables.

#[local] Obligation Tactic := cat_simpl.

Inductive Obj : Type :=
  | One_    : Obj
  | Prod_   : Obj → Obj → Obj
  | Exp_    : Obj → Obj → Obj
  | Zero_   : Obj
  | Coprod_ : Obj → Obj → Obj.

Fixpoint denote `(o : Obj) :
  ∀ {C : Category}
    {A : @Cartesian C}
    `{@Closed C A}
    `{@Cocartesian C}
    `{@Terminal C}
    `{@Initial C}, C := fun _ _ _ _ _ _ =>
  match o with
  | One_        => 1
  | Prod_ x y   => denote x × denote y
  | Exp_ x y    => denote y ^ denote x
  | Zero_       => 0
  | Coprod_ x y => denote x + denote y
  end.

(* jww (2017-06-21): This describes the morphisms of a magmoid. *)
Inductive Hom : Obj → Obj → Type :=
  | Id      : ∀ {a}, Hom a a
  | Compose : ∀ {a b c}, Hom b c → Hom a b → Hom a c

  | One'    : ∀ {a}, Hom a One_

  | Exl     : ∀ {a b}, Hom (Prod_ a b) a
  | Exr     : ∀ {a b}, Hom (Prod_ a b) b
  | Fork    : ∀ {a c d}, Hom a c → Hom a d → Hom a (Prod_ c d)

  | Curry   : ∀ {a b c}, Hom (Prod_ a b) c → Hom a (Exp_ b c)
  | Uncurry : ∀ {a b c}, Hom a (Exp_ b c) → Hom (Prod_ a b) c

  | Zero'   : ∀ {a}, Hom Zero_ a

  | Inl     : ∀ {a b}, Hom a (Coprod_ a b)
  | Inr     : ∀ {a b}, Hom b (Coprod_ a b)
  | Merge   : ∀ {a c d}, Hom c a → Hom d a → Hom (Coprod_ c d) a.

Program Fixpoint interp `(c : Hom a b) :
  ∀ {C : Category}
    {A : @Cartesian C}
    `{@Closed C A}
    `{@Cocartesian C}
    `{@Terminal C}
    `{@Initial C}, denote a ~{C}~> denote b := fun _ _ _ _ _ _ =>
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

#[export]
Program Instance AST : Category := {
  obj     := Obj;
  hom     := Hom;
  id      := @Id;
  compose := @Compose;
  homset  := fun _ _ =>
    {| equiv := fun f g =>
         ∀ (C : Category)
                (A : @Cartesian C)
                `(@Closed C A)
                `(@Cocartesian C)
                `(@Terminal C)
                `(@Initial C),
           interp f ≈ interp g |}
}.
Next Obligation.
  equivalence.
  transitivity (interp y); auto.
Qed.

#[export]
Program Instance Hom_Terminal : @Terminal AST := {
  terminal_obj := One_;
  one := @One'
}.
Next Obligation. apply one_unique. Qed.

#[export]
Program Instance Hom_Cartesian : @Cartesian AST := {
  product_obj := Prod_;
  fork := @Fork;
  exl  := @Exl;
  exr  := @Exr
}.
Next Obligation. proper; rewrite X, X0; reflexivity. Qed.
Next Obligation.
  split; intros HA.
    split; intros; rewrite HA; cat.
  intros.
  destruct HA as [? ?].
  rewrite <- e, <- e0.
  rewrite fork_comp; cat.
Qed.

#[export]
Program Instance Hom_Closed : @Closed AST _ := {
  exponent_obj := Exp_;
  exp_iso := fun x y z =>
    {| to   := {| morphism := @Curry x y z |}
     ; from := {| morphism := @Uncurry x y z |} |}
}.
Next Obligation. proper; rewrite X; reflexivity. Qed.
Next Obligation. proper; rewrite X; reflexivity. Qed.

#[export]
Program Instance Hom_Initial : @Initial AST := {
  terminal_obj := Zero_;
  one := @Zero'
}.
Next Obligation. apply zero_unique. Qed.

#[export]
Program Instance Hom_Cocartesian : @Cocartesian AST := {
  product_obj := Coprod_;
  fork := @Merge;
  exl  := @Inl;
  exr  := @Inr
}.
Next Obligation. proper; rewrite X, X0; reflexivity. Qed.
Next Obligation.
  split; intros HA.
    split; intros; rewrite HA; cat.
  intros.
  destruct HA as [? ?].
  rewrite <- e, <- e0.
  rewrite merge_comp; cat.
Qed.

#[export]
Program Instance interp_proper {x y : Obj}
        {C : Category} {A : @Cartesian C}
        `{@Closed C A} `{@Cocartesian C}
        `{@Terminal C} `{@Initial C} :
  Proper (@equiv _ (@homset AST x y) ==>
                     @equiv _ (@homset C _ _))
         (fun f => @interp x y f C A _ _ _ _).

Require Import Category.Functor.Structure.Terminal.
Require Import Category.Functor.Structure.Cartesian.
Require Import Category.Functor.Structure.Cartesian.Closed.

Section AST.

Context {C : Category}.
Context {A : @Cartesian C}.
Context `{@Closed C A}.
Context `{@Cocartesian C}.
Context `{@Terminal C}.
Context `{@Initial C}.

#[export] Program Instance AST_Functor : AST ⟶ C := {
  fobj := λ x, denote x;
  fmap := λ _ _ f, interp f
}.

Program Definition Hom_TerminalFunctor : TerminalFunctor := {|
  fobj_one_iso := _
|}.

#[local] Program Instance Hom_CartesianFunctor : CartesianFunctor := {
  fobj_prod_iso := _
}.

Program Definition Hom_ClosedFunctor : ClosedFunctor := {|
  fobj_exp_iso := _
|}.

Program Definition Hom_InitialFunctor : InitialFunctor AST_Functor := {|
  fobj_one_iso := _
|}.

Program Definition Hom_CocartesianFunctor : CocartesianFunctor AST_Functor := {|
  fobj_prod_iso := _
|}.

End AST.
