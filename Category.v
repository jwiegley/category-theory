Require Import
  Coq.Unicode.Utf8
  Coq.Init.Datatypes
  Coq.Classes.Morphisms
  Coq.Classes.RelationClasses
  Coq.Relations.Relation_Definitions
  Coq.Setoids.Setoid
  Coq.Logic.JMeq
  Coq.Program.Tactics
  FunctionalExtensionality.

(*
- Break into multiple files
- Move into category-theory
*)

Generalizable All Variables.

Close Scope nat_scope.
Close Scope type_scope.

Notation "f -> g" := (f -> g)%type : category_scope.

Open Scope category_scope.
Delimit Scope category_scope with category.

Reserved Infix "∘" (at level 30, right associativity).
Reserved Infix "~>" (at level 90, right associativity).
Reserved Infix "≈" (at level 79).

Class Category (ob : Type) := {
  uhom := Type : Type;
  hom  : ob → ob → uhom where "a ~> b" := (hom a b);

  id {A} : A ~> A;
  compose {A B C} (f: B ~> C) (g : A ~> B) : A ~> C
    where "f ∘ g" := (compose f g);

  eqv {A B : ob} : relation (A ~> B)
    where "f ≈ g" := (eqv f g);

  eqv_equivalence : ∀ A B, Equivalence (@eqv A B);
  compose_respects : ∀ A B C,
    Proper (@eqv B C ==> @eqv A B ==> @eqv A C) compose;

  id_left {X Y} (f : X ~> Y) : id ∘ f ≈ f;
  id_right {X Y} (f : X ~> Y) : f ∘ id ≈ f;

  comp_assoc {X Y Z W} (f : Z ~> W) (g : Y ~> Z) (h : X ~> Y) :
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h
}.

Infix "~>" := hom : category_scope.
Infix "≈" := eqv : category_scope.
Infix "~{ C }~>" := (@hom C _) (at level 90) : category_scope.
Infix "∘" := compose : category_scope.

Notation "id[ X  ]" := (@id _ _ X)  (at level 50) : category_scope.

Add Parametric Relation `{Category C} (a b : C) : (hom a b) eqv
  reflexivity proved by  (@Equivalence_Reflexive  _ _ (eqv_equivalence a b))
  symmetry proved by     (@Equivalence_Symmetric  _ _ (eqv_equivalence a b))
  transitivity proved by (@Equivalence_Transitive _ _ (eqv_equivalence a b))
    as parametric_relation_eqv.

Add Parametric Morphism `{Category C} (a b c : C) : (@compose C _ a b c)
  with signature (eqv ==> eqv ==> eqv) as parametric_morphism_compose.
Proof.
  exact (@compose_respects _ _ a b c).
Defined.

Add Parametric Morphism `{Category C} (a b : C) : eqv
  with signature (eqv --> @eqv _ _ a b ++> Basics.impl)
    as impl_eqv.
Proof.
  intros.
  rewrite H0, <- H1.
  reflexivity.
Qed.

Add Parametric Morphism `{Category C} (a b : C) : eqv
  with signature (eqv --> @eqv _ _ a b ++> Basics.flip Basics.impl)
    as flip_impl_eqv.
Proof.
  intros.
  rewrite H0, <- H1.
  reflexivity.
Qed.

Hint Constructors Equivalence.

Hint Unfold Reflexive.
Hint Unfold Symmetric.
Hint Unfold Transitive.

Hint Extern 1 (Proper _ _) => unfold Proper; auto.
Hint Extern 1 (Reflexive ?X) => unfold Reflexive; auto.
Hint Extern 1 (Symmetric ?X) => unfold Symmetric; intros; auto.
Hint Extern 1 (Transitive ?X) => unfold Transitive; intros; auto.
Hint Extern 1 (Equivalence ?X) => apply Build_Equivalence.
Hint Extern 8 (respectful _ _ _ _) => unfold respectful; auto.

Hint Extern 4 (?A ≈ ?A) => reflexivity.
Hint Extern 6 (?X ≈ ?Y) => apply Equivalence_Symmetric.
Hint Extern 7 (?X ≈ ?Z) =>
  match goal with
    [H : ?X ≈ ?Y, H' : ?Y ≈ ?Z |- ?X ≈ ?Z] => transitivity Y
  end.
Hint Extern 10 (?X ∘ ?Y ≈ ?Z ∘ ?Q) => apply compose_respects; auto.

Definition arrow (A B : Type) := A -> B.

Global Program Instance Coq_Category : Category Type := {
  hom     := arrow;
  id      := fun _ x => x;
  compose := fun _ _ _ g f x => g (f x);
  eqv     := fun _ _ => eq
}.

Record isomorphism `{Category ob}
       `(iso_to : X ~> Y) `(iso_from: Y ~> X) : Prop := {
  iso_to_from : iso_to   ∘ iso_from ≈ id;
  iso_from_to : iso_from ∘ iso_to   ≈ id
}.

Arguments iso_to_from {_ _ _ _ _ _} _.
Arguments iso_from_to {_ _ _ _ _ _} _.

Record isomorphic `{Category ob} (X Y : ob) : Type := {
  iso_to   : X ~> Y;
  iso_from : Y ~> X;
  iso_witness : isomorphism iso_to iso_from
}.

Arguments iso_to {_ _ X Y} _.
Arguments iso_from {_ _ X Y} _.
Arguments iso_witness {_ _ X Y} _.

Infix "≅" := isomorphic (at level 90) : category_scope.

Theorem iso_refl `{Category ob} (X : ob) : X ≅ X.
Proof.
  intros.
  apply Build_isomorphic with (iso_to:=id) (iso_from:=id).
  constructor; rewrite id_left; auto.
Defined.

Theorem iso_sym `{Category ob} (X Y : ob) : X ≅ Y -> Y ≅ X.
Proof.
  intros.
  destruct X0.
  apply Build_isomorphic with (iso_to:=iso_from0) (iso_from:=iso_to0).
  destruct iso_witness0.
  constructor; auto.
Defined.

Theorem iso_trans `{Category ob} (X Y Z : ob) : X ≅ Y -> Y ≅ Z -> X ≅ Z.
Proof.
  intros.
  destruct X0, X1.
  apply Build_isomorphic with (iso_to:=iso_to1 ∘ iso_to0)
                              (iso_from:=iso_from0 ∘ iso_from1).
  destruct iso_witness0, iso_witness1.
  constructor.
    rewrite <- comp_assoc.
    rewrite (@comp_assoc _ _ _ _ _ _ iso_to0).
    rewrite iso_to_from0.
    rewrite id_left.
    assumption.
  rewrite <- comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ _ iso_from1).
  rewrite iso_from_to1.
  rewrite id_left.
  assumption.
Defined.

Class Terminal (ob : Type) := {
  terminal_category :> Category ob;
  One : ob;
  one {A} : A ~> One;

  one_eqv {A} (f g : A ~> One) : f ≈ g
}.

Notation "X ~> 1" := (X ~> One) (at level 50) : category_scope.

Corollary one_comp `{Terminal C} {A B : C} {f : A ~> B} :
  one ∘ f ≈ one.
Proof.
  intros.
  apply one_eqv.
Defined.

Global Program Instance Coq_Terminal : Terminal Type := {
  terminal_category := Coq_Category;
  One := unit : Type;
  one := fun _ a => tt
}.
Obligation 1.
  extensionality x.
  destruct (f x), (g x).
  reflexivity.
Qed.

Reserved Infix "×" (at level 40, left associativity).

Class Cartesian (ob : Type) := {
  cartesian_terminal :> Terminal ob;

  Prod : ob -> ob -> ob
    where "X × Y" := (Prod X Y);

  fork {X Z W} (f : X ~> Z) (g : X ~> W) : X ~> Z × W;
  exl  {X Y} : X × Y ~> X;
  exr  {X Y} : X × Y ~> Y;

  fork_respects : ∀ X Z W,
    Proper (@eqv _ _ X Z ==> @eqv _ _ X W ==> @eqv _ _ X (Z × W)) fork;

  univ_products {X Y Z} (f : X ~> Y) (g : X ~> Z) (h : X ~> Y × Z) :
    h ≈ fork f g <-> exl ∘ h ≈ f ∧ exr ∘ h ≈ g
}.

Infix "×" := Prod : category_scope.
Infix "△" := fork (at level 28) : category_scope.

Add Parametric Morphism `(_ : Cartesian ob) (a b c : ob) : (@fork ob _ a b c)
  with signature (eqv ==> eqv ==> eqv) as parametric_morphism_fork.
Proof.
  exact (@fork_respects _ _ a b c).
Defined.

Definition first `{Cartesian C} {X Y Z : C} (f : X ~> Y) : X × Z ~> Y × Z :=
  (f ∘ exl) △ exr.

Definition second `{Cartesian C} {X Y Z : C} (f : X ~> Y) : Z × X ~> Z × Y :=
  exl △ (f ∘ exr).

Definition swap `{Cartesian C} {X Y : C} : X × Y ~> Y × X := exr △ exl.

Corollary exl_fork `{Cartesian C} {X Z W : C} (f : X ~> Z) (g : X ~> W) :
  exl ∘ f △ g ≈ f.
Proof.
  intros.
  apply (proj1 (univ_products f g (f △ g)) (reflexivity _)).
Qed.

Corollary exr_fork `{Cartesian C} {X Z W : C} (f : X ~> Z) (g : X ~> W) :
  exr ∘ f △ g ≈ g.
Proof.
  intros.
  apply (proj1 (univ_products f g (f △ g)) (reflexivity _)).
Qed.

Corollary fork_exl_exr `{Cartesian C} {X Y : C} :
  exl △ exr ≈ @id C _ (X × Y).
Proof.
  intros.
  symmetry.
  apply (proj2 (univ_products exl exr id)).
  rewrite !id_right; auto.
Qed.

Corollary fork_inv `{Cartesian C} {X Y Z : C} (f h : X ~> Y) (g i : X ~> Z) :
  f △ g ≈ h △ i <-> f ≈ h ∧ g ≈ i.
Proof.
  pose proof (@univ_products _ _ X Y Z h i (f △ g)).
  rewrite exl_fork in H0.
  rewrite exr_fork in H0.
  apply H0.
Qed.

Corollary fork_comp_hetero `{Cartesian C} {X Y Z W : C}
          (f : Y ~> Z) (h : Y ~> W) (g i : X ~> Y) :
  (f ∘ g) △ (h ∘ i) ≈ (f ∘ exl) △ (h ∘ exr) ∘ g △ i.
Proof.
  intros.
  symmetry.
  apply univ_products.
  rewrite !comp_assoc.
  rewrite exl_fork.
  rewrite exr_fork.
  rewrite <- !comp_assoc.
  rewrite exl_fork.
  rewrite exr_fork.
  auto.
Qed.

Corollary fork_comp `{Cartesian C} {X Y Z W : C}
          (f : Y ~> Z) (h : Y ~> W) (g : X ~> Y) :
  (f ∘ g) △ (h ∘ g) ≈ f △ h ∘ g.
Proof.
  intros.
  symmetry.
  apply univ_products.
  rewrite !comp_assoc.
  rewrite exl_fork.
  rewrite exr_fork.
  auto.
Qed.

Definition swap_invol `{Cartesian C} {X Y : C} :
  swap ∘ swap ≈ @id _ _ (X × Y).
Proof.
  unfold swap.
  rewrite <- fork_comp.
  rewrite exl_fork.
  rewrite exr_fork.
  rewrite fork_exl_exr.
  reflexivity.
Qed.

Definition swap_inj_l `{Cartesian C} {X Y Z : C} (f g : X ~> Y × Z) :
  swap ∘ f ≈ swap ∘ g -> f ≈ g.
Proof.
  intros.
  rewrite <- id_left.
  rewrite <- (id_left g).
  rewrite <- swap_invol.
  rewrite <- comp_assoc.
  rewrite H0.
  rewrite comp_assoc.
  reflexivity.
Qed.

Definition swap_inj_r `{Cartesian C} {X Y Z : C} (f g : X × Y ~> Z) :
  f ∘ swap ≈ g ∘ swap -> f ≈ g.
Proof.
  intros.
  rewrite <- id_right.
  rewrite <- (id_right g).
  rewrite <- swap_invol.
  rewrite comp_assoc.
  rewrite H0.
  rewrite <- comp_assoc.
  reflexivity.
Qed.

Notation "1 × X" := (Prod One X) (at level 40).
Notation "X × 1" := (Prod X One) (at level 40).

Theorem prod_one_l `{Cartesian C} {X : C} :
  1 × X ≅ X.
Proof.
  intros.
  refine {| iso_to   := exr
          ; iso_from := one △ id |}.
  constructor; simpl; intros.
    rewrite exr_fork.
    reflexivity.
  rewrite <- fork_comp.
  rewrite id_left.
  rewrite <- fork_exl_exr.
  apply fork_respects; auto.
  apply one_eqv.
Defined.

Theorem prod_one_r `{Cartesian C} {X : C} :
  X × 1 ≅ X.
Proof.
  intros.
  refine {| iso_to   := exl
          ; iso_from := id △ one |}.
  constructor; simpl; intros.
    rewrite exl_fork.
    reflexivity.
  rewrite <- fork_comp.
  rewrite id_left.
  rewrite <- fork_exl_exr.
  apply fork_respects; auto.
  apply one_eqv.
Defined.

Theorem prod_comp `{Cartesian C} {X Y Z : C} :
  (X × Y) × Z ≅ X × (Y × Z).
Proof.
  intros.
  refine {| iso_to   := (exl ∘ exl) △ ((exr ∘ exl) △ exr)
          ; iso_from := (exl △ (exl ∘ exr)) △ (exr ∘ exr) |}.
  constructor; simpl; intros.
    rewrite <- !fork_comp.
    rewrite exr_fork.
    rewrite <- comp_assoc.
    rewrite !exl_fork.
    rewrite <- comp_assoc.
    rewrite !exl_fork.
    rewrite !exr_fork.
    rewrite fork_comp.
    rewrite fork_exl_exr.
    rewrite id_left.
    rewrite fork_exl_exr.
    reflexivity.
  rewrite <- !fork_comp.
  rewrite exl_fork.
  rewrite <- comp_assoc.
  rewrite !exr_fork.
  rewrite <- comp_assoc.
  rewrite !exr_fork.
  rewrite !exl_fork.
  rewrite fork_comp.
  rewrite fork_exl_exr.
  rewrite id_left.
  rewrite fork_exl_exr.
  reflexivity.
Qed.

Global Program Instance Coq_Cartesian : Cartesian Type := {
  cartesian_terminal := Coq_Terminal;
  Prod := prod;
  fork := fun _ _ _ f g x => (f x, g x);
  exl  := fun _ _ p => fst p;
  exr  := fun _ _ p => snd p
}.
Obligation 1.
  split; intros; subst.
    split; extensionality x; reflexivity.
  destruct H.
  subst; simpl.
  extensionality x.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.

Class Closed (ob : Type) := {
  closed_cartesian :> Cartesian ob;

  Exp : ob -> ob -> ob    (* internal homs *)
    where "Y ^ X" := (Exp X Y);

  curry   {X Y Z} (f : X × Y ~> Z) : X ~> Z^Y;
  uncurry {X Y Z} (f : X ~> Z^Y) : X × Y ~> Z;

  curry_respects   : ∀ X Y Z, Proper (eqv ==> @eqv _ _ X (Z^Y))   curry;
  uncurry_respects : ∀ X Y Z, Proper (eqv ==> @eqv _ _ (X × Y) Z) uncurry;

  curry_uncurry {X Y Z} (f : X ~> Z^Y) :   curry   (uncurry f) ≈ f;
  uncurry_curry {X Y Z} (f : X × Y ~> Z) : uncurry (curry   f) ≈ f;

  univ_exponentials {X Y Z} (f : X × Y ~> Z) :
    uncurry id ∘ first (curry f) ≈ f
}.

Notation "Y ^ X" := (Exp X Y) : category_scope.

Add Parametric Morphism `(_ : Closed C) (a b c : C) : (@curry C _ a b c)
  with signature (eqv ==> eqv) as parametric_morphism_curry.
Proof.
  exact (@curry_respects _ _ a b c).
Defined.

Add Parametric Morphism `(_ : Closed C) (a b c : C) : (@uncurry C _ a b c)
  with signature (eqv ==> eqv) as parametric_morphism_uncurry.
Proof.
  exact (@uncurry_respects _ _ a b c).
Defined.

Definition eval `{Closed C} {X Y : C} : Y^X × X ~> Y := uncurry id.

Corollary eval_curry `{Closed C}
          {X Y Z W : C} (f : Y × Z ~> W) (g : X ~> Y) (h : X ~> Z) :
  eval ∘ ((curry f ∘ g) △ h) ≈ f ∘ g △ h.
Proof.
  intros.
  pose proof (@univ_exponentials C H _ _ _ f).
  rewrite <- H0 at 2; clear H0.
  rewrite <- comp_assoc.
  unfold first.
  rewrite <- fork_comp.
  rewrite exr_fork.
  rewrite <- comp_assoc.
  rewrite exl_fork.
  reflexivity.
Qed.

Corollary curry_uncurry' `{Closed C} {X Y Z : C} (f : X ~> Z^Y) :
  curry (uncurry f) ≈ f.
Proof.
Abort.

Corollary curry_inj `{Closed C} {X Y Z : C} (f g : X × Y ~> Z) :
  curry f ≈ curry g -> f ≈ g.
Proof.
  intros.
  rewrite <- (uncurry_curry f).
  rewrite <- (uncurry_curry g).
  rewrite H0.
  reflexivity.
Qed.

Corollary uncurry_inj `{Closed C} {X Y Z : C} (f g : X ~> Z^Y) :
  uncurry f ≈ uncurry g -> f ≈ g.
Proof.
  intros.
  rewrite <- (curry_uncurry f).
  rewrite <- (curry_uncurry g).
  rewrite H0.
  reflexivity.
Qed.

Corollary curry_eval `{Closed C} {X Y : C} :
  curry eval ≈ @id _ _ (Y^X).
Proof.
  intros.
  unfold eval.
  rewrite curry_uncurry.
  reflexivity.
Qed.

Corollary curry_comp `{Closed C}
          {X Y Z W : C} (f : Z ~> W) (g : X × Y ~> Z) :
  curry (f ∘ g) ≈ curry (f ∘ eval) ∘ curry g.
Proof.
  intros.
Abort.

Corollary curry_comp_l `{Closed C}
          {X Y Z W : C} (f : Y × Z ~> W) (g : X ~> Y) :
  curry f ∘ g ≈ curry (f ∘ first g).
Proof.
  intros.
  apply uncurry_inj.
  rewrite uncurry_curry.
  pose proof (@univ_exponentials _ _ X Z W (uncurry (curry f ∘ g))).
  rewrite <- H0; clear H0.
  unfold first in *.
  rewrite curry_uncurry.
  rewrite <- curry_eval.
  rewrite uncurry_curry.
  rewrite <- comp_assoc.
  rewrite eval_curry.
  reflexivity.
Qed.

Corollary uncurry_comp `{Closed C}
          {X Y Z W : C} (f : Y ~> W^Z) (g : X ~> Y) :
  uncurry (f ∘ g) ≈ uncurry f ∘ uncurry (curry id ∘ g).
Proof.
  intros.
Abort.

Corollary uncurry_comp_r `{Closed C}
          {X Y Z W : C} (f : Z ~> W) (g : X ~> Z^Y) :
  f ∘ uncurry g ≈ uncurry (curry (f ∘ eval) ∘ g).
Proof.
  intros.
Abort.

Theorem curry_id `{Closed C} {X Y Z : C} (f : X ~> Y) :
  curry (@id _ _ (Y × Z)) ∘ f ≈ curry (first f).
Proof.
  intros.
  rewrite curry_comp_l.
  apply uncurry_inj.
  rewrite !uncurry_curry.
  rewrite id_left.
  reflexivity.
Qed.

Theorem exp_prod_l `{Closed C} {X Y Z : C} :
  Z^(X × Y) ≅ (Z^Y)^X.
Proof.
  intros.
  refine {| iso_to   := curry (curry (eval ∘ iso_to prod_comp))
          ; iso_from := curry (uncurry eval ∘ iso_from prod_comp) |}.
  constructor; simpl; intros.
Abort.

Theorem exp_prod_r `{Closed C} {X Y Z : C} :
  (Y × Z)^X ≅ Y^X × Z^X.
Proof.
  intros.
Abort.

Notation "X ^ 1" := (Exp One X) (at level 30).

Theorem exp_one `{Closed C} {X : C} :
  X^1 ≅ X.
Proof.
  intros.
  refine {| iso_to   := eval ∘ id △ one
          ; iso_from := curry exl |}.
  constructor; simpl; intros.
    rewrite <- comp_assoc.
    rewrite <- fork_comp.
    rewrite id_left.
    rewrite <- (@id_right _ _ _ _ (curry exl)).
    rewrite eval_curry.
    rewrite exl_fork.
    reflexivity.
  rewrite comp_assoc.
  rewrite curry_comp_l.
  rewrite curry_comp_l.
  apply uncurry_inj.
  rewrite uncurry_curry.
  unfold first.
  rewrite exl_fork.
  rewrite <- comp_assoc.
  rewrite exl_fork.
  rewrite <- fork_comp.
  rewrite id_left.
  cut (@one _ _ (X^1) ∘ exl ≈ exr).
    intros.
    rewrite H0.
    rewrite fork_exl_exr.
    rewrite id_right.
    reflexivity.
  rewrite one_comp.
  rewrite (one_eqv exr one).
  reflexivity.
Qed.

Global Program Instance Coq_Closed : Closed Type := {
  closed_cartesian := Coq_Cartesian;
  Exp := arrow;
  curry := fun _ _ _ f a b => f (a, b);
  uncurry := fun _ _ _ f p => f (fst p) (snd p)
}.
Obligation 2.
  extensionality x.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.
Obligation 3.
  extensionality x.
  rewrite <- surjective_pairing.
  reflexivity.
Qed.

Class Initial `(_ : Category ob) := {
  Zero : ob;
  zero {A} : Zero ~> A;

  zero_eqv {A} {f g : Zero ~> A} : f ≈ g
}.

Arguments Initial ob {_}.

Notation "0 ~> X" := (Zero ~> X) (at level 50).

Notation "X ^ 0" := (Exp Zero X) (at level 30).
Notation "0 ^ X" := (Exp X Zero) (at level 30).

Corollary zero_comp `{Initial C} {A B : C} {f : A ~> B} :
  f ∘ zero ≈ zero.
Proof.
  intros.
  apply zero_eqv.
Defined.

Notation "0 × X" := (Prod Zero X) (at level 40).
Notation "X × 0" := (Prod X Zero) (at level 40).

Theorem prod_zero_l `{Closed C} `{@Initial C _} {X : C} :
  0 × X ≅ Zero.
Proof.
  intros.
  refine {| iso_to   := uncurry zero
          ; iso_from := zero |}.
  constructor; simpl; intros.
    apply zero_eqv.
  apply curry_inj.
  apply zero_eqv.
Defined.

Theorem prod_zero_r `{Closed C} `{@Initial C _} {X : C} :
  X × 0 ≅ Zero.
Proof.
  intros.
  refine {| iso_to   := uncurry zero ∘ swap
          ; iso_from := zero |}.
  constructor; simpl; intros.
    apply zero_eqv.
  apply swap_inj_r.
  apply curry_inj.
  apply zero_eqv.
Defined.

Global Program Instance Coq_Initial : Initial Type := {
  Zero := False;
  zero := fun _ _ => False_rect _ _
}.
Obligation 2.
  extensionality x.
  contradiction.
Qed.

Class Cocartesian `(_ : Initial ob) := {
  Sum : ob -> ob -> ob
    where "X + Y" := (Sum X Y);

  merge {X Z W} (f : Z ~> X) (g : W ~> X) : Z + W ~> X;
  inl   {X Y} : X ~> X + Y;
  inr   {X Y} : Y ~> X + Y;

  merge_respects : ∀ X Z W,
    Proper (@eqv _ _ Z X ==> @eqv _ _ W X ==> @eqv _ _ (Z + W) X) merge;

  univ_sums {X Y Z} (f : Y ~> X) (g : Z ~> X) (h : Y + Z ~> X) :
    h ≈ merge f g <-> h ∘ inl ≈ f ∧ h ∘ inr ≈ g
}.

Arguments Cocartesian ob {_ _}.

Infix "+" := Sum : category_scope.
Infix "▽" := merge (at level 26) : category_scope.

Add Parametric Morphism `(_ : Cocartesian ob) (a b c : ob) :
  (@merge ob _ _ _ a b c)
  with signature (eqv ==> eqv ==> eqv) as parametric_morphism_merge.
Proof.
  exact (@merge_respects _ _ _ _ a b c).
Defined.

Corollary inl_merge `{Cocartesian C} {X Z W : C} (f : Z ~> X) (g : W ~> X) :
  f ▽ g ∘ inl ≈ f.
Proof.
  intros.
  apply (proj1 (univ_sums f g (f ▽ g)) (reflexivity _)).
Qed.

Corollary inr_merge `{Cocartesian C} {X Z W : C} (f : Z ~> X) (g : W ~> X) :
  f ▽ g ∘ inr ≈ g.
Proof.
  intros.
  apply (proj1 (univ_sums f g (f ▽ g)) (reflexivity _)).
Qed.

Corollary merge_inl_inr `{Cocartesian C} {X Y : C} :
  inl ▽ inr ≈ @id C _ (X + Y).
Proof.
  intros.
  symmetry.
  apply (proj2 (univ_sums inl inr id)).
  rewrite !id_left.
  auto.
Qed.

Corollary merge_comp `{Cocartesian C}
          {X Y Z W : C} (f : Y ~> Z) (h : W ~> Z) (g : Z ~> X) :
  (g ∘ f) ▽ (g ∘ h) ≈ g ∘ f ▽ h.
Proof.
  intros.
  symmetry.
  apply (univ_sums (g ∘ f) (g ∘ h) (g ∘ f ▽ h)).
  rewrite <- !comp_assoc.
  rewrite inl_merge.
  rewrite inr_merge.
  auto.
Qed.

Notation "0 + X" := (Sum Zero X) (at level 30).
Notation "X + 0" := (Sum X Zero) (at level 30).

Theorem sum_zero_l `{Cocartesian C} {X : C} :
  0 + X ≅ X.
Proof.
  intros.
  refine {| iso_to   := zero ▽ id
          ; iso_from := inr |}.
  constructor; simpl; intros.
    rewrite inr_merge; auto.
  rewrite <- merge_comp.
  rewrite id_right.
  rewrite <- merge_inl_inr.
  apply merge_respects; auto.
  apply zero_eqv.
Defined.

Theorem sum_zero_r `{Cocartesian C} {X : C} :
  X + 0 ≅ X.
Proof.
  intros.
  refine {| iso_to   := id ▽ zero
          ; iso_from := inl |}.
  constructor; simpl; intros.
    rewrite inl_merge; auto.
  rewrite <- merge_comp.
  rewrite id_right.
  rewrite <- merge_inl_inr.
  apply merge_respects; auto.
  apply zero_eqv.
Defined.

Global Program Instance Coq_Cocartesian : Cocartesian Type := {
  Sum := sum;
  merge := fun _ _ _ f g x =>
            match x with
            | Datatypes.inl v => f v
            | Datatypes.inr v => g v
            end;
  inl  := fun _ _ p => Datatypes.inl p;
  inr  := fun _ _ p => Datatypes.inr p
}.
Obligation 1.
  split; intros; subst.
    split; extensionality x; reflexivity.
  destruct H.
  subst; simpl.
  extensionality x.
  destruct x; auto.
Qed.

Class Bicartesian `(_ : Cartesian C) `{Cocartesian C}.

Global Program Instance Coq_Bicartesian : Bicartesian Coq_Cartesian.

Class Distributive `(_ : Bicartesian C) := {
  prod_sum_dist {X Y Z : C} : X × (Y + Z) ≅ X × Y + X × Z
}.

Theorem prod_sum `{Closed C} `{@Initial C _} `{@Cocartesian C _ _} {X Y Z : C} :
  X × (Y + Z) ≅ X × Y + X × Z.
Proof.
  intros.
  refine {| iso_to   :=
              eval ∘ (curry (inl ∘ swap) ▽ curry (inr ∘ swap) ∘ exr) △ exl
          ; iso_from :=
              (exl △ (inl ∘ exr)) ▽ (exl △ (inr ∘ exr)) |}.
  constructor; simpl; intros.
    rewrite <- comp_assoc.
    pose proof (@univ_sums C _ _ _).
    unfold eval, first in *.
Abort.

Theorem exp_sum `{Closed C}
        `{@Initial C _} `{@Cocartesian C _ _}
        `{@Bicartesian C _ _ _ _}
        `{@Distributive C _ _ _ _ _} {X Y Z : C} :
  X^(Y + Z) ≅ X^Y × X^Z.
Proof.
  intros.
  refine {| iso_to   := curry (eval ∘ second inl) △ curry (eval ∘ second inr)
          ; iso_from := curry (merge (eval ∘ first exl) (eval ∘ first exr)
                                    ∘ iso_to prod_sum_dist) |}.
  constructor; simpl; intros.
Abort.

Theorem exp_zero `{Closed C} `{@Initial C _} {X : C} :
  X^0 ≅ One.
Proof.
  intros.
  refine {| iso_to   := one
          ; iso_from := curry (zero ∘ iso_to prod_zero_r) |}.
  constructor; simpl; intros.
    apply one_eqv.
  apply uncurry_inj.
  apply swap_inj_r.
  apply curry_inj.
  apply zero_eqv.
Qed.

Global Program Instance Coq_Distributive : Distributive Coq_Bicartesian.
Obligation 1.
  apply Build_isomorphic with
    (iso_to:=
       fun p : (X × (Y + Z)) =>
         match p with
         | (x, Datatypes.inl y) => Datatypes.inl (x, y)
         | (x, Datatypes.inr z) => Datatypes.inr (x, z)
         end)
    (iso_from:=
       fun p : ((X × Y) + (X × Z)) =>
         match p with
         | Datatypes.inl (x, y) => (x, Datatypes.inl y)
         | Datatypes.inr (x, z) => (x, Datatypes.inr z)
         end).
  constructor; simpl;
  extensionality p;
  intuition.
Qed.

Class Functor `(_ : Category C) `(_ : Category D) := {
  fobj : C -> D;
  fmap {X Y : C} (f : X ~> Y) : fobj X ~> fobj Y;

  fmap_respects : ∀ X Y,
    Proper (@eqv _ _ X Y ==> @eqv _ _ (fobj X) (fobj Y)) fmap;

  fmap_id {X : C} : fmap (@id C _ X) ≈ id;
  fmap_comp {X Y Z : C} (f : Y ~> Z) (g : X ~> Y) :
    fmap (f ∘ g) ≈ fmap f ∘ fmap g
}.

Arguments Functor C {_} D {_}.

Notation "C ⟶ D" := (Functor C D) (at level 90, right associativity).

Add Parametric Morphism `(_ : Functor C D) (a b : C) : (@fmap C _ D _ _ a b)
  with signature (eqv ==> eqv) as parametric_morphism_fmap.
Proof.
  exact (@fmap_respects _ _ _ _ _ a b).
Defined.

Class TerminalFunctor `(_ : Terminal C) `(_ : Terminal D) := {
  terminal_category_functor :> @Functor C _ D _;

  map_one : One ~> fobj One;

  fmap_one {X : C} : fmap one ≈ map_one ∘ @one _ _ (fobj X)
}.

Arguments TerminalFunctor C {_} D {_}.

Class CartesianFunctor `(_ : Cartesian C) `(_ : Cartesian D) := {
  terminal_functor :> TerminalFunctor C D;

  fobj_prod_iso {X Y : C} : fobj (X × Y) ≅ fobj X × fobj Y;

  prod_in  := fun X Y => iso_from (@fobj_prod_iso X Y);
  prod_out := fun X Y => iso_to   (@fobj_prod_iso X Y);

  fmap_exl {X Y : C} : fmap (@exl C _ X Y) ≈ exl ∘ prod_out _ _;
  fmap_exr {X Y : C} : fmap (@exr C _ X Y) ≈ exr ∘ prod_out _ _;
  fmap_fork {X Y Z : C} (f : X ~> Y) (g : X ~> Z) :
    fmap (f △ g) ≈ prod_in _ _ ∘ fmap f △ fmap g
}.

Arguments CartesianFunctor C {_} D {_}.

Arguments prod_in {C _ D _ _ _ _} /.
Arguments prod_out {C _ D _ _ _ _} /.

Notation "prod_in[ C -> D | X ~> Y  ]" := (@prod_in C _ _ _ D _ _ _ _ X Y).
Notation "prod_out[ C -> D | X ~> Y  ]" := (@prod_out C _ _ _ D _ _ _ _ X Y).

Corollary prod_in_out `{CartesianFunctor C D} (X Y : C) :
  prod_in ∘ prod_out ≈ @id _ _ (fobj (X × Y)).
Proof.
  intros.
  exact (iso_from_to (iso_witness (@fobj_prod_iso _ _ _ _ _ X Y))).
Qed.

Corollary prod_out_in `{CartesianFunctor C D} (X Y : C) :
  prod_out ∘ prod_in ≈ @id _ _ (fobj X × fobj Y).
Proof.
  intros.
  exact (iso_to_from (iso_witness (@fobj_prod_iso _ _ _ _ _ X Y))).
Qed.

Corollary prod_in_inj `{CartesianFunctor C D}
          {X Y Z : C} (f g : fobj X ~> fobj X × fobj Y) :
  prod_in ∘ f ≈ prod_in ∘ g <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_left.
    rewrite <- prod_out_in.
    rewrite <- comp_assoc.
    rewrite H2.
    rewrite comp_assoc.
    rewrite prod_out_in.
    rewrite id_left.
    reflexivity.
  subst.
  rewrite H2.
  reflexivity.
Qed.

Corollary prod_out_inj `{CartesianFunctor C D}
          {X Y Z : C} (f g : fobj X ~> fobj (Y × Z)) :
  prod_out ∘ f ≈ prod_out ∘ g <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_left.
    rewrite <- prod_in_out.
    rewrite <- comp_assoc.
    rewrite H2.
    rewrite comp_assoc.
    rewrite prod_in_out.
    rewrite id_left.
    reflexivity.
  subst.
  rewrite H2.
  reflexivity.
Qed.

Class ClosedFunctor `(_ : Closed C) `(_ : Closed D) := {
  cartesian_functor :> CartesianFunctor C D;

  fobj_exp_iso {X Y : C} : fobj (Y^X) ≅ fobj Y ^ fobj X;

  exp_in  := fun X Y => iso_from (@fobj_exp_iso X Y);
  exp_out := fun X Y => iso_to   (@fobj_exp_iso X Y);

  fmap_curry {X Y Z : C} {f : X × Y ~> Z} :
    fmap (@curry C _ X Y Z f) ≈ exp_in _ _ ∘ curry (fmap f ∘ prod_in);
  fmap_uncurry {X Y Z : C} (f : X ~> Z^Y) :
    fmap (@uncurry C _ X Y Z f) ≈ uncurry (exp_out _ _ ∘ fmap f) ∘ prod_out
}.

Arguments ClosedFunctor C {_} D {_}.

Arguments exp_in {C _ D _ _ _ _} /.
Arguments exp_out {C _ D _ _ _ _} /.

Corollary fmap_eval `{ClosedFunctor C D} {X Y : C} :
  fmap (@eval C _ X Y) ≈ uncurry (curry eval ∘ exp_out) ∘ prod_out.
Proof.
  intros.
  unfold eval.
  rewrite fmap_uncurry.
  rewrite curry_uncurry.
  rewrite fmap_id.
  rewrite id_left.
  rewrite id_right.
  reflexivity.
Qed.

Corollary exp_in_out `{ClosedFunctor C D} {X Y : C} :
  exp_in ∘ exp_out ≈ @id _ _ (fobj (Y^X)).
Proof.
  intros.
  apply iso_from_to.
  apply iso_witness.
Qed.

Corollary exp_out_in `{ClosedFunctor C D} {X Y : C} :
  exp_out ∘ exp_in ≈ @id _ _ (fobj Y ^ fobj X).
Proof.
  intros.
  apply iso_to_from.
  apply iso_witness.
Qed.

Corollary exp_in_inj `{ClosedFunctor C D}
          {X Y Z : C} (f g : fobj X ~> fobj Z ^ fobj Y) :
  exp_in ∘ f ≈ exp_in ∘ g <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_left.
    rewrite <- exp_out_in.
    rewrite <- comp_assoc.
    rewrite H2.
    rewrite comp_assoc.
    rewrite exp_out_in.
    rewrite id_left.
    reflexivity.
  subst.
  rewrite H2.
  reflexivity.
Qed.

Corollary exp_out_inj `{ClosedFunctor C D}
          {X Y Z : C} (f g : fobj X ~> fobj (Z^Y)) :
  exp_out ∘ f ≈ exp_out ∘ g <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_left.
    rewrite <- exp_in_out.
    rewrite <- comp_assoc.
    rewrite H2.
    rewrite comp_assoc.
    rewrite exp_in_out.
    rewrite id_left.
    reflexivity.
  subst.
  rewrite H2.
  reflexivity.
Qed.

Class InitialFunctor `(_ : Initial C) `(_ : Initial D) := {
  initial_category_functor :> @Functor C _ D _;

  map_zero : fobj Zero ~> Zero;

  fmap_zero {X : C} :
    @fmap C _ D _ _ Zero X zero ≈ @zero _ _ _ (fobj X) ∘ map_zero
}.

Arguments InitialFunctor C {_ _} D {_ _}.

Class CocartesianFunctor `(_ : Cocartesian C) `(_ : Cocartesian D) := {
  initial_functor :> InitialFunctor C D;

  fobj_sum_iso {X Y : C} : fobj (X + Y) ≅ fobj X + fobj Y;

  sum_in  := fun X Y => iso_from (@fobj_sum_iso X Y);
  sum_out := fun X Y => iso_to   (@fobj_sum_iso X Y);

  fmap_inl {X Y : C} : fmap (@inl C _ _ _ X Y) ≈ sum_in _ _ ∘ inl;
  fmap_inr {X Y : C} : fmap (@inr C _ _ _ X Y) ≈ sum_in _ _ ∘ inr;
  fmap_merge {X Y Z : C} (f : Y ~> X) (g : Z ~> X) :
    fmap (f ▽ g) ≈ fmap f ▽ fmap g ∘ sum_out _ _
}.

Arguments CocartesianFunctor C {_ _ _} D {_ _ _}.

Arguments sum_in {C _ _ _ D _ _ _ _ _ _} /.
Arguments sum_out {C _ _ _ D _ _ _ _ _ _} /.

Notation "sum_in[ C -> D | X ~> Y  ]" := (@sum_in C _ _ _ D _ _ _ _ X Y).
Notation "sum_out[ C -> D | X ~> Y  ]" := (@sum_out C _ _ _ D _ _ _ _ X Y).

Corollary sum_in_out `{CocartesianFunctor C D} {X Y : C} :
  sum_in ∘ sum_out ≈ @id _ _ (fobj (X + Y)).
Proof.
  intros.
  exact (iso_from_to (iso_witness (@fobj_sum_iso _ _ _ _ _ _ _ _ _ X Y))).
Qed.

Corollary sum_out_in `{CocartesianFunctor C D} {X Y : C} :
  sum_out ∘ sum_in ≈ @id _ _ (fobj X + fobj Y).
Proof.
  intros.
  exact (iso_to_from (iso_witness (@fobj_sum_iso _ _ _ _ _ _ _ _ _ X Y))).
Qed.

Corollary sum_in_surj `{CocartesianFunctor C D}
          {X Y Z : C} (f g : fobj (X + Y) ~> fobj X) :
  f ∘ sum_in ≈ g ∘ sum_in <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_right.
    rewrite <- sum_in_out.
    rewrite comp_assoc.
    rewrite H6.
    rewrite <- comp_assoc.
    rewrite sum_in_out.
    rewrite id_right.
    reflexivity.
  subst.
  rewrite H6.
  reflexivity.
Qed.

Corollary sum_out_inj `{CocartesianFunctor C D}
          {X Y Z : C} (f g : fobj Y + fobj Z ~> fobj X) :
  f ∘ sum_out ≈ g ∘ sum_out <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_right.
    rewrite <- sum_out_in.
    rewrite comp_assoc.
    rewrite H6.
    rewrite <- comp_assoc.
    rewrite sum_out_in.
    rewrite id_right.
    reflexivity.
  subst.
  rewrite H6.
  reflexivity.
Qed.

Class Constant `(_ : Terminal ob) := {
  Const : ob -> Type;
  constant {A} (x : Const A) : One ~{ob}~> A
}.

Arguments Constant ob {_}.

Global Program Instance Coq_Constant : Constant Type := {
  Const := fun A => A;
  constant := fun _ => Basics.const
}.

Class ConstantFunctor `(_ : Constant C) `(_ : Constant D) := {
  constant_closed_functor :> Functor C D;

  unmap_one : fobj One ~{D}~> One;

  map_const {A} (x : @Const C _ _ A) : @Const D _ _ (fobj A);

  fmap_constant {A : C} (x : Const A) :
    fmap (constant x) ≈ constant (map_const x) ∘ unmap_one;
}.

Arguments ConstantFunctor C {_ _} D {_ _}.

Module CCC.

Section CCC.

Variable ob : Type.
Context `{Closed ob}.
Context `{F : @ClosedFunctor Type _ ob _}.

Import EqNotations.

Definition rel `(lam : a -> b) (ccc : fobj a ~> fobj b) : Prop :=
  fmap (H:=terminal_category
          (Terminal:=cartesian_terminal
             (Cartesian:=closed_cartesian
                (Closed:=Coq_Closed)))) lam ≈ ccc.

Infix "===>" := rel (at level 99) : category_scope.

Theorem ccc_id : ∀ (a : Type), (λ x : a, x) ===> id.
Proof.
  unfold rel; intros.
  rewrite <- fmap_id.
  reflexivity.
Qed.

Tactic Notation "step" constr(x) "=>" constr(y) :=
  replace x with y by auto.

Theorem ccc_apply :
  ∀ (a b c : Type)
    (U : a -> b -> c) (U' : fobj a ~> fobj c ^ fobj b)
    (V : a -> b) (V' : fobj a ~> fobj b),
  U ===> exp_in ∘ U' ->
  V ===> V' ->
    (λ x, U x (V x)) ===> eval ∘ (U' △ V').
Proof.
  unfold rel; intros; subst.
  step (λ x, U x (V x)) => (λ x, @eval Type _ b c (U x, V x)).
  step (λ x, U x (V x)) => (λ x, @eval Type _ b c (U x, V x)).
  step (λ x, @eval Type _ b c (U x, V x))
    => (λ x, @eval Type _ b c ((U △ V) x)).
  step (λ x, @eval Type _ b c ((U △ V) x))
    => (@eval Type _ b c ∘ (U △ V)).
  rewrite fmap_comp.
  rewrite fmap_eval.
  rewrite fmap_fork.
  rewrite comp_assoc.
  rewrite <- (@comp_assoc _ _ _ _ _ _ _ prod_out).
  rewrite prod_out_in.
  rewrite id_right.
  generalize (proj2 (exp_out_inj (fmap U) (exp_in ∘ U')) H0).
  rewrite comp_assoc.
  rewrite exp_out_in.
  rewrite id_left.
  intros; subst.
  rewrite <- eval_curry.
  rewrite curry_uncurry.
  rewrite curry_eval.
  rewrite id_left.
  rewrite H1, H2.
  reflexivity.
Qed.

Theorem ccc_curry :
  ∀ (a b c : Type)
    (U : a * b -> c) (U' : fobj a × fobj b ~> fobj c),
    U ===> U' ∘ prod_out ->
      (λ x, λ y, U (x, y)) ===> exp_in ∘ curry U'.
Proof.
  unfold rel; intros; subst.
  generalize (@fmap_curry Type _ ob _ _ a b c U).
  simpl.
  unfold arrow.
  intro H1; rewrite H1; clear H1.
  pose proof (@exp_in_inj Type _ ob _ _ a b c) as H1.
  apply H1; clear H1.
  simpl in H0; rewrite H0; clear H0.
  rewrite <- comp_assoc.
  pose proof (@prod_out_in Type _ ob _ _ a b) as H1.
  simpl in H1; rewrite H1; clear H1.
  rewrite id_right.
  reflexivity.
Qed.

Theorem ccc_terminal : ∀ (a : Type),
  (λ _ : a, tt) ===> map_one ∘ @one _ _ (fobj a).
Proof.
  unfold rel; intros.
  step (λ _ : a, tt) => (@one _ _ a).
  pose proof @fmap_one.
  simpl in H0.
  rewrite H0.
  reflexivity.
Qed.

End CCC.

End CCC.

Module Expr.

Section Expr.

Inductive Obj : Type :=
  | One_   : Obj
  | Prod_  : Obj -> Obj -> Obj
  | Exp_   : Obj -> Obj -> Obj
  | Zero_  : Obj
  | Sum_   : Obj -> Obj -> Obj.

Fixpoint denote `(o : Obj) :
  ∀ `{Closed C}
    `{@Initial C _}
    `{@Cocartesian C _ _}
    `{@Bicartesian C _ _ _ _}
    `{@Distributive C _ _ _ _ _}, C := fun _ _ _ _ _ _ =>
  match o with
  | One_      => One
  | Prod_ x y => denote x × denote y
  | Exp_ x y  => denote y ^ denote x
  | Zero_     => Zero
  | Sum_ x y  => denote x + denote y
  end.

Inductive Hom : Obj -> Obj -> Type :=
  | Id      : ∀ a, Hom a a
  | Compose : ∀ a b c, Hom b c -> Hom a b -> Hom a c

  | One'    : ∀ a, Hom a One_

  | Exl     : ∀ a b, Hom (Prod_ a b) a
  | Exr     : ∀ a b, Hom (Prod_ a b) b
  | Fork    : ∀ a c d, Hom a c -> Hom a d -> Hom a (Prod_ c d)

  | Curry   : ∀ a b c, Hom (Prod_ a b) c -> Hom a (Exp_ b c)
  | Uncurry : ∀ a b c, Hom a (Exp_ b c) -> Hom (Prod_ a b) c

  | Zero'   : ∀ a, Hom Zero_ a

  | Inl     : ∀ a b, Hom a (Sum_ a b)
  | Inr     : ∀ a b, Hom b (Sum_ a b)
  | Merge   : ∀ a c d, Hom c a -> Hom d a -> Hom (Sum_ c d) a

  | ProdSum : ∀ u v a, Hom (Prod_ a (Sum_ u v)) (Sum_ (Prod_ a u) (Prod_ a v))
  | SumProd : ∀ u v a, Hom (Sum_ (Prod_ a u) (Prod_ a v)) (Prod_ a (Sum_ u v)).

Program Fixpoint interp `(c : Hom a b) :
  ∀ `{Closed C}
    `{@Initial C _}
    `{@Cocartesian C _ _}
    `{@Bicartesian C _ _ _ _}
    `{@Distributive C _ _ _ _ _}, denote a ~{C}~> denote b := fun _ _ _ _ _ _ =>
  match c with
  | Id _              => id
  | Compose _ _ _ f g => interp f ∘ interp g

  | One' _            => one

  | Exl _ _           => exl
  | Exr _ _           => exr
  | Fork _ _ _ f g    => fork (interp f) (interp g)

  | Curry _ _ _ f     => curry (interp f)
  | Uncurry _ _ _ f   => uncurry (interp f)

  | Zero' _           => zero

  | Inl _ _           => inl
  | Inr _ _           => inr
  | Merge _ _ _ f g   => merge (interp f) (interp g)

  | ProdSum _ _ _     => iso_to   prod_sum_dist
  | SumProd _ _ _     => iso_from prod_sum_dist
  end.

Global Program Instance Hom_Category : Category Obj := {
  hom := Hom;
  id := Id;
  compose := Compose;
  eqv := fun _ _ f g =>
           forall `{Closed C}
                  `{@Initial C _}
                  `{@Cocartesian C _ _}
                  `{@Bicartesian C _ _ _ _}
                  `{@Distributive C _ _ _ _ _},
             @eqv C _ _ _ (interp f) (interp g)
}.
Obligation 1.
  constructor.
  - intros ???????.
    reflexivity.
  - intros ?????????.
    symmetry.
    apply H.
  - intros ???????????.
    rewrite H, H0.
    reflexivity.
Defined.
Obligation 2.
  intros ?????? ??????.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.
Obligation 3.
  rewrite id_left.
  reflexivity.
Qed.
Obligation 4.
  rewrite id_right.
  reflexivity.
Qed.
Obligation 5.
  rewrite comp_assoc.
  reflexivity.
Qed.

Global Program Instance Hom_Terminal : Terminal Obj := {
  terminal_category := Hom_Category;
  One := One_;
  one := One'
}.
Obligation 1.
  apply one_eqv.
Qed.

Global Program Instance Hom_Cartesian : Cartesian Obj := {
  cartesian_terminal := Hom_Terminal;
  Prod := Prod_;
  fork := Fork;
  exl  := Exl;
  exr  := Exr
}.
Obligation 1.
  intros ?????? ??????.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.
Obligation 2.
  split; intros.
    split; intros.
      rewrite H.
      rewrite exl_fork.
      reflexivity.
    rewrite H.
    rewrite exr_fork.
    reflexivity.
  destruct H.
  rewrite <- H.
  rewrite <- H5.
  rewrite fork_comp.
  rewrite fork_exl_exr.
  rewrite id_left.
  reflexivity.
Qed.

Global Program Instance Hom_Closed : Closed Obj := {
  closed_cartesian := Hom_Cartesian;
  Exp := Exp_;
  curry := Curry;
  uncurry := Uncurry
}.
Obligation 1.
  intros ??? ??????.
  simpl.
  rewrite H.
  reflexivity.
Qed.
Obligation 2.
  intros ??? ??????.
  simpl.
  rewrite H.
  reflexivity.
Qed.
Obligation 3.
  apply curry_uncurry.
Qed.
Obligation 4.
  apply uncurry_curry.
Qed.
Obligation 5.
  rewrite eval_curry.
  rewrite fork_exl_exr.
  rewrite id_right.
  reflexivity.
Qed.

Global Program Instance Hom_Initial : Initial Obj := {
  Zero := Zero_;
  zero := Zero'
}.
Obligation 1.
  apply zero_eqv.
Qed.

Global Program Instance Hom_Cocartesian : Cocartesian Obj := {
  Sum  := Sum_;
  merge := Merge;
  inl  := Inl;
  inr  := Inr
}.
Obligation 1.
  intros ?????? ??????.
  simpl.
  rewrite H, H0.
  reflexivity.
Qed.
Obligation 2.
  split; intros.
    split; intros.
      rewrite H.
      rewrite inl_merge.
      reflexivity.
    rewrite H.
    rewrite inr_merge.
    reflexivity.
  destruct H.
  rewrite <- H.
  rewrite <- H5.
  rewrite merge_comp.
  rewrite merge_inl_inr.
  rewrite id_right.
  reflexivity.
Qed.

Global Program Instance Hom_Bicartesian : @Bicartesian Obj _ _ _ _.

Global Program Instance Hom_Distributive : @Distributive Obj _ _ _ _ _.
Obligation 1.
  intros.
  refine {| iso_to   := _
          ; iso_from := _ |}.
  Unshelve.
  Focus 2.
  apply Uncurry.
  constructor; simpl; intros.
Admitted.

Context `{Closed C}.
Context `{@Initial C _}.
Context `{@Cocartesian C _ _}.
Context `{@Bicartesian C _ _ _ _}.
Context `{@Distributive C _ _ _ _ _}.

Hint Rewrite (@id_left C _) : category.
Hint Rewrite (@id_right C _) : category.

Local Obligation Tactic :=
  simpl; intros; try apply iso_refl; autorewrite with category; auto.

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
  fobj_sum_iso := _
}.

(* Global Program Instance Hom_BicartesianFunctor : *)
(* Global Program Instance Hom_DistributiveFunctor : *)

End Expr.

(* Coq abstract data types are represented in CCC by identifying their
   equivalent construction. *)
Class Represented (A : Type) `{Terminal ob} `(Repr : ob) := {
  repr : A -> One ~> Repr;
  abst : One ~> Repr -> A;

  repr_abst : ∀ x, abst (repr x) = x
}.

Arguments Represented A {_ _} Repr.

Program Instance unit_Represented : Represented (unit : Type) One := {
  repr := fun _ : unit => one;
  abst := fun _ : _ => tt
}.
Obligation 1.
  destruct x.
  reflexivity.
Qed.

Program Instance bool_Represented : Represented bool (Sum One One) := {
  repr := fun b => if b
                   then inl
                   else inr;
  abst := fun h => _
}.
Obligation 1.
  pose proof (@interp _ _ h Type _ _ _ _ _).
  destruct (X tt).
    exact true.
  exact false.
Defined.
Obligation 2.
  unfold bool_Represented_obligation_1.
  destruct x; auto.
Defined.

Program Instance prod_Represented
        `{H1 : @Represented A _ Hom_Terminal C}
        `{H2 : @Represented B _ Hom_Terminal D} :
  Represented (@Datatypes.prod A B) (C × D) := {
  repr := fun p => repr (fst p) △ repr (snd p);
  abst := fun h => (abst (Represented:=H1) (exl ∘ h), abst (exr ∘ h))
}.
Obligation 1.
  simpl.
Admitted.

Definition add `(f : Sum One One ~> A) :=
  Eval simpl in f ∘ inl.
Print add.

Definition foo `(f : A × B ~> C) :=
  Eval simpl in eval ∘ (curry f ∘ exl) △ exr.
Print foo.

End Expr.
