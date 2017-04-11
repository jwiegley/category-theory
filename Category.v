Require Import
  Coq.Unicode.Utf8
  Coq.Init.Datatypes
  Coq.Setoids.Setoid
  Coq.Logic.JMeq
  Coq.Program.Tactics
  FunctionalExtensionality.

Require Import
  Coq.Classes.Morphisms
  Coq.Classes.Equivalence
  Coq.Classes.RelationClasses.

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

Global Program Instance parametric_relation_eqv `{Category C} {a b : C} :
  Equivalence (@eqv C _ a b) := eqv_equivalence a b.

Global Program Instance parametric_morphism_compose `{Category C} {a b c : C} :
  Proper (eqv ==> eqv ==> eqv) (@compose C _ a b c) := compose_respects a b c.

Global Program Instance impl_eqv `{Category C} {a b : C} :
  Proper (eqv --> @eqv _ _ a b ++> Basics.impl) eqv.
Obligation 1.
  intros ???????.
  transitivity x; auto.
  transitivity x0; auto.
Qed.

Global Program Instance flip_impl_eqv `{Category C} (a b : C) :
  Proper (eqv --> @eqv _ _ a b ++> Basics.flip Basics.impl) eqv.
Obligation 1.
  intros ???????.
  unfold Basics.flip in H0.
  rewrite <- H0, H1.
  assumption.
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
       `(iso_to : X ~> Y) `(iso_from: Y ~> X) : Type := {
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

Global Program Instance isomorphic_equivalence `{Category ob} :
  CRelationClasses.Equivalence isomorphic.
Obligation 1.
  intros ?.
  apply Build_isomorphic with (iso_to:=id) (iso_from:=id).
  constructor; rewrite id_left; auto.
Defined.
Obligation 2.
  intros ???.
  destruct X.
  apply Build_isomorphic with (iso_to:=iso_from0) (iso_from:=iso_to0).
  destruct iso_witness0.
  constructor; auto.
Defined.
Obligation 3.
  intros ?????.
  destruct X, X0.
  apply Build_isomorphic with (iso_to:=iso_to1 ∘ iso_to0)
                              (iso_from:=iso_from0 ∘ iso_from1).
  destruct iso_witness0, iso_witness1.
  constructor.
    rewrite <- comp_assoc.
    rewrite (comp_assoc iso_to0).
    rewrite iso_to_from0.
    rewrite id_left.
    assumption.
  rewrite <- comp_assoc.
  rewrite (@comp_assoc _ _ _ _ _ _ iso_from1).
  rewrite iso_from_to1.
  rewrite id_left.
  assumption.
Defined.

Global Program Instance arrow_isomorphic `{Category C} :
  CMorphisms.Proper
    (@CMorphisms.respectful
       _ _ (Basics.flip isomorphic)
       (@CMorphisms.respectful
          _ _ isomorphic Basics.arrow)) isomorphic.
Obligation 1.
  intros ???????.
  transitivity x; auto.
  transitivity x0; auto.
Qed.

Global Program Instance flip_arrow_isomorphic `{Category C} :
  CMorphisms.Proper
    (@CMorphisms.respectful
       _ _ (Basics.flip isomorphic)
       (@CMorphisms.respectful
          _ _ isomorphic (Basics.flip Basics.arrow))) isomorphic.
Obligation 1.
  intros ???????.
  unfold Basics.flip in X.
  rewrite <- X, X0.
  assumption.
Qed.

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

Global Program Instance parametric_morphism_fork `(_ : Cartesian ob) (a b c : ob) :
  Proper (eqv ==> eqv ==> eqv) (@fork ob _ a b c) := fork_respects a b c.

Definition first `{Cartesian C} {X Y Z : C} (f : X ~> Y) : X × Z ~> Y × Z :=
  (f ∘ exl) △ exr.

Definition second `{Cartesian C} {X Y Z : C} (f : X ~> Y) : Z × X ~> Z × Y :=
  exl △ (f ∘ exr).

Global Program Instance parametric_morphism_first `{Cartesian C} {a b c : C} :
  Proper (eqv ==> eqv) (@first C _ a b c).
Obligation 1.
Admitted.

Global Program Instance parametric_morphism_second `{Cartesian C} {a b c : C} :
  Proper (eqv ==> eqv) (@second C _ a b c).
Obligation 1.
Admitted.

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

Theorem first_comp `{Cartesian C} {X Y Z W : C} (f : Y ~> Z) (g : X ~> Y) :
  first (Z:=W) (f ∘ g) ≈ first f ∘ first g.
Proof.
Admitted.

Theorem second_comp `{Cartesian C} {X Y Z W : C} (f : Y ~> Z) (g : X ~> Y) :
  second (Z:=W) (f ∘ g) ≈ second f ∘ second g.
Proof.
Admitted.

Theorem swap_first `{Cartesian C} {X Y Z : C} (f : X ~> Y) :
  swap ∘ first (Z:=Z) f ≈ second f ∘ swap.
Proof.
Admitted.

Theorem swap_second `{Cartesian C} {X Y Z : C} (f : X ~> Y) :
  swap ∘ second f ≈ first (Z:=Z) f ∘ swap.
Proof.
Admitted.

Global Program Instance parametric_morphism_prod `(_ : Cartesian ob) :
  CMorphisms.Proper
    (@CMorphisms.respectful
       _ _ isomorphic
       (@CMorphisms.respectful _ _ isomorphic isomorphic)) Prod.
Obligation 1.
  intros ??????.
  destruct X, X0.
  refine {| iso_to   := second iso_to1 ∘ first iso_to0
          ; iso_from := second iso_from1 ∘ first iso_from0 |}.
  destruct iso_witness0, iso_witness1.
  unfold first, second.
  constructor; simpl; intros.
    rewrite <- !fork_comp.
    rewrite !exl_fork.
    rewrite !fork_comp.
    rewrite <- !comp_assoc.
Admitted.

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

  univ_exponents {X Y Z} (f : X × Y ~> Z) :
    uncurry id ∘ first (curry f) ≈ f
}.

Notation "Y ^ X" := (Exp X Y) : category_scope.

Global Program Instance parametric_morphism_curry `(_ : Closed C) (a b c : C) :
  Proper (eqv ==> eqv)  (@curry C _ a b c) := curry_respects a b c.

Global Program Instance parametric_morphism_uncurry `(_ : Closed C) (a b c : C) :
  Proper (eqv ==> eqv)  (@uncurry C _ a b c) := uncurry_respects a b c.

Definition eval `{Closed C} {X Y : C} : Y^X × X ~> Y := uncurry id.

Corollary eval_curry `{Closed C}
          {X Y Z W : C} (f : Y × Z ~> W) (g : X ~> Y) (h : X ~> Z) :
  eval ∘ ((curry f ∘ g) △ h) ≈ f ∘ g △ h.
Proof.
  intros.
  pose proof (@univ_exponents C H _ _ _ f).
  rewrite <- H0 at 2; clear H0.
  rewrite <- comp_assoc.
  unfold first.
  rewrite <- fork_comp.
  rewrite exr_fork.
  rewrite <- comp_assoc.
  rewrite exl_fork.
  reflexivity.
Qed.

Corollary uncurry_first `{Closed C} {X Y Z : C} (f : X ~> Z^Y) :
  uncurry id ∘ first f ≈ uncurry f.
Proof.
  rewrite <- (curry_uncurry f).
  rewrite univ_exponents.
  rewrite curry_uncurry.
  reflexivity.
Qed.

Corollary curry_uncurry' `{Closed C} {X Y Z : C} (f : X ~> Z^Y) :
  curry (uncurry f) ≈ f.
Proof.
  (* Can this be proven in terms of the universal property? *)
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
Admitted.

Corollary curry_comp_l `{Closed C}
          {X Y Z W : C} (f : Y × Z ~> W) (g : X ~> Y) :
  curry f ∘ g ≈ curry (f ∘ first g).
Proof.
  intros.
  apply uncurry_inj.
  rewrite uncurry_curry.
  pose proof (@univ_exponents _ _ X Z W (uncurry (curry f ∘ g))).
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
Admitted.

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

Global Program Instance Coq_Initial : Initial Type := {
  Zero := False;
  zero := fun _ _ => False_rect _ _
}.
Obligation 2.
  extensionality x.
  contradiction.
Qed.

Class Cocartesian `(_ : Initial ob) := {
  Coprod : ob -> ob -> ob
    where "X + Y" := (Coprod X Y);

  merge {X Z W} (f : Z ~> X) (g : W ~> X) : Z + W ~> X;
  inl   {X Y} : X ~> X + Y;
  inr   {X Y} : Y ~> X + Y;

  merge_respects : ∀ X Z W,
    Proper (@eqv _ _ Z X ==> @eqv _ _ W X ==> @eqv _ _ (Z + W) X) merge;

  univ_coproducts {X Y Z} (f : Y ~> X) (g : Z ~> X) (h : Y + Z ~> X) :
    h ≈ merge f g <-> h ∘ inl ≈ f ∧ h ∘ inr ≈ g
}.

Arguments Cocartesian ob {_ _}.

Infix "+" := Coprod : category_scope.
Infix "▽" := merge (at level 26) : category_scope.

Global Program Instance parametric_morphism_merge
       `(H : Category ob)
       `(J : @Initial ob H)
       `(O : @Cocartesian ob H J) (a b c : ob) :
  Proper (eqv ==> eqv ==> eqv) (@merge ob H J O a b c) := merge_respects a b c.

Corollary inl_merge `{Cocartesian C} {X Z W : C} (f : Z ~> X) (g : W ~> X) :
  f ▽ g ∘ inl ≈ f.
Proof.
  intros.
  apply (proj1 (univ_coproducts f g (f ▽ g)) (reflexivity _)).
Qed.

Corollary inr_merge `{Cocartesian C} {X Z W : C} (f : Z ~> X) (g : W ~> X) :
  f ▽ g ∘ inr ≈ g.
Proof.
  intros.
  apply (proj1 (univ_coproducts f g (f ▽ g)) (reflexivity _)).
Qed.

Corollary merge_inl_inr `{Cocartesian C} {X Y : C} :
  inl ▽ inr ≈ @id C _ (X + Y).
Proof.
  intros.
  symmetry.
  apply (proj2 (univ_coproducts inl inr id)).
  rewrite !id_left.
  auto.
Qed.

Corollary merge_inv `{Cocartesian C} {X Y Z : C} (f h : Y ~> X) (g i : Z ~> X) :
  f ▽ g ≈ h ▽ i <-> f ≈ h ∧ g ≈ i.
Proof.
  pose proof (univ_coproducts h i (f ▽ g)).
  rewrite inl_merge in H2.
  rewrite inr_merge in H2.
  apply H2.
Qed.

Corollary merge_comp `{Cocartesian C}
          {X Y Z W : C} (f : Y ~> Z) (h : W ~> Z) (g : Z ~> X) :
  (g ∘ f) ▽ (g ∘ h) ≈ g ∘ f ▽ h.
Proof.
  intros.
  symmetry.
  apply (univ_coproducts (g ∘ f) (g ∘ h) (g ∘ f ▽ h)).
  rewrite <- !comp_assoc.
  rewrite inl_merge.
  rewrite inr_merge.
  auto.
Qed.

Corollary fork_merge `{Cartesian C} `{@Initial C _} `{@Cocartesian C _ _}
          {X Y Z W : C} (f : X ~> Y) (g : X ~> Z) (h : W ~> Y) (i : W ~> Z) :
  (f △ g) ▽ (h △ i) ≈ (f ▽ h) △ (g ▽ i).
Proof.
Admitted.

Notation "0 + X" := (Coprod Zero X) (at level 30).
Notation "X + 0" := (Coprod X Zero) (at level 30).

Theorem coprod_zero_l `{Cocartesian C} {X : C} :
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

Theorem coprod_zero_r `{Cocartesian C} {X : C} :
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
  Coprod := sum;
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

Class Bicartesian `(_ : Cartesian C) `{@Initial C _} `{@Cocartesian C _ _}.

Global Program Instance Coq_Bicartesian : Bicartesian Coq_Cartesian.

Class BicartesianClosed `(_ : Closed C) `{@Initial C _} `{@Cocartesian C _ _}.

Global Program Instance Coq_BicartesianClosed : BicartesianClosed Coq_Closed.

Theorem prod_coprod `{Closed C} `{@Initial C _} `{@Cocartesian C _ _} {X Y Z : C} :
  (* Products distribute over coproducts in every bicartesian closed
     category. *)
  X × (Y + Z) ≅ X × Y + X × Z.
Proof.
  intros.
  refine {| iso_to   :=
              eval ∘ swap ∘ second (curry (inl ∘ swap) ▽ curry (inr ∘ swap))
          ; iso_from := second inl ▽ second inr |}.
  constructor; simpl; intros.
    rewrite <- !comp_assoc.
    rewrite <- !merge_comp.
    rewrite <- merge_inl_inr.
    rewrite <- !second_comp.
    apply merge_inv; split.
      rewrite inl_merge.
      unfold swap, second.
      rewrite <- fork_comp.
      rewrite exr_fork.
      rewrite exl_fork.
      rewrite eval_curry.
      rewrite <- comp_assoc.
      rewrite swap_invol.
      rewrite id_right.
      reflexivity.
    rewrite inr_merge.
    unfold swap, second.
    rewrite <- fork_comp.
    rewrite exr_fork.
    rewrite exl_fork.
    rewrite eval_curry.
    rewrite <- comp_assoc.
    rewrite swap_invol.
    rewrite id_right.
    reflexivity.
  rewrite swap_second.
  rewrite <- curry_uncurry.
  rewrite (comp_assoc eval).
  rewrite univ_exponents.
  rewrite comp_assoc.
  apply swap_inj_r.
  rewrite <- comp_assoc.
  rewrite swap_invol.
  rewrite id_left.
  rewrite id_right.
  unfold second.
  rewrite fork_merge.
  rewrite <- fork_comp.
  unfold swap at 5.
  apply fork_inv; split.
    rewrite uncurry_comp_r.
    rewrite <- merge_comp.
    apply curry_inj.
    rewrite curry_uncurry.
    rewrite <- (id_right (curry exr)).
    rewrite <- merge_inl_inr.
    rewrite <- merge_comp.
    apply merge_inv; split;
    rewrite <- curry_comp;
    rewrite curry_comp_l;
    apply uncurry_inj;
    rewrite !uncurry_curry;
    apply swap_inj_r;
    rewrite <- !comp_assoc;
    rewrite swap_invol;
    rewrite id_right;
    unfold first, swap;
    rewrite comp_assoc;
    rewrite exr_fork;
    rewrite exr_fork.
      rewrite inl_merge.
      reflexivity.
    rewrite inr_merge.
    reflexivity.
  rewrite uncurry_comp_r.
  rewrite <- merge_comp.
  apply curry_inj.
  rewrite curry_uncurry.
  rewrite <- (id_right (curry exl)).
  rewrite <- merge_inl_inr.
  rewrite <- merge_comp.
  apply merge_inv; split;
  rewrite <- curry_comp;
  rewrite curry_comp_l;
  apply uncurry_inj;
  rewrite !uncurry_curry;
  apply swap_inj_r;
  rewrite <- !comp_assoc;
  rewrite swap_invol;
  rewrite id_right;
  unfold first, swap;
  rewrite comp_assoc;
  rewrite exl_fork;
  rewrite <- comp_assoc;
  rewrite exl_fork.
    rewrite inl_merge.
    reflexivity.
  rewrite inr_merge.
  reflexivity.
Qed.

Theorem exp_coprod `{BicartesianClosed C} {X Y Z : C} :
  X^(Y + Z) ≅ X^Y × X^Z.
Proof.
  intros.
  refine {| iso_to   := curry (eval ∘ second inl) △ curry (eval ∘ second inr)
          ; iso_from := curry (merge (eval ∘ first exl) (eval ∘ first exr)
                                    ∘ iso_to prod_coprod) |}.
  unfold first, second.
  constructor; simpl; intros.
Abort.

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

Global Program Instance parametric_morphism_fmap `(_ : Functor C D) (a b : C) :
  Proper (eqv ==> eqv) (@fmap C _ D _ _ a b) := fmap_respects a b.

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

  fobj_coprod_iso {X Y : C} : fobj (X + Y) ≅ fobj X + fobj Y;

  coprod_in  := fun X Y => iso_from (@fobj_coprod_iso X Y);
  coprod_out := fun X Y => iso_to   (@fobj_coprod_iso X Y);

  fmap_inl {X Y : C} : fmap (@inl C _ _ _ X Y) ≈ coprod_in _ _ ∘ inl;
  fmap_inr {X Y : C} : fmap (@inr C _ _ _ X Y) ≈ coprod_in _ _ ∘ inr;
  fmap_merge {X Y Z : C} (f : Y ~> X) (g : Z ~> X) :
    fmap (f ▽ g) ≈ fmap f ▽ fmap g ∘ coprod_out _ _
}.

Arguments CocartesianFunctor C {_ _ _} D {_ _ _}.

Arguments coprod_in {C _ _ _ D _ _ _ _ _ _} /.
Arguments coprod_out {C _ _ _ D _ _ _ _ _ _} /.

Notation "coprod_in[ C -> D | X ~> Y  ]" := (@coprod_in C _ _ _ D _ _ _ _ X Y).
Notation "coprod_out[ C -> D | X ~> Y  ]" := (@coprod_out C _ _ _ D _ _ _ _ X Y).

Corollary coprod_in_out `{CocartesianFunctor C D} {X Y : C} :
  coprod_in ∘ coprod_out ≈ @id _ _ (fobj (X + Y)).
Proof.
  intros.
  exact (iso_from_to (iso_witness (@fobj_coprod_iso _ _ _ _ _ _ _ _ _ X Y))).
Qed.

Corollary coprod_out_in `{CocartesianFunctor C D} {X Y : C} :
  coprod_out ∘ coprod_in ≈ @id _ _ (fobj X + fobj Y).
Proof.
  intros.
  exact (iso_to_from (iso_witness (@fobj_coprod_iso _ _ _ _ _ _ _ _ _ X Y))).
Qed.

Corollary coprod_in_surj `{CocartesianFunctor C D}
          {X Y Z : C} (f g : fobj (X + Y) ~> fobj X) :
  f ∘ coprod_in ≈ g ∘ coprod_in <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_right.
    rewrite <- coprod_in_out.
    rewrite comp_assoc.
    rewrite H6.
    rewrite <- comp_assoc.
    rewrite coprod_in_out.
    rewrite id_right.
    reflexivity.
  subst.
  rewrite H6.
  reflexivity.
Qed.

Corollary coprod_out_inj `{CocartesianFunctor C D}
          {X Y Z : C} (f g : fobj Y + fobj Z ~> fobj X) :
  f ∘ coprod_out ≈ g ∘ coprod_out <-> f ≈ g.
Proof.
  split; intros.
    rewrite <- id_right.
    rewrite <- coprod_out_in.
    rewrite comp_assoc.
    rewrite H6.
    rewrite <- comp_assoc.
    rewrite coprod_out_in.
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
  | One_    : Obj
  | Prod_   : Obj -> Obj -> Obj
  | Exp_    : Obj -> Obj -> Obj
  | Zero_   : Obj
  | Coprod_ : Obj -> Obj -> Obj.

Fixpoint denote `(o : Obj) : ∀ `{BicartesianClosed C}, C := fun _ _ _ _ _ =>
  match o with
  | One_        => One
  | Prod_ x y   => denote x × denote y
  | Exp_ x y    => denote y ^ denote x
  | Zero_       => Zero
  | Coprod_ x y => denote x + denote y
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

  | Inl     : ∀ a b, Hom a (Coprod_ a b)
  | Inr     : ∀ a b, Hom b (Coprod_ a b)
  | Merge   : ∀ a c d, Hom c a -> Hom d a -> Hom (Coprod_ c d) a.

Program Fixpoint interp `(c : Hom a b) :
  ∀ `{BicartesianClosed C}, denote a ~{C}~> denote b := fun _ _ _ _ _ =>
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
  end.

Global Program Instance Hom_Category : Category Obj := {
  hom := Hom;
  id := Id;
  compose := Compose;
  eqv := fun _ _ f g =>
           forall `{BicartesianClosed C},
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
  intros ?????? ?????.
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
  rewrite <- H4.
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
  Coprod  := Coprod_;
  merge := Merge;
  inl  := Inl;
  inr  := Inr
}.
Obligation 1.
  intros ?????? ?????.
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
  rewrite <- H4.
  rewrite merge_comp.
  rewrite merge_inl_inr.
  rewrite id_right.
  reflexivity.
Qed.

Global Program Instance Hom_Bicartesian : @Bicartesian Obj _ _ _.

Global Program Instance Hom_BicartesianClosed : @BicartesianClosed Obj _ _ _.

Context `{BicartesianClosed C}.

Hint Rewrite (@id_left C _) : category.
Hint Rewrite (@id_right C _) : category.

Local Obligation Tactic :=
  simpl; intros; try reflexivity; autorewrite with category; auto.

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

(* Global Program Instance Hom_BicartesianFunctor : *)

(* Global Program Instance Hom_BicartesianClosedFunctor : *)

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

Program Instance bool_Represented : Represented bool (Coprod One One) := {
  repr := fun b => if b
                   then inl
                   else inr;
  abst := fun h => _
}.
Obligation 1.
  pose proof (@interp _ _ h Type _ _ _ _).
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
  (* jww (2017-04-11): Define what it means to abstract composition. *)
Admitted.

Definition add `(f : One + One ~> A) :=
  Eval simpl in f ∘ inl.
Print add.

Definition foo `(f : A × B ~> C) :=
  Eval simpl in eval ∘ (curry f ∘ exl) △ exr.
Print foo.

End Expr.

(* Notation "f ++> g" := (f ++> g)%signature : csignature_scope. *)
(* Notation "f ==> g" := (f ==> g)%signature : csignature_scope. *)
(* Notation "f --> g" := (f --> g)%signature : csignature_scope. *)

(* Delimit Scope csignature_scope with csignature. *)

(* Delimit Scope equiv_scope with equiv. *)

(* Notation "f === g" := (f === g)%equiv : pequiv_scope. *)
(* Notation "f =~= g" := (f =~= g)%equiv : pequiv_scope. *)
(* Notation "f =/= g" := (f =/= g)%equiv : pequiv_scope. *)

(* Delimit Scope pequiv_scope with pequiv. *)
