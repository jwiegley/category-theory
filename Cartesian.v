Require Import Lib.
Require Export Iso.
Require Export Terminal.

Generalizable All Variables.
Set Primitive Projection.
Set Universe Polymorphism.

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

Program Instance parametric_morphism_fork `(_ : Cartesian ob) (a b c : ob) :
  Proper (eqv ==> eqv ==> eqv) (@fork ob _ a b c) := fork_respects a b c.

Definition first `{Cartesian C} {X Y Z : C} (f : X ~> Y) : X × Z ~> Y × Z :=
  (f ∘ exl) △ exr.

Definition second `{Cartesian C} {X Y Z : C} (f : X ~> Y) : Z × X ~> Z × Y :=
  exl △ (f ∘ exr).

Definition split `{Cartesian C} {X Y Z W : C} (f : X ~> Y) (g : Z ~> W) :
  X × Z ~> Y × W :=
  (f ∘ exl) △ (g ∘ exr).

Program Instance parametric_morphism_first `{Cartesian C} {a b c : C} :
  Proper (eqv ==> eqv) (@first C _ a b c).
Obligation 1.
  intros ???.
  unfold first.
  rewrite H0.
  reflexivity.
Qed.

Program Instance parametric_morphism_second `{Cartesian C} {a b c : C} :
  Proper (eqv ==> eqv) (@second C _ a b c).
Obligation 1.
  intros ???.
  unfold second.
  rewrite H0.
  reflexivity.
Qed.

Definition swap `{Cartesian C} {X Y : C} : X × Y ~> Y × X := exr △ exl.

Corollary exl_fork `{Cartesian C} {X Z W : C} (f : X ~> Z) (g : X ~> W) :
  exl ∘ f △ g ≈ f.
Proof.
  intros.
  apply (proj1 (univ_products f g (f △ g))).
  reflexivity.
Qed.

Hint Rewrite @exl_fork : categories.

Corollary exr_fork `{Cartesian C} {X Z W : C} (f : X ~> Z) (g : X ~> W) :
  exr ∘ f △ g ≈ g.
Proof.
  intros.
  apply (proj1 (univ_products f g (f △ g))).
  reflexivity.
Qed.

Hint Rewrite @exr_fork : categories.

Corollary fork_exl_exr `{Cartesian C} {X Y : C} :
  exl △ exr ≈ @id C _ (X × Y).
Proof.
  intros.
  symmetry.
  apply univ_products; cat.
Qed.

Hint Rewrite @fork_exl_exr : categories.

Corollary fork_inv `{Cartesian C} {X Y Z : C} (f h : X ~> Y) (g i : X ~> Z) :
  f △ g ≈ h △ i <-> f ≈ h ∧ g ≈ i.
Proof.
  generalize (univ_products h i (f △ g)); cat.
Qed.

Corollary fork_comp_hetero `{Cartesian C} {X Y Z W : C}
          (f : Y ~> Z) (h : Y ~> W) (g i : X ~> Y) :
  (f ∘ g) △ (h ∘ i) ≈ split f h ∘ g △ i.
Proof.
  unfold split; intros.
  symmetry.
  apply univ_products.
  rewrite !comp_assoc; cat.
  rewrite <- !comp_assoc; cat.
Qed.

Corollary fork_comp `{Cartesian C} {X Y Z W : C}
          (f : Y ~> Z) (h : Y ~> W) (g : X ~> Y) :
  (f ∘ g) △ (h ∘ g) ≈ f △ h ∘ g.
Proof.
  intros.
  symmetry.
  apply univ_products.
  rewrite !comp_assoc; cat.
Qed.

Definition swap_invol `{Cartesian C} {X Y : C} :
  swap ∘ swap ≈ @id _ _ (X × Y).
Proof.
  unfold swap.
  rewrite <- fork_comp; cat.
Qed.

Hint Rewrite @swap_invol : categories.

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
  unfold first.
  rewrite <- fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

Theorem second_comp `{Cartesian C} {X Y Z W : C} (f : Y ~> Z) (g : X ~> Y) :
  second (Z:=W) (f ∘ g) ≈ second f ∘ second g.
Proof.
  unfold second.
  rewrite <- fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

Theorem swap_first `{Cartesian C} {X Y Z : C} (f : X ~> Y) :
  swap ∘ first (Z:=Z) f ≈ second f ∘ swap.
Proof.
  unfold first, second, swap.
  rewrite <- fork_comp; cat.
  rewrite <- fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

Theorem swap_second `{Cartesian C} {X Y Z : C} (f : X ~> Y) :
  swap ∘ second f ≈ first (Z:=Z) f ∘ swap.
Proof.
  unfold first, second, swap.
  rewrite <- fork_comp; cat.
  rewrite <- fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

Program Instance parametric_morphism_prod `(_ : Cartesian ob) :
  CMorphisms.Proper
    (CMorphisms.respectful isomorphic
       (CMorphisms.respectful isomorphic isomorphic)) Prod.
Obligation 1.
  intros ??????.
  destruct X, X0.
  refine {| iso_to   := second iso_to0 ∘ first iso_to
          ; iso_from := second iso_from0 ∘ first iso_from |}.
  destruct iso_witness, iso_witness0.
  unfold first, second.
  constructor; simpl; intros;
  rewrite <- !fork_comp; cat;
  rewrite <- !comp_assoc; cat;
  rewrite <- !fork_comp; cat;
  rewrite !comp_assoc.
    rewrite iso_to_from.
    rewrite iso_to_from0; cat.
  rewrite iso_from_to.
  rewrite iso_from_to0; cat.
Qed.

Notation "1 × X" := (Prod One X) (at level 40).
Notation "X × 1" := (Prod X One) (at level 40).

Program Instance prod_one_l `{Cartesian C} {X : C} :
  1 × X ≅ X := {
  iso_to   := exr;
  iso_from := one △ id
}.
Obligation 1.
  constructor; simpl; intros; cat.
  rewrite <- fork_comp; cat.
  rewrite <- fork_exl_exr.
  apply fork_respects; cat.
Qed.

Hint Rewrite @prod_one_l : isos.

Program Instance prod_one_r `{Cartesian C} {X : C} :
  X × 1 ≅ X := {
  iso_to   := exl;
  iso_from := id △ one
}.
Obligation 1.
  constructor; simpl; intros; cat.
  rewrite <- fork_comp; cat.
  rewrite <- fork_exl_exr.
  apply fork_respects; cat.
Qed.

Hint Rewrite @prod_one_r : isos.

Program Instance prod_assoc `{Cartesian C} {X Y Z : C} :
  (X × Y) × Z ≅ X × (Y × Z) := {
  iso_to   := (exl ∘ exl) △ ((exr ∘ exl) △ exr);
  iso_from := (exl △ (exl ∘ exr)) △ (exr ∘ exr)
}.
Obligation 1.
  constructor; simpl; intros;
  rewrite <- !fork_comp; cat;
  rewrite <- comp_assoc; cat;
  rewrite <- comp_assoc; cat;
  rewrite fork_comp; cat.
Qed.

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

Hint Rewrite @prod_in_out : functors.

Corollary prod_out_in `{CartesianFunctor C D} (X Y : C) :
  prod_out ∘ prod_in ≈ @id _ _ (fobj X × fobj Y).
Proof.
  intros.
  exact (iso_to_from (iso_witness (@fobj_prod_iso _ _ _ _ _ X Y))).
Qed.

Hint Rewrite @prod_out_in : functors.

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
    autorewrite with functors; cat.
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
    autorewrite with functors; cat.
  subst.
  rewrite H2.
  reflexivity.
Qed.
