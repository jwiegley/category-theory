Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Structure.Terminal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Reserved Infix "×" (at level 40, left associativity).

Section Cartesian.

Context `{C : Category}.

Class Cartesian:= {
  Prod : ob -> ob -> ob
    where "X × Y" := (Prod X Y);

  fork {X Y Z} (f : X ~> Y) (g : X ~> Z) : X ~> Y × Z;
  exl  {X Y} : X × Y ~> X;
  exr  {X Y} : X × Y ~> Y;

  fork_respects {X Y Z} :> Proper (equiv ==> equiv ==> equiv) (@fork X Y Z);

  ump_products {X Y Z} (f : X ~> Y) (g : X ~> Z) (h : X ~> Y × Z) :
    h ≈ fork f g <<>> exl ∘ h ≈ f //\\ exr ∘ h ≈ g
}.

Infix "×" := Prod : category_scope.
Infix "△" := fork (at level 28) : category_scope.

Context `{@Cartesian}.

Definition first  {X Y Z : C} (f : X ~> Y) : X × Z ~> Y × Z :=
  (f ∘ exl) △ exr.

Definition second  {X Y Z : C} (f : X ~> Y) : Z × X ~> Z × Y :=
  exl △ (f ∘ exr).

Definition split  {X Y Z W : C} (f : X ~> Y) (g : Z ~> W) :
  X × Z ~> Y × W :=
  (f ∘ exl) △ (g ∘ exr).

Global Program Instance parametric_morphism_first {a b c : C} :
  Proper (equiv ==> equiv) (@first a b c).
Obligation 1.
  intros ?? HA.
  unfold first.
  rewrite HA.
  reflexivity.
Qed.

Global Program Instance parametric_morphism_second {a b c : C} :
  Proper (equiv ==> equiv) (@second a b c).
Obligation 1.
  intros ?? HA.
  unfold second.
  rewrite HA.
  reflexivity.
Qed.

Definition swap {X Y : C} : X × Y ~> Y × X := exr △ exl.

Corollary exl_fork {X Z W : C} (f : X ~> Z) (g : X ~> W) :
  exl ∘ f △ g ≈ f.
Proof.
  intros.
  apply (ump_products f g (f △ g)).
  reflexivity.
Qed.

Hint Rewrite @exl_fork : categories.

Corollary exr_fork {X Z W : C} (f : X ~> Z) (g : X ~> W) :
  exr ∘ f △ g ≈ g.
Proof.
  intros.
  apply (ump_products f g (f △ g)).
  reflexivity.
Qed.

Hint Rewrite @exr_fork : categories.

Corollary fork_exl_exr {X Y : C} :
  exl △ exr ≈ @id C (X × Y).
Proof.
  intros.
  symmetry.
  apply ump_products; split; cat.
Qed.

Hint Rewrite @fork_exl_exr : categories.

Corollary fork_inv {X Y Z : C} (f h : X ~> Y) (g i : X ~> Z) :
  f △ g ≈ h △ i <<>> f ≈ h //\\ g ≈ i.
Proof.
  pose proof (ump_products h i (f △ g)) as HA.
  firstorder.
  - rewrite <- H0; cat.
  - rewrite <- H3; cat.
  - rewrite H2, H3; reflexivity.
Qed.

Corollary fork_comp_hetero {X Y Z W : C}
          (f : Y ~> Z) (h : Y ~> W) (g i : X ~> Y) :
  (f ∘ g) △ (h ∘ i) ≈ split f h ∘ g △ i.
Proof.
  unfold split; intros.
  symmetry.
  apply ump_products; split;
  rewrite !comp_assoc; cat;
  rewrite <- !comp_assoc; cat.
Qed.

Corollary fork_comp {X Y Z W : C}
          (f : Y ~> Z) (h : Y ~> W) (g : X ~> Y) :
  (f ∘ g) △ (h ∘ g) ≈ f △ h ∘ g.
Proof.
  intros.
  symmetry.
  apply ump_products; split;
  rewrite !comp_assoc; cat.
Qed.

Definition swap_invol {X Y : C} :
  swap ∘ swap ≈ @id C (X × Y).
Proof.
  unfold swap.
  rewrite <- fork_comp; cat.
Qed.

Hint Rewrite @swap_invol : categories.

Definition swap_inj_l {X Y Z : C} (f g : X ~> Y × Z) :
  swap ∘ f ≈ swap ∘ g -> f ≈ g.
Proof.
  intro HA.
  rewrite <- id_left.
  rewrite <- (id_left g).
  rewrite <- swap_invol.
  rewrite <- comp_assoc.
  rewrite HA.
  rewrite comp_assoc.
  reflexivity.
Qed.

Definition swap_inj_r {X Y Z : C} (f g : X × Y ~> Z) :
  f ∘ swap ≈ g ∘ swap -> f ≈ g.
Proof.
  intro HA.
  rewrite <- id_right.
  rewrite <- (id_right g).
  rewrite <- swap_invol.
  rewrite comp_assoc.
  rewrite HA.
  rewrite <- comp_assoc.
  reflexivity.
Qed.

Theorem first_comp {X Y Z W : C} (f : Y ~> Z) (g : X ~> Y) :
  first (Z:=W) (f ∘ g) ≈ first f ∘ first g.
Proof.
  unfold first.
  rewrite <- fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

Theorem second_comp {X Y Z W : C} (f : Y ~> Z) (g : X ~> Y) :
  second (Z:=W) (f ∘ g) ≈ second f ∘ second g.
Proof.
  unfold second.
  rewrite <- fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

Theorem swap_first {X Y Z : C} (f : X ~> Y) :
  swap ∘ first (Z:=Z) f ≈ second f ∘ swap.
Proof.
  unfold first, second, swap.
  rewrite <- fork_comp; cat.
  rewrite <- fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

Theorem swap_second {X Y Z : C} (f : X ~> Y) :
  swap ∘ second f ≈ first (Z:=Z) f ∘ swap.
Proof.
  unfold first, second, swap.
  rewrite <- fork_comp; cat.
  rewrite <- fork_comp; cat.
  rewrite <- !comp_assoc; cat.
Qed.

(*
Global Program Instance parametric_morphism_prod :
  Proper
    (respectful Isomorphism
       (respectful Isomorphism Isomorphism)) Prod.
Obligation 1.
  intros ?? XA ?? XB.
  destruct XA, XB.
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
*)

Context `{@Terminal C}.

Notation "1 × X" := (Prod One X) (at level 40).
Notation "X × 1" := (Prod X One) (at level 40).

Global Program Instance prod_one_l  {X : C} :
  1 × X ≅ X := {
  to   := exr;
  from := one △ id
}.
Next Obligation. cat. Qed.
Next Obligation.
  rewrite <- fork_comp.
  rewrite <- fork_exl_exr.
  apply fork_respects; cat.
Qed.

Hint Rewrite @prod_one_l : isos.

Global Program Instance prod_one_r  {X : C} :
  X × 1 ≅ X := {
  to   := exl;
  from := id △ one
}.
Next Obligation. cat. Qed.
Next Obligation.
  rewrite <- fork_comp; cat.
  rewrite <- fork_exl_exr.
  apply fork_respects; cat.
Qed.

Hint Rewrite @prod_one_r : isos.

Global Program Instance prod_assoc  {X Y Z : C} :
  (X × Y) × Z ≅ X × (Y × Z) := {
  to   := (exl ∘ exl) △ ((exr ∘ exl) △ exr);
  from := (exl △ (exl ∘ exr)) △ (exr ∘ exr)
}.
Next Obligation.
  rewrite <- !fork_comp; cat;
  rewrite <- comp_assoc; cat;
  rewrite <- comp_assoc; cat;
  rewrite fork_comp; cat.
Qed.
Next Obligation.
  rewrite <- !fork_comp; cat;
  rewrite <- comp_assoc; cat;
  rewrite <- comp_assoc; cat;
  rewrite fork_comp; cat.
Qed.

End Cartesian.

Infix "×" := (@Prod _ _) : category_scope.
Infix "△" := (@fork _ _ _ _ _) (at level 28) : category_scope.

Notation "1 × X" := (Prod One X) (at level 40).
Notation "X × 1" := (Prod X One) (at level 40).

Hint Rewrite @exl_fork : categories.
Hint Rewrite @exr_fork : categories.
Hint Rewrite @fork_exl_exr : categories.
Hint Rewrite @swap_invol : categories.
Hint Rewrite @prod_one_l : isos.
Hint Rewrite @prod_one_r : isos.

Section CartesianFunctor.

Context `{F : C ⟶ D}.
Context `{@Cartesian C}.
Context `{@Cartesian D}.

Class CartesianFunctor := {
  fobj_prod_iso {X Y : C} : F (X × Y) ≅ F X × F Y;

  prod_in  := fun X Y => from (@fobj_prod_iso X Y);
  prod_out := fun X Y => to   (@fobj_prod_iso X Y);

  fmap_exl {X Y : C} : fmap (@exl C _ X Y) ≈ exl ∘ prod_out _ _;
  fmap_exr {X Y : C} : fmap (@exr C _ X Y) ≈ exr ∘ prod_out _ _;
  fmap_fork {X Y Z : C} (f : X ~> Y) (g : X ~> Z) :
    fmap (f △ g) ≈ prod_in _ _ ∘ fmap f △ fmap g
}.

Arguments prod_in {_ _ _} /.
Arguments prod_out {_ _ _} /.

Context `{@CartesianFunctor}.

Corollary prod_in_out (X Y : C) :
  prod_in ∘ prod_out ≈ @id _ (F (X × Y)).
Proof.
  intros.
  exact (iso_from_to fobj_prod_iso).
Qed.

Hint Rewrite @prod_in_out : functors.

Corollary prod_out_in (X Y : C) :
  prod_out ∘ prod_in ≈ @id _ (F X × F Y).
Proof.
  intros.
  exact (iso_to_from fobj_prod_iso).
Qed.

Hint Rewrite @prod_out_in : functors.

Corollary prod_in_inj {X Y Z : C} (f g : F X ~> F X × F Y) :
  prod_in ∘ f ≈ prod_in ∘ g <<>> f ≈ g.
Proof.
  split; intros Hprod.
    rewrite <- id_left.
    rewrite <- prod_out_in.
    rewrite <- comp_assoc.
    rewrite Hprod.
    rewrite comp_assoc.
    autorewrite with functors; cat.
  subst.
  rewrite Hprod.
  reflexivity.
Qed.

Corollary prod_out_inj {X Y Z : C} (f g : F X ~> F (Y × Z)) :
  prod_out ∘ f ≈ prod_out ∘ g <<>> f ≈ g.
Proof.
  split; intros Hprod.
    rewrite <- id_left.
    rewrite <- prod_in_out.
    rewrite <- comp_assoc.
    rewrite Hprod.
    rewrite comp_assoc.
    autorewrite with functors; cat.
  subst.
  rewrite Hprod.
  reflexivity.
Qed.

End CartesianFunctor.

Arguments prod_in {_ _ _ _ _ _ _ _} /.
Arguments prod_out {_ _ _ _ _ _ _ _} /.

Hint Rewrite @prod_in_out : functors.
Hint Rewrite @prod_out_in : functors.

(* This only works if 'f' was previously the result of merging two functions,
   so that the left result is only determined from the left side, and vice-
   versa. *)
(* Definition bridge `{Cartesian} `(f : X × Y ~> Z × W) : (X ~> Z) * (Y ~> W) := *)
(*   (exl ∘ f ∘ (id △ id), exr ∘ f ∘ (id △ id)). *)

Program Definition functor_prod `{C : Category} `{D : Category}
        `{@Cartesian D} (F : C ⟶ D) (G : C ⟶ D) : C ⟶ D := {|
  fobj := fun x => Prod (F x) (G x);
  fmap := fun _ _ f => (fmap f ∘ exl) △ (fmap f ∘ exr)
|}.
Next Obligation.
  intros ?? HA.
  rewrite HA; reflexivity.
Defined.
Next Obligation. cat. Qed.
Next Obligation.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc; cat.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc; cat.
Qed.

Delimit Scope functor_scope with functor.
Bind Scope functor_scope with Functor.

Notation "F × G" := (@functor_prod _ _ _ F G) : functor_scope.
