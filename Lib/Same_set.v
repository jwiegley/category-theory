Set Warnings "-notation-overridden".


Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Finite_sets_facts.
Require Import Category.Lib.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

#[global] Program Instance Same_set_Equivalence {A} : Equivalence (@Same_set A).
Obligation 1.
  intro x.
  constructor; intros y H; exact H.
Qed.
Obligation 2.
  intros x y H.
  destruct H.
  split; trivial.
Qed.
Obligation 3.
  intros x y z H1 H2.
  destruct H1, H2.
  split; trivial.
    intros w H3.
    apply H1.
    apply H.
    exact H3.
  intros w H3.
  apply H0.
  apply H2.
  exact H3.
Qed.

#[global] Program Instance Same_set_equiv {A} :
  Proper (Same_set A ==> Same_set A ==> Basics.impl) (Same_set A).
Next Obligation.
  repeat intro.
  destruct H, H0, H1.
  split; intros z H5.
    apply H0, H1, H2, H5.
  apply H, H4, H3, H5.
Qed.

#[global] Program Instance Same_set_equiv' {A} :
  Proper (Same_set A ==> Same_set A ==> Basics.flip Basics.impl) (Same_set A).
Next Obligation.
  repeat intro.
  destruct H, H0, H1.
  split; intros z H5.
    apply H3, H1, H, H5.
  apply H2, H4, H0, H5.
Qed.

#[global] Program Instance Singleton_Same_set {A} :
  Proper (eq ==> Same_set A) (Singleton A).
Next Obligation. intros; reflexivity. Qed.

#[global] Program Instance In_Same_set {A} : Proper (Same_set A ==> Same_set A) (In A).

#[global] Program Instance In_Same_set_eq {A} : Proper (Same_set A ==> eq ==> Basics.impl) (In A).
Next Obligation.
  repeat intro.
  destruct H.
  subst.
  apply H, H1.
Qed.

#[global] Program Instance In_Same_set_eq' {A} :
  Proper (Same_set A ==> eq ==> Basics.flip Basics.impl) (In A).
Next Obligation.
  repeat intro.
  destruct H.
  subst.
  apply H2, H1.
Qed.

#[global] Program Instance In_Same_set_eq'' {A} :
  Proper (Same_set A --> eq ==> Basics.impl) (In A).
Next Obligation.
  repeat intro.
  destruct H.
  subst.
  apply H2, H1.
Qed.

#[global] Program Instance In_Same_set_eq''' {A} :
  Proper (Same_set A --> eq ==> Basics.flip Basics.impl) (In A).
Next Obligation.
  repeat intro.
  destruct H.
  subst.
  apply H, H1.
Qed.

#[global] Program Instance Union_Same_set {A} :
  Proper (Same_set A ==> Same_set A ==> Same_set A) (Union A).
Next Obligation.
  repeat intro.
  subst.
  destruct H, H0.
  split; intros z H3;
  inversion H3; subst; clear H3.
  - apply Union_introl.
    apply H, H4.
  - apply Union_intror.
    apply H0, H4.
  - apply Union_introl.
    apply H1, H4.
  - apply Union_intror.
    apply H2, H4.
Qed.

#[global] Program Instance Add_Same_set {A} :
  Proper (Same_set A ==> eq ==> Same_set A) (Add A).
Next Obligation.
  repeat intro.
  subst.
  destruct H.
  split; repeat intro.
    inversion_clear H1.
      left.
      now apply H.
    inversion_clear H2.
    now right.
  inversion_clear H1.
    left.
    now apply H0.
  inversion_clear H2.
  now right.
Qed.

#[global] Program Instance Setminus_Same_set {A} :
  Proper (Same_set A ==> Same_set A ==> Same_set A) (Setminus A).
Next Obligation.
  repeat intro.
  destruct H, H0.
  split; intros z H3;
  inversion H3; subst; clear H3.
    split.
      apply H, H4.
    unfold not; intros.
    contradiction H5.
    apply H2, H3.
  split.
    apply H1, H4.
  unfold not; intros.
  contradiction H5.
  apply H0, H3.
Qed.

#[global] Program Instance Subtract_Same_set {A} :
  Proper (Same_set A ==> eq ==> Same_set A) (Subtract A).
Next Obligation.
  repeat intro.
  subst.
  destruct H.
  split; repeat intro.
    inversion_clear H1.
    split; auto.
  inversion_clear H1.
  split; auto.
Qed.

#[global] Program Instance Included_Same_set {A} :
  Proper (Same_set A ==> Same_set A ==> Basics.impl) (Included A).
Next Obligation.
  repeat intro.
  destruct H, H0.
  now apply H0, H1, H3.
Qed.

#[global] Program Instance Included_Same_set_subrelation A :
  subrelation (@Same_set A) (@Included A).
Next Obligation.
  repeat intro.
  now apply H.
Qed.

#[global] Program Instance Finite_Proper A :
  Proper (Same_set A ==> Basics.impl) (Finite A).
Next Obligation.
  intros ????.
  eapply Finite_downward_closed; eauto with sets.
  intros ? H1.
  now apply H.
Qed.

#[global] Program Instance Finite_Proper_flip A :
  Proper (Same_set A --> Basics.flip Basics.impl) (Finite A).
Obligation 1.
  intros ????.
  eapply Finite_downward_closed; eauto with sets.
  intros ? H1.
  now apply H.
Qed.
