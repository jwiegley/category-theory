Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

From Equations Require Import Equations.
Require Import Equations.Type.EqDec.

Require Import Category.Lib.
Require Export Category.Theory.Functor.
From Category.Instance.Lambda Require Import Definitions Lemmas.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Infix "-->" := typ_arrow.
Infix "==>" := step.

Program Instance step_PreOrder : PreOrder step.
Next Obligation.
  repeat intro.
  induction x; auto.
Admitted.
Next Obligation.
Admitted.

Inductive multi `(R : crelation X) : crelation X :=
  | multi_refl : ∀ (x : X), multi R x x
  | multi_step : ∀ (x y z : X),
      R x y → multi R y z → multi R x z.

Program Instance multi_PreOrder `(R : crelation X) :
  PreOrder R -> PreOrder (multi R).
Next Obligation.
  repeat intro.
  constructor.
Defined.
Next Obligation.
  repeat intro.
  inversion_clear X0; auto.
  induction X3; intros; auto.
    eapply multi_step; eauto.
  intuition.
Defined.

Infix "==>*" := (multi step) (at level 100).

Import StlcNotations.

Program Definition Lambda : Category := {|
  obj     := typ;
  hom     := fun x y => ∃ Γ (t : exp), lc_exp t ∧ typing Γ t (x --> y);
  homset  := fun x y => {| equiv := fun f g =>
    ∀ x f' g', (app `1`2 f x ==>* f') -> (app `1`2 g x ==>* g') -> f' = g' |};
  id      := fun x => (nil; (abs (var_b 0); _));
  compose := fun x y z f g => (nil; (abs (app `1`2 f (app `1`2 g (var_b 0))); _))
|}.
Next Obligation.
  equivalence; simpl in *.
  - admit.
  - admit.
Admitted.
Next Obligation.
  split.
    auto with lngen.
  unshelve econstructor; intros.
    apply MetatheoryAtom.AtomSetImpl.empty.
  rewrite List.app_nil_r.
  unshelve econstructor; intros;
  auto with lngen.
Qed.
Next Obligation.
  simpl.
  split.
    admit.
  unshelve econstructor; intros.
    apply MetatheoryAtom.AtomSetImpl.empty.
  rewrite List.app_nil_r.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
