Require Import Category.Lib.
Require Import Category.Theory.Coq.Functor.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Strong.
Require Import Category.Functor.Hom.Internal.
Require Import Category.Functor.Applicative.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Balanced.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Relevance.
Require Import Category.Structure.Monoidal.Cartesian.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Pure.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(* jww (2022-09-07): TODO
(* "Coq applicative functors" are strong lax monoidal functors in the category
   Coq. *)
Program Definition Coq_Applicative `{IsApplicative F} :
  Functor.Applicative.Applicative (C:=Coq) (F:=Coq_Functor) := {|
  applicative_is_strong := Coq_StrongFunctor (F:=F);
  applicative_is_lax_monoidal := {|
    lax_pure       := pure;
    ap_functor_nat := _;
    pure_left      := _;
    pure_right     := _;
  |};
|}.
Next Obligation.
  construct.
  - intros [x0 y0].
    exact (liftA2 pair x0 y0).
  - simpl.
    rewrite !uncomp.
    extensionality x0.
    destruct x0.
    simpl.
    unfold liftA2.
    rewrite <- !fmap_comp_x.
    destruct x, y, f; simpl in *.
    rewrite <- !ap_fmap.
    rewrite !uncomp.
    rewrite <- !ap_assoc.
    f_equal.
    clear f1.
    rewrite !ap_assoc.
    admit.
  - simpl.
    rewrite !uncomp.
    extensionality x0.
    destruct x0.
    simpl.
    admit.
Admitted.
Next Obligation.
  construct.
  - intros [x0 y0].
    exact (fmap (λ y, (tt, y)) y0).
  - intros y0.
    split.
    + exact tt.
    + exact (fmap (λ '(_, y), y) y0).
  - simpl.
    rewrite !uncomp.
    extensionality x0.
    rewrite <- fmap_comp_x.
    rewrite uncomp.
    admit.
  - simpl.
    rewrite !uncomp.
    extensionality x0.
    simplify.
    rewrite <- fmap_comp_x.
    rewrite uncomp.
    now rewrite fmap_id.
Admitted.
Next Obligation. Admitted.
Next Obligation. Admitted.
Next Obligation.
  rewrite !uncomp.
  extensionality x0.
  simplify.
  simpl.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

#[export]
Program Instance Compose_IsApplicative `{IsApplicative F} `{IsApplicative G} :
  IsApplicative (F ∘ G) := {
  ap_id          := _;
  ap_assoc       := _;
  ap_homo        := _;
  ap_interchange := _;
  ap_fmap        := _;
}.
Next Obligation. Admitted.
Next Obligation.
  spose (@comp_assoc Coq) as X; rewrite X.
  spose (@ap_homo F _ _ _ _ _ _ (ap[_] (pure[_] f))) as Y.
  setoid_rewrite Y.
  spose (@comp_assoc Coq) as Z; rewrite <- Z.
  rewrite ap_homo; cat.
Next Obligation.
  (* Discharge w *)
  rewrite <- ap_assoc.
  f_equal.
  clear w.
  (* Discharge v *)
  rewrite <- !ap_fmap.
  rewrite <- ap_assoc.
  symmetry.
  rewrite <- ap_assoc.
  f_equal.
  clear v.
  (* Discharge u *)
  applicative_laws.
  clear u.
  (* Trivial rewriting *)
  extensionality x.
  extensionality y.
  extensionality z.
  simpl.
  rewrite <- ap_assoc.
  applicative_laws.
Qed.
Next Obligation.
  extensionality x.
  applicative_laws.
Qed.
*)
