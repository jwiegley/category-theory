Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Functor.Product.
Require Export Category.Functor.Strong.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section ProductStrong.

Context `{C : Category}.
Context `{@Monoidal C}.
Context `{@SymmetricMonoidal C _}.
Context `{@CartesianMonoidal C _}.
Context `{F : C ⟶ C}.
Context `{G : C ⟶ C}.

Local Obligation Tactic := idtac.

(*
Program Definition Product_Strong :
  StrongFunctor F -> StrongFunctor G -> StrongFunctor (F :*: G) := fun O P => {|
  strength := _;
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation.
  simpl; intros.
  exact (strength ⨂ strength ∘ twist2 ∘ ∆X ⨂ id).
Defined.
Next Obligation.
  simpl; intros.
  unfold Product_Strong_obligation_1.
  pose proof (@strength_natural _ _ _ O _ _ g _ _ h) as X0.
  pose proof (@strength_natural _ _ _ P _ _ g _ _ h) as X1.
  pose proof (twist2_natural _ _ g _ _ g _ _ (fmap[F] h) _ _ (fmap[G] h)) as X2.
  simpl in *; normal.
  rewrite X0; clear X0.
  rewrite X1; clear X1.
  rewrite bimap_comp.
  rewrite <- comp_assoc.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (bimap (bimap _ _) _)).
  rewrite X2; clear X2.
  normal.
  srewrite diagonal_natural.
  reflexivity.
Qed.
Next Obligation.
  intros.
  simpl; intros.
  unfold Product_Strong_obligation_1.
  pose proof (@strength_id_left _ _ _ O) as X0.
  pose proof (@strength_id_left _ _ _ P) as X1.
  normal.
  rewrite X0, X1; clear X0 X1.
  unfold twist2.
  rewrite !comp_assoc.
  rewrite <- bimap_id_left_right.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (tensor_assoc⁻¹)).
  rewrite <- bimap_triangle_left.
  rewrite (comp_assoc unit_left).
  rewrite <- to_unit_left_natural.
  normal.
  rewrite <- triangle_identity.
  normal.
  rewrite unit_right_twist.
  rewrite <- bimap_triangle_left.
  rewrite to_unit_left_natural.
  rewrite inverse_triangle_identity.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (tensor_assoc⁻¹)).
  rewrite iso_from_to; normal.
  rewrite (@unit_terminal _ _ _ _ _ id); cat.
Qed.
Next Obligation.
  intros.
  simpl; intros.
  unfold Product_Strong_obligation_1.
  pose proof (@strength_assoc _ _ _ O) as X0.
  pose proof (@strength_assoc _ _ _ P) as X1.
  normal.
  rewrite X0, X1; clear X0 X1.
  rewrite !bimap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  normal.
  unfold twist2.
  normal.
  apply (iso_monic tensor_assoc).
  rewrite !comp_assoc.
  rewrite iso_to_from, id_left.
  rewrite bimap_comp.
  rewrite comp_assoc.
  rewrite <- to_tensor_assoc_natural.
  rewrite <- bimap_id_left_right.
  normal.
Admitted.
*)

End ProductStrong.
