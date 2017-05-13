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

Definition braid2 {X Y Z W} : (X ⨂ Y) ⨂ (Z ⨂ W) ~{ C }~> (X ⨂ Z) ⨂ (Y ⨂ W) :=
  tensor_assoc⁻¹
    ∘ bimap id (tensor_assoc ∘ bimap braid id ∘ tensor_assoc⁻¹)
    ∘ tensor_assoc.

Lemma braid2_natural : natural (@braid2).
Proof.
  simpl; intros.
  rewrite <- (comp_assoc braid2).
  rewrite <- !bimap_comp.
  rewrite !id_left, !id_right.
  rewrite <- !bimap_comp.
  rewrite !id_left, !id_right.
  rewrite <- (comp_assoc braid2).
  rewrite <- !bimap_comp.
  rewrite !id_left, !id_right.
  rewrite <- (comp_assoc braid2).
  rewrite <- !bimap_comp.
  rewrite !id_left, !id_right.
  unfold braid2.
  pose proof (@pentagon_identity _ _).
  pose proof (@hexagon_identity).
Admitted.

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
  exact (bimap strength strength ∘ braid2 ∘ bimap diagonal id).
Defined.
Next Obligation.
  simpl; intros.
  unfold Product_Strong_obligation_1.
  rewrite <- bimap_comp.
  rewrite <- !fmap_comp.
  rewrite <- bimap_comp.
  rewrite id_left, id_right.
  rewrite <- !(comp_assoc _ (bimap _ _) (bimap _ _)).
  rewrite <- !bimap_comp.
  rewrite !id_left, !id_right.
  rewrite !comp_assoc.
  rewrite <- !bimap_comp.
  pose proof (@strength_natural _ _ _ O _ _ g _ _ h); simpl in X0.
  rewrite <- !fmap_comp in X0.
  rewrite <- bimap_comp in X0.
  rewrite <- comp_assoc in X0.
  rewrite <- bimap_comp in X0.
  rewrite !id_left, !id_right in X0.
  rewrite X0; clear X0.
  pose proof (@strength_natural _ _ _ P _ _ g _ _ h); simpl in X0.
  rewrite <- !fmap_comp in X0.
  rewrite <- bimap_comp in X0.
  rewrite <- comp_assoc in X0.
  rewrite <- bimap_comp in X0.
  rewrite !id_left, !id_right in X0.
  rewrite X0; clear X0.
  rewrite bimap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  enough (bimap[(⨂)] (bimap[(⨂)] g (fmap[F] h)) (bimap[(⨂)] g (fmap[G] h)) ∘ braid2
            ≈ braid2 ∘ bimap[(⨂)] (bimap[(⨂)] g g) (bimap[(⨂)] (fmap[F] h) (fmap[G] h))).
    rewrite X0.
    rewrite <- !comp_assoc.
    apply compose_respects; [reflexivity|].
    rewrite <- !bimap_comp.
    rewrite !id_left, !id_right.
    rewrite diagonal_natural.
    reflexivity.
  pose proof (braid2_natural
                _ _ g _ _ g _ _ (fmap[F] h) _ _ (fmap[G] h)); simpl in X0.
  rewrite <- !bimap_comp in X0.
  rewrite <- !comp_assoc in X0.
  rewrite <- !bimap_comp in X0.
  rewrite !id_left, !id_right in X0.
  rewrite <- !bimap_comp in X0.
  rewrite !id_left, !id_right in X0.
  apply X0.
Qed.
Next Obligation.
Admitted.
*)

End ProductStrong.
