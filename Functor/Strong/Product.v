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

(* jww (2017-05-12): TODO
Program Definition Product_Strong :
  StrongFunctor F -> StrongFunctor G -> StrongFunctor (F :*: G) := fun O P => {|
  strength := _;
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation.
  simpl; intros O P x y.
  exact
    ((bimap strength strength
        : (x ⨂ F y) ⨂ (x ⨂ G y) ~> F (x ⨂ y) ⨂ G (x ⨂ y)) ∘
     (tensor_assoc
        : ((x ⨂ F y) ⨂ x) ⨂ G y ~> _) ∘
     (bimap sym_swap id
        : (x ⨂ (x ⨂ F y)) ⨂ G y ~> _) ∘
     (bimap tensor_assoc id
        : ((x ⨂ x) ⨂ F y) ⨂ G y ~> _) ∘
     (tensor_assoc⁻¹
        : (x ⨂ x) ⨂ (F y ⨂ G y) ~> _) ∘
     (bimap diagonal id
        : x ⨂ (F y ⨂ G y) ~> _)).
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
  (* rewrite <- !bimap_comp. *)
  (* rewrite id_left. *)
  (* rewrite !comp_assoc. *)
Admitted.
Next Obligation.
Admitted.
*)

End ProductStrong.
