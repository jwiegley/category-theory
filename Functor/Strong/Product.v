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
  normal.
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
  pose proof (@strength_natural _ _ _ O _ _ g _ _ h) as X0.
  pose proof (@strength_natural _ _ _ P _ _ g _ _ h) as X1.
  pose proof (braid2_natural _ _ g _ _ g _ _ (fmap[F] h) _ _ (fmap[G] h)) as X2.
  simpl in *; normal.
  rewrite X0; clear X0.
  rewrite X1; clear X1.
  rewrite bimap_comp.
  rewrite <- comp_assoc.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (bimap (bimap _ _) _)).
  rewrite X2; clear X2.
  normal.
  rewrite diagonal_natural.
  reflexivity.
Qed.
Next Obligation.
Admitted.
*)

End ProductStrong.
