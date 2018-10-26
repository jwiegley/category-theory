Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Adjunction.
Require Export Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Local Obligation Tactic := intros.

(* The category Adj(C,D), of adjoint functors between C and D:

    objects                (F, U, F ⊣ U)
    arrows                 (σ : F ⟹ F', τ : U ⟹ U')
    identity               identity of natural transformation
    composition            pairwise composition of natural transformations
*)

Program Definition Adj (C D : Category) : Category := {|
  obj := ∃ (F : D ⟶ C) (U : C ⟶ D), F ⊣ U;
  hom := fun x y => (`1 x ⟹ `1 y) ∧ (`1`2 x ⟹ `1`2 y);
  id  := fun x => (nat_id, nat_id);
  compose := fun _ _ _ f g => (fst f ∙ fst g, snd f ∙ snd g)
|}.
Next Obligation. apply prod_setoid. Defined.
Next Obligation.
  proper; simpl in *; simplify;
  rewrites; reflexivity.
Qed.
Next Obligation. split; simpl; cat. Qed.
Next Obligation. split; simpl; cat. Qed.
Next Obligation. split; simpl; cat. Qed.
Next Obligation. split; simpl; cat. Qed.
