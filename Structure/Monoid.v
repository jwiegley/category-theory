Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Internal.Product.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section MonoidObject.

Context {C : Category}.
Context `{@Monoidal C}.

Class MonoidObject (mon : C) := {
  mempty  : I ~> mon;
  mappend : mon ⨂ mon ~> mon;

  (* I ⨂ mon ≈ mon, mon ⨂ I ≈ mon *)
  mempty_left : mappend ∘ bimap mempty id ≈ to (@unit_left C _ mon);
  mempty_right : mappend ∘ bimap id mempty ≈ to (@unit_right C _ mon);

  (* (mon ⨂ mon) ⨂ mon ≈ mon ⨂ (mon ⨂ mon) *)
  mappend_assoc :
    mappend ∘ bimap mappend id ≈ mappend ∘ bimap id mappend ∘ to tensor_assoc
}.

Context (mon : C).
Context `{@MonoidObject mon}.

Lemma mappend_assoc_sym :
  mappend ∘ bimap id mappend ≈ mappend ∘ bimap mappend id ∘ (tensor_assoc ⁻¹).
Proof.
  rewrite mappend_assoc.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  cat.
Qed.

End MonoidObject.

Notation "mempty[ M ]" := (@mempty _ _ _ M)
  (at level 9, format "mempty[ M ]") : category_scope.
Notation "mappend[ M ]" := (@mappend _ _ _ M)
  (at level 9, format "mappend[ M ]") : category_scope.

Section Monoid.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

(** A Monoid object in C defined in terms of the internal product is a monoid
    in the usual sense (i.e., mappend reducing two objects to one). *)
Definition Monoid := @MonoidObject C InternalProduct_Monoidal.

Program Instance Product_Monoid `(X : Monoid x) `(Y : Monoid y) :
  @MonoidObject C InternalProduct_Monoidal (x × y) := {|
  mempty  := mempty (MonoidObject:=X) △ mempty (MonoidObject:=Y);
  mappend := split (@mappend _ _ _ X) (@mappend _ _ _ Y) ∘ toggle
|}.
Next Obligation.
  spose (@mempty_left _ _ _ X) as HX.
  spose (@mempty_left _ _ _ Y) as HY.
  rewrite <- (split_fork mempty[X]) in HX.
  rewrite <- (split_fork mempty[Y]) in HY.
  rewrite fork_exl_exr, id_right in HX.
  rewrite fork_exl_exr, id_right in HY.
  simpl.
  unfold toggle.
  rewrite <- fork_comp.
  rewrite split_fork.
  rewrite <- fork_comp.
  unfork.
  rewrite <- (split_fork mempty[X]).
  rewrite fork_exl_exr, id_right.
  rewrite <- (split_fork mempty[Y]).
  rewrite fork_exl_exr, id_right.
  unfold split in *.
  rewrite second_id, id_right in HX.
  rewrite second_id, id_right in HY.
  rewrite !comp_assoc.
  rewrite HX, HY.
  unfold second.
  rewrite !exr_fork.
  rewrite fork_comp.
  rewrite fork_exl_exr, id_left.
  reflexivity.
Qed.
Next Obligation.
  spose (@mempty_right _ _ _ X) as HX.
  spose (@mempty_right _ _ _ Y) as HY.
  rewrite <- (split_fork _ mempty[X]) in HX.
  rewrite <- (split_fork _ mempty[Y]) in HY.
  rewrite fork_exl_exr, id_right in HX.
  rewrite fork_exl_exr, id_right in HY.
  simpl.
  unfold toggle.
  rewrite <- fork_comp.
  rewrite split_fork.
  rewrite <- fork_comp.
  unfork.
  rewrite <- (split_fork _ mempty[X]).
  rewrite fork_exl_exr, id_right.
  rewrite <- (split_fork _ mempty[Y]).
  rewrite fork_exl_exr, id_right.
  unfold split in *.
  rewrite first_id, id_left in HX.
  rewrite first_id, id_left in HY.
  rewrite !first_second.
  rewrite !comp_assoc.
  rewrite HX, HY.
  unfold first.
  rewrite !exl_fork.
  rewrite fork_comp.
  rewrite fork_exl_exr, id_left.
  reflexivity.
Qed.
Next Obligation.
  spose (@mappend_assoc _ _ _ X) as HX.
  spose (@mappend_assoc _ _ _ Y) as HY.
  rewrite <- (split_fork mappend[X]) in HX.
  rewrite <- (split_fork mappend[Y]) in HY.
  rewrite fork_exl_exr, id_right in HX.
  rewrite fork_exl_exr, id_right in HY.
  rewrite <- (split_fork _ mappend[X]) in HX.
  rewrite <- (split_fork _ mappend[Y]) in HY.
  rewrite fork_exl_exr, id_right in HX.
  rewrite fork_exl_exr, id_right in HY.
  rewrite <- !comp_assoc in HX.
  rewrite split_fork, id_left in HX.
  rewrite <- !comp_assoc in HY.
  rewrite split_fork, id_left in HY.
  unfold split at 1 in HX.
  rewrite second_id, id_right in HX.
  unfold split at 1 in HY.
  rewrite second_id, id_right in HY.
  simpl.
  unfold toggle.
  rewrite !split_fork.
  rewrite <- !(split_fork _ _ exl exr).
  rewrite !fork_exl_exr, !id_right.
  rewrite <- !comp_assoc.
  rewrite !split_fork.
  rewrite <- fork_comp.
  unfold split.
  rewrite !second_id, !id_right.
  rewrite id_left.
  rewrite !first_second.
  rewrite <- !comp_assoc.
  rewrite <- !first_comp.
  rewrite exl_fork.
  rewrite <- first_second.
  rewrite first_comp.
  rewrite !comp_assoc.
  rewrite HX; clear HX.
  rewrite exr_fork.
  rewrite <- !comp_assoc.
  rewrite <- !first_second.
  rewrite !first_comp.
  rewrite !comp_assoc.
  rewrite HY; clear HY.
  rewrite <- !comp_assoc.
  rewrite <- !split_fork.
  comp_left.
  rewrite !comp_assoc.
  rewrite !split_comp.
  rewrite !split_fork.
  rewrite <- !comp_assoc.
  rewrite <- !fork_comp.
  rewrite <- !comp_assoc.
  rewrite <- !fork_comp.
  unfold split.
  rewrite <- !comp_assoc.
  rewrite !second_fork.
  rewrite !first_fork.
  rewrite !second_fork.
  rewrite !first_fork.
  rewrite !comp_assoc.
  rewrite !exl_fork, !exr_fork.
  rewrite <- !comp_assoc.
  rewrite !second_fork.
  rewrite !first_fork.
  rewrite !comp_assoc.
  apply fork_respects; apply fork_respects;
  unfold first, second;
  now unfork.
Qed.

End Monoid.
