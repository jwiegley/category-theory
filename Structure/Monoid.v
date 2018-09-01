Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Closed.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section MonoidObject.

Context {C : Category}.
Context `{M : @Monoidal C}.

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

Global Program Instance Product_Monoid `(X : Monoid x) `(Y : Monoid y) :
  @MonoidObject C InternalProduct_Monoidal (x × y) := {|
  mempty  := @mempty _ _ _ X △ @mempty _ _ _ Y;
  mappend := split (@mappend _ _ _ X) (@mappend _ _ _ Y) ∘ toggle
|}.
Next Obligation.
  spose (@mempty_left _ _ _ X) as HX.
  spose (@mempty_left _ _ _ Y) as HY.
  assert ((mempty[X] △ mempty[Y] ∘ exl) △ (id[x × y] ∘ exr)
            ≈ split (mempty[X] △ mempty[Y]) id[x × y])
    by (unfork; cat).
  rewrite X0; clear X0.
  unfold toggle.
  rewrite <- !comp_assoc.
  rewrite <- fork_comp.
  rewrite !split_comp.
  rewrite exl_fork, exr_fork.
  rewrite !id_right.
  rewrite <- (id_right mempty[X]).
  rewrite <- (id_left exl).
  rewrite <- (id_right mempty[Y]).
  rewrite <- (id_left exr).
  rewrite <- !split_comp.
  rewrite split_fork.
  rewrite !comp_assoc.
  rewrite HX, HY.
  unfold split; cat.
  now rewrite fork_comp; cat.
Qed.
Next Obligation.
  spose (@mempty_right _ _ _ X) as HX.
  spose (@mempty_right _ _ _ Y) as HY.
  assert ((id[x × y] ∘ exl) △ (mempty[X] △ mempty[Y] ∘ exr)
            ≈ split id[x × y] (mempty[X] △ mempty[Y]))
    by (unfork; cat).
  rewrite X0; clear X0.
  unfold toggle.
  rewrite <- !comp_assoc.
  rewrite <- fork_comp.
  rewrite !split_comp.
  rewrite exl_fork, exr_fork.
  rewrite !id_right.
  rewrite <- (id_right mempty[X]).
  rewrite <- (id_left exl).
  rewrite <- (id_right mempty[Y]).
  rewrite <- (id_left exr).
  rewrite <- !split_comp.
  rewrite split_fork.
  rewrite !comp_assoc.
  rewrite HX, HY.
  unfold split; cat.
  now rewrite fork_comp; cat.
Qed.
Next Obligation.
  spose (@mappend_assoc _ _ _ X) as HX.
  spose (@mappend_assoc _ _ _ Y) as HY.
  assert ((split mappend[X] mappend[Y] ∘ toggle ∘ exl) △ (id[x × y] ∘ exr)
            ≈ split (split mappend[X] mappend[Y] ∘ toggle) id[x × y])
    by (unfork; cat).
  rewrite X0; clear X0.
  assert ((id[x × y] ∘ exl) △ (split mappend[X] mappend[Y] ∘ toggle ∘ exr)
            ≈ split id[x × y] (split mappend[X] mappend[Y] ∘ toggle))
    by (unfork; cat).
  rewrite X0; clear X0.
  unfold toggle.
  rewrite !split_fork.
  rewrite <- !fork_comp.
  rewrite <- !comp_assoc.
  rewrite !split_fork.
  rewrite !id_left.
  rewrite !comp_assoc.
  rewrite !exl_fork.
  rewrite !exr_fork.
  rewrite <- !comp_assoc.
  rewrite !split_comp.
  rewrite !exl_fork.
  rewrite !exr_fork.
  rewrite !id_right.
  rewrite <- (id_left (exl (x:=x) (y:=y))) at 1.
  rewrite <- (id_left (exr (x:=x) (y:=y))) at 1.
  rewrite <- !split_comp.
  rewrite !comp_assoc.
  rewrite HX, HY.
  rewrite !id_left.
  apply fork_respects; clear;
  now unfold split; unfork; cat.
Qed.

Context `{@Closed C _}.

Definition doppel {x y z : C} : x × y × z ~> x × z × (y × z) :=
  first exl △ first exr.

Global Program Instance Hom_Monoid {x} `(Y : Monoid y) :
  @MonoidObject C InternalProduct_Monoidal (y ^ x) := {
  mempty  := curry (@mempty _ _ _ Y ∘ exl);
  mappend := curry (@mappend _ _ _ Y ∘ split eval eval ∘ doppel)
}.
Next Obligation.
  spose (@mempty_left _ _ _ Y) as HY.
  remember ((curry _ ∘ exl) △ (id[y ^ x] ∘ exr)) as h.
  assert (h ≈ split (curry (mempty[Y] ∘ exl)) id[y ^ x])
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  unfold doppel.
  rewrite <- comp_assoc.
  rewrite split_fork.
  rewrite curry_comp_l.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc.
  rewrite <- !first_comp.
  rewrite exl_split.
  rewrite exr_split.
  rewrite !eval_first.
  rewrite !uncurry_comp.
  rewrite !uncurry_curry.
  rewrite <- !comp_assoc.
  rewrite !exl_first.
  rewrite <- split_fork.
  rewrite <- (id_right mempty[Y]) at 1.
  rewrite <- (id_left (uncurry id[y ^ x])).
  rewrite <- split_comp.
  rewrite !comp_assoc.
  rewrite HY; clear HY.
  rewrite <- comp_assoc.
  rewrite split_fork.
  rewrite exr_fork.
  rewrite eval_first.
  now rewrite curry_uncurry.
Qed.
Next Obligation.
  spose (@mempty_right _ _ _ Y) as HY.
  remember ((id[y ^ x] ∘ exl) △ (curry _ ∘ exr)) as h.
  assert (h ≈ split id[y ^ x] (curry (mempty[Y] ∘ exl)))
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  unfold doppel.
  rewrite <- comp_assoc.
  rewrite split_fork.
  rewrite curry_comp_l.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc.
  rewrite <- !first_comp.
  rewrite exl_split.
  rewrite exr_split.
  rewrite !eval_first.
  rewrite !uncurry_comp.
  rewrite !uncurry_curry.
  rewrite <- !comp_assoc.
  rewrite !exl_first.
  rewrite <- split_fork.
  rewrite <- (id_right mempty[Y]) at 1.
  rewrite <- (id_left (uncurry id[y ^ x])).
  rewrite <- split_comp.
  rewrite !comp_assoc.
  rewrite HY; clear HY.
  rewrite <- comp_assoc.
  rewrite split_fork.
  rewrite exl_fork.
  rewrite eval_first.
  now rewrite curry_uncurry.
Qed.
Next Obligation.
  spose (@mappend_assoc _ _ _ Y) as HY.
  remember ((curry _ ∘ exl) △ (id[y ^ x] ∘ exr)) as h.
  assert (h ≈ split (curry (mappend[Y] ∘ split eval eval ∘ doppel)) id[y ^ x])
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  remember ((id[y ^ x] ∘ exl) △ (curry _ ∘ exr)) as h.
  assert (h ≈ split id[y ^ x] (curry (mappend[Y] ∘ split eval eval ∘ doppel)))
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  unfold doppel.
  rewrite <- !comp_assoc.
  rewrite !split_fork.
  rewrite !eval_first.
  simpl.
  rewrite split_fork.
  rewrite !eval_first.
  unfold split.
  rewrite !id_left.
  rewrite !curry_comp_l.
  rewrite <- !comp_assoc.
  rewrite <- !fork_comp.
  rewrite <- !uncurry_comp.
  rewrite exl_fork.
  rewrite exr_fork.
  rewrite !uncurry_curry.
  rewrite <- (id_left (uncurry exr)).
  rewrite <- split_fork.
  rewrite comp_assoc.
  rewrite HY; clear HY.
  rewrite id_left.
  rewrite <- !comp_assoc.
  rewrite <- !fork_comp.
  rewrite <- !comp_assoc.
  rewrite !exl_fork.
  rewrite !exr_fork.
  now rewrite uncurry_curry.
Qed.

End Monoid.
