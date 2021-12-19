Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Functor.Bifunctor.
Require Export Category.Structure.Monoidal.
Require Export Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Cartesian.Closed.

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
            ≈ split (mempty[X] △ mempty[Y]) id[x × y]).
  { symmetry.
    unfold split.
    fork_simpl; reflexivity.
  }
  etransitivity.
  { apply compose_respects; [reflexivity|].
    eapply X0.
  }
  clear X0.
  transitivity (split mappend[X] mappend[Y] ∘ split mempty[X] exl △ split mempty[Y] exr).
  { unfold toggle.
    rewrite comp_assoc_sym.
    apply compose_respects; [reflexivity|].
    fork_simpl. apply fork_respects.
    - rewrite split_comp.
      apply split_respects.
      + apply exl_fork.
      + apply id_right.
    - rewrite split_comp.
      apply split_respects.
      + apply exr_fork.
      + apply id_right.
  }
  transitivity (split mappend[X] mappend[Y]
  ∘ split (mempty[X] ∘ id{C}) (id{C} ∘ exl) △ split (mempty[Y] ∘ id{C}) (id{C} ∘ exr)).
  { apply compose_respects; [reflexivity|].
    apply fork_respects; apply split_respects;
      try rewrite id_right; try rewrite id_left;
      reflexivity.
  }
  transitivity ((mappend[X] ∘ split mempty[X] id{C} ∘ split id{C} exl)
  △ (mappend[Y] ∘ split mempty[Y] id{C} ∘ split id{C} exr)).
  { etransitivity.
    { apply compose_respects; [reflexivity|].
      rewrite <- split_comp.
      reflexivity.
    }
    rewrite split_fork.
    apply fork_respects.
    - apply comp_assoc.
    - etransitivity.
      { apply compose_respects; [reflexivity|].
        rewrite <- split_comp.
        reflexivity.
      }
      apply comp_assoc.
  }
  etransitivity.
  { apply fork_respects; apply compose_respects;
      try eassumption; reflexivity.
  }
  clear HX HY.
  unfold split.
  etransitivity.
  { apply fork_respects; fork_simpl; reflexivity. }
  now rewrite fork_comp; cat.
Qed.
Next Obligation.
  spose (@mempty_right _ _ _ X) as HX.
  spose (@mempty_right _ _ _ Y) as HY.
  assert ((id[x × y] ∘ exl) △ (mempty[X] △ mempty[Y] ∘ exr)
            ≈ split id[x × y] (mempty[X] △ mempty[Y])).
  { symmetry.
    unfold split.
    fork_simpl; reflexivity.
  }
  etransitivity.
  { apply compose_respects; [reflexivity|].
    eapply X0.
  }
  clear X0.
  unfold toggle.
  transitivity (split mappend[X] mappend[Y] ∘ split exl mempty[X] △ split exr mempty[Y]).
  { rewrite comp_assoc_sym.
    apply compose_respects; [reflexivity|].
    repeat fork_simpl;
      rewrite split_comp;
      apply split_respects; fork_simpl; reflexivity.
  }
  transitivity (split mappend[X] mappend[Y]
                      ∘ split (id{C} ∘ exl) (mempty[X] ∘ id{C}) △ split (id{C} ∘ exr) (mempty[Y] ∘ id{C})).
  { apply compose_respects; [reflexivity|].
    fork_simpl; apply split_respects; cat.
  }
  etransitivity.
  { apply compose_respects; [reflexivity|].
    rewrite <- !split_comp.
    reflexivity.
  }
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
            ≈ split (split mappend[X] mappend[Y] ∘ toggle) id[x × y]).
  { unfold toggle, split.
    fork_simpl.
    2: reflexivity.
    fork_simpl.
    fork_simpl.
    fork_simpl.
    - reflexivity.
    - reflexivity.
  }
  rewrite X0; clear X0.
  assert ((id[x × y] ∘ exl) △ (split mappend[X] mappend[Y] ∘ toggle ∘ exr)
            ≈ split id[x × y] (split mappend[X] mappend[Y] ∘ toggle)).
  { unfold toggle, split.
    fork_simpl.
    1: reflexivity.
    fork_simpl.
    fork_simpl.
    fork_simpl.
    - reflexivity.
    - reflexivity.
  }
  rewrite X0; clear X0.
  unfold toggle.
  etransitivity.
  { apply compose_respects.
    - apply split_fork.
    - apply split_respects; [|reflexivity].
      apply split_fork.
  }
  etransitivity.
  2: {
    symmetry.
    apply compose_respects.
    2: reflexivity.
    apply compose_respects.
    - apply split_fork.
    - apply split_respects; [reflexivity|].
      apply split_fork.
  }
  rewrite <- !fork_comp.
  apply fork_respects.
  - rewrite <- !comp_assoc.
    etransitivity.
    2: {
      symmetry.
      apply compose_respects; [reflexivity|].
      etransitivity.
      { apply compose_respects; [reflexivity|].
        rewrite split_fork.
        rewrite id_left.
        reflexivity.
      }
      rewrite split_fork.
      apply fork_respects.
      + apply comp_assoc.
      + rewrite comp_assoc.
        rewrite exl_fork.
        reflexivity.
    }
    etransitivity.
    { apply compose_respects; [reflexivity|].
      rewrite split_comp.
      apply split_respects.
      - apply exl_fork.
      - apply id_right.
    }
    rewrite <- (id_left (exl (x:=x) (y:=y))) at 1.
    rewrite <- split_comp.
    rewrite !comp_assoc.
    rewrite HX.
    rewrite id_left.
    clear.
    unfold split.
    etransitivity.
    { fork_simpl. fork_simpl.
      apply compose_respects; [reflexivity|].
      fork_simpl. fork_simpl.
      apply fork_respects.
      - rewrite comp_assoc.
        etransitivity.
        { apply compose_respects; [| reflexivity].
          fork_simpl.
          reflexivity.
        }
        fork_simpl.
        etransitivity.
        { apply compose_respects; [reflexivity|].
          fork_simpl.
          reflexivity.
        }
        rewrite comp_assoc.
        apply compose_respects; [|reflexivity].
        fork_simpl.
        reflexivity.
      - fork_simpl.
        apply compose_respects; [reflexivity|].
        rewrite comp_assoc.
        etransitivity.
        { apply compose_respects.
          2: reflexivity.
          fork_simpl.
          reflexivity.
        }
        fork_simpl.
        apply fork_respects.
        + fork_simpl.
          etransitivity.
          { apply compose_respects; [reflexivity|].
            fork_simpl.
            reflexivity.
          }
          rewrite comp_assoc.
          apply compose_respects; [|reflexivity].
          fork_simpl.
          reflexivity.
        + fork_simpl.
          reflexivity.
    }
    apply compose_respects; [reflexivity|].
    apply fork_respects; [reflexivity|].
    rewrite <- comp_assoc.
    apply compose_respects; [reflexivity|].
    rewrite <- comp_assoc.
    unfork.
  - rewrite <- !comp_assoc.
    etransitivity.
    2: {
      symmetry.
      apply compose_respects; [reflexivity|].
      etransitivity.
      { apply compose_respects; [reflexivity|].
        rewrite split_fork.
        rewrite id_left.
        reflexivity.
      }
      rewrite split_fork.
      apply fork_respects.
      + apply comp_assoc.
      + rewrite comp_assoc.
        rewrite exr_fork.
        reflexivity.
    }
    etransitivity.
    { apply compose_respects; [reflexivity|].
      rewrite split_comp.
      apply split_respects.
      - apply exr_fork.
      - apply id_right.
    }
    rewrite <- (id_left (exr (x:=x) (y:=y))) at 1.
    rewrite <- split_comp.
    rewrite !comp_assoc.
    rewrite HY.
    rewrite id_left.
    clear.
    unfold split.
    etransitivity.
    { fork_simpl. fork_simpl.
      apply compose_respects; [reflexivity|].
      fork_simpl. fork_simpl.
      apply fork_respects.
      - rewrite comp_assoc.
        etransitivity.
        { apply compose_respects; [| reflexivity].
          fork_simpl.
          reflexivity.
        }
        fork_simpl.
        etransitivity.
        { apply compose_respects; [reflexivity|].
          fork_simpl.
          reflexivity.
        }
        rewrite comp_assoc.
        apply compose_respects; [|reflexivity].
        fork_simpl.
        reflexivity.
      - fork_simpl.
        apply compose_respects; [reflexivity|].
        rewrite comp_assoc.
        etransitivity.
        { apply compose_respects.
          2: reflexivity.
          fork_simpl.
          reflexivity.
        }
        fork_simpl.
        apply fork_respects.
        + fork_simpl.
          etransitivity.
          { apply compose_respects; [reflexivity|].
            fork_simpl.
            reflexivity.
          }
          rewrite comp_assoc.
          apply compose_respects; [|reflexivity].
          fork_simpl.
          reflexivity.
        + fork_simpl.
          reflexivity.
    }
    apply compose_respects; [reflexivity|].
    apply fork_respects; [reflexivity|].
    rewrite <- comp_assoc.
    apply compose_respects; [reflexivity|].
    rewrite <- comp_assoc.
    unfork.
Qed.

Context `{@Closed C _}.

Definition doppel {x y z : C} : x × y × z ~> x × z × (y × z) :=
  first exl △ first exr.

Lemma uncurry_exl_fork_exr {x y : C} :
  uncurry exl △ uncurry exr ≈ split eval eval ∘ @doppel (y ^ x) (y ^ x) x.
Proof.
  unfold doppel.
  rewrite split_fork.
  now rewrite !eval_first.
Qed.

Global Program Instance Hom_Monoid {x} `(Y : Monoid y) :
  @MonoidObject C InternalProduct_Monoidal (y ^ x) := {
  mempty  := curry (@mempty _ _ _ Y ∘ exl);
  mappend := curry (@mappend _ _ _ Y ∘ uncurry exl △ uncurry exr)
}.
Next Obligation.
  spose (@mempty_left _ _ _ Y) as HY.
  remember ((curry _ ∘ exl) △ (id[y ^ x] ∘ exr)) as h.
  assert (h ≈ split (curry (mempty[Y] ∘ exl)) id[y ^ x]).
  { rewrite Heqh.
    reflexivity.
  }
  rewrite X; clear X Heqh h.
  rewrite uncurry_exl_fork_exr.
  unfold doppel.
  rewrite split_fork.
  rewrite curry_comp_l.
  etransitivity.
  { apply curry_respects.
    rewrite comp_assoc_sym.
    apply compose_respects; [reflexivity|].
    rewrite <- fork_comp.
    rewrite <- !comp_assoc.
    rewrite <- !first_comp.
    rewrite exl_split.
    rewrite exr_split.
    rewrite !eval_first.
    rewrite !uncurry_comp.
    rewrite !uncurry_curry.
    reflexivity.
  }
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
  assert (h ≈ split id[y ^ x] (curry (mempty[Y] ∘ exl))).
  { rewrite Heqh.
    reflexivity.
  }
  rewrite X; clear X Heqh h.
  rewrite uncurry_exl_fork_exr.
  unfold doppel.
  rewrite split_fork.
  rewrite curry_comp_l.
  etransitivity.
  { apply curry_respects.
    rewrite comp_assoc_sym.
    apply compose_respects; [reflexivity|].
    rewrite <- fork_comp.
    rewrite <- !comp_assoc.
    rewrite <- !first_comp.
    rewrite exl_split.
    rewrite exr_split.
    rewrite !eval_first.
    rewrite !uncurry_comp.
    rewrite !uncurry_curry.
    reflexivity.
  }
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
  etransitivity.
  { apply compose_respects.
    - apply curry_respects.
      apply compose_respects; [reflexivity|].
      apply uncurry_exl_fork_exr.
    - apply fork_respects.
      2: reflexivity.
      apply compose_respects; [|reflexivity].
      apply curry_respects.
      apply compose_respects; [reflexivity|].
      apply uncurry_exl_fork_exr.
  }
  etransitivity.
  2: {
    symmetry.
    apply compose_respects; [|reflexivity].
    apply compose_respects.
    - apply curry_respects.
      apply compose_respects; [reflexivity|].
      apply uncurry_exl_fork_exr.
    - apply fork_respects.
      1: reflexivity.
      apply compose_respects; [|reflexivity].
      apply curry_respects.
      apply compose_respects; [reflexivity|].
      apply uncurry_exl_fork_exr.
  }
  remember ((curry _ ∘ exl) △ (id[y ^ x] ∘ exr)) as h.
  assert (h ≈ split (curry (mappend[Y] ∘ split eval eval ∘ doppel)) id[y ^ x]).
  { rewrite Heqh.
    unfold split.
    apply fork_respects; try reflexivity.
    apply compose_respects; try reflexivity.
    apply curry_respects.
    apply comp_assoc.
  }
  rewrite X; clear X Heqh h.
  remember ((id[y ^ x] ∘ exl) △ (curry _ ∘ exr)) as h.
  assert (h ≈ split id[y ^ x] (curry (mappend[Y] ∘ split eval eval ∘ doppel))).
  { rewrite Heqh.
    unfold split.
    apply fork_respects; try reflexivity.
    apply compose_respects; try reflexivity.
    apply curry_respects.
    apply comp_assoc.
  }
  rewrite X; clear X Heqh h.
  unfold doppel.
  etransitivity.
  { apply compose_respects.
    - apply curry_respects.
      apply compose_respects; [reflexivity|].
      rewrite !split_fork.
      rewrite !eval_first.
      reflexivity.
    - rewrite <- !comp_assoc.
      reflexivity.
  }
  rewrite <- !comp_assoc.
  rewrite !split_fork.
  rewrite !eval_first.
  simpl.
  etransitivity.
  { apply compose_respects; [reflexivity|].
    apply split_respects; [|reflexivity].
    rewrite split_fork.
    rewrite !eval_first.
    reflexivity.
  }
  etransitivity.
  2: {
    symmetry.
    apply compose_respects; [reflexivity|].
    apply fork_respects; [reflexivity|].
    rewrite split_fork.
    rewrite !eval_first.
    reflexivity.
  }
  unfold split.
  rewrite !id_left.
  rewrite !curry_comp_l.
  etransitivity.
  { apply curry_respects.
    fork_simpl.
    apply compose_respects; [reflexivity|].
    fork_simpl.
    apply fork_respects.
    - rewrite <- !comp_assoc.
      rewrite <- !fork_comp.
      rewrite <- !uncurry_comp.
      reflexivity.
    - rewrite <- !comp_assoc.
      rewrite <- !fork_comp.
      rewrite <- !uncurry_comp.
      reflexivity.
  }
  etransitivity.
  2: {
    symmetry.
    apply curry_respects.
    fork_simpl.
    apply compose_respects; [reflexivity|].
    fork_simpl.
    apply fork_respects.
    - rewrite <- !comp_assoc.
      rewrite <- !fork_comp.
      rewrite <- !uncurry_comp.
      reflexivity.
    - rewrite <- !comp_assoc.
      rewrite <- !fork_comp.
      rewrite <- !uncurry_comp.
      reflexivity.
  }
  rewrite exl_fork.
  rewrite exr_fork.
  rewrite !uncurry_curry.
  rewrite <- (id_left (uncurry exr)).
  rewrite <- split_fork.
  rewrite comp_assoc.
  rewrite HY; clear HY.
  rewrite id_left.
  etransitivity.
  { apply curry_respects.
    fork_simpl. fork_simpl.
    etransitivity.
    { apply compose_respects; [reflexivity|].
      fork_simpl.
      apply fork_respects.
      - rewrite <- !fork_comp.
        fork_simpl.
        fork_simpl.
        reflexivity.
      - rewrite <- !fork_comp.
        fork_simpl.
        rewrite exr_fork.
        rewrite <- comp_assoc.
        rewrite exl_fork.
        rewrite !exr_fork.
        reflexivity.
    }
    rewrite !exl_fork.
    reflexivity.
  }
  etransitivity.
  2: {
    symmetry.
    apply curry_respects.
    apply compose_respects; [reflexivity|].
    apply fork_respects.
    - rewrite !exl_fork.
      reflexivity.
    - apply uncurry_respects.
      rewrite exr_fork.
      apply curry_respects.
      rewrite exl_fork.
      rewrite exr_fork.
      reflexivity.
  }
  etransitivity.
  2: {
    symmetry.
    apply curry_respects.
    apply compose_respects; [reflexivity|].
    apply fork_respects; [reflexivity|].
    apply uncurry_curry.
  }
  reflexivity.
Qed.

End Monoid.
