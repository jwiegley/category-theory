Require Import Lib.
Require Export Bicartesian.
Require Export Closed.

Generalizable All Variables.

Class BiCCC `(_ : Closed C) `{@Initial C _} `{@Cocartesian C _ _}.

Notation "0 × X" := (Prod Zero X) (at level 40).
Notation "X × 0" := (Prod X Zero) (at level 40).

Theorem prod_zero_l `{Closed C} `{@Initial C _} {X : C} :
  0 × X ≅ Zero.
Proof.
  intros.
  refine {| iso_to   := uncurry zero
          ; iso_from := zero |}.
  constructor; simpl; intros; cat.
  apply curry_inj; cat.
Defined.

Hint Rewrite @prod_zero_l : isos.

Theorem prod_zero_r `{Closed C} `{@Initial C _} {X : C} :
  X × 0 ≅ Zero.
Proof.
  intros.
  refine {| iso_to   := uncurry zero ∘ swap
          ; iso_from := zero |}.
  constructor; simpl; intros; cat.
  apply swap_inj_r.
  apply curry_inj; cat.
Defined.

Hint Rewrite @prod_zero_r : isos.

Notation "X ^ 0" := (Exp Zero X) (at level 30).
Notation "0 ^ X" := (Exp X Zero) (at level 30).

Theorem exp_zero `{Closed C} `{@Initial C _} {X : C} :
  X^0 ≅ One.
Proof.
  intros.
  refine {| iso_to   := one
          ; iso_from := curry (zero ∘ iso_to prod_zero_r) |}.
  constructor; simpl; intros; cat.
  apply uncurry_inj.
  apply swap_inj_r.
  apply curry_inj; cat.
Qed.

Theorem prod_coprod `{Closed C} `{@Initial C _} `{@Cocartesian C _ _} {X Y Z : C} :
  (* Products distribute over coproducts in every bicartesian closed
     category. *)
  X × (Y + Z) ≅ X × Y + X × Z.
Proof.
  intros.
  refine {| iso_to   :=
              eval ∘ swap ∘ second (curry (inl ∘ swap) ▽ curry (inr ∘ swap))
          ; iso_from := second inl ▽ second inr |}.
  constructor; simpl; intros.
    rewrite <- !comp_assoc.
    rewrite <- !merge_comp.
    rewrite <- merge_inl_inr.
    rewrite <- !second_comp.
    apply merge_inv; split;
    unfold swap, second; cat;
    rewrite <- fork_comp; cat;
    rewrite <- comp_assoc; cat.
  rewrite swap_second.
  rewrite <- curry_uncurry.
  rewrite (comp_assoc eval); cat.
  rewrite comp_assoc.
  apply swap_inj_r.
  rewrite <- comp_assoc; cat.
  unfold second.
  rewrite fork_merge.
  rewrite <- fork_comp.
  unfold swap at 5.
  apply fork_inv; split;
  rewrite uncurry_comp_r;
  rewrite <- merge_comp;
  apply curry_inj; cat;
  [ rewrite <- (id_right (curry exr))
  | rewrite <- (id_right (curry exl)) ];
  rewrite <- merge_inl_inr;
  rewrite <- merge_comp;
  apply merge_inv; split;
  rewrite <- curry_comp;
  rewrite curry_comp_l;
  apply uncurry_inj; cat;
  apply swap_inj_r;
  rewrite <- !comp_assoc; cat;
  unfold first, swap;
  rewrite comp_assoc; cat;
  rewrite <- comp_assoc; cat.
Qed.

Hint Rewrite @prod_coprod : isos.

Theorem exp_coprod `{BiCCC C} {X Y Z : C} :
  X^(Y + Z) ≅ X^Y × X^Z.
Proof.
  intros.
  refine {| iso_to   := curry (eval ∘ second inl) △ curry (eval ∘ second inr)
          ; iso_from := curry (merge (eval ∘ first exl) (eval ∘ first exr)
                                    ∘ iso_to prod_coprod) |}.
  unfold first, second.
  constructor; simpl; intros.
Admitted.

Hint Rewrite @exp_coprod : isos.
