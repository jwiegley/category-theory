Require Import Category.Lib.
Require Export Category.Structure.Bicartesian.
Require Export Category.Structure.Closed.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

Section BiCCC.

Context `{C : Category}.
Context `{A : @Cartesian C}.
Context `{@Closed C A}.
Context `{@Cocartesian C}.

Global Program Instance prod_coprod {X Y Z : C} :
  (* Products distribute over coproducts in every bicartesian closed
     category. *)
  X × (Y + Z) ≅ X × Y + X × Z := {
  to   := eval ∘ swap ∘ second (curry (inl ∘ swap) ▽ curry (inr ∘ swap));
  from := second inl ▽ second inr
}.
Next Obligation.
  rewrite <- !comp_assoc.
  rewrite <- !merge_comp.
  rewrite <- merge_inl_inr.
  rewrite <- !second_comp.
  apply merge_inv; split;
  unfold swap, second; cat;
  rewrite <- fork_comp; cat;
  rewrite <- comp_assoc; cat.
Qed.
Next Obligation.
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

Global Program Instance exp_coprod `{BiCCC C} {X Y Z : C} :
  X^(Y + Z) ≅ X^Y × X^Z := {
  to   := curry (eval ∘ second inl) △ curry (eval ∘ second inr);
  from := curry (merge (eval ∘ first exl) (eval ∘ first exr) ∘ to prod_coprod)
}.
Next Obligation.
  rewrite (curry_comp (_ ▽ _)).
  rewrite comp_assoc.
  rewrite swap_second.
  rewrite eval_first.
  rewrite eval_first.
  rewrite comp_assoc.
  rewrite eval_first.
  rewrite <- comp_assoc.
  rewrite <- curry_comp.
  rewrite comp_assoc.
  rewrite uncurry_comp_r.
  rewrite (curry_comp (uncurry _)).
  rewrite <- uncurry_comp_r.
  rewrite <- curry_comp.
  rewrite <- comp_assoc.
  rewrite (curry_comp _ (_ ∘ swap)).
  rewrite comp_assoc.
  rewrite <- fork_comp.
  rewrite <- fork_comp.
  rewrite <- fork_exl_exr.
  apply fork_inv; split.
    rewrite <- comp_assoc.
    rewrite <- curry_comp.
    rewrite curry_comp_l.
    rewrite <- comp_assoc.
    unfold second, first.
    rewrite <- fork_comp; cat.
    rewrite <- !comp_assoc.
    rewrite exr_fork.
    unfold swap.
    rewrite <- fork_comp; cat.
    rewrite comp_assoc.
    rewrite uncurry_comp_r.
    rewrite <- merge_comp.
    rewrite <- curry_comp.
    rewrite <- curry_comp.
    rewrite comp_assoc.
    rewrite inl_merge.
    rewrite comp_assoc.
    rewrite inr_merge.
    rewrite (curry_comp (uncurry exl)).
    rewrite (curry_comp (uncurry exr)).
Admitted.
Next Obligation.
  unfold first, second, swap.
Admitted.

Hint Rewrite @exp_coprod : isos.

Context `{@Initial C}.

Notation "0 × X" := (Prod Zero X) (at level 40).
Notation "X × 0" := (Prod X Zero) (at level 40).

Global Program Instance prod_zero_l {X : C} :
  0 × X ≅ Zero := {
  to   := uncurry zero;
  from := zero
}.
Next Obligation. cat. Qed.
Next Obligation. apply curry_inj; simpl; cat. Qed.

Hint Rewrite @prod_zero_l : isos.

Global Program Instance prod_zero_r {X : C} :
  X × 0 ≅ Zero := {
  to   := uncurry zero ∘ swap;
  from := zero
}.
Next Obligation. cat. Qed.
Next Obligation. apply swap_inj_r, curry_inj; simpl; cat. Qed.

Hint Rewrite @prod_zero_r : isos.

Context `{@Terminal C}.

Notation "X ^ 0" := (Exp Zero X) (at level 30).
Notation "0 ^ X" := (Exp X Zero) (at level 30).

Global Program Instance exp_zero {X : C} :
  X^0 ≅ One := {
  to   := one;
  from := curry (zero ∘ to prod_zero_r)
}.
Next Obligation. cat. Qed.
Next Obligation.
  apply uncurry_inj.
  apply swap_inj_r.
  apply curry_inj; simpl; cat.
Qed.

End BiCCC.
