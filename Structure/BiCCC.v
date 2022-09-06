Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Distributive.

Generalizable All Variables.

Section BiCCC.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Cocartesian C}.
Context `{@Closed C _}.

#[export] Program Instance prod_coprod_l {x y z : C} :
  (* Products distribute over coproducts in every bicartesian closed
     category. *)
  (y + z) × x ≅ y × x + z × x := {
  to   := uncurry (curry inl ▽ curry inr);
  from := first inl ▽ first inr
}.
Next Obligation.
  rewrite <- !merge_comp.
  rewrite <- eval_first.
  rewrite <- !comp_assoc.
  rewrite <- !first_comp; cat.
Qed.
Next Obligation.
  rewrite uncurry_comp_r.
  apply curry_inj.
  rewrite curry_uncurry.
  rewrite <- merge_comp.
  rewrite <- !curry_comp; cat.
  rewrite <- !curry_id.
  rewrite merge_comp; cat.
Qed.

#[local] Hint Rewrite @prod_coprod_l : isos.

Lemma uncurry_merge {x y z w : C} (f : x ~> y^z) (g : w ~> y^z) :
  uncurry (f ▽ g) ≈ uncurry f ▽ uncurry g ∘ to prod_coprod_l.
Proof.
  simpl.
  apply curry_inj; cat.
  rewrite curry_comp; cat.
  rewrite <- merge_comp.
  apply merge_inv; split;
  rewrite <- curry_comp; cat.
Qed.

Corollary unmerge_uncurry {x y z w : C} (f : x ~> y^z) (g : w ~> y^z) :
  uncurry f ▽ uncurry g ≈ uncurry (f ▽ g) ∘ from prod_coprod_l.
Proof.
  rewrite uncurry_merge.
  rewrite <- comp_assoc.
  rewrite iso_to_from; cat.
Qed.

#[export] Program Instance prod_coprod_r {x y z : C} :
  (* Products distribute over coproducts in every bicartesian closed
     category. *)
  x × (y + z) ≅ x × y + x × z := {
  to   := uncurry (curry (inl ∘ swap) ▽ curry (inr ∘ swap)) ∘ swap;
  from := second inl ▽ second inr
}.
Next Obligation.
  rewrite <- !comp_assoc.
  rewrite <- !merge_comp.
  rewrite <- eval_first.
  rewrite <- !comp_assoc.
  rewrite !swap_second.
  rewrite !(comp_assoc (first _)).
  rewrite <- !first_comp; cat.
  rewrite !(comp_assoc eval).
  rewrite !eval_first; cat.
  rewrite <- !comp_assoc; cat.
Qed.
Next Obligation.
  rewrite uncurry_merge. simpl.
  rewrite !comp_assoc; cat.
  rewrite <- merge_comp.
  rewrite !comp_assoc; cat.
  rewrite <- !swap_first.
  rewrite merge_comp.
  rewrite <- !comp_assoc.
  apply swap_inj_l, swap_inj_r.
  rewrite comp_assoc.
  rewrite swap_invol, id_left, id_right.
  rewrite <- !comp_assoc.
  rewrite swap_invol, id_right.
  rewrite uncurry_comp_r.
  rewrite <- merge_comp.
  apply curry_inj.
  rewrite curry_uncurry.
  rewrite <- !curry_comp; cat.
  rewrite <- !curry_id.
  rewrite merge_comp; cat.
Qed.

#[local] Hint Rewrite @prod_coprod_r : isos.

#[export] Program Instance exp_coprod {x y z : C} :
  x^(y + z) ≅ x^y × x^z := {
  to   := curry (eval ∘ second inl) △ curry (eval ∘ second inr);
  from := curry (uncurry exl ▽ uncurry exr ∘ to prod_coprod_r)
}.
Next Obligation.
  rewrite <- fork_comp.
  rewrite <- fork_exl_exr.
  apply fork_inv; split;
  rewrite curry_comp_l;
  rewrite <- comp_assoc;
  rewrite <- first_second;
  rewrite comp_assoc;
  rewrite eval_first;
  rewrite uncurry_curry;
  rewrite <- !comp_assoc;
  rewrite swap_second;
  rewrite curry_comp;
  rewrite <- !eval_first;
  rewrite <- comp_assoc;
  rewrite (comp_assoc (first _));
  rewrite <- first_comp; cat;
  rewrite !eval_first;
  rewrite (comp_assoc eval);
  rewrite !eval_first; cat;
  rewrite <- comp_assoc; cat;
  rewrite <- curry_comp; cat.
Qed.
Next Obligation.
  remember (_ △ _) as p.
  enough (∀ {w : C} (f g : w ~> x^(y + z)), p ∘ f ≈ p ∘ g → f ≈ g) as HA. {
    apply HA.
    rewrite comp_assoc.
    rewrite Heqp.
    rewrite exp_coprod_obligation_1; cat.
  }
  intros ??? e.
  rewrite Heqp in e.
  rewrite <- !fork_comp in e.
  apply fork_inv in e.
  destruct e as [HA HB].
  rewrite !curry_comp_l in HA.
  rewrite !curry_comp_l in HB.
  apply curry_inj in HA.
  apply curry_inj in HB.
  rewrite <- !comp_assoc in HA.
  rewrite <- !comp_assoc in HB.
  rewrite <- !first_second in HA.
  rewrite <- !first_second in HB.
  rewrite !comp_assoc in HA.
  rewrite !comp_assoc in HB.
  apply uncurry_inj.
  rewrite <- !eval_first.
  enough (∀ {w : C} (f g : w × (y + z) ~> x),
             f ∘ second inl ≈ g ∘ second inl ->
             f ∘ second inr ≈ g ∘ second inr → f ≈ g) as HC. {
    exact (HC _ _ _ HA HB).
  }
  intros ? h i HD HE.
  unfold second in HD, HE.
  rewrite <- id_right.
  rewrite <- (id_right i).
  rewrite <- (iso_from_to prod_coprod_r).
  simpl.
  rewrite !comp_assoc.
  rewrite <- !merge_comp.
  rewrites.
  reflexivity.
Qed.

#[local] Hint Rewrite @exp_coprod : isos.

Context `{@Initial C}.

#[export] Program Instance prod_zero_l {x : C} :
  0 × x ≅ 0 := {
  to   := uncurry zero;
  from := zero
}.
Next Obligation. apply zero_unique. Qed.
Next Obligation.
  apply curry_inj; simpl; cat.
  apply zero_unique.
Qed.

#[local] Hint Rewrite @prod_zero_l : isos.

#[export] Program Instance prod_zero_r {x : C} :
  x × 0 ≅ 0 := {
  to   := uncurry zero ∘ swap;
  from := zero
}.
Next Obligation. apply zero_unique. Qed.
Next Obligation.
  apply swap_inj_r, curry_inj; simpl; cat.
  apply zero_unique.
Qed.

#[local] Hint Rewrite @prod_zero_r : isos.

Context `{@Terminal C}.

#[export] Program Instance exp_zero {x : C} :
  x^0 ≅ 1 := {
  to   := one;
  from := curry (zero ∘ to prod_zero_r)
}.
Next Obligation. apply one_unique. Qed.
Next Obligation.
  apply uncurry_inj.
  apply swap_inj_r.
  apply curry_inj; simpl; cat.
  apply zero_unique.
Qed.

End BiCCC.

#[export]
Program Instance BiCCC_Distributive {C : Category}
        `{@Cartesian C} `{@Cocartesian C} `{@Closed C _} `{@Initial C} :
  @Distributive C _ _ _.
