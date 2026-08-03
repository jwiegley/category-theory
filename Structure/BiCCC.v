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

(* nLab: https://ncatlab.org/nlab/show/bicartesian+closed+category
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category
   Wikipedia: https://en.wikipedia.org/wiki/Distributive_category

   A bicartesian closed category (BiCCC) is a cartesian closed category that
   also has finite coproducts: it is simultaneously cartesian (finite products
   ×, terminal object 1), closed (exponentials →, written `y^x` here), and
   cocartesian (finite coproducts +, initial object 0). It is the categorical
   model of the simply-typed lambda calculus with sums - the internal language
   is a type theory with the type formers ×, →, +, 1 and 0.

   This file does not introduce a `BiCCC` class: rather than bundle a fourth
   redundant record, a BiCCC is obtained simply by assuming all four pieces of
   structure together (Cartesian, Closed, Cocartesian and Initial in the same
   Context), exactly as the section header below does.

   The mathematical content of the file is that this combination is forced to
   be distributive. Distributivity is not an extra axiom: because the category
   is closed, each functor `_ × x` has a right adjoint `_ ^ x`, hence preserves
   all colimits, in particular finite coproducts and the initial object. The
   canonical comparison maps are therefore isomorphisms, and the section
   derives them as concrete instances `prod_coprod_l`, `prod_coprod_r`,
   `prod_zero_l`, `prod_zero_r`, `exp_coprod` and `exp_zero`. The final
   instance [BiCCC_Distributive] packages the relevant ones as a
   [Distributive] structure. *)

Section BiCCC.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Cocartesian C}.
Context `{@Closed C _}.

#[export] Program Instance prod_coprod_l {x y z : C} :
  (* Right distributivity: `_ × x` preserves the coproduct y + z, so it
     distributes over it (the left-hand, mirror form of prod_coprod_r). *)
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
  (* Left distributivity: `x × _` preserves the coproduct y + z, so it
     distributes over it. This is the canonical distributivity iso of a
     distributive category, supplying [distr_prod_coprod] below. *)
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

(* Any two morphisms out of an object isomorphic to `0` agree. Transport both
   along the isomorphism -- `p ≈ (p ∘ from i) ∘ to i` -- and the transported
   halves are morphisms out of `0` proper, where [zero_unique] applies. *)
Lemma iso_initial_arrow_unique {y z : C} (i : y ≅ 0) (p q : y ~> z) : p ≈ q.
Proof.
  rewrite <- (id_right p), <- (id_right q).
  rewrite <- (iso_from_to i).
  rewrite !comp_assoc.
  now rewrite (zero_unique (p ∘ from i) (q ∘ from i)).
Qed.

(* The collapse `x × 0 ~> 0` followed by the unique `0 ~> x` is just the first
   projection: both are morphisms out of `x × 0`, an object isomorphic to `0`,
   so [iso_initial_arrow_unique] identifies them. *)
Lemma zero_prod_zero_r {x : C} :
  zero ∘ to (@prod_zero_r x) ≈ exl.
Proof. apply (iso_initial_arrow_unique prod_zero_r). Qed.

(* Strict initiality (Fong & Spivak, *Seven Sketches*, §1.2.1 Exercise 1.25;
   nLab: strict initial object). In a bicartesian closed category the initial
   object is STRICT: an object with *any* morphism at all into `0` is already
   isomorphic to `0`. The set-level reading is that a set with a function to
   the empty set is itself empty.

   The witness is NOT `f` itself but the composite through the annihilation
   isomorphism `x × 0 ≅ 0`: pair `f` with the identity to land in `x × 0`,
   then collapse. The inverse is the unique `zero : 0 ~> x`. One round trip is
   a morphism out of `0`, killed by [zero_unique]; the other rests on
   `zero ∘ to prod_zero_r ≈ exl`, which holds because both sides emanate from
   `x × 0`, an object isomorphic to `0`. *)
Program Definition initial_strict {x : C} (f : x ~> 0) : x ≅ 0 := {|
  to   := to prod_zero_r ∘ (id △ f);
  from := zero
|}.
Next Obligation. apply zero_unique. Qed.
Next Obligation.
  rewrite comp_assoc.
  rewrite (zero_prod_zero_r (x:=x)).
  now rewrite exl_fork.
Qed.

(* The morphism one starts from is itself that isomorphism: once `x ≅ 0`, `x`
   is initial too, so morphisms out of it are unique. This is why strictness
   does not depend on which `f : x ~> 0` is supplied. *)
Corollary initial_strict_unique {x : C} (f : x ~> 0) :
  f ≈ to (initial_strict f).
Proof. now apply (iso_initial_arrow_unique (initial_strict f)). Qed.

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

(* Every BiCCC is distributive. The two [Distributive] fields,
   [distr_prod_coprod] (x × (y + z) ≅ x × y + x × z) and [distr_zero]
   (x × 0 ≅ 0), are exactly the instances [prod_coprod_r] and [prod_zero_r]
   derived above, so the structure is found by instance resolution with no
   further proof obligations. *)
#[export]
Program Instance BiCCC_Distributive {C : Category}
        `{@Cartesian C} `{@Cocartesian C} `{@Closed C _} `{@Initial C} :
  @Distributive C _ _ _.
