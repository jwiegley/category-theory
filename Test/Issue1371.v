Require Import Category.Lib Category.Theory.Category.

(* The product eliminator used by iffT transport cannot operate at this
   hom-equivalence level. Keep the restriction local to these tests. *)
Section AboveProduct.
  Universe o h p.
  Constraint h <= p.
  Constraint prod_rect.u0 < p.
  Constraint prod_rect.u1 < p.
  Constraint prod_rect.u2 < p.

  Context {C : Category@{o h p}} {x y z : C} (f f' : y ~> z) (g k : x ~> y).

  Lemma one_side (H : f ≈ f') (t : x ~> z) (K : f' ∘ g ≈ t) : f ∘ g ≈ t.
  Proof. rewrite H. exact K. Defined.

  Lemma both_sides (H : f ≈ f') (K : f' ∘ g ≈ f' ∘ k) : f ∘ g ≈ f ∘ k.
  Proof. rewrite H. exact K. Defined.

  Lemma both_sides_opaque (H : f ≈ f') (K : f' ∘ g ≈ f' ∘ k) : f ∘ g ≈ f ∘ k.
  Proof. rewrite H. exact K. Qed.

  Lemma both_sides_hyp (H : f ≈ f') (K : f ∘ g ≈ f ∘ k) : f' ∘ g ≈ f' ∘ k.
  Proof. rewrite H in K. exact K. Defined.
End AboveProduct.
