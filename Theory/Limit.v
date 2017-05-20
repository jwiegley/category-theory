Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Cone.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Limit.

Context `{J : Category}.
Context `{C : Category}.

(* Wikipedia:

   "Let F : J ⟶ C be a diagram of shape J in a category C. A cone to F is an
   object N of C together with a family ψX : N ⟶ F(X) of morphisms indexed by
   the objects X of J, such that for every morphism f : X ⟶ Y in J, we have
   F(f) ∘ ψX = ψY.

   "A limit of the diagram F : J ⟶ C is a cone (L, φ) to F such that for any
   other cone (N, ψ) to F there exists a unique morphism u : N ⟶ L such that
   φX ∘ u = ψX for all X in J.

   "One says that the cone (N, ψ) factors through the cone (L, φ) with the
   unique factorization u. The morphism u is sometimes called the mediating
   morphism."

   In this presentation, L = Lim, u = limit, and N is a universally quantified
   argument of the uniqueness and universal properties. *)

Class HasLimit (F : J ⟶ C) := {
  Limit : Cone F;

  (* This just restates the fact that limits are terminal objects in the
     category of cones to F (which in turn is the comma category (Δ ↓ F)). *)
  limit_terminal {N : Cone F} : N ~> Limit;
  limit_unique {N : Cone F} (f g : N ~> Limit) : f ≈ g;

  ump_limits {N : Cone F} {X : J} :
    vertex_map[Limit] ∘ limit_terminal ≈ @vertex_map _ _ _ N X
}.

Set Transparent Obligations.

End Limit.

Arguments HasLimit {_ _} F.
Arguments Limit {_ _} F {_}.

Coercion Limit_object `{J : Category} `{C : Category} `{F : J ⟶ C}
         (L : HasLimit F) : C := Limit F.

Require Import Category.Theory.Kan.Extension.
Require Import Category.Instance.One.
Require Import Category.Instance.Nat.

Theorem Kan_Limit `{J : Category} `{C : Category} (F : J ⟶ C)
        `{@HasLimit J C F} `{@HasRan J 1%object one[J] C} :
  Limit F ≅ Ran (one[J]) F ().
Proof.
  given (cone : Cone F).
    pose (from ((@adj_iso _ _ _ _ ran_adjoint
                          (Ran (Erase J) F) F)) nat_identity) as adj_from;
    simpl in adj_from.

    unshelve (refine {| vertex := Ran (Erase J) F tt |}).
      apply adj_from.
    abstract (intros; rewrite (naturality[adj_from]); simpl; cat).

  given (nat : Select (Limit F) ○ Erase J ⟹ F).
    transform; simpl; intros.
      apply vertex_map.
    abstract (cat; apply ump_cones).

  pose (to (@adj_iso _ _ _ _ ran_adjoint (Select (Limit F)) F) nat) as adj_to;
  simpl in adj_to.

  isomorphism; simpl.
  - apply adj_to.
  - apply (@limit_terminal J C F H cone).
  - simpl.
    pose proof (@ump_limits J C F H cone).
    pose proof (iso_to_from
                  ((@adj_iso _ _ _ _ ran_adjoint
                             (Ran (Erase J) F) F)) nat_identity tt).
    simpl in X0.
    rewrite fmap_id in X0.
    rewrite <- X0.
    unfold adj_to; simpl.

    given (from_ran : Ran (Erase J) F ⟹ Select (Limit F)).
      transform; simpl; intros.
        destruct X1.
        apply (@limit_terminal _ _ _ H cone).
      abstract cat.

    pose proof (@adj_left_nat_l' _ _ _ _ ran_adjoint
                                 (Ran (Erase J) F) (Select (Limit F))
                                 F nat from_ran tt).
    simpl in X1; rewrite <- X1; clear X1.
    unfold nat_compose; simpl.
    assert (∀ f g, f ≈ g
              -> to (@adj_iso _ _ _ _ ran_adjoint (Ran (Erase J) F) F) f
               ≈ to (@adj_iso _ _ _ _ ran_adjoint (Ran (Erase J) F) F) g).
      intros; rewrite X1; reflexivity.
    simpl in X1; apply X1; clear X1.
    intros; simpl.
    abstract apply X.
  - abstract apply limit_unique.
Qed.
