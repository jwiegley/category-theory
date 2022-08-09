Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Theorem Kan_Limit `(F : J ⟶ C) `{Lim : @Limit _ _ F} `{@RightKan _ _ (Erase J) C} :
  Lim ≅ Ran (Erase J) F ().
Proof.
  given (cone : Cone F).
    pose (from ((@adj _ _ _ _ ran_adjoint
                      (Ran (Erase J) F) F)) nat_id) as adj_from;
    simpl in adj_from.

    unshelve (refine {| vertex_obj := Ran (Erase J) F tt |}).
      apply adj_from.
    abstract (intros; rewrite (naturality[adj_from]); simpl; cat).

  given (nat : Δ(Lim) ◯ Erase J ⟹ F). {
    transform; simpl; intros.
    + apply vertex_map.
    + abstract (cat; apply ump_cones).
    + abstract (cat; symmetry; apply ump_cones).
  }

  pose (to (@adj _ _ _ _ ran_adjoint (Δ(Lim)) F) nat)
    as adj_to; simpl in adj_to.

  assert (to_from : adj_to () ∘ unique_obj (ump_limits cone) ≈ id). {
    simpl.
    spose (iso_to_from
             ((@adj _ _ _ _ ran_adjoint
                    (Ran (Erase J) F) F)) nat_id tt) as X.
    rewrite fmap_id in X.
    rewrites.
    unfold adj_to; simpl.

    given (from_ran : Ran (Erase J) F ⟹ Δ(Lim)). {
      transform; simpl; intros.
      + destruct x.
        apply (unique_obj (ump_limits cone)).
      + abstract cat.
      + abstract cat.
    }

    spose (@to_adj_nat_l _ _ _ _ ran_adjoint
                         (Ran (Erase J) F) (Δ(Lim))
                         F nat from_ran tt) as X0.
    rewrites.

    assert (∀ f g, f ≈ g
              -> to (@adj _ _ _ _ ran_adjoint (Ran (Erase J) F) F) f
               ≈ to (@adj _ _ _ _ ran_adjoint (Ran (Erase J) F) F) g).
      intros; rewrites; reflexivity.
    simpl in X.
    rewrite <- X.
      rewrite <- X0.
      apply X; simpl.
      apply (unique_property (ump_limits cone)).
    intros; reflexivity.
  }

  isomorphism; simpl.
  - apply adj_to.
  - apply (unique_obj (ump_limits cone)).
  - apply to_from.
  - simpl in *.
    (* Since half of the isomorphism has already been proven in [to_from], it
       is sufficient to show that either [(adj nat) ()] is monic, or
       [unique_morphism (ump_limits cone)] is epic. I've chosen the latter due
       to Emily Riehl's statement in "Category Theory in Context" (p. 76):
       "... Proposition 3.1.7 implies that the only automorphism of [a limit
       object] l that commutes with the specified limit cone λ is the
       identity." *)
    assert (∀ (f g : Lim ~{ C }~> Lim),
              (∀ x, vertex_map[Lim] ∘ f ≈ @vertex_map _ _ _ Lim x) ->
              (∀ x, vertex_map[Lim] ∘ g ≈ @vertex_map _ _ _ Lim x) ->
              f ∘ unique_obj (ump_limits cone) ≈
              g ∘ unique_obj (ump_limits cone) -> f ≈ g) as HA.
      intros; clear adj_to to_from nat.
      rewrite <- (uniqueness (ump_limits Lim) _ X).
      rewrite <- (uniqueness (ump_limits Lim) _ X0).
      reflexivity.

    (* Apply the consequence that [unique_morphism (ump_limits cone)] is epic
      on morphisms commuting with the limit cone, leaving us with the burden
      of showing that the two sides of our equivalence do in fact commute for
      [Lim F]. The right side is trivial (id), while the left side relies on
      the naturality of the Kan adjunction. *)
    apply HA; simpl; intros; cat; swap 1 2.
      rewrite <- comp_assoc.
      rewrite to_from; cat.

    rewrite comp_assoc.
    srewrite (unique_property (ump_limits cone)).
    srewrite_r (iso_from_to
                  ((@adj _ _ _ _ ran_adjoint (Δ(Lim)) F)) nat x).
    unfold adj_to.
    srewrite_r (@from_adj_nat_l _ _ _ _ ran_adjoint
                  (Δ(Lim)) (Ran (Erase J) F) F nat_id
                  (to (@adj _ _ _ _ ran_adjoint (Δ(Lim)) F) nat) x).
    sapply (@from_adj_respects
              _ _ _ _ (@ran_adjoint _ _ _ _ H) (Δ(Lim)) F).
    simpl; intros; cat.
Qed.
