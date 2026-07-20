Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Cone.Const.

Generalizable All Variables.

(** * Limits as right Kan extensions along the terminal functor *)

(* nLab: https://ncatlab.org/nlab/show/Kan+extension
   Wikipedia: https://en.wikipedia.org/wiki/Kan_extension

   The limit of a functor F : J ⟶ C is the right Kan extension of F along the
   unique functor to the terminal category 1.  Dually the colimit is the left
   Kan extension along that functor.  Writing E := Erase J : J ⟶ 1 for the
   terminal functor (Wikipedia/nLab call it the unique functor to 1), the
   restriction Induced = (− ◯ E) sends an object d of 1 to the constant functor
   Δ_d, so the adjunction Induced ⊣ Ran makes Ran E F corepresent the cones
   over F; that universal property is exactly the limit of F.

   Since the global right Kan extension Ran E F is a functor 1 ⟶ C, evaluating
   it at the unique object ttt of 1 yields the limit object in C.  This is the
   slogan "lim F = Ran_E F" (Wikipedia) / "the right Kan extension operation
   forms the limit of a functor" (nLab) made into a concrete isomorphism.

   Theorem (Kan_Limit): for F : J ⟶ C with a limit and a right Kan extension
   along Erase J, the limit object is isomorphic in C to (Ran (Erase J) F) ttt.

   Notation:
     Erase J        the terminal functor J ⟶ 1
     1              the terminal category (single object ttt, Instance/One)
     ttt            the unique object of 1 (poly_unit)
     Ran K F        the right Kan extension functor (Theory/Kan/Extension)
     Δ(c)           the constant/diagonal functor at c
     ≅              isomorphism of objects (Theory/Isomorphism) *)

Theorem Kan_Limit `(F : J ⟶ C) `{Lim : @Limit _ _ F} `{@RightKan _ _ (Erase J) C} :
  Lim ≅ Ran (Erase J) F ttt.
Proof.
  given (cone : Cone F). {
    pose (from ((@adj _ _ _ _ ran_adjoint
                   (Ran (Erase J) F) F)) nat_id) as adj_from.
    simpl carrier in adj_from.
    unshelve (refine {| vertex_obj := Ran (Erase J) F ttt |});
      [ assumption | unshelve econstructor ].
    - apply adj_from.
    - abstract (intros; rewrite (naturality[adj_from]); simpl; cat).
  }
  given (nat : Δ(Lim) ◯ Erase J ⟹ F). {
    transform; simpl.
    + exact vertex_map.
    + abstract(rewrite id_right; apply cone_coherence).
    + abstract(rewrite id_right; symmetry; apply cone_coherence).
  }
  pose (to (@adj _ _ _ _ ran_adjoint (Δ(Lim)) F) nat)
    as adj_to; simpl in adj_to.

  assert (to_from : adj_to ttt ∘ unique_obj (ump_limits cone) ≈ id). {
    simpl.
    spose (iso_to_from
             ((@adj _ _ _ _ ran_adjoint
                    (Ran (Erase J) F) F)) nat_id ttt) as X.
    rewrite fmap_id in X.
    rewrites.
    unfold adj_to; simpl.

    given (from_ran : Ran (Erase J) F ⟹ Δ(Lim)). {
      transform; simpl; intros.
      - destruct x.
        apply (unique_obj (ump_limits cone)).
      - destruct x, y, f; simpl.
        abstract cat.
      - destruct x, y, f; simpl.
        abstract cat.
    }

    spose (@to_adj_nat_l _ _ _ _ ran_adjoint
                         (Ran (Erase J) F) (Δ(Lim))
                         F nat from_ran ttt) as X0.
    rewrites.

    assert (∀ f g, f ≈ g
              → to (@adj _ _ _ _ ran_adjoint (Ran (Erase J) F) F) f
               ≈ to (@adj _ _ _ _ ran_adjoint (Ran (Erase J) F) F) g). {
      intros; rewrites; reflexivity.
    }
    simpl in X.
    rewrite <- X.
    - rewrite <- X0.
      apply X; simpl.
      apply (unique_property (ump_limits cone)).
    - simpl; reflexivity.
  }

  isomorphism; simpl.
  - apply adj_to.
  - apply (unique_obj (ump_limits cone)).
  - apply to_from.
  - simpl in *.
    (* Since half of the isomorphism has already been proven in [to_from], it
       is sufficient to show that either [(adj nat) ttt] is monic, or
       [unique_obj (ump_limits cone)] is epic. I've chosen the latter due
       to Emily Riehl's statement in "Category Theory in Context" (p. 76):
       "... Proposition 3.1.7 implies that the only automorphism of [a limit
       object] l that commutes with the specified limit cone λ is the
       identity." *)

    assert (∀ (f g : Lim ~{ C }~> Lim),
              (∀ x, vertex_map[Lim] ∘ f ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ Lim) x) ->
              (∀ x, vertex_map[Lim] ∘ g ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ Lim) x) ->
              f ∘ unique_obj (ump_limits cone) ≈
              g ∘ unique_obj (ump_limits cone) → f ≈ g) as HA. {
      intros; clear adj_to to_from nat.
      rewrite <- (uniqueness (ump_limits Lim) _ X).
      rewrite <- (uniqueness (ump_limits Lim) _ X0).
      reflexivity.
    }

    (* Apply the consequence that [unique_obj (ump_limits cone)] is epic
      on morphisms commuting with the limit cone, leaving us with the burden
      of showing that the two sides of our equivalence do in fact commute for
      [Lim F]. The right side is trivial (id), while the left side relies on
      the naturality of the Kan adjunction. *)
    apply HA; simpl; intros; cat; swap 1 2.
    + rewrite <- comp_assoc.
      rewrite to_from; cat.

    + rewrite comp_assoc.
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
