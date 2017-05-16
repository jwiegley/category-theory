Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Export Category.Construction.Comma.
Require Export Category.Construction.Product.
Require Export Category.Instance.Cat.
Require Export Category.Isomorphism.Natural.Comma.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section AdjunctionComma.

(* Wikipedia: "Lawvere showed that the functors F : C → D and G : D → C are
   adjoint if and only if the comma categories (F ↓ Id[D]) and (Id[C] ↓ G) are
   isomorphic, and equivalent elements in the comma category can be projected
   onto the same element of C × D. This allows adjunctions to be described
   without involving sets, and was in fact the original motivation for
   introducing comma categories."

   From ncatlab: "To give an adjunction i ⊣ r it suffices to give, for each k
   : x → pe in B ↓ p, an object rk in E such that prk = x and an arrow irk =
   1x → k in B ↓ p that is universal from i to k."

   Lawvere's own statement of the theorem, from his thesis (page 40):

   "For each functor f : A ⟶ B, there exists a functor g : B ⟶ A such that g
   is adjoint to f iff for every object B ∈ |B| there exists an object A ∈ |A|
   and a map φ : B ~> Af in B such that for every object A′ ∈ |A| and every
   map x : B ~> A′f in B, there exists a unique map y : A ~> A′ in A such that
   x = φ(yf) in B."

   Repeating this using the names and syntax of this module:

   "∀ (G : C ⟶ D) (F : D ⟶ C), F ⊣ G <-->
      ∀ d : D, ∃ (c : C) (phi : d ~{D}~> G c),
        ∀ (c′ : C) (psi : d ~{D}~> G c′), ∃! y : c ~{C}~> c′,
          psi ≈ fmap[G] y ∘ phi" *)

Context `{C : Category}.
Context `{D : Category}.
Context `{G : C ⟶ D}.
Context `{F : D ⟶ C}.

Record fibered_equivalence := {
  fiber_iso : (F ↓ Id[C]) ≅[Cat] (Id[D] ↓ G);

  projG_commutes : comma_proj ≈[Cat] comma_proj ○ from fiber_iso;
  projF_commutes : comma_proj ≈[Cat] comma_proj ○ to fiber_iso;

  functoriality_of_F {X Y} g :
    fmap[G] (snd (@fmap _ _ (to fiber_iso)
                        ((X, F X); id[F X])
                        ((Y, F Y); id[F Y]) (g, fmap[F] g)))
        ∘ projT2 (to fiber_iso ((X, F X); id[F X]))
      ≈ projT2 (to fiber_iso ((Y, F Y); id[F Y]))
        ∘ fst (fmap[to fiber_iso] (g, fmap[F] g));

  functoriality_of_G {X Y} g :
    (snd (@fmap _ _ (from fiber_iso)
                ((G X, X); id[G X])
                ((G Y, Y); id[G Y]) (fmap[G] g, g)))
        ∘ projT2 (from fiber_iso ((G X, X); id[G X]))
      ≈ projT2 (from fiber_iso ((G Y, Y); id[G Y]))
        ∘ fmap[F] (fst (@fmap _ _ (from fiber_iso)
                              ((G X, X); id[G X])
                              ((G Y, Y); id[G Y]) (fmap[G] g, g)))
}.

Theorem Adjunction_Comma :
  F ⊣ G  <-->  fibered_equivalence.
Proof.
  split; intros H. {
    given (to : (F ↓ Id[C]) ~{Cat}~> (Id[D] ↓ G)). {

      given (fobj : F ↓ Id[C] -> Id[D] ↓ G). {
        destruct 1 as [x ?]; exists x.
        apply H; assumption.
      }

      given (fmap : ∀ X Y, X ~> Y -> fobj X ~> fobj Y).
        destruct X, Y; auto.

      assert (∀ X Y, Proper (equiv ==> equiv) (fmap X Y))
        by (destruct X, Y; auto).

      assert (∀ X, fmap X X (id[X]) ≈ id)
        by (destruct X0; cat).

      assert (∀ X Y Z f g, fmap X Z (f ∘ g) ≈ fmap Y Z f ∘ fmap X Y g)
        by (destruct X1, Y, Z; cat).

      econstructor; eauto.
    }

    given (from : (Id[D] ↓ G) ~{Cat}~> (F ↓ Id[C])). {

      given (fobj : Id[D] ↓ G -> F ↓ Id[C]). {
        destruct 1 as [x ?]; exists x.
        apply H; assumption.
      }

      given (fmap : ∀ X Y, X ~> Y -> fobj X ~> fobj Y).
        destruct X, Y; auto.

      assert (∀ X Y, Proper (equiv ==> equiv) (fmap X Y))
        by (destruct X, Y; auto).

      assert (∀ X, fmap X X (id[X]) ≈ id)
        by (destruct X0; cat).

      assert (∀ X Y Z f g, fmap X Z (f ∘ g) ≈ fmap Y Z f ∘ fmap X Y g)
        by (destruct X1, Y, Z; cat).

      econstructor; eauto.
    }

    assert (from ∘ to ≈ id) as from_to. {
      constructive; simpl; intros.
      all:swap 2 3.
      - destruct X; simpl.
        exact (id, id).
      - destruct X; simpl.
        exact (id, id).
      - destruct X, Y; simpl; cat.
      - destruct X, Y; simpl; cat.
      - destruct A; cat.
      - destruct A; cat.
    }

    assert (to ∘ from ≈ id). {
      constructive; simpl; intros.
      all:swap 2 3.
      - destruct X; simpl.
        exact (id, id).
      - destruct X; simpl.
        exact (id, id).
      - destruct X, Y; simpl; cat.
      - destruct X, Y; simpl; cat.
      - destruct A; cat.
      - destruct A; cat.
    }

    unshelve econstructor.
    - isomorphism; auto.
    - isomorphism; simpl.
      + transform; simpl; intros.
        * destruct X0; simpl.
          exact (id, id).
        * destruct X0, Y; simpl; cat.
      + transform; simpl; intros.
        * destruct X0; simpl.
          exact (id, id).
        * destruct X0, Y; simpl; cat.
      + destruct A; simpl; cat.
      + destruct A; simpl; cat.
    - isomorphism; simpl.
      + transform; simpl; intros.
        * destruct X0; simpl.
          exact (id, id).
        * destruct X0, Y; simpl; cat.
      + transform; simpl; intros.
        * destruct X0; simpl.
          exact (id, id).
        * destruct X0, Y; simpl; cat.
      + destruct A; simpl; cat.
      + destruct A; simpl; cat.
    - simpl in *; intros.
      clear from_to X to from.
      rewrite <- (@adj_left_nat_r' _ _ F G H).
      rewrite <- (@adj_left_nat_l' _ _ F G H); cat.
    - simpl in *; intros.
      rewrite <- (@adj_right_nat_r' _ _ F G H).
      rewrite <- (@adj_right_nat_l' _ _ F G H); cat.
  }

  pose proof (@functoriality_of_F H) as FF.
  pose proof (@functoriality_of_G H) as FG.
  destruct H.
  unshelve (eapply adj_from_unit_conuit).
  unshelve econstructor.

  - intro a.
    exact (fmap (snd (projF_commutes0⁻¹ ((a, F a); id[F a])))
                ∘ projT2 (to fiber_iso0 ((a, F a); id[F a]))
                ∘ fst (to projF_commutes0 ((a, F a); id[F a]))).

  - intro a.
    exact (snd (projG_commutes0⁻¹ ((G a, a); id[G a]))
               ∘ projT2 (fiber_iso0⁻¹ ((G a, a); id[G a]))
               ∘ fmap (fst (to projG_commutes0 ((G a, a); id[G a])))).

  - simpl in *; intros.
    rewrite !comp_assoc.
    rewrite <- fmap_comp.
    pose proof (snd (naturality[from projF_commutes0]
                               ((X, F X); id[F X]) ((Y, F Y); id[F Y])
                               (f, fmap[F] f))); simpl in X0.
    rewrite X0; clear X0.
    rewrite fmap_comp.
    rewrite <- !comp_assoc.
    apply compose_respects; [reflexivity|].
    pose proof (fst (naturality[to projF_commutes0]
                               ((X, F X); id[F X]) ((Y, F Y); id[F Y])
                               (f, fmap[F] f))); simpl in X0.
    rewrite <- X0; clear X0.
    rewrite !comp_assoc.
    apply compose_respects; [|reflexivity].

    apply FF.

  - simpl in *; intros.
    rewrite <- !comp_assoc.
    rewrite <- fmap_comp.
    pose proof (snd (naturality[from projG_commutes0]
                               ((G X, X); id[G X]) ((G Y, Y); id[G Y])
                               (fmap[G] f, f))); simpl in X0.
    rewrite !comp_assoc.
    rewrite X0; clear X0.
    rewrite fmap_comp.
    rewrite <- !comp_assoc.
    apply compose_respects; [reflexivity|].
    pose proof (fst (naturality[to projG_commutes0]
                               ((G X, X); id[G X]) ((G Y, Y); id[G Y])
                               (fmap[G] f, f))); simpl in X0.
    rewrite <- fmap_comp.
    rewrite <- X0; clear X0.
    rewrite !comp_assoc.
    rewrite fmap_comp.
    rewrite !comp_assoc.
    apply compose_respects; [|reflexivity].

    apply FG.

  - simpl in *; intros.
    rewrite <- !comp_assoc.
    rewrite <- !fmap_comp.
    rewrite (comp_assoc (fmap[G] _)).
    admit.

  - admit.
Abort.

End AdjunctionComma.
