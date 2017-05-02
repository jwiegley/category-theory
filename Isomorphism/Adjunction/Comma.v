Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Export Category.Construction.Comma.
Require Export Category.Construction.Product.
Require Export Category.Instance.Cat.
Require Export Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Lawvere.

(* Wikipedia: "Lawvere showed that the functors F : C → D and G : D → C are
   adjoint if and only if the comma categories (F ↓ Id[D]) and (Id[C] ↓ G) are
   isomorphic, and equivalent elements in the comma category can be projected
   onto the same element of C × D. This allows adjunctions to be described
   without involving sets, and was in fact the original motivation for
   introducing comma categories."

   From ncatlab: "To give an adjunction i ⊣ r it suffices to give, for each
   k : x → pe in B ↓ p, an object rk in E such that prk = x and an arrow
   irk = 1x → k in B ↓ p that is universal from i to k." *)

Context `{C : Category}.
Context `{D : Category}.
Context `{G : C ⟶ D}.
Context `{F : D ⟶ C}.

Record fibered_equivalence := {
  fiber_iso : (F ↓ Id[C]) ≅[Cat] (Id[D] ↓ G);

  projG_commutes : comma_proj ≈[Cat] comma_proj ○ from fiber_iso;
  projF_commutes : comma_proj ≈[Cat] comma_proj ○ to fiber_iso
}.

Theorem Lawvere_Adjunction :
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
      + natural; simpl; intros.
        * destruct X0; simpl.
          exact (id, id).
        * destruct X0, Y; simpl; cat.
      + natural; simpl; intros.
        * destruct X0; simpl.
          exact (id, id).
        * destruct X0, Y; simpl; cat.
      + destruct A; simpl; cat.
      + destruct A; simpl; cat.
    - isomorphism; simpl.
      + natural; simpl; intros.
        * destruct X0; simpl.
          exact (id, id).
        * destruct X0, Y; simpl; cat.
      + natural; simpl; intros.
        * destruct X0; simpl.
          exact (id, id).
        * destruct X0, Y; simpl; cat.
      + destruct A; simpl; cat.
      + destruct A; simpl; cat.
  }

  destruct H.
  unshelve (eapply adj_from_unit_conuit).
  unshelve econstructor.

  - intro a.
(*
    assert (comma_proj f ≈ (a, F a)). {
      isomorphism; unfold f; simpl.
      - apply projF_commutes0.
      - apply (transform[to projF_commutes0] ((a, F a); id[F a])).
      - simpl; cat; simpl; cat.
          destruct projF_commutes0; simpl in *.
          apply (fst (iso_from_to ((a, F a); id[F a]))).
        destruct projF_commutes0; simpl in *.
        apply (snd (iso_from_to ((a, F a); id[F a]))).
      - simpl; cat; simpl; cat.
          destruct projF_commutes0; simpl in *.
          rewrite (fst (iso_to_from ((a, F a); id[F a]))).
          simpl.
          destruct (Isomorphism.to fiber_iso0); simpl in *.
          rewrite (fst (@fmap_id _)).
          reflexivity.
        destruct projF_commutes0; simpl in *.
        rewrite (snd (iso_to_from ((a, F a); id[F a]))).
        simpl.
        destruct (Isomorphism.to fiber_iso0); simpl in *.
        rewrite (snd (@fmap_id _)).
        reflexivity.
    }
*)
    exact (fmap (snd (transform[from projF_commutes0] ((a, F a); id[F a])))
                ∘ projT2 (to fiber_iso0 ((a, F a); id[F a]))
                ∘ fst (transform[to projF_commutes0] ((a, F a); id[F a]))).

  - intro a.
    exact (snd (transform[from projG_commutes0] ((G a, a); id[G a]))
               ∘ projT2 (from fiber_iso0 ((G a, a); id[G a]))
               ∘ fmap (fst (transform[to projG_commutes0] ((G a, a); id[G a])))).

  - simpl; intros.
(*
  fmap[G] (fmap[F] f)
    ∘ fmap[G] (snd ((from projF_commutes0) ((X, F X); id[F X])))
    ∘ projT2 (to1 ((X, F X); id[F X]))
    ∘ fst (transform ((X, F X); id[F X]))
      ≈
      fmap[G] (snd (transform0 ((Y, F Y); id[F Y])))
    ∘ projT2 (to1 ((Y, F Y); id[F Y]))
    ∘ fst (transform ((Y, F Y); id[F Y]))
  ∘ f
*)
Abort.

End Lawvere.
