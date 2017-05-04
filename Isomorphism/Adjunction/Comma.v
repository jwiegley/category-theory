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

   "∀ (G : C ⟶ D) (F : D ⟶ C),
      F ⊣ G
      <-->
      ∀ d : D,
        { c : C
        & { phi : d ~{D}~> G c)
          & ∀ (c′ : C) (psi : d ~{D}~> G c′),
            { y : c ~{C}~> c′
            & uniqueT (fun x => psi ≈ fmap[G] x ∘ phi) y } }." *)

Context `{C : Category}.
Context `{D : Category}.
Context `{G : C ⟶ D}.
Context `{F : D ⟶ C}.

Definition uniqueT (A : Type) (P : A -> Type) (x : A) :=
  P x * ∀ x' : A, P x' -> x = x'.

Record fibered_equivalence := {
  fiber_iso : (F ↓ Id[C]) ≅[Cat] (Id[D] ↓ G);

  projG_commutes : comma_proj ≈[Cat] comma_proj ○ from fiber_iso;
  projF_commutes : comma_proj ≈[Cat] comma_proj ○ to fiber_iso
}.

Lemma fiber_projT2 (a : D) (b c : C) g (f : G b ~> G c) :
  f ∘ projT2 (((a, b); g) : (Id[D] ↓ G)) ≈
    projT2 (((a, c); f ∘ g) : (Id[D] ↓ G)).
Proof. reflexivity. Qed.

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
    exact (fmap (snd (transform[from projF_commutes0] ((a, F a); id[F a])))
                ∘ projT2 (to fiber_iso0 ((a, F a); id[F a]))
                ∘ fst (transform[to projF_commutes0] ((a, F a); id[F a]))).

  - intro a.
    exact (snd (transform[from projG_commutes0] ((G a, a); id[G a]))
               ∘ projT2 (from fiber_iso0 ((G a, a); id[G a]))
               ∘ fmap (fst (transform[to projG_commutes0] ((G a, a); id[G a])))).

  - simpl; intros.

Abort.

End AdjunctionComma.
