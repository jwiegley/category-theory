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
   introducing comma categories." *)

Context `{C : Category}.
Context `{D : Category}.
Context `{G : C ⟶ D}.
Context `{F : D ⟶ C}.

Record fibered_equivalence := {
  fiber_iso : (F ↓ Id[C]) ≅[Cat] (Id[D] ↓ G);

  fiber_iso_mor {a b} : F a ~> b ≊ a ~> G b
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

    constructor.
      econstructor; eauto.
    simpl; intros.
    isomorphism; simpl.
    - morphism.
    - morphism.
    - simpl; apply adj_left_right.
    - simpl; apply adj_right_left.
  }

  destruct H as [H iso_to iso_from].
  unshelve (eapply adj_from_unit_conuit).

  - intros.
    apply iso_to.
    exact id.

  - intros.
    apply iso_to.
    exact id.

  - simpl; intros.
    destruct (iso_to X (F X)); simpl in *.
    destruct (iso_to Y (F Y)); simpl in *.
Abort.

End Lawvere.
