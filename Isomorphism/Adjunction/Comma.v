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
   adjoint if and only if the comma categories (F ↓ id D) and (id C ↓ G), with
   id D and id C the identity functors on D and C respectively, are
   isomorphic, and equivalent elements in the comma category can be projected
   onto the same element of C × D. This allows adjunctions to be described
   without involving sets, and was in fact the original motivation for
   introducing comma categories." *)

Context `{C : Category}.
Context `{D : Category}.
Context `{G : C ⟶ D}.
Context `{F : D ⟶ C}.

Definition fibered_equivalence :=
  { iso : (F ↓ C) ≅[Cat] (D ↓ G)
  & ∀ p f, `` (to   iso (p; f)) = p
  & ∀ p g, `` (from iso (p; g)) = p }.

Theorem Lawvere_Adjunction :
  F ⊣ G  <-->  fibered_equivalence.
Proof.
  split; intros H. {
    given (to : (F ↓ C) ~{Cat}~> (D ↓ G)). {

      given (fobj : F ↓ C -> D ↓ G). {
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

    given (from : (D ↓ G) ~{Cat}~> (F ↓ C)). {

      given (fobj : D ↓ G -> F ↓ C). {
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

    unshelve eexists.
    - econstructor; eauto.
    - simpl; intros; reflexivity.
    - simpl; intros; reflexivity.
  }

  destruct H as [H iso_to iso_from].
  unshelve (eapply adj_from_unit_conuit).

  - intros.
    pose (a, fobj[F] a) as p.
    pose (existT (fun p : D * C => F (fst p) ~{ C }~> snd p) p id) as FI.
    pose proof (iso_to p (projT2 FI)) as h; subst.
    pose (fobj[to H] FI) as IG.
    repeat unfold p, FI in *; simpl in *; clear p FI.
    pose (projT2 IG) as i; unfold IG in i; simpl in i; clear IG.
    rewrite h in i; simpl in i.
    exact i.

  - intros.
    pose (fobj[G] a, a) as p.
    pose (existT (fun p : D * C => fst p ~{ D }~> G (snd p)) p id) as IG.
    pose proof (iso_from p (projT2 IG)) as h; subst.
    pose (fobj[from H] IG) as FI.
    repeat unfold p, IG in *; simpl in *; clear p IG.
    pose (projT2 FI) as i; unfold FI in i; simpl in i; clear FI.
    rewrite h in i; simpl in i.
    exact i.

  - simpl; intros; clear.
    unfold eq_rect; simpl.
Abort.

End Lawvere.
