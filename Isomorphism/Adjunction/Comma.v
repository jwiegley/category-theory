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

Theorem iso_commas_impl {A B C D}
        {S : A ⟶ C} {T : B ⟶ C} {U : A ⟶ D} {V : B ⟶ D}
        (iso : S ↓ T ≅[Cat] U ↓ V) (x : S ↓ T) :
  ` (fobj[to iso] x) ≅[A ∏ B] `x.
Proof.
  destruct iso; simpl in *;
  autounfold in *; simpl in *;
  destruct x, x; simpl in *;
  unfold Comma in *; simpl in *;
  destruct to, from; simpl in *.
Admitted.

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

Theorem Lawvere_Adjunction :
  F ⊣ G  <-->  (F ↓ Identity) ≅[Cat] (Identity ↓ G).
Proof.
  split; intros H. {

    given (to : (F ↓ Identity) ~{Cat}~> (Identity ↓ G)).
    Unshelve. all:swap 1 2. {

      given (fobj : F ↓ Identity -> Identity ↓ G).
      Unshelve. all:swap 1 2. {
        destruct 1 as [x ?]; exists x.
        apply H; assumption.
      }

      given (fmap : ∀ X Y, X ~> Y -> fobj X ~> fobj Y).
      Unshelve. all:swap 1 2.
        destruct X, Y; auto.

      assert (∀ X Y, Proper (equiv ==> equiv) (fmap X Y))
        by (destruct X, Y; auto).

      assert (∀ X, fmap X X (id[X]) ≈ id)
        by (destruct X; cat).

      assert (∀ X Y Z f g, fmap X Z (f ∘ g) ≈ fmap Y Z f ∘ fmap X Y g)
        by (destruct X, Y, Z; cat).

      econstructor; eauto.
    }

    given (from : (Identity ↓ G) ~{Cat}~> (F ↓ Identity)).
    Unshelve. all:swap 1 2. {

      given (fobj : Identity ↓ G -> F ↓ Identity).
      Unshelve. all:swap 1 2. {
        destruct 1 as [x ?]; exists x.
        apply H; assumption.
      }

      given (fmap : ∀ X Y, X ~> Y -> fobj X ~> fobj Y).
      Unshelve. all:swap 1 2.
        destruct X, Y; auto.

      assert (∀ X Y, Proper (equiv ==> equiv) (fmap X Y))
        by (destruct X, Y; auto).

      assert (∀ X, fmap X X (id[X]) ≈ id)
        by (destruct X; cat).

      assert (∀ X Y Z f g, fmap X Z (f ∘ g) ≈ fmap Y Z f ∘ fmap X Y g)
        by (destruct X, Y, Z; cat).

      econstructor; eauto.
    }

    assert (from ∘ to ≈ id) as from_to. {
      unfold from, to; clear from to; simpl.
      autounfold; simpl; intro X.
      destruct X; simpl.
      exists (id, id).
      exists (id, id).
      simpl; cat.
    }

    assert (to ∘ from ≈ id). {
      unfold to, from; clear from_to to from; simpl.
      autounfold; simpl; intro X.
      destruct X; simpl.
      exists (id, id).
      exists (id, id).
      simpl; cat.
    }

    econstructor; eauto.
  }

  given (adj_iso : ∀ a b, F a ~{C}~> b ≊ a ~{D}~> G b).
  Unshelve. all:swap 1 2. {

    given (to : ∀ a b,
              {| carrier := F a ~{C}~> b |}
                ~{Sets}~> {| carrier := a ~{D}~> G b |}).
    Unshelve. all:swap 1 2. {

      given (to' : ∀ a b, F a ~{ C }~> b -> a ~{ D }~> G b).
      Unshelve. all:swap 1 2. {
        intros a b f.
        pose proof (iso_commas_impl H) as X.
        pose (existT (fun p => F (fst p) ~> snd p) (a, b) f) as g.
        exact (fmap (snd (to (X g)))
                 ∘ projT2 (fobj[to H] g)
                 ∘ fst (from (X g))).
      }

      assert (∀ a b, Proper (equiv ==> equiv) (to' a b)).
        admit.

      econstructor; eauto.
    }

    given (from : ∀ a b,
              {| carrier := a ~{D}~> G b |}
                ~{Sets}~> {| carrier := F a ~{C}~> b |}).
    Unshelve. all:swap 1 2. {

      given (from' : ∀ a b, a ~{ D }~> G b -> F a ~{ C }~> b).
      Unshelve. all:swap 1 2. {
        admit.
      }

      assert (∀ a b, Proper (equiv ==> equiv) (from' a b)).
        admit.

      econstructor; eauto.
    }

    assert (∀ a b, from a b ∘ to a b ≈ id). {
      admit.
    }

    assert (∀ a b, to a b ∘ from a b ≈ id). {
      admit.
    }

    econstructor; eauto.
  }

  assert (∀ a b c f g,
             (to (adj_iso a c)) (f ∘ fmap g) ≈ (to (adj_iso b c)) f ∘ g). {
    admit.
  }

  assert (∀ a b c f g,
             (to (adj_iso a c)) (f ∘ g) ≈ fmap f ∘ (to (adj_iso a b)) g). {
    admit.
  }

  assert (∀ a b c f g,
             (from (adj_iso a c)) (f ∘ g) ≈ (from (adj_iso b c)) f ∘ fmap g). {
    admit.
  }

  assert (∀ a b c f g,
             (from (adj_iso a c)) (fmap f ∘ g) ≈ f ∘ (from (adj_iso a b)) g). {
    admit.
  }

  econstructor; auto.
Abort.

End Lawvere.
