Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Cayley.

Context {C : Category}.

(* Given any category, the Cayley representation forces all associations to
   the left. *)
Program Instance Cayley_Representation : Category := {
  obj     := C;
  hom     := fun x y =>
    { f : ∀ r, (y ~> r) -> (x ~> r)
    & Proper (forall_relation (fun r => (equiv ==> equiv)%signature)) f ∧
      ∀ r k, f r k ≈ k ∘ f _ id[y] };
  homset  := fun x y =>
    {| equiv := fun f g => ∀ r k, `1 f r k ≈ `1 g r k |};
  id      := fun _ => (fun _ => Datatypes.id; _);
  compose := fun x y z f g  => (fun r k => `1 g r (`1 f r k); _)
}.
Next Obligation.
  equivalence.
  now rewrite X, X0.
Qed.
Next Obligation.
  split.
    proper.
  intros; cat.
Qed.
Next Obligation.
  split.
    proper.
    apply p.
    apply p0.
    apply X.
  intros.
  symmetry.
  rewrite e.
  rewrite comp_assoc.
  rewrite <- e0.
  rewrite <- e.
  reflexivity.
Qed.
Next Obligation.
  proper.
  simpl in *.
  rewrite H, H0.
  rewrite X.
  comp_left.
  apply X0.
Qed.

Program Instance To_Cayley : C ⟶ Cayley_Representation := {
  fobj := fun x => x;
  fmap := fun _ _ f => (fun _ k => k ∘ f; _);
}.
Next Obligation.
  proper.
  proper.
Qed.

Program Instance From_Cayley : Cayley_Representation ⟶ C := {
  fobj := fun x => x;
  fmap := fun x y f => `1 f y (@id C y);
}.

Context `{Cayley_Representation}.

(* No matter how we associate the mapped morphism, the functor back from
   Cayley returns them left-associated. *)

Lemma Cayley_Right (x y z w : C) (f : z ~> w) (g : y ~> z) (h : x ~> y) :
  (forall a b (k : a ~{C}~> b), id[b] ∘ k = k) ->
    f ∘ g ∘ h = fmap[From_Cayley]
                  (fmap[To_Cayley] f ∘ (fmap[To_Cayley] g
                                          ∘ fmap[To_Cayley] h)).
Proof.
  intros.
  simpl.
  rewrite H0.
  reflexivity.
Qed.

Lemma Cayley_Left (x y z w : C) (f : z ~> w) (g : y ~> z) (h : x ~> y) :
  (forall a b (k : a ~{C}~> b), id[b] ∘ k = k) ->
    f ∘ g ∘ h = fmap[From_Cayley]
                  (((fmap[To_Cayley] f ∘ fmap[To_Cayley] g)
                      ∘ fmap[To_Cayley] h)).
Proof.
  intros.
  simpl.
  rewrite H0.
  reflexivity.
Qed.
