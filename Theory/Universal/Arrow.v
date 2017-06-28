Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Unique.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section UniversalArrow.

Context `{C : Category}.
Context `{D : Category}.

Require Import Category.Structure.Initial.
Require Import Category.Construction.Comma.
Require Import Category.Functor.Diagonal.

(* A universal arrow is an initial object in the comma category (=(c) ↓ F). *)
Class UniversalArrow (c : C) (F : D ⟶ C) := {
  arrow_initial : @Initial (=(c) ↓ F);

  arrow_obj := snd (`1 (@initial_obj _ arrow_initial));
  arrow : c ~> F arrow_obj := `2 (@initial_obj _ arrow_initial)
}.

Notation "c ⟿ F" := (UniversalArrow c F) (at level 20) : category_theory_scope.

(* The following UMP follows directly from the nature of initial objects in a
   comma category. *)
Corollary ump_universal_arrows `(c ⟿ F) `(h : c ~> F d) :
  ∃! g : arrow_obj ~> d, h ≈ fmap[F] g ∘ arrow.
Proof.
  unfold arrow_obj, arrow; simpl.
  destruct (@zero _ arrow_initial ((tt, d); h)), x.
  simpl in *.
  rewrite id_right in e.
  exists h1.
    assumption.
  intros.
  rewrite <- id_right in e.
  rewrite <- id_right in X.
  exact (snd (@zero_unique _ arrow_initial ((tt, d); h)
                           ((tt, h1); e) ((tt, v); X))).
Qed.

End UniversalArrow.
