Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.

Generalizable All Variables.

(** Bifunctors (functors of two variables) *)

(* nLab: https://ncatlab.org/nlab/show/bifunctor
   Wikipedia: https://en.wikipedia.org/wiki/Bifunctor

   A bifunctor is just a functor F : C ∏ D ⟶ E out of a product category, so we
   do not formalize it as a separate structure; we only provide helpers for the
   action of such an F on pairs of arrows.  The central helper is [bimap f g],
   the lift of (f, g) through F.  A functor on C ∏ D is equivalent to giving two
   "partial" actions, one in each variable, that are separately functorial and
   compatible via the interchange (middle-four exchange) law

     bimap (f ∘ h) (g ∘ i) ≈ bimap f g ∘ bimap h i    ([bimap_comp]),

   together with bimap id id ≈ id ([bimap_id_id]).  The two "swap" forms of
   interchange, bimap f id ∘ bimap id g ≈ bimap f g and its mirror, are recorded
   as [bimap_id_right_left] / [bimap_id_left_right].  Currying a bifunctor
   C ∏ D ⟶ E into C ⟶ [D, E] is exhibited concretely for the hom-bifunctor by
   [Curried_Hom] in Functor/Hom.v; the prototypical bifunctor, the tensor ⊗,
   appears in Structure/Monoidal. *)

Section Bifunctor.

Context {C : Category}.
Context {D : Category}.
Context {E : Category}.

(* A bimap takes two arrows in C and D, and lifts them to an arrow in E over
   some bifunctor F : C ∏ D ⟶ E. *)
Definition bimap {F : C ∏ D ⟶ E} {x w : C} {y z : D}
           (f : x ~{C}~> w) (g : y ~{D}~> z) :
  F (x, y) ~{E}~> F (w, z) := @fmap (C ∏ D) E F (x, y) (w, z) (f, g).

(* [bimap] is definitionally [fmap] on a pair; this folds the [fmap] notation
   back into [bimap] during rewriting.  The equality is Leibniz (=), not ≈,
   because both sides are the very same term. *)
Corollary bimap_fmap {F : C ∏ D ⟶ E} {x w : C} {y z : D}
      (f : x ~{C}~> w) (g : y ~{D}~> z) :
  @fmap (C ∏ D) E F (x, y) (w, z) (f, g) = bimap f g.
Proof. reflexivity. Defined.

#[export] Program Instance bimap_respects {F : C ∏ D ⟶ E} {x w : C} {y z : D} :
  Proper (equiv ==> equiv ==> equiv) (@bimap F x w y z).
Next Obligation.
  proper.
  unfold bimap.
  apply fmap_respects.
  split; assumption.
Qed.

Lemma bimap_id_id {F : C ∏ D ⟶ E} {x y} :
  bimap (id[x]) (id[y]) ≈ id.
Proof.
  destruct F; simpl.
  apply fmap_id.
Qed.

(* Interchange (middle-four exchange): F preserves composition in both
   variables simultaneously. *)
Lemma bimap_comp {F : C ∏ D ⟶ E} {x y z w u v}
      (f : y ~{C}~> z) (h : x ~{C}~> y)
      (g : v ~{D}~> w) (i : u ~{D}~> v) :
  bimap (f ∘ h) (g ∘ i) ≈ bimap f g ∘ bimap h i.
Proof.
  unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects.
  reflexivity.
Qed.

(* Functoriality of the partial functor F(w, -) in the second variable. *)
Lemma bimap_comp_id_left {F : C ∏ D ⟶ E} {w}
      `(f : y ~{D}~> z) `(g : x ~{D}~> y) :
  bimap (id[w]) (f ∘ g) ≈ bimap id f ∘ bimap id g.
Proof.
  unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects.
  split; simpl; cat.
Qed.

(* Functoriality of the partial functor F(-, w) in the first variable. *)
Lemma bimap_comp_id_right {F : C ∏ D ⟶ E} {w}
      `(f : y ~{C}~> z) `(g : x ~{C}~> y) :
  bimap (f ∘ g) (id[w]) ≈ bimap f id ∘ bimap g id.
Proof.
  unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects.
  split; simpl; cat.
Qed.

(* Interchange, swap form: acting first in D then in C agrees with the joint
   action.  Together with [bimap_id_left_right] this expresses that the two
   partial actions commute (the middle-four exchange). *)
Lemma bimap_id_right_left {F : C ∏ D ⟶ E} {w}
      `(f : z ~{C}~> w) `(g : x ~{D}~> y) :
  bimap f id ∘ bimap id g ≈ bimap f g.
Proof.
  unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects.
  split; simpl; cat.
Qed.

(* Interchange, swap form: acting first in C then in D agrees with the joint
   action (mirror of [bimap_id_right_left]). *)
Lemma bimap_id_left_right {F : C ∏ D ⟶ E} {w}
      `(f : z ~{D}~> w) `(g : x ~{C}~> y) :
  bimap id f ∘ bimap g id ≈ bimap g f.
Proof.
  unfold bimap.
  rewrite <- fmap_comp.
  apply fmap_respects.
  split; simpl; cat.
Qed.

(* A bifunctor preserves isomorphisms in each variable: isomorphic inputs in
   both factors yield isomorphic objects in E, with bimap of the component
   isos as the witness. *)
#[export] Program Instance bifunctor_respects {F : C ∏ D ⟶ E} :
  Proper ((fun p q => Isomorphism (fst p) (fst q) ∧
                      Isomorphism (snd p) (snd q))
            ==> Isomorphism) F.
Next Obligation.
  proper; simpl in *.
  isomorphism.
  - exact (bimap X H).
  - exact (bimap (X⁻¹) (H⁻¹)).
  - rewrite <- bimap_comp.
    rewrite !iso_to_from.
    rewrite bimap_id_id.
    reflexivity.
  - rewrite <- bimap_comp.
    rewrite !iso_from_to.
    rewrite bimap_id_id.
    reflexivity.
Defined.

End Bifunctor.

Notation "bimap[ F ]" := (@bimap _ _ _ F%functor _ _ _ _)
  (at level 9, format "bimap[ F ]") : morphism_scope.

#[export] Hint Rewrite @bimap_id_id : categories.

Ltac bimap_left :=
  apply bimap_respects; [reflexivity|].

Ltac bimap_right :=
  apply bimap_respects; [|reflexivity].

Ltac normal :=
  repeat
    match goal with
    | [ |- context [?F ∘ (?G ∘ ?H)] ] =>
      rewrite (comp_assoc F G H)

    | [ |- context [fmap[?F] ?G ∘ fmap[?F] _] ] =>
      rewrite <- (@fmap_comp _ _ F _ _ _ G)

    | [ |- context [fmap[?F] id] ] =>
      rewrite <- (@fmap_id _ _ F)

    | [ |- context [bimap ?F _ ∘ bimap _ _] ] =>
      rewrite <- (bimap_comp F)
    | [ |- context [(?F ∘ bimap ?G _) ∘ bimap _ _] ] =>
      rewrite <- (comp_assoc F (bimap _ _));
      rewrite <- (bimap_comp G)

    | [ |- context [id ∘ ?F] ] => rewrite (id_left F)
    | [ |- context [?F ∘ id] ] => rewrite (id_right F)

    | [ |- context [bimap id id] ] =>
      rewrite bimap_id_id
    | [ |- context [bimap ?F id ∘ bimap id ?G] ] =>
      rewrite (bimap_id_right_left F)
    | [ |- context [bimap id ?F ∘ bimap ?G id] ] =>
      rewrite (bimap_id_left_right F G)

    | [ H : context [fmap[?F] ?G ∘ fmap[?F] _] |- _ ] =>
      rewrite <- (@fmap_comp _ _ F _ _ _ G) in H
    | [ H : context [bimap ?F id ∘ bimap id ?G] |- _ ] =>
      rewrite (bimap_id_right_left F) in H
    | [ H : context [bimap id ?F ∘ bimap ?G id] |- _ ] =>
      rewrite (bimap_id_left_right F G) in H
    | [ H : context [bimap ?F _ ∘ bimap _ _] |- _ ] =>
      rewrite <- (bimap_comp F) in H
    | [ H : context [(?F ∘ bimap ?G _) ∘ bimap _ _] |- _ ] =>
      rewrite <- (comp_assoc F (bimap _ _)) in H;
      rewrite <- (bimap_comp G) in H
    | [ H : context [id ∘ ?F] |- _ ] => rewrite (id_left F) in H
    | [ H : context [?F ∘ id] |- _ ] => rewrite (id_right F) in H
    end.
