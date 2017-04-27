Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Implicit Arguments.

Section FunctorEquiv.

Context `{C : Category}.
Context `{D : Category}.

Global Program Instance fobj_respects `{F : C ⟶ D} {A : C} :
  Proper (equiv ==> equiv) (@fobj C D F).
Next Obligation.
  proper.
  destruct F; simpl in *.
  destruct H as [to [from [to_from from_to]]]; simpl in *.
  exists (fmap x y to), (fmap y x from).
  rewrite <- fmap_comp, to_from; cat.
  rewrite <- fmap_comp, from_to; cat.
Qed.

Global Program Instance fobj_setoid `{F : C ⟶ Sets} {A : C} : Setoid (F A).

Definition functor_equiv : relation (C ⟶ D) :=
  fun F G => (∀ X : C, F X ≃ G X)%type.

Global Program Definition functor_equiv_equivalence :
  Equivalence functor_equiv.
Proof.
  unfold functor_equiv.
  equivalence.
  - symmetry; apply H.
  - transitivity (y X); auto.
Qed.

Global Program Instance functor_setoid : Setoid (C ⟶ D) := {
  equiv := functor_equiv;
  setoid_equiv := functor_equiv_equivalence
}.

(* The Identity Functor *)

Global Program Instance Identity : C ⟶ C := {
  fobj := fun X => X;
  fmap := fun _ _ f => f
}.

End FunctorEquiv.

Arguments Identity {C} /.

Hint Unfold functor_equiv.

(* Horizontal composition of functors. *)

Program Definition functor_comp
        `{C : Category} `{D : Category} `{E : Category}
        (F : D ⟶ E) (G : C ⟶ D) : C ⟶ E := {|
  fobj := fun x => fobj (fobj x);
  fmap := fun _ _ f => fmap (fmap f)
|}.
Next Obligation.
  proper.
  rewrite H; reflexivity.
Qed.
Next Obligation.
  intros.
  rewrite !fmap_comp.
  reflexivity.
Qed.

Infix "○" := functor_comp (at level 30, right associativity) : category_scope.

Program Instance Cat : Category := {
  ob      := Category;
  hom     := @Functor;
  homset  := @functor_setoid;
  id      := @Identity;
  compose := @functor_comp
}.
Next Obligation.
  proper.
  unfold functor_equiv in *.
  destruct (H (x0 X0)) as [to [from [to_from from_to]]].
  destruct (H0 X0) as [to0 [from0 [to_from0 from_to0]]].
  exists (fmap to0 ∘ to), (from ∘ fmap from0).
  rewrite <- comp_assoc.
  rewrite (comp_assoc to), to_from; cat.
  rewrite <- fmap_comp, to_from0; cat.
  rewrite <- comp_assoc, (comp_assoc (fmap from0)).
  rewrite <- fmap_comp, from_to0; cat.
Qed.
