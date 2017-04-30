Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Instance.Sets.
Require Export Category.Instance.Nat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.
Set Implicit Arguments.

Section FunctorEquiv.

Context `{C : Category}.
Context `{D : Category}.

Global Program Instance fobj_respects `{F : C ⟶ D} :
  Proper (equiv ==> equiv) (@fobj C D F).
Next Obligation.
  proper.
  destruct F, X; simpl.
  refine {| to   := fmap x y to
          ; from := fmap y x from |}.
    rewrite <- fmap_comp, iso_to_from; cat.
  rewrite <- fmap_comp, iso_from_to; cat.
Qed.

Global Program Instance fobj_setoid `{F : C ⟶ Sets} {A : C} : Setoid (F A).

(* The Identity Functor *)

Global Program Instance Identity : C ⟶ C := {
  fobj := fun X => X;
  fmap := fun _ _ f => f
}.

End FunctorEquiv.

Arguments Identity {C} /.

(* Horizontal composition of functors. *)

Program Definition functor_comp
        `{C : Category} `{D : Category} `{E : Category}
        (F : D ⟶ E) (G : C ⟶ D) : C ⟶ E := {|
  fobj := fun x => fobj (fobj x);
  fmap := fun _ _ f => fmap (fmap f)
|}.
Next Obligation.
  proper.
  rewrite X0; reflexivity.
Qed.
Next Obligation.
  intros; rewrite !fmap_comp; reflexivity.
Qed.

Hint Unfold functor_comp.

Infix "○" := functor_comp (at level 30, right associativity) : category_scope.

Ltac constructive :=
  unshelve (refine {| to := _; from := _ |}; simpl);
  simpl; intros;
  [ unshelve (refine {| transform := _ |}; simpl; intros);
    simpl; intros
  | unshelve (refine {| transform := _ |}; simpl; intros);
    simpl; intros
  | .. ]; simpl; intros.

(* Cat is the category of all small categories:

    objects               Categories
    arrows                Functors
    arrow equivalence     Natural Isomorphisms
    identity              Identity Functor
    composition           Horizontal composition of Functors *)

Program Instance Cat : Category := {
  ob      := Category;
  hom     := @Functor;
  homset  := fun _ _ => {| equiv := fun F G => F ≅[Nat] G |};
  id      := @Identity;
  compose := @functor_comp
}.
Next Obligation.
  equivalence.
  transitivity y; auto.
Qed.
Next Obligation.
  proper.
  constructive.
  all:swap 2 3.
  - apply (transform[to X0] (y0 X2) ∘ fmap (transform[to X1] X2)).
  - apply (transform[from X0] (x0 X2) ∘ fmap (transform[from X1] X2)).
  - rewrite <- !comp_assoc.
    rewrite <- fmap_comp.
    rewrite <- !natural_transformation.
    rewrite !fmap_comp.
    rewrite comp_assoc.
    reflexivity.
  - rewrite <- !comp_assoc.
    rewrite <- fmap_comp.
    rewrite <- !natural_transformation.
    rewrite !fmap_comp.
    rewrite comp_assoc.
    reflexivity.
  - simplify equiv; intros; simplify equiv.
    destruct X0 as [to0 from0 iso_to_from0 ?];
    destruct X1 as [to1 from1 iso_to_from1 ?]; simpl in *.
    simplify equiv in iso_to_from0.
    simplify equiv in iso_to_from1.
    rewrite <- natural_transformation.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (transform[to0] _)).
    rewrite iso_to_from0; cat.
    rewrite <- fmap_comp.
    rewrite iso_to_from1; cat.
  - simplify equiv; intros; simplify equiv.
    destruct X0 as [to0 from0 ? iso_from_to0 ?];
    destruct X1 as [to1 from1 ? iso_from_to1 ?]; simpl in *.
    simplify equiv in iso_from_to0.
    simplify equiv in iso_from_to1.
    rewrite <- natural_transformation.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (transform[from0] _)).
    rewrite iso_from_to0; cat.
    rewrite <- fmap_comp.
    rewrite iso_from_to1; cat.
Qed.
Next Obligation.
  simplify equiv.
  constructive.
  all:swap 2 3;try exact (fmap id).
  all:simplify equiv; intros; simplify equiv; cat.
Qed.
Next Obligation.
  simplify equiv.
  constructive.
  all:swap 2 3;try exact (fmap id).
  all:simplify equiv; intros; simplify equiv; cat.
Qed.
Next Obligation.
  simplify equiv.
  constructive.
  all:swap 2 3;try exact (fmap id).
  all:simplify equiv; intros; simplify equiv; cat.
Qed.
