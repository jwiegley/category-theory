Require Import Lib.
Require Export Natural.
Require Import Opposite.
Require Import Coq.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

(*
Bifunctors can be curried:

  C × D ⟶ E   -->  C ⟶ [D, E]
  ~~~
  (C, D) -> E  -->  C -> D -> E

Where ~~~ should be read as "Morally equivalent to".

Note: We do not need to define Bifunctors as a separate class, since they can
be derived from functors mapping to a category of functors.  So in the
following two definitions, [P] is effectively our bifunctor.

The trick to [bimap] is that both the [Functor] instances we need (for [fmap]
and [fmap1]), and the [Natural] instance, can be found in the category of
functors we're mapping to by applying [P].
*)

Definition fmap1 `{P : C ⟶ [D, E]} {A : C} `(f : X ~{D}~> Y) :
  P A X ~{E}~> P A Y := fmap f.

Definition bimap `{P : C ⟶ [D, E]} {X W : C} {Y Z : D} (f : X ~{C}~> W) (g : Y ~{D}~> Z) :
  P X Y ~{E}~> P W Z := let N := @fmap _ _ P _ _ f in transform[N] _ ∘ fmap1 g.

Definition contramap `{F : C^op ⟶ D} `(f : X ~{C}~> Y) :
  F Y ~{D}~> F X := fmap (unop f).

Definition dimap `{P : C^op ⟶ [D, E]} `(f : X ~{C}~> W) `(g : Y ~{D}~> Z) :
  P W Y ~{E}~> P X Z := bimap (unop f) g.

Program Instance Hom `(C : Category) : C^op ⟶ [C, Coq] := {
  fobj := fun X : C^op =>
            {| fobj := fun Y : C => @hom C X Y
             ; fmap := fun (Y Z : C) (f : Y ~> Z) (g : X ~{C}~> Y) =>
                         (f ∘ g) : X ~{C}~> Z  |};
  fmap := fun _ _ f =>
            {| transform := fun _ g => g ∘ unop f |}
}.
Next Obligation.
  intros ????.
  (* jww (2017-04-14): I need to use a subcategory of Coq, call it Sets, since
     Coq's equivalence is too strong. *)
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
  unfold nat_identity.
Admitted.
Next Obligation.
  unfold nat_compose, nat_identity.
Admitted.
Next Obligation.
  unfold nat_compose, nat_identity.
Admitted.
Next Obligation.
  unfold nat_compose, nat_identity.
Admitted.

Coercion Hom : Category >-> Functor.
