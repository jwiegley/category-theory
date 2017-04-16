Require Import Category.Lib.
Require Export Category.Theory.Natural.
Require Import Category.Construct.Opposite.
Require Import Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Set Shrink Obligations.

(* Bifunctors can be curried:

  C × D ⟶ E --> C ⟶ [D, E] ~~~ (C, D) -> E --> C -> D -> E

Where ~~~ should be read as "Morally equivalent to".

Note: We do not need to define Bifunctors as a separate class, since they can
be derived from functors mapping to a category of functors. So in the
following two definitions, [P] is effectively our bifunctor.

The trick to [bimap] is that both the [Functor] instances we need (for [fmap]
and [fmap1]), and the [Natural] instance, can be found in the category of
functors we're mapping to by applying [P]. *)

Definition fmap1 `{P : C ⟶ [D, E]} {A : C} `(f : X ~{D}~> Y) :
  P A X ~{E}~> P A Y := fmap f.

Definition bimap `{P : C ⟶ [D, E]} {X W : C} {Y Z : D}
           (f : X ~{C}~> W) (g : Y ~{D}~> Z) :
  P X Y ~{E}~> P W Z := let N := @fmap _ _ P _ _ f in transform[N] _ ∘ fmap1 g.

Definition contramap `{F : C^op ⟶ D} `(f : X ~{C}~> Y) :
  F Y ~{D}~> F X := fmap (unop f).

Definition dimap `{P : C^op ⟶ [D, E]} `(f : X ~{C}~> W) `(g : Y ~{D}~> Z) :
  P W Y ~{E}~> P X Z := bimap (unop f) g.

Program Instance HomFunctor `(C : Category) : C^op ⟶ [C, Sets] := {
  fobj := fun X => {|
    fobj := fun Y => {| carrier := @hom C X Y
                          ; is_setoid := @homset C X Y |};
    fmap := fun Y Z (f : Y ~{C}~> Z) =>
              {| morphism := fun (g : X ~{C}~> Y) =>
                               (f ∘ g) : X ~{C}~> Z |}
  |};
  fmap := fun X Y (f : X ~{C^op}~> Y) => {|
    transform := fun _ => {| morphism := fun g => g ∘ unop f |}
  |}
}.
Next Obligation.
  intros ?? HA.
  rewrite HA; reflexivity.
Defined.
Next Obligation.
  intros ?? HA ?; simpl.
  rewrite HA; reflexivity.
Defined.
Next Obligation. cat. Defined.
Next Obligation.
  unfold Basics.compose.
  rewrite comp_assoc; reflexivity.
Defined.
Next Obligation.
  repeat intro; intuition.
Defined.
Next Obligation.
  unfold Basics.compose.
  rewrite comp_assoc; reflexivity.
Defined.
Next Obligation.
  repeat intro; intuition; simpl in *.
  unfold unop.
  rewrite X0; reflexivity.
Defined.
Next Obligation.
  intro; simpl; unfold unop; intros; cat.
Defined.
Next Obligation.
  intro; simpl; unfold unop, Basics.compose; intros.
  rewrite comp_assoc; reflexivity.
Defined.

Coercion HomFunctor : Category >-> Functor.

Notation "'Hom' ( A , ─ )" := (@HomFunctor _ A) : category_scope.

Program Instance CoHomFunctor `(C : Category) : C ⟶ [C^op, Sets] := {
  fobj := fun X => {|
    fobj := fun Y => {| carrier := @hom (C^op) X Y
                      ; is_setoid := @homset (C^op) X Y |};
    fmap := fun Y Z (f : Y ~{C^op}~> Z) =>
              {| morphism := fun (g : X ~{C^op}~> Y) =>
                               (f ∘ g) : X ~{C^op}~> Z |}
  |};
  fmap := fun X Y (f : X ~{C}~> Y) => {|
    transform := fun _ => {| morphism := fun g => g ∘ op f |}
  |}
}.
Next Obligation.
  intros ?? HA.
  rewrite HA; reflexivity.
Defined.
Next Obligation.
  intros ?? HA ?; simpl.
  rewrite HA; reflexivity.
Defined.
Next Obligation. cat. Defined.
Next Obligation.
  unfold Basics.compose.
  rewrite comp_assoc; reflexivity.
Defined.
Next Obligation.
  repeat intro; intuition.
Defined.
Next Obligation.
  unfold Basics.compose.
  rewrite comp_assoc; reflexivity.
Defined.
Next Obligation.
  repeat intro; intuition; simpl in *.
  unfold op.
  rewrite X0; reflexivity.
Defined.
Next Obligation.
  intro; simpl; unfold unop; intros; cat.
Defined.
Next Obligation.
  intro; simpl; unfold unop, Basics.compose; intros.
  rewrite comp_assoc; reflexivity.
Defined.

Coercion CoHomFunctor : Category >-> Functor.

Notation "'Hom' ( ─ , A )" := (@CoHomFunctor _ A) : category_scope.
