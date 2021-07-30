Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section Closed.

Context {C : Category}.
Context {D : Category}.
Context {E : Category}.

Program Definition Curry (F : C^op ∏ D ⟶ E) : C^op ⟶ [D, E] := {|
  fobj := fun x => {|
    fobj := fun y => F (x, y);
    fmap := fun y z (f : y ~{D}~> z) => fmap[F] (id[x], f)
  |};
  fmap := fun x y (f : x ~{C^op}~> y) => {|
    transform := fun z => fmap[F] (f, id[z])
  |}
|}.
Next Obligation. now proper; simpl_eq; rewrite X. Qed.
Next Obligation. now rewrite <- fmap_comp; simpl; cat. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.
Next Obligation. now proper; rewrite X. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.

Program Definition Flip (F : C^op ∏ D ⟶ E) : D ∏ C^op ⟶ E := {|
  fobj := fun x => F (snd x, fst x);
  fmap := fun _ _ f => fmap[F] (snd f, fst f)
|}.
Next Obligation. now proper; simpl_eq; simpl in *; rewrite X, H. Qed.
Next Obligation. now rewrite <- fmap_comp. Qed.

Reserved Notation "[ X , Y ]"
  (at level 90, right associativity, format "[ X ,  Y ]").

(* jww (2018-10-05): TODO

Class Closed := {
  internal_hom_functor : C^op ∏ C ⟶ C
    where "[ X , Y ]" := (@internal_hom_functor (X, Y));
  unit_object : C;

  (* hom_id_iso  : Id[C] ≅[Fun] Curry internal_hom_functor unit_object; *)
  hom_id_iso {x} : x ≅ [unit_object, x];

  hom_id {x} : unit_object ~> [x, x];
  hom_compose {x y z} : [y, z] ~> [[x, y], [x, z]];

  hom_id_right {x y} :
    @hom_compose x y y ∘ hom_id << unit_object ~~> [[x, y], [x, y]] >> hom_id;

  hom_ {x y} :
    _ ∘ @hom_compose x x y
      << [x, y] ~~> [unit_object, [x, y]] >>
    to (hom_id_iso ([x, y]))
}.

Notation "[ X , Y ]" := (internal_hom_functor (X, Y))
  (at level 90, right associativity, format "[ X ,  Y ]") : object_scope.

Notation "[ X , ─ ]" := (Curry internal_hom_functor X)
  (at level 90, right associativity, format "[ X ,  ─ ]") : object_scope.

Notation "[ ─ , X ]" := (Curry (Flip internal_hom_functor) X)
  (at level 90, right associativity, format "[ ─ ,  X ]") : object_scope.

*)

End Closed.
