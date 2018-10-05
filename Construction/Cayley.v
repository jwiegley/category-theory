Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Cayley.

Context {C : Category}.

(* Given any category, the Cayley representation forces all associations to
   the left. *)
Program Instance Cayley : Category := {
  obj     := C;
  hom     := fun x y =>
    { f : ∀ r, (y ~> r) -> (x ~> r)
    & Proper (forall_relation (fun r => (equiv ==> equiv)%signature)) f ∧
      ∀ r k, f r k ≈ k ∘ f _ id[y] };
  homset  := fun x y => {| equiv := fun f g => ∀ r k, `1 f r k ≈ `1 g r k |};
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

Program Instance To_Cayley : C ⟶ Cayley := {
  fobj := fun x => x;
  fmap := fun _ _ f => (fun _ k => k ∘ f; _);
}.
Next Obligation.
  proper.
  proper.
Defined.

Program Instance From_Cayley : Cayley ⟶ C := {
  fobj := fun x => x;
  fmap := fun x y f => `1 f y (@id C y);
}.

Context `{Cayley}.

(* No matter how we associate the mapped morphisms, the functor back from
   Cayley yields them left-associated. *)

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

Program Instance Cayley_Cartesian `{CA : @Cartesian C} : @Cartesian Cayley := {
  product_obj := @product_obj C CA;
  fork := fun x y z f g =>
    let f' := to (Covariant_Yoneda_Embedding C x y) (_ f) in
    let g' := to (Covariant_Yoneda_Embedding C x z) (_ g) in
    _ f' g';
  exl := fun x y =>
    let f' := from (Covariant_Yoneda_Embedding C _ _) (@exl C CA x y) in
    _ f';
  exr := fun x y =>
    let f' := from (Covariant_Yoneda_Embedding C _ _) (@exr C CA x y) in
    _ f';
}.
Next Obligation.
  construct.
  - construct.
    + apply f.
      exact X.
    + proper.
      rewrite e1.
      rewrite X.
      rewrite <- e1.
      reflexivity.
  - simpl.
    rewrite e1.
    rewrite comp_assoc.
    rewrite <- e1.
    reflexivity.
  - simpl.
    rewrite e1.
    rewrite <- comp_assoc.
    rewrite <- e1.
    reflexivity.
Defined.
Next Obligation.
  construct.
  - construct.
    + apply g.
      exact X.
    + proper.
      rewrite e0.
      rewrite X.
      rewrite <- e0.
      reflexivity.
  - simpl.
    rewrite e0.
    rewrite comp_assoc.
    rewrite <- e0.
    reflexivity.
  - simpl.
    rewrite e0.
    rewrite <- comp_assoc.
    rewrite <- e0.
    reflexivity.
Defined.
Next Obligation.
  exists (fun r h => h ∘ x0 △ x1).
  split.
    proper.
  intros; cat.
Defined.
Next Obligation.
  destruct x0; simpl in *.
  exists (fun r h => transform r h).
  split.
    proper.
    now apply proper_morphism.
  intros.
  rewrite naturality.
  apply proper_morphism; cat.
Defined.
Next Obligation.
  destruct x0; simpl in *.
  exists (fun r h => transform r h).
  split.
    proper.
    now apply proper_morphism.
  intros.
  rewrite naturality.
  apply proper_morphism; cat.
Defined.
Next Obligation.
  proper; simpl in *.
  comp_left.
  apply fork_respects.
    apply X.
  apply X0.
Qed.
Next Obligation.
  proper; simpl in *.
  - rewrite X.
    rewrite <- comp_assoc.
    rewrite exl_fork.
    rewrite <- e1.
    reflexivity.
  - rewrite X.
    rewrite <- comp_assoc.
    rewrite exr_fork.
    rewrite <- e0.
    reflexivity.
  - rewrite <- X, <- H0.
    rewrite e.
    comp_left.
    rewrite (e _ (_ ∘ exl)).
    rewrite (e _ (_ ∘ exr)).
    cat.
    rewrite fork_comp.
    rewrite fork_exl_exr.
    cat.
Qed.

End Cayley.

Require Import Category.Functor.Structure.Cartesian.

Program Instance To_Cayley_CartesianFunctor `{@Cartesian C} :
  @CartesianFunctor _ _ To_Cayley _ Cayley_Cartesian.

Program Instance From_Cayley_CartesianFunctor `{@Cartesian C} :
  @CartesianFunctor _ _ From_Cayley Cayley_Cartesian _.
