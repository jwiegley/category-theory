Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Product.
Require Export Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Program Instance Diagonal {C : Category} (J : Category) : C ⟶ [J, C] := {
  fobj := fun x =>
    {| fobj := fun _ => x
     ; fmap := fun _ _ _ => id[x] |};
  fmap := fun _ _ f =>
    {| transform := fun _ => f |}
}.

Program Instance Diagonal_Product `(C : Category) : C ⟶ C ∏ C.

Notation "Δ( C )" := (@Diagonal_Product C)
  (at level 90, format "Δ( C )") : category_scope.

Require Export Category.Instance.One.

Program Instance Const {C : Category} (c : C) : 1 ⟶ C := Diagonal 1 c.

(* Wikipedia: "In category theory, a branch of mathematics, the diagonal
   functor C → C × C is given by Δ(a) = ⟨a, a⟩, which maps objects as well as
   morphisms. This functor can be employed to give a succinct alternate
   description of the product of objects within the category C: a product a ×
   b is a universal arrow from Δ to ⟨a, b⟩. The arrow comprises the projection
   maps."

  "More generally, in any functor category Cᴶ (here J should be thought of as
  a small index category), for each object a in C, there is a constant functor
  with fixed object a : Δ(a) ∈ Cᴶ. The diagonal functor Δ : C → Cᴶ assigns to
  each object of C the functor Δ(a), and to each morphism f : a → b in C the
  obvious natural transformation η in Cᴶ (given by ηⱼ = f). In the case that J
  is a discrete category with two objects, the diagonal functor C → C × C is
  recovered." *)

Require Export Category.Instance.Two.Discrete.

Theorem Diagonal_Product_Two (C : Category) :
  (∀ x, Diagonal_Product C x ≅ (Diagonal Two_Discrete x TwoDX,
                                Diagonal Two_Discrete x TwoDY)) *
  (∀ x y (f : x ~> y),
     fmap[Diagonal_Product C] f
       ≈ (transform[fmap[Diagonal Two_Discrete] f] TwoDX,
          transform[fmap[Diagonal Two_Discrete] f] TwoDY)).
Proof.
  split; intros.
    isomorphism; simpl; intros; try exact (id, id); cat.
  reflexivity.
Qed.

(* jww (2017-04-13): TODO
Program Instance Const_Transport `(C : Category) `(J : Category)
    `(x ~{C}~> y) : @Natural J C (@Const C J x) (@Const C J y).
Obligation 2.
  rewrite left_identity.
  rewrite right_identity.
  unfold Const_Transport_obligation_1.
  reflexivity.
Qed.

Program Instance Delta {C : Category} {J : Category} : C ⟶ [J, C] := {
    fobj := @Const C J
}.
Obligation 1.
  apply Const_Transport.
  assumption.
Qed.
Obligation 2.
  unfold Delta_obligation_1.
  unfold Const_Transport.
  unfold Const_Transport_obligation_1.
  unfold Const_Transport_obligation_2.
  apply nat_irrelevance.
  extensionality e.
  reflexivity.
Qed.
Obligation 3.
  unfold Delta_obligation_1.
  unfold Const_Transport.
  unfold Const_Transport_obligation_1.
  unfold Const_Transport_obligation_2.
  apply nat_irrelevance.
  extensionality e.
  reflexivity.
Qed.

Class Complete `(C : Category) := {
  complete : ∀ (J : Category), ∃ Lim : [J, C] ⟶ C, @Delta C J ⊣ Lim
}.

Program Definition Sets_Const_Nat (J : Category) (F : [J, Sets])
  (a : Type) (f : a → ∀ x : J, F x) : @Const Sets J a ⟾ F.
Obligation 2.
  extensionality e.
  unfold Sets_Const_Nat_obligation_1.
  remember (f e) as j.
  destruct F. simpl. clear.
  destruct J.
  crush. clear.
  (* jww (2014-08-12): We don't believe this is true. *)

Program Instance Sets_Const_Lim_Iso (J : Category) (a : Sets) (F : [J, Sets])
  : @Isomorphism Sets (Const a ⟾ F) (a → Lim_Sets J F).
Obligation 1.
  destruct F. simpl.
  destruct X.
  apply transport0.
  auto.
Qed.
Obligation 2.
  apply Sets_Const_Nat.
  auto.
Qed.
Obligation 3.
  extensionality e.
  unfold Sets_Const_Lim_Iso_obligation_1.
  unfold Sets_Const_Lim_Iso_obligation_2.
  extensionality f.
  extensionality g.
  destruct F. simpl.
  unfold Sets_Const_Nat_obligation_1.
  reflexivity.
Qed.
Obligation 4.
  extensionality e.
  unfold Sets_Const_Lim_Iso_obligation_1.
  unfold Sets_Const_Lim_Iso_obligation_2.
  unfold Sets_Const_Nat.
  destruct e.
  unfold Sets_Const_Nat_obligation_1.
  unfold Sets_Const_Nat_obligation_2.
  apply nat_irrelevance.
  extensionality f.
  extensionality g.
  destruct F. simpl.
  reflexivity.
Qed.

Program Instance Sets_Complete : Complete Sets.
Obligation 1.
  exists (Lim_Sets J).
  apply Build_Adjunction.
  intros. simpl.
  apply Sets_Const_Lim_Iso.
Qed.
*)
