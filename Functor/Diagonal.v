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

(* jww (2017-05-26): TODO

   Wikipedia: "Diagonal functors provide a way to define limits and colimits
   of functors. The limit of any functor F : J → C is a universal arrow Δ → F
   and a colimit is a universal arrow F → Δ. If every functor from J to C has
   a limit (which will be the case if C is complete), then the operation of
   taking limits is itself a functor from Cᴶ to C. The limit functor is the
   right-adjoint of the diagonal functor. Similarly, the colimit functor
   (which exists if the category is cocomplete) is the left-adjoint of the
   diagonal functor. For example, the diagonal functor C → C × C described
   above is the left-adjoint of the binary product functor and the
   right-adjoint of the binary coproduct functor." *)
