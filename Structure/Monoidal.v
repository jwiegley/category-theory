Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Product.
Require Export Category.Instance.Nat.
Require Export Category.Instance.Cat.
Require Export Category.Instance.Cat.Closed.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Monoidal.

Context `{C : Category}.

Reserved Infix "⨂" (at level 30, right associativity).

Class Monoidal := {
  tensor : C ⟶ [C, C]           (* uncurried = C ∏ C ⟶ C *)
    where "x ⨂ y" := (tensor x y);

  munit : C;

  unit_left  {X} : munit ⨂ X ≅ X;
  unit_right {X} : X ⨂ munit ≅ X;

  tensor_assoc {X Y Z} : (X ⨂ Y) ⨂ Z ≅ X ⨂ (Y ⨂ Z)
}.

Infix "⨂" := tensor (at level 30, right associativity).

Class SymmetricMonoidal `{Monoidal} := {
  swap {X Y} : X ⨂ Y ≅ Y ⨂ X
}.

End Monoidal.

Infix "⨂" := (@tensor _ _) (at level 30, right associativity).

Definition functor_precomp {C D E} (G : C ⟶ D) (F : D ⟶ E) := functor_comp F G.

Section MonoidalFunctor.

(* λ (C D E : Category) (F : D ⟶ E) (G : C ⟶ D), *)

Context `{C : Category}.
Context `{D : Category}.
Context `{@Monoidal C}.
Context `{@Monoidal D}.
Context `{F : C ⟶ D}.

(* A lax monoidal functor's natural transformation can be projected to a
   morphism between objects in D. This forgets the naturality of the
   transformation, which is why it is only provided as a convenience
   definition below in [LaxMonoidalFunctor]. *)

Class LaxMonoidalFunctor := {
  pure : munit ~> F munit;

  ap_functor_nat :
    (@functor_comp (C × C) (D × D) D (uncurry (@tensor D _)) (split F F))
      ~{[C × C, D]}~>
    (@functor_comp (C × C) C D F (uncurry (@tensor C _)));

  ap {X Y} : F X ⨂ F Y ~> F (X ⨂ Y) := transform[ap_functor_nat] (X, Y);

  pure_left {X}  : munit ⨂ F X ≈ F (munit ⨂ X);
  pure_right {X} : F X ⨂ munit ≈ F (X ⨂ munit);

  ap_assoc {X Y Z} : (F X ⨂ F Y) ⨂ F Z ≈ F (X ⨂ (Y ⨂ Z))
}.

(* The strong monoidal functor isomorphism can be projected to an isomorphism
   between objects in D. This forgets the naturality of the original natural
   isomorphism, which is why it is only provided as a convenience definition
   below in [StrongMonoidalFunctor]. *)

Program Definition project_monoidal_iso
        (iso : (@functor_comp (C × C) (D × D) D
                              (uncurry (@tensor D _)) (split F F))
                 ≅[[C × C, D]]
               (@functor_comp (C × C) C D F (uncurry (@tensor C _))))
        (X Y : C) :
  F X ⨂ F Y ≅[D] F (X ⨂ Y) := {|
  to   := to   iso (X, Y);
  from := from iso (X, Y)
|}.
Next Obligation.
  rewrite (iso_to_from iso (X, Y)); simpl.
  rewrite fmap_id; cat.
  pose proof (@fmap_id _ _ (@tensor C H)) as X1.
  simpl in X1; rewrite X1; cat.
Qed.
Next Obligation.
  rewrite (iso_from_to iso (X, Y)); simpl.
  rewrite fmap_id; cat.
  rewrite <- fmap_id.
  pose proof (@fmap_id _ _ (@tensor D H0) (F X) (F Y)) as X1.
  simpl in X1; rewrite <- X1.
  pose proof (@fmap_respects _ _ (@tensor D H0) _ _ (fmap[F] (id[X]))) as X3.
  simpl in X3; apply X3; cat.
Qed.

Class MonoidalFunctor := {
  pure_iso : munit ≅ F munit;

  ap_functor_iso :
    (@functor_comp (C × C) (D × D) D (uncurry (@tensor D _)) (split F F))
      ≅[[C × C, D]]
    (@functor_comp (C × C) C D F (uncurry (@tensor C _)));

  ap_iso {X Y} : F X ⨂ F Y ≅ F (X ⨂ Y) :=
    project_monoidal_iso ap_functor_iso X Y;

  pure_iso_left {X}  : munit ⨂ F X ≈ F (munit ⨂ X);
  pure_iso_right {X} : F X ⨂ munit ≈ F (X ⨂ munit);

  ap_iso_assoc {X Y Z} : (F X ⨂ F Y) ⨂ F Z ≈ F (X ⨂ (Y ⨂ Z))
}.

Program Definition MonoidalFunctor_Is_Lax (S : MonoidalFunctor) :
  LaxMonoidalFunctor := {|
  pure := to (@pure_iso S);
  ap_functor_nat := to (@ap_functor_iso S)
|}.
Next Obligation. apply pure_iso_left. Qed.
Next Obligation. apply pure_iso_right. Qed.
Next Obligation. apply ap_iso_assoc. Qed.

End MonoidalFunctor.

Class StrongFunctor `{C : Category} `{@Monoidal C} (F : C ⟶ C) := {
  strength {X Y} : X ⨂ F Y ~> F (X ⨂ Y)
}.

Class RightStrongFunctor `{C : Category} `{@Monoidal C} (F : C ⟶ C) := {
  right_strength {X Y} : F X ⨂ Y ~> F (X ⨂ Y)
}.

(* A strong lax monoidal functor is called an "applicative functor" in
   Haskell. *)

Set Warnings "-non-primitive-record".

Class StrongLaxMonoidalFunctor
      `{C : Category} `{@Monoidal C} (F : C ⟶ C)
      `{@StrongFunctor _ _ F} `{@LaxMonoidalFunctor _ _ _ _ F}.

(* Every cartesian category with terminal objects gives rise to a monoidal
   category taking the terminal object as unit, and the tensor as product. *)

Program Definition Product_Monoidal
        `{C : Category} `{@Cartesian C} `{@Terminal C} :
  @Monoidal C := {|
  tensor := curry (@ProductFunctor C _);
  munit := One
|}.
