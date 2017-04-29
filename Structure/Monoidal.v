Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Construction.Product.
Require Export Category.Instance.Nat.
Require Export Category.Instance.Cat.

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

(*
Definition right_side : C ⟶ [C, D] :=
  transform F ∘ tensor.
*)

Class LaxMonoidalFunctor := {
  pure : munit ~> F munit;
  ap {X Y} : F X ⨂ F Y ~> F (X ⨂ Y);

  (* ap_natural {X Y Z W} (f : X ⨂ Y ~> Z ⨂ W) : *)
  (*   fmap[F] f ∘ ap ≈ ap ∘ fmap[F] f; *)

  pure_left {X}  : munit ⨂ F X ≈ F (munit ⨂ X);
  pure_right {X} : F X ⨂ munit ≈ F (X ⨂ munit);

  ap_assoc {X Y Z} : (F X ⨂ F Y) ⨂ F Z ≈ F (X ⨂ (Y ⨂ Z))
}.

(* also called OpLax *)
(* Class CoLaxMonoidalFunctor := { *)
  (* copure : munit <~ F munit; *)
  (* (* jww (2017-04-27): This needs to be a natural transformation *) *)
  (* coap {X Y} : F X ⨂ F Y <~ F (X ⨂ Y); *)

Class StrongMonoidalFunctor := {
  pure_iso : munit ≅ F munit;
  (* jww (2017-04-27): This needs to be a natural isomorphism *)
  ap_iso {X Y} : F X ⨂ F Y ≅ F (X ⨂ Y);

  pure_iso_left {X}  : munit ⨂ F X ≈ F (munit ⨂ X);
  pure_iso_right {X} : F X ⨂ munit ≈ F (X ⨂ munit);

  ap_iso_assoc {X Y Z} : (F X ⨂ F Y) ⨂ F Z ≈ F (X ⨂ (Y ⨂ Z))
}.

Program Definition StrongMonoidalFunctor_Is_Lax (S : StrongMonoidalFunctor) :
  LaxMonoidalFunctor := {|
  pure := to (@pure_iso S);
  ap := fun X Y => to (@ap_iso S X Y)
|}.
Next Obligation. apply pure_iso_left. Qed.
Next Obligation. apply pure_iso_right. Qed.
Next Obligation. apply ap_iso_assoc. Qed.

End MonoidalFunctor.

Class StrongFunctor `{C : Category} `{@Monoidal C} (F : C ⟶ C) := {
  strength {X Y} : X ⨂ F Y ≅ F (X ⨂ Y)
}.

Class RightStrongFunctor `{C : Category} `{@Monoidal C} (F : C ⟶ C) := {
  right_strength {X Y} : F X ⨂ Y ≅ F (X ⨂ Y)
}.

(* A strong lax monoidal functor is called an "applicative functor" in
   Haskell. *)

Set Warnings "-non-primitive-record".

Class StrongLaxMonoidalFunctor
      `{C : Category}
      `{@Monoidal C}
      (F : C ⟶ C)
      `{@StrongFunctor _ _ F}
      `{@LaxMonoidalFunctor _ _ _ _ F}.
