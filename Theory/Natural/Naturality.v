Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Naturality (A : Type) : Type := {
  natural (f : A) : Type
}.

Arguments natural {A _} _ /.

Program Instance Identity_Naturality `{C : Category} :
  @Naturality (∀ A, A ~> A) := {
  natural := fun f => ∀ X Y (g : X ~> Y), g ∘ f X ≈ f Y ∘ g
}.

Program Instance Functor_Naturality
        `{C : Category} `{D : Category} (F G : C ⟶ D) :
  @Naturality (∀ A, F A ~> G A) := {
  natural := fun f =>
    ∀ X Y (g : X ~{C}~> Y), fmap[G] g ∘ f X ≈ f Y ∘ fmap[F] g
}.

(*
Program Instance Tensor_LeftMapF `{C : Category} `{@Monoidal C} {Y : C} :
  Functor := {
  fobj := fun X => X ⨂ Y;
  fmap := fun _ _ f => bimap f id
}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Program Instance Tensor_RightMapF `{C : Category} `{@Monoidal C} {X : C} :
  Functor := {
  fobj := fun Y => X ⨂ Y;
  fmap := fun _ _ f => bimap id f
}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
*)

Class CanonicalMap `{C : Category} (F : C -> C) : Type := {
  map {A B} (f : A ~> B) : F A ~> F B;

  related_functor : C ⟶ C;
  fobj_related {A} : F A ≅ related_functor A;
  fmap_related {A B} (f : A ~> B) :
    map f ≈ from fobj_related ∘ fmap[related_functor] f ∘ to fobj_related
}.

Program Instance Identity_CanonicalMap `{C : Category} :
  @CanonicalMap C (fun X => X) := {
  map := fun _ _ f => f;
  related_functor := Id
}.

(*
Global Program Instance Skip `{C : Category} : C ⟶ [C, C] := {
  fobj := fun x => {| fobj := fun y => y |};
  fmap := fun _ _ f =>
            {| transform := _ |}
}.
Next Obligation.
  exact id.
Defined.
*)

Require Import Category.Functor.Constant.

Program Instance ConstMap `{C : Category} {B : C} :
  @CanonicalMap C (λ _, B) := {
  map := fun _ _ _ => id;
  related_functor := Constant _ B
}.

(*
Program Instance Tensor_LeftMap `{C : Category} `{@Monoidal C} {Y : C} :
  @CanonicalMap C (fun X => X ⨂ Y) := {
  map := fun _ _ f => bimap f id;
  related_functor := Tensor_LeftMapF
}.

Program Instance Tensor_RightMap `{C : Category} `{@Monoidal C} {X : C} :
  @CanonicalMap C (fun Y => X ⨂ Y) := {
  map := fun _ _ f => bimap id f;
  related_functor := Tensor_RightMapF
}.

Program Instance Tensor_LeftLeftMap `{C : Category} `{@Monoidal C} {Y Z : C} :
  @CanonicalMap C (fun X => X ⨂ (Y ⨂ Z)) := {
  map := fun _ _ f => bimap f id
}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Program Instance Tensor_LeftRightMap `{C : Category} `{@Monoidal C} {X Z : C} :
  @CanonicalMap C (fun Y => X ⨂ (Y ⨂ Z)) := {
  map := fun _ _ f => bimap id (bimap f id)
}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Program Instance Tensor_RightRightMap `{C : Category} `{@Monoidal C} {X Y : C} :
  @CanonicalMap C (fun Z => X ⨂ (Y ⨂ Z)) := {
  map := fun _ _ f => bimap id (bimap id f)
}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Program Instance Tensor_LeftLeftMap' `{C : Category} `{@Monoidal C} {Y Z : C} :
  @CanonicalMap C (fun X => (X ⨂ Y) ⨂ Z) := {
  map := fun _ _ f => bimap (bimap f id) id
}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Program Instance Tensor_LeftRightMap' `{C : Category} `{@Monoidal C} {X Z : C} :
  @CanonicalMap C (fun Y => (X ⨂ Y) ⨂ Z) := {
  map := fun _ _ f => bimap (bimap id f) id
}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Program Instance Tensor_RightRightMap' `{C : Category} `{@Monoidal C} {X Y : C} :
  @CanonicalMap C (fun Z => (X ⨂ Y) ⨂ Z) := {
  map := fun _ _ f => bimap id f
}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

Program Instance Tensor_Left `{C : Category} {B : C}
        (P : C -> C -> C) (H : ∀ X Y Z, X ~> Y -> P X Z ~> P Y Z) :
  @CanonicalMap C (fun A => P A B) := {
  map := fun _ _ f => _
}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
*)

(*
Program Instance Functor_First `{F : C × C ⟶ C} {X : C} : C ⟶ C := {
  fobj := fun Y => F (X, Y);
  fmap := fun _ _ f => fmap[F] (id[X], f)
}.
Next Obligation.
  proper.
  rewrite X1; reflexivity.
Qed.
Next Obligation.
  rewrite <- fmap_comp.
  simpl.
  rewrite id_left.
  reflexivity.
Qed.

Program Instance Functor_Supply_First `{F : C ⟶ [C, C]} {X : C} : C ⟶ C := {
  fobj := fun Y => F X Y;
  fmap := fun _ _ f => fmap[F X] f
}.
Next Obligation. apply fmap_comp. Qed.

Program Instance Functor_Second `{F : C × C ⟶ C} {Y : C} : C ⟶ C := {
  fobj := fun X => F (X, Y);
  fmap := fun _ _ f => fmap[F] (f, id[Y])
}.
Next Obligation.
  proper.
  rewrite X0; reflexivity.
Qed.
Next Obligation.
  rewrite <- fmap_comp.
  simpl.
  rewrite id_left.
  reflexivity.
Qed.

Program Instance Functor_Supply_Second `{F : C ⟶ [C, C]} {Y : C} : C ⟶ C := {
  fobj := fun X => F X Y;
  fmap := fun _ _ f => fmap[F] f Y
}.
Next Obligation.
  proper.
  sapply (@fmap_respects _ _ F X Y0 x y X0).
Qed.
Next Obligation.
  pose proof (@fmap_id _ _ F X Y).
  simpl in X0.
  rewrite X0.
  apply fmap_id.
Qed.
Next Obligation.
  sapply (@fmap_comp _ _ F X Y0 Z f g Y).
Qed.
*)

Program Instance ArityOne `{C : Category}
        (P : C -> C) `{F : @CanonicalMap C P}
        (Q : C -> C) `{G : @CanonicalMap C Q} :
  @Naturality (∀ A, P A ~> Q A) := {
  natural := fun f => ∀ X Y (g : X ~> Y), map g ∘ f X ≈ f Y ∘ map g
}.

Program Instance ArityTwo `{C : Category}
        (P : C -> C -> C)
            `{FA : ∀ B, @CanonicalMap C (fun A => P A B)}
            `{FB : ∀ A, @CanonicalMap C (fun B => P A B)}
        (Q : C -> C -> C)
            `{GA : ∀ B, @CanonicalMap C (fun A => Q A B)}
            `{GB : ∀ A, @CanonicalMap C (fun B => Q A B)} :
  @Naturality (∀ A B, P A B ~> Q A B) := {
  natural := fun f => ∀ X Y (g : X ~> Y) Z W (h : Z ~> W),
    @map _ _ (GB _) _ _ h ∘ @map _ _ (GA _) _ _ g ∘ f X Z
      ≈ f Y W ∘ @map _ _ (FB _) _ _ h ∘ @map _ _ (FA _) _ _ g
}.

Program Instance ArityThree `{C : Category}
        (P : C -> C -> C -> C)
            `{FA : ∀ B D : C, @CanonicalMap C (fun A => P A B D)}
            `{FB : ∀ A D : C, @CanonicalMap C (fun B => P A B D)}
            `{FC : ∀ A B : C, @CanonicalMap C (fun D => P A B D)}
        (Q : C -> C -> C -> C)
            `{GA : ∀ B D : C, @CanonicalMap C (fun A => Q A B D)}
            `{GB : ∀ A D : C, @CanonicalMap C (fun B => Q A B D)}
            `{GC : ∀ A B : C, @CanonicalMap C (fun D => Q A B D)} :
  @Naturality (∀ A B D, P A B D ~> Q A B D) := {
  natural := fun f => ∀ X Y (g : X ~> Y)
                        Z W (h : Z ~> W)
                        V U (i : V ~> U),
    @map _ _ (GC _ _) _ _ i ∘
    @map _ _ (GB _ _) _ _ h ∘
    @map _ _ (GA _ _) _ _ g
      ∘ f X Z V
      ≈ f Y W U
      ∘ @map _ _ (FC _ _) _ _ i
      ∘ @map _ _ (FB _ _) _ _ h
      ∘ @map _ _ (FA _ _) _ _ g
}.

(*
Class FooCategory `{C : Category} `{@Monoidal C} := {
  morphism {X Y : C} : X ⨂ Y ~> Y;
  morphism_natural : natural (@morphism)
}.

Axiom foo : ∀ `{C : Category} `{@Cartesian C} `{@Monoidal C} X Y, X ⨂ Y ~> Y.

Goal ∀ `{C : Category} `{@Cartesian C} `{@Monoidal C}, FooCategory.
intros.
unshelve econstructor; simpl.
exact foo.
intros.
simpl.
Abort.

Class BarCategory `{C : Category} `{@Monoidal C} := {
  morphism3 {X Y Z : C} : X ⨂ (Y ⨂ Z) ~> (X ⨂ Y) ⨂ Z;
  morphism3_natural : natural (@morphism3)
}.

Axiom bar : ∀ `{C : Category} `{@Cartesian C} `{@Monoidal C} X Y Z,
  X ⨂ (Y ⨂ Z) ~> (X ⨂ Y) ⨂ Z.

Goal ∀ `{C : Category} `{@Cartesian C} `{@Monoidal C}, BarCategory.
intros.
unshelve econstructor; simpl.
exact bar.
intros.
simpl.
Abort.
*)
