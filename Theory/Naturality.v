Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Functor.
Require Export Category.Theory.Functor.Endo.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Class Naturality (A : Type) : Type := {
  natural (f : A) : Type
}.

Arguments natural {A _} _ /.

Ltac prove_naturality H tac :=
  simpl; destruct H; simpl;
  split; [split|];
  split; simpl;
  intros; tac; intuition.

#[global]
Program Instance Identity_Naturality {C : Category} :
  Naturality (∀ A, A ~> A) := {
  natural := fun f => ∀ x y (g : x ~> y), g ∘ f x ≈ f y ∘ g
}.

#[global]
Program Instance Functor_Naturality
        {C : Category} {D : Category} (F G : C ⟶ D) :
  Naturality (∀ A, F A ~> G A) := {
  natural := fun f =>
    ∀ x y (g : x ~{C}~> y), fmap[G] g ∘ f x ≈ f y ∘ fmap[F] g
}.

(*
Require Import Category.Functor.Constant.

Program Instance ConstMap {C : Category} {B : C} :
  EndoFunctor (λ _, B) | 9 := {
  map := fun _ _ _ => id;
  is_functor := Constant _ B
}.
*)

(*
Program Instance PartialApply_Product_Left {F : C × C ⟶ C} {x : C} : C ⟶ C := {
  fobj := fun y => F (x, y);
  fmap := fun _ _ f => fmap[F] (id[x], f)
}.
Next Obligation.
  proper; rewrites; reflexivity.
Qed.
Next Obligation.
  rewrite <- fmap_comp.
  simpl.
  rewrite id_left.
  reflexivity.
Qed.

Program Instance PartialApply_Curried_Left {F : C ⟶ [C, C]} {x : C} : C ⟶ C := {
  fobj := fun y => F x y;
  fmap := fun _ _ f => fmap[F x] f
}.
Next Obligation. apply fmap_comp. Qed.

Program Instance PartialApply_Product_Right {F : C × C ⟶ C} {y : C} : C ⟶ C := {
  fobj := fun x => F (x, y);
  fmap := fun _ _ f => fmap[F] (f, id[y])
}.
Next Obligation.
  proper; rewrites; reflexivity.
Qed.
Next Obligation.
  rewrite <- fmap_comp.
  simpl.
  rewrite id_left.
  reflexivity.
Qed.

Program Instance PartialApply_Curried_Right {F : C ⟶ [C, C]} {y : C} : C ⟶ C := {
  fobj := fun x => F x y;
  fmap := fun _ _ f => fmap[F] f y
}.
Next Obligation.
  proper.
  sapply (@fmap_respects _ _ F x Y0 x y X0).
Qed.
Next Obligation.
  pose proof (@fmap_id _ _ F x y).
  simpl in X0.
  rewrite X0.
  apply fmap_id.
Qed.
Next Obligation.
  sapply (@fmap_comp _ _ F x Y0 z f g y).
Qed.
*)

#[global]
Program Instance ArityOne {C : Category}
        (P : C -> C) {F : @EndoFunctor C P}
        (Q : C -> C) {G : @EndoFunctor C Q} :
  @Naturality (∀ A, P A ~> Q A) := {
  natural := fun f => ∀ x y (g : x ~> y), @map _ _ G _ _ g ∘ f x ≈ f y ∘ @map _ _ F _ _ g
}.

#[global]
Program Instance ArityTwo {C : Category}
        (P : C -> C -> C)
            {FA : ∀ B, @EndoFunctor C (fun A => P A B)}
            {FB : ∀ A, @EndoFunctor C (fun B => P A B)}
        (Q : C -> C -> C)
            {GA : ∀ B, @EndoFunctor C (fun A => Q A B)}
            {GB : ∀ A, @EndoFunctor C (fun B => Q A B)} :
  @Naturality (∀ A B, P A B ~> Q A B) := {
  natural := fun f => ∀ x y (g : x ~> y) z w (h : z ~> w),
    @map _ _ (GB _) _ _ h ∘ @map _ _ (GA _) _ _ g ∘ f x z
      ≈ f y w ∘ @map _ _ (FB _) _ _ h ∘ @map _ _ (FA _) _ _ g
}.

#[global]
Program Instance ArityThree {C : Category}
        (P : C -> C -> C -> C)
            {FA : ∀ B D : C, @EndoFunctor C (fun A => P A B D)}
            {FB : ∀ A D : C, @EndoFunctor C (fun B => P A B D)}
            {FC : ∀ A B : C, @EndoFunctor C (fun D => P A B D)}
        (Q : C -> C -> C -> C)
            {GA : ∀ B D : C, @EndoFunctor C (fun A => Q A B D)}
            {GB : ∀ A D : C, @EndoFunctor C (fun B => Q A B D)}
            {GC : ∀ A B : C, @EndoFunctor C (fun D => Q A B D)} :
  @Naturality (∀ A B D, P A B D ~> Q A B D) := {
  natural := fun f => ∀ x y (g : x ~> y)
                        z w (h : z ~> w)
                        v u (i : v ~> u),
    @map _ _ (GC _ _) _ _ i ∘
    @map _ _ (GB _ _) _ _ h ∘
    @map _ _ (GA _ _) _ _ g
      ∘ f x z v
      ≈ f y w u
      ∘ @map _ _ (FC _ _) _ _ i
      ∘ @map _ _ (FB _ _) _ _ h
      ∘ @map _ _ (FA _ _) _ _ g
}.

#[global]
Program Instance ArityFour {C : Category}
        (P : C -> C -> C -> C -> C)
            {FA : ∀ B D E : C, @EndoFunctor C (fun A => P A B D E)}
            {FB : ∀ A D E : C, @EndoFunctor C (fun B => P A B D E)}
            {FC : ∀ A B E : C, @EndoFunctor C (fun D => P A B D E)}
            {FD : ∀ A B D : C, @EndoFunctor C (fun E => P A B D E)}
        (Q : C -> C -> C -> C -> C)
            {GA : ∀ B D E : C, @EndoFunctor C (fun A => Q A B D E)}
            {GB : ∀ A D E : C, @EndoFunctor C (fun B => Q A B D E)}
            {GC : ∀ A B E : C, @EndoFunctor C (fun D => Q A B D E)}
            {GD : ∀ A B D : C, @EndoFunctor C (fun E => Q A B D E)} :
  @Naturality (∀ A B D E, P A B D E ~> Q A B D E) := {
  natural := fun f => ∀ x y (g : x ~> y)
                        z w (h : z ~> w)
                        v u (i : v ~> u)
                        t s (j : t ~> s),
    @map _ _ (GD _ _ _) _ _ j ∘
    @map _ _ (GC _ _ _) _ _ i ∘
    @map _ _ (GB _ _ _) _ _ h ∘
    @map _ _ (GA _ _ _) _ _ g
      ∘ f x z v t
      ≈ f y w u s
      ∘ @map _ _ (FD _ _ _) _ _ j
      ∘ @map _ _ (FC _ _ _) _ _ i
      ∘ @map _ _ (FB _ _ _) _ _ h
      ∘ @map _ _ (FA _ _ _) _ _ g
}.


#[global]
Program Instance ArityFive {C : Category}
        (P : C -> C -> C -> C -> C -> C)
            {FA : ∀ B D E F : C, @EndoFunctor C (fun A => P A B D E F)}
            {FB : ∀ A D E F : C, @EndoFunctor C (fun B => P A B D E F)}
            {FC : ∀ A B E F : C, @EndoFunctor C (fun D => P A B D E F)}
            {FD : ∀ A B D F : C, @EndoFunctor C (fun E => P A B D E F)}
            {FE : ∀ A B D E : C, @EndoFunctor C (fun F => P A B D E F)}
        (Q : C -> C -> C -> C -> C -> C)
            {GA : ∀ B D E F : C, @EndoFunctor C (fun A => Q A B D E F)}
            {GB : ∀ A D E F : C, @EndoFunctor C (fun B => Q A B D E F)}
            {GC : ∀ A B E F : C, @EndoFunctor C (fun D => Q A B D E F)}
            {GD : ∀ A B D F : C, @EndoFunctor C (fun E => Q A B D E F)}
            {GE : ∀ A B D E : C, @EndoFunctor C (fun F => Q A B D E F)} :
  @Naturality (∀ A B D E F, P A B D E F ~> Q A B D E F) := {
  natural := fun f => ∀ x y (g : x ~> y)
                        z w (h : z ~> w)
                        v u (i : v ~> u)
                        t s (j : t ~> s)
                        q r (k : q ~> r),
    @map _ _ (GE _ _ _ _) _ _ k ∘
    @map _ _ (GD _ _ _ _) _ _ j ∘
    @map _ _ (GC _ _ _ _) _ _ i ∘
    @map _ _ (GB _ _ _ _) _ _ h ∘
    @map _ _ (GA _ _ _ _) _ _ g
      ∘ f x z v t q
      ≈ f y w u s r
      ∘ @map _ _ (FE _ _ _ _) _ _ k
      ∘ @map _ _ (FD _ _ _ _) _ _ j
      ∘ @map _ _ (FC _ _ _ _) _ _ i
      ∘ @map _ _ (FB _ _ _ _) _ _ h
      ∘ @map _ _ (FA _ _ _ _) _ _ g
}.

#[global]
Program Instance Transform_ArityOne {C : Category}
        (P : C -> C) `{@EndoFunctor C P}
        (Q : C -> C) `{@EndoFunctor C Q} :
  @Naturality (∀ A, P A ≅ Q A) := {
  natural := fun f => natural (fun A => to (f A)) *
                      natural (fun A => from (f A))
}.

#[global]
Program Instance Transform_ArityTwo {C : Category}
        (P : C -> C -> C)
            `{∀ B, @EndoFunctor C (fun A => P A B)}
            `{∀ A, @EndoFunctor C (fun B => P A B)}
        (Q : C -> C -> C)
            `{∀ B, @EndoFunctor C (fun A => Q A B)}
            `{∀ A, @EndoFunctor C (fun B => Q A B)} :
  @Naturality (∀ A B, P A B ≅ Q A B) := {
  natural := fun f => natural (fun A B => to (f A B)) *
                      natural (fun A B => from (f A B))
}.

#[global]
Program Instance Transform_ArityThree {C : Category}
        (P : C -> C -> C -> C)
            `{∀ B D : C, @EndoFunctor C (fun A => P A B D)}
            `{∀ A D : C, @EndoFunctor C (fun B => P A B D)}
            `{∀ A B : C, @EndoFunctor C (fun D => P A B D)}
        (Q : C -> C -> C -> C)
            `{∀ B D : C, @EndoFunctor C (fun A => Q A B D)}
            `{∀ A D : C, @EndoFunctor C (fun B => Q A B D)}
            `{∀ A B : C, @EndoFunctor C (fun D => Q A B D)} :
  @Naturality (∀ A B D, P A B D ≅ Q A B D) := {
  natural := fun f => natural (fun A B D => to (f A B D)) *
                      natural (fun A B D => from (f A B D))
}.

#[global]
Program Instance Transform_ArityFour {C : Category}
        (P : C -> C -> C -> C -> C)
            `{∀ B D E : C, @EndoFunctor C (fun A => P A B D E)}
            `{∀ A D E : C, @EndoFunctor C (fun B => P A B D E)}
            `{∀ A B E : C, @EndoFunctor C (fun D => P A B D E)}
            `{∀ A B D : C, @EndoFunctor C (fun E => P A B D E)}
        (Q : C -> C -> C -> C -> C)
            `{∀ B D E : C, @EndoFunctor C (fun A => Q A B D E)}
            `{∀ A D E : C, @EndoFunctor C (fun B => Q A B D E)}
            `{∀ A B E : C, @EndoFunctor C (fun D => Q A B D E)}
            `{∀ A B D : C, @EndoFunctor C (fun E => Q A B D E)} :
  @Naturality (∀ A B D E, P A B D E ≅ Q A B D E) := {
  natural := fun f => natural (fun A B D E => to (f A B D E)) *
                      natural (fun A B D E => from (f A B D E))
}.


#[global]
Program Instance Transform_ArityFive {C : Category}
        (P : C -> C -> C -> C -> C -> C)
            `{∀ B D E F : C, @EndoFunctor C (fun A => P A B D E F)}
            `{∀ A D E F : C, @EndoFunctor C (fun B => P A B D E F)}
            `{∀ A B E F : C, @EndoFunctor C (fun D => P A B D E F)}
            `{∀ A B D F : C, @EndoFunctor C (fun E => P A B D E F)}
            `{∀ A B D E : C, @EndoFunctor C (fun F => P A B D E F)}
        (Q : C -> C -> C -> C -> C -> C)
            `{∀ B D E F : C, @EndoFunctor C (fun A => Q A B D E F)}
            `{∀ A D E F : C, @EndoFunctor C (fun B => Q A B D E F)}
            `{∀ A B E F : C, @EndoFunctor C (fun D => Q A B D E F)}
            `{∀ A B D F : C, @EndoFunctor C (fun E => Q A B D E F)}
            `{∀ A B D E : C, @EndoFunctor C (fun F => Q A B D E F)} :
  @Naturality (∀ A B D E F, P A B D E F ≅ Q A B D E F) := {
  natural := fun f => natural (fun A B D E F => to (f A B D E F)) *
                      natural (fun A B D E F => from (f A B D E F))
}.
