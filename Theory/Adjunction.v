Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Naturality.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Adjunction.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Class Adjunction := {
  adj {a b} : F a ~{C}~> b ≊ a ~{D}~> U b;

  to_adj_nat_l {a b c} (f : F b ~> c) (g : a ~> b) :
    to adj (f ∘ fmap[F] g) ≈ to adj f ∘ g;
  to_adj_nat_r {a} {b} {c : C} (f : b ~> c) (g : F a ~> b) :
    to adj (f ∘ g) ≈ fmap[U] f ∘ to adj g;

  from_adj_nat_l {a b c} (f : b ~> U c) (g : a ~> b) :
    adj⁻¹ (f ∘ g) ≈ adj⁻¹ f ∘ fmap[F] g;
  from_adj_nat_r {a} {b} {c : C} (f : b ~> c) (g : a ~> U b) :
    adj⁻¹ (fmap[U] f ∘ g) ≈ f ∘ adj⁻¹ g
}.

Context `{@Adjunction}.

Definition unit   {a : D} : a ~> U (F a) := to adj id.
Definition counit {a : C} : F (U a) ~> a := adj⁻¹ id.

Corollary adj_unit  {a b} (f : F a ~> b) :
  to adj f ≈ fmap f ∘ unit.
Proof.
  rewrite <- (id_right f).
  rewrite to_adj_nat_r.
  rewrite fmap_comp; cat.
Qed.

Corollary from_adj_counit {a b} (f : a ~> U b) :
  adj⁻¹ f ≈ counit ∘ fmap f.
Proof.
  rewrite <- (id_left f).
  rewrite from_adj_nat_l.
  rewrite fmap_comp; cat.
Qed.

Corollary adj_counit {a} : to adj counit ≈ @id D (U a).
Proof. sapply (@iso_to_from Sets _ _ (@adj _ (U a) a)). Qed.

Corollary from_adj_unit {a} : adj⁻¹ unit ≈ @id C (F a).
Proof. sapply (@iso_from_to Sets _ _ (@adj _ a (F a))). Qed.

Corollary counit_fmap_unit  {a} : counit ∘ fmap[F] unit ≈ @id C (F a).
Proof.
  unfold unit, counit.
  rewrite <- from_adj_nat_l; cat.
  sapply (@iso_from_to Sets _ _ (@adj _ a (F a))).
Qed.

Corollary fmap_counit_unit  {a} : fmap[U] counit ∘ unit ≈ @id D (U a).
Proof.
  unfold unit, counit.
  rewrite <- to_adj_nat_r; cat.
  sapply (@iso_to_from Sets _ _ (@adj _ (U a) a)).
Qed.

(* If F is a faithful functor, and f is monic, then adj f is monic. *)
Theorem adj_monic  {a b} (f : F a ~> b) c (g h : c ~> a) :
  Faithful F -> Monic f
    -> to adj f ∘ g ≈ to adj f ∘ h -> g ≈ h.
Proof.
  intros.
  rewrite <- !to_adj_nat_l in X1.
  pose proof (monic (Monic:=@iso_monic Sets _ _ (@adj H c b))
                    {| carrier   := Datatypes.unit
                     ; is_setoid := {| equiv := eq |} |}
                    {| morphism  := fun _ => f ∘ fmap[F] g |}
                    {| morphism  := fun _ => f ∘ fmap[F] h |}) as X2;
  simpl in X2.
  apply X.
  apply X0.
  apply X2; intros.
  exact X1.
  exact tt.
Qed.

Corollary from_adj_respects {a b} (f g : a ~{D}~> U b) :
  f ≈ g -> adj⁻¹ f ≈ adj⁻¹ g.
Proof. intros; rewrites; reflexivity. Qed.

Corollary adj_respects {a b} (f g : F a ~{C}~> b) :
  f ≈ g -> to adj f ≈ to adj g.
Proof. intros; rewrites; reflexivity. Qed.

End Adjunction.

Arguments Adjunction {C D} F%functor U%functor.

Bind Scope adjunction_scope with Adjunction.
Delimit Scope adjunction_type_scope with adjunction_type.
Delimit Scope adjunction_scope with adjunction.
Open Scope adjunction_type_scope.
Open Scope adjunction_scope.

Notation "F ⊣ G" := (@Adjunction _ _ F G) (at level 59) : category_scope.
