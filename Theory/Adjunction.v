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

(* Adjunctions relate two functors that map between the same two categories
  (though in opposite directions), in a manner that is weaker than isomorphism
  or equivalence, but still quite informative. In general, one functor is
  forgetful, and maps constructions from a more expressive domain into one
  that captures only the essence of that structure; while the other is free,
  and maps essential constructions into the fuller setting.

  As an example: the category of ASTs may be mapped forgetfully to the
  category of interpretated objects, which themselves map freely to some
  "canonical" representation of each such object. So, "3", "1 + 2", and "2 +
  1" all mean 3, while 3 is canonically represented by the constant "3". The
  forgetful functor is the evaluator, and the free functor a parser, giving
  rise to the following isomorphism (in the category of Sets, whose objects
  may be hom-sets):

      AST x ~{category of syntax or ASTs}~> y
        ≅ x ~{category of semantics or denotations}~> Denote y *)

Section Adjunction.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Class Adjunction := {
  adj {x y} : F x ~{C}~> y ≊ x ~{D}~> U y;

  to_adj_nat_l {x y c} (f : F y ~> c) (g : x ~> y) :
    to adj (f ∘ fmap[F] g) ≈ to adj f ∘ g;
  to_adj_nat_r {x} {y} {c : C} (f : y ~> c) (g : F x ~> y) :
    to adj (f ∘ g) ≈ fmap[U] f ∘ to adj g;

  from_adj_nat_l {x y c} (f : y ~> U c) (g : x ~> y) :
    adj⁻¹ (f ∘ g) ≈ adj⁻¹ f ∘ fmap[F] g;
  from_adj_nat_r {x} {y} {c : C} (f : y ~> c) (g : x ~> U y) :
    adj⁻¹ (fmap[U] f ∘ g) ≈ f ∘ adj⁻¹ g
}.

Context `{@Adjunction}.

Definition unit   {x : D} : x ~> U (F x) := to adj id.
Definition counit {x : C} : F (U x) ~> x := adj⁻¹ id.

Corollary adj_unit  {x y} (f : F x ~> y) :
  to adj f ≈ fmap f ∘ unit.
Proof.
  rewrite <- (id_right f).
  rewrite to_adj_nat_r.
  rewrite fmap_comp; cat.
Qed.

Corollary from_adj_counit {x y} (f : x ~> U y) :
  adj⁻¹ f ≈ counit ∘ fmap f.
Proof.
  rewrite <- (id_left f).
  rewrite from_adj_nat_l.
  rewrite fmap_comp; cat.
Qed.

Corollary adj_counit {x} : to adj counit ≈ @id D (U x).
Proof. sapply (@iso_to_from Sets _ _ (@adj _ (U x) x)). Qed.

Corollary from_adj_unit {x} : adj⁻¹ unit ≈ @id C (F x).
Proof. sapply (@iso_from_to Sets _ _ (@adj _ x (F x))). Qed.

Corollary counit_fmap_unit  {x} : counit ∘ fmap[F] unit ≈ @id C (F x).
Proof.
  unfold unit, counit.
  rewrite <- from_adj_nat_l; cat.
  sapply (@iso_from_to Sets _ _ (@adj _ x (F x))).
Qed.

Corollary fmap_counit_unit  {x} : fmap[U] counit ∘ unit ≈ @id D (U x).
Proof.
  unfold unit, counit.
  rewrite <- to_adj_nat_r; cat.
  sapply (@iso_to_from Sets _ _ (@adj _ (U x) x)).
Qed.

(* If F is a faithful functor, and f is monic, then adj f is monic. *)
Theorem adj_monic  {x y} (f : F x ~> y) c (g h : c ~> x) :
  Faithful F -> Monic f
    -> to adj f ∘ g ≈ to adj f ∘ h -> g ≈ h.
Proof.
  intros.
  rewrite <- !to_adj_nat_l in X1.
  pose proof (monic (Monic:=@iso_monic Sets _ _ (@adj H c y))
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

Corollary from_adj_respects {x y} (f g : x ~{D}~> U y) :
  f ≈ g -> adj⁻¹ f ≈ adj⁻¹ g.
Proof. intros; rewrites; reflexivity. Qed.

Corollary adj_respects {x y} (f g : F x ~{C}~> y) :
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

(* jww (2017-06-02): TODO *)
(* Wikipedia: "If the functor F : C ← D has two right adjoints G and G', then
   G and G' are naturally isomorphic. The same is true for left adjoints." *)

(* jww (2017-06-02): TODO *)
(* Wikipedia: "The most important property of adjoints is their continuity:
   every functor that has a left adjoint (and therefore is a right adjoint) is
   continuous (i.e. commutes with limits in the category theoretical sense);
   every functor that has a right adjoint (and therefore is a left adjoint) is
   cocontinuous (i.e. commutes with colimits).

   Since many common constructions in mathematics are limits or colimits, this
   provides a wealth of information. For example:

   - applying a right adjoint functor to a product of objects yields the
   - product of the images; applying a left adjoint functor to a coproduct of
   - objects yields the coproduct of the images; every right adjoint functor
   - is left exact; every left adjoint functor is right exact." *)
