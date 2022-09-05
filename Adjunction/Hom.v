Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Export Category.Adjunction.Natural.Transformation.
Require Export Category.Functor.Hom.
Require Export Category.Functor.Construction.Product.
Require Export Category.Functor.Opposite.
Require Export Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section AdjunctionHom.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

(* Wikipedia: "A hom-set adjunction between two categories C and D consists of
   two functors F : C ← D and G : C → D and a natural isomorphism

     Φ : homC(F −, −) → homD(−, G −).

   "This specifies a family of bijections

     Φy,x : homC(F y, x) → homD(y, G x)

   for all objects x in C and y in D.

   "In this situation we say that F is left adjoint to G and G is right
   adjoint to F, and may indicate this relationship by writing Φ : F ⊣ G, or
   simply F ⊣ G.

   "This definition is a logical compromise in that it is somewhat more
   difficult to satisfy than the universal morphism definitions [see
   Category.Theory.Adjunction], and has fewer immediate implications than the
   counit-unit definition [see Category.Adjunction.Natural.Transformation]. It
   is useful because of its obvious symmetry, and as a stepping-stone between
   the other definitions.

   "In order to interpret Φ as a natural isomorphism, one must recognize
   homC(F –, –) and homD(–, G –) as functors. In fact, they are both
   bifunctors from D^op × C to Set (the category of sets)." *)

Class Adjunction_Hom := {
  hom_adj : Hom C ◯ F^op ∏⟶ Id ≅[[D^op ∏ C, Sets]] Hom D ◯ Id^op ∏⟶ U
}.

Context `{Adjunction_Hom}.

Program Definition hom_unit : Id ⟹ U ◯ F := {|
  transform := fun x => @morphism _ _ _ _ (to hom_adj (x, F x)) id
|}.
Next Obligation.
  spose (naturality[to hom_adj] (x, F x) (x, F y) (id, fmap[F] f) id) as X.
  rewrite id_right in X.
  rewrites.

  spose (naturality[to hom_adj] (y, F y) (x, F y) (f, id) id) as X.
  rewrite fmap_id, id_left in X.
  rewrites.

  apply proper_morphism; cat.
Qed.
Next Obligation.
  symmetry.
  apply hom_unit_obligation_1.
Qed.

Program Definition hom_counit : F ◯ U ⟹ Id := {|
  transform := fun x => @morphism _ _ _ _ (from hom_adj (U x, x)) id
|}.
Next Obligation.
  spose (naturality[from hom_adj] (U x, x) (U x, y) (id, f) id) as X.
  rewrite fmap_id, id_right in X.
  rewrites.

  spose (naturality[from hom_adj] (U y, y) (U x, y) (fmap[U] f, id) id) as X.
  rewrite id_left in X.
  rewrites.

  apply proper_morphism; cat.
Qed.
Next Obligation.
  symmetry.
  apply hom_counit_obligation_1.
Qed.

Theorem hom_unit_naturality_consequence {x y} (f : F x ~> y) :
  to hom_adj (x, y) f ≈ fmap[U] f ∘ hom_unit _.
Proof.
  unfold hom_unit; simpl.
  spose (naturality[to hom_adj] (x, F x) (x, y) (id, f) id) as X.
  rewrite id_right in X.
  rewrites.
  apply proper_morphism; cat.
Qed.

Theorem hom_counit_naturality_consequence {x y} (f : x ~> U y) :
  from hom_adj (x, y) f ≈ hom_counit _ ∘ fmap[F] f.
Proof.
  unfold hom_counit; simpl.
  spose (naturality[from hom_adj] (U y, y) (x, y) (f, id) id) as X.
  rewrite id_left in X.
  rewrites.
  apply proper_morphism; cat.
Qed.

Theorem hom_counit_fmap_unit {x} :
  hom_counit (F x) ∘ fmap[F] (hom_unit x) ≈ id.
Proof.
  spose (@hom_counit_naturality_consequence x (F x) (hom_unit x)) as X.
  rewrites.
  unfold hom_unit; simpl.
  srewrite (iso_from_to hom_adj (x, F x) id); cat.
Qed.

Theorem hom_fmap_counit_unit {x} :
  fmap[U] (hom_counit x) ∘ hom_unit (U x) ≈ id.
Proof.
  spose (@hom_unit_naturality_consequence (U x) x (hom_counit x)) as X.
  rewrites.
  unfold hom_unit; simpl.
  srewrite (iso_to_from hom_adj (U x, x) id); cat.
Qed.

Program Definition Adjunction_Hom_to_Transform : F ∹ U := {|
  unit   := hom_unit;
  counit := hom_counit;
  counit_fmap_unit := @hom_counit_fmap_unit;
  fmap_counit_unit := @hom_fmap_counit_unit
|}.

Program Definition Adjunction_Transform_to_Hom (A : F ∹ U) : Adjunction_Hom := {|
  hom_adj :=
    {| to   := {| transform := fun _ =>
        {| morphism := fun f => fmap[U] f ∘ unit _ |} |}
     ; from := {| transform := fun _ =>
        {| morphism := fun f => counit _ ∘ fmap[F] f |} |} |}
|}.
Next Obligation.
  proper; rewrites; reflexivity.
Qed.
Next Obligation.
  simpl.
  rewrite <- !comp_assoc.
  srewrite_r (naturality[unit]).
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  reflexivity.
Qed.
Next Obligation.
  simpl.
  rewrite <- !comp_assoc.
  srewrite_r (naturality[unit]).
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  reflexivity.
Qed.
Next Obligation.
  proper; rewrites; reflexivity.
Qed.
Next Obligation.
  simpl.
  rewrite !comp_assoc.
  srewrite (naturality[counit]).
  rewrite <- !comp_assoc.
  rewrite <- !fmap_comp.
  reflexivity.
Qed.
Next Obligation.
  simpl.
  rewrite !comp_assoc.
  srewrite (naturality[counit]).
  rewrite <- !comp_assoc.
  rewrite <- !fmap_comp.
  reflexivity.
Qed.
Next Obligation.
  simpl; cat.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  srewrite (naturality[unit]).
  rewrite comp_assoc.
  srewrite (@fmap_counit_unit _ _ _ _ A); cat.
Qed.
Next Obligation.
  simpl; cat.
  rewrite fmap_comp.
  rewrite comp_assoc.
  srewrite_r (naturality[counit]).
  rewrite <- comp_assoc.
  srewrite (@counit_fmap_unit _ _ _ _ A); cat.
Qed.

Program Definition Adjunction_Hom_to_Universal : F ⊣ U := {|
  adj := fun a b =>
    {| to   := transform (to hom_adj) (a, b)
     ; from := transform (from hom_adj) (a, b) |}
|}.
Next Obligation.
  simpl; srewrite (iso_to_from hom_adj (a, b) x); cat.
Qed.
Next Obligation.
  simpl; srewrite (iso_from_to hom_adj (a, b) x); cat.
Defined.
Next Obligation.
  spose (naturality (to hom_adj) (y, z) (x, z) (g, id) f) as X.
  rewrite fmap_id, id_left in X.
  rewrites.
  apply proper_morphism; cat.
Qed.
Next Obligation.
  spose (naturality (to hom_adj) (x, y) (x, z) (id, f) g) as X.
  rewrite id_right in X.
  rewrites.
  apply proper_morphism; cat.
Qed.
Next Obligation.
  spose (naturality (from hom_adj) (y, z) (x, z) (g, id) f) as X.
  rewrite id_left in X.
  rewrites.
  apply proper_morphism; cat.
Qed.
Next Obligation.
  spose (naturality (from hom_adj) (x, y) (x, z) (id, f) g) as X.
  rewrite fmap_id, id_right in X.
  rewrites.
  apply proper_morphism; cat.
Qed.

Program Definition Adjunction_Universal_to_Hom (A : F ⊣ U) : Adjunction_Hom := {|
  hom_adj :=
    {| to   := {| transform := fun _ =>
        {| morphism := fun f => to adj f |} |}
     ; from := {| transform := fun _ =>
        {| morphism := fun f => from adj f |} |} |}
|}.
Next Obligation.
  proper; rewrites; reflexivity.
Qed.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite to_adj_nat_l.
  rewrite comp_assoc.
  rewrite to_adj_nat_r.
  reflexivity.
Qed.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite to_adj_nat_r.
  rewrite <- comp_assoc.
  rewrite to_adj_nat_l.
  reflexivity.
Qed.
Next Obligation.
  proper; rewrites; reflexivity.
Qed.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite from_adj_nat_l.
  rewrite comp_assoc.
  rewrite from_adj_nat_r.
  reflexivity.
Qed.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite from_adj_nat_r.
  rewrite <- comp_assoc.
  rewrite from_adj_nat_l.
  reflexivity.
Qed.
Next Obligation.
  simpl; cat.
  apply (iso_to_from adj _).
Qed.
Next Obligation.
  simpl; cat.
  apply (iso_from_to adj _).
Qed.

End AdjunctionHom.

Arguments Adjunction_Hom {C D} F%functor U%functor.
