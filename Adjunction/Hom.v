Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Isomorphism.
Require Export Category.Theory.Adjunction.
Require Export Category.Adjunction.Natural.Transformation.
Require Export Category.Functor.Hom.
Require Export Category.Functor.Construction.Product.
Require Export Category.Functor.Opposite.
Require Export Category.Instance.Fun.
Require Export Category.Instance.Sets.

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

     ΦY,X : homC(F Y, X) → homD(Y, G X)

   for all objects X in C and Y in D.

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
  hom_adj : Hom C ○ F^op ∏⟶ Id ≅[[D^op ∏ C, Sets]] Hom D ○ Id^op ∏⟶ U
}.

Context `{Adjunction_Hom}.

Program Definition hom_unit : Id ⟹ U ○ F := {|
  transform := fun X => @morphism _ _ _ _ (to hom_adj (X, F X)) id
|}.
Next Obligation.
  pose proof (naturality[to hom_adj] (X, F X) (X, F Y) (id, fmap[F] f) id).
  simpl in X0.
  rewrite id_right in X0.
  rewrites.

  pose proof (naturality[to hom_adj] (Y, F Y) (X, F Y) (f, id) id).
  simpl in X0.
  rewrite fmap_id, id_left in X0.
  rewrites.

  apply proper_morphism; cat.
Qed.
Next Obligation.
  symmetry.
  apply hom_unit_obligation_1.
Qed.

Program Definition hom_counit : F ○ U ⟹ Id := {|
  transform := fun X => @morphism _ _ _ _ (from hom_adj (U X, X)) id
|}.
Next Obligation.
  pose proof (naturality[from hom_adj] (U X, X) (U X, Y) (id, f) id).
  simpl in X0.
  rewrite fmap_id, id_right in X0.
  rewrites.

  pose proof (naturality[from hom_adj] (U Y, Y) (U X, Y) (fmap[U] f, id) id).
  simpl in X0.
  rewrite id_left in X0.
  rewrites.

  apply proper_morphism; cat.
Qed.
Next Obligation.
  symmetry.
  apply hom_counit_obligation_1.
Qed.

Theorem hom_unit_naturality_consequence {X Y} (f : F X ~> Y) :
  to hom_adj (X, Y) f ≈ fmap[U] f ∘ hom_unit _.
Proof.
  unfold hom_unit; simpl.
  pose proof (naturality[to hom_adj] (X, F X) (X, Y) (id, f) id); simpl in X0.
  rewrite id_right in X0.
  rewrites.
  apply proper_morphism; cat.
Qed.

Theorem hom_counit_naturality_consequence {X Y} (f : X ~> U Y) :
  from hom_adj (X, Y) f ≈ hom_counit _ ∘ fmap[F] f.
Proof.
  unfold hom_counit; simpl.
  pose proof (naturality[from hom_adj] (U Y, Y) (X, Y) (f, id) id); simpl in X0.
  rewrite id_left in X0.
  rewrites.
  apply proper_morphism; cat.
Qed.

Theorem hom_counit_fmap_unit {X} :
  hom_counit (F X) ∘ fmap[F] (hom_unit X) ≈ id.
Proof.
  pose proof (@hom_counit_naturality_consequence X (F X) (hom_unit X)).
  rewrites.
  unfold hom_unit; simpl.
  srewrite (iso_from_to hom_adj (X, F X) id); cat.
Qed.

Theorem hom_fmap_counit_unit {X} :
  fmap[U] (hom_counit X) ∘ hom_unit (U X) ≈ id.
Proof.
  pose proof (@hom_unit_naturality_consequence (U X) X (hom_counit X)).
  rewrites.
  unfold hom_unit; simpl.
  srewrite (iso_to_from hom_adj (U X, X) id); cat.
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
  pose proof (naturality (to hom_adj) (b, c) (a, c) (g, id) f);
  simpl in X.
  rewrite fmap_id, id_left in X.
  rewrites.
  apply proper_morphism; cat.
Qed.
Next Obligation.
  pose proof (naturality (to hom_adj) (a, b) (a, c) (id, f) g);
  simpl in X.
  rewrite id_right in X.
  rewrites.
  apply proper_morphism; cat.
Qed.
Next Obligation.
  pose proof (naturality (from hom_adj) (b, c) (a, c) (g, id) f);
  simpl in X.
  rewrite id_left in X.
  rewrites.
  apply proper_morphism; cat.
Qed.
Next Obligation.
  pose proof (naturality (from hom_adj) (a, b) (a, c) (id, f) g);
  simpl in X.
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
