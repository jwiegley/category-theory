Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Adjunction.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Adjunctions: hom-set form ⇔ unit/counit form *)

(* nLab: https://ncatlab.org/nlab/show/adjoint+functor
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   The two standard presentations of an adjunction F ⊣ U, with F : D ⟶ C the
   left adjoint and U : C ⟶ D the right adjoint, are equivalent, and this file
   exhibits both directions of that equivalence.

   The hom-set form (Theory.Adjunction, F ⊣ U) packages a natural isomorphism
   adj : (F a ~{C}~> b) ≊ (a ~{D}~> U b). The unit/counit form
   (Adjunction.Natural.Transformation, F ∹ U) packages a unit η : Id ⟹ U ◯ F
   and counit ε : F ◯ U ⟹ Id satisfying the two triangle (zig-zag) identities.

   [Adjunction_from_Transform] builds the hom-set isomorphism from the
   unit/counit data using the universal-arrow transposes: the forward map sends
   f : F a ~> b to fmap[U] f ∘ η a (so η a is a universal arrow from a to U —
   every a ~> U b factors through it), and the backward map sends g : a ~> U b
   to ε b ∘ fmap[F] g. Naturality of η and ε plus the triangle identities make
   these mutually inverse and natural. [Adjunction_to_Transform] runs the
   reverse direction, reading off η and ε as the transposes of the identities
   and deriving their naturality and triangle laws from naturality of adj. *)

Section AdjunctionToTransform.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.

Program Definition Adjunction_from_Transform (A : F ∹ U) : F ⊣ U := {|
  adj := fun a b =>
    {| to   := {| morphism := fun f => fmap f ∘ transform[unit[A]] a |}
     ; from := {| morphism := fun f => transform[counit[A]] b ∘ fmap f |} |}
|}.
Next Obligation. proper; now rewrites. Qed.
Next Obligation. proper; now rewrites. Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite (@naturality _ _ _ _ unit[A] _ _ x).
  rewrite comp_assoc; simpl.
  srewrite (@Transformation.fmap_counit_unit); cat.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- (@naturality _ _ _ _ counit[A] _ _ x).
  rewrite <- comp_assoc; simpl.
  srewrite (@Transformation.counit_fmap_unit); cat.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite (@naturality _ _ _ _ unit[A] _ _ g).
  now rewrite comp_assoc.
Qed.
Next Obligation.
  rewrite fmap_comp.
  now rewrite comp_assoc.
Qed.
Next Obligation.
  rewrite fmap_comp.
  now rewrite comp_assoc.
Qed.
Next Obligation.
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- (@naturality _ _ _ _ counit[A] _ _ f).
  now rewrite <- comp_assoc.
Qed.

Program Definition Adjunction_to_Transform {A : F ⊣ U} : F ∹ U := {|
  Transformation.unit   := {| transform := fun _ => unit |};
  Transformation.counit := {| transform := fun _ => counit |}
|}.
Next Obligation.
  unfold unit.
  rewrite <- to_adj_nat_r, <- to_adj_nat_l; cat.
Qed.
Next Obligation.
  unfold unit.
  rewrite <- to_adj_nat_r, <- to_adj_nat_l; cat.
Qed.
Next Obligation.
  unfold counit.
  rewrite <- from_adj_nat_r, <- from_adj_nat_l; cat.
Qed.
Next Obligation.
  unfold counit.
  rewrite <- from_adj_nat_r, <- from_adj_nat_l; cat.
Qed.
Next Obligation.
  unfold unit, counit.
  rewrite <- from_adj_nat_l; cat.
  apply (@iso_from_to _ _ _ adj _).
Qed.
Next Obligation.
  unfold unit, counit.
  rewrite <- to_adj_nat_r; cat.
  apply (@iso_to_from _ _ _ adj _).
Qed.

End AdjunctionToTransform.
