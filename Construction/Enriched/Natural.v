Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.Enriched.

Generalizable All Variables.

(** V-natural transformations between K-enriched functors. *)

(* nLab: https://ncatlab.org/nlab/show/enriched+natural+transformation

   Given two K-enriched functors F, G : C ⟶ D between K-categories, a
   K-enriched (or V-natural) transformation σ assigns to every object x of C
   a component σ_x : I ~> (F x ⟿ G x) in K, naming an element of the hom-object
   from F x to G x.  The naturality condition is the equality of two
   K-morphisms (x ⟿ y) ~> (F x ⟿ G y): whiskering σ_y after F and whiskering
   σ_x before G must agree.  The two composites are set up over the tensor unit
   using ecompose (the enriched composition of D), with the unitors of K
   supplying the coercions that make the sources match — mirroring the
   unit_left / unit_right plumbing of eid_left / eid_right in Enriched.v.

   Taking K = Set recovers ordinary natural transformations: σ_x : I ~> (F x ⟿
   G x) picks out a morphism component, and the naturality square becomes the
   usual commuting square. *)

Class EnrichedTransform {K : Category} `{@Monoidal K} {C D : Enriched K}
      (F G : EnrichedFunctor K C D) := {
  (* component at x: names the morphism F x ~> G x inside the hom-object *)
  etransform (x : C) :
    I ~{K}~> @ehom K _ D (@efobj K _ C D F x) (@efobj K _ C D G x);

  (* V-naturality: the F-then-σ and σ-then-G whiskerings agree, as an
     equality of K-morphisms (x ⟿ y) ~> (F x ⟿ G y).

     Left path : coerce (x ⟿ y) to I ⨂ (x ⟿ y) via unit_left⁻¹, then tensor
       σ_y : I ~> (F y ⟿ G y) with efmap F : (x ⟿ y) ~> (F x ⟿ F y), and
       compose in D to land in (F x ⟿ G y).
     Right path: coerce (x ⟿ y) to (x ⟿ y) ⨂ I via unit_right⁻¹, then tensor
       efmap G : (x ⟿ y) ~> (G x ⟿ G y) with σ_x : I ~> (F x ⟿ G x), and
       compose in D to land in (F x ⟿ G y). *)
  enaturality {x y : C} :
    ecompose ∘ (etransform y ⨂ @efmap K _ C D F x y) ∘ unit_left⁻¹
      << @ehom K _ C x y ~~>
         @ehom K _ D (@efobj K _ C D F x) (@efobj K _ C D G y) >>
    ecompose ∘ (@efmap K _ C D G x y ⨂ etransform x) ∘ unit_right⁻¹
}.

(** The componentwise setoid on V-natural transformations: two transformations
    are equal when all their components agree in K. *)

Program Definition EnrichedTransform_Setoid
        {K : Category} `{@Monoidal K} {C D : Enriched K}
        (F G : EnrichedFunctor K C D) :
  Setoid (EnrichedTransform F G) := {|
  equiv := fun σ τ =>
    ∀ x, @etransform K _ C D F G σ x ≈ @etransform K _ C D F G τ x
|}.
Next Obligation.
  constructor.
  - intros σ x; reflexivity.
  - intros σ τ Hστ x; symmetry; apply Hστ.
  - intros σ τ ρ Hστ Hτρ x;
    now transitivity (@etransform K _ C D F G τ x).
Qed.
