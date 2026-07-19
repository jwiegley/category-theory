Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

Reserved Infix "⟿" (at level 90, right associativity).

(** A category enriched over a monoidal category K (a K-category). *)

(* nLab: https://ncatlab.org/nlab/show/enriched+category
   Wikipedia: https://en.wikipedia.org/wiki/Enriched_category

   Given a monoidal category (K, ⨂, I) playing the role of V, a K-enriched
   category replaces each hom-set by a hom-object (x ⟿ y) : K.  Composition
   is the K-morphism ecompose : (y ⟿ z) ⨂ (x ⟿ y) ~> (x ⟿ z) (the codomain
   factor on the left, mirroring ordinary composition order), and the
   identity is the K-morphism eid : I ~> (x ⟿ x) that names the identity
   inside the hom-object.  The three coherence axioms below assert, as
   equalities of K-morphisms, the associativity diagram and the two unit
   diagrams of Kelly's definition, with unit_left, unit_right and
   tensor_assoc supplying the unitors and associator of K.

   Taking K = Set recovers ordinary (locally small) categories: hom-objects
   become hom-sets, eid picks out an element, and ecompose a function.
   Taking K = Ab gives preadditive categories, with bilinear composition. *)

(* Why enrichment, and the bases that tune it

   nLab:      https://ncatlab.org/nlab/show/enriched+category
   Wikipedia: https://en.wikipedia.org/wiki/Enriched_category
   Paper: Eilenberg, Kelly, "Closed Categories", in Proceedings of the
          Conference on Categorical Algebra (La Jolla 1965), Springer
          1966, pp. 421-562
   Book:  Kelly, "Basic Concepts of Enriched Category Theory", London
          Mathematical Society Lecture Note Series 64, Cambridge University
          Press 1982; reprinted Repr. Theory Appl. Categ. No. 10 (2005)
   Paper: Lawvere, "Metric spaces, generalized logic, and closed
          categories", Rend. Sem. Mat. Fis. Milano 43 (1973), 135-166

   Ordinary category theory records between two objects only a SET of
   morphisms, and thereby discards whatever structure that collection
   naturally carries.  Yet what lies between two objects very often carries
   more than a bare set: the linear maps between vector spaces form a
   vector space, the maps between chain complexes a chain complex, the
   arrows between two points of a preorder are one or none — a truth value
   — and the separation between two points of a metric space is a distance.
   Enrichment is the discipline that keeps this structure rather than
   discarding it: the hom-object (x ⟿ y) of the header is asked to live in
   whatever monoidal base K carries the structure at hand, its tensor
   composing hom-objects and its unit naming identities, and a theorem
   proved over K then respects that structure by construction (nLab).

   The definition descends from Eilenberg and Kelly, "Closed Categories"
   (La Jolla 1965, Springer 1966), which introduced the closed and monoidal
   machinery from which the coherence axioms are drawn, and was consolidated
   into the standard reference by Kelly's "Basic Concepts of Enriched
   Category Theory" (1982), the source for the enriched Yoneda lemma and
   weighted limits.  A complete, cocomplete, closed symmetric monoidal base,
   the setting over which the theory is usually developed, is often called a
   cosmos (nLab).

   The base acts as a dial that sets what a hom IS, and each classical
   setting names a familiar theory (nLab): K = Set recovers ordinary locally
   small categories; K = Ab gives preadditive categories with bilinear
   composition, the entry to homological algebra; K = 2, the two truth
   values under meet, gives preorders; K = Cat gives strict 2-categories;
   K = Vect and K = Top give linear and topological categories; K = Ch, the
   chain complexes, gives the dg-categories behind derived and triangulated
   categories; and K = sSet, the simplicial sets, gives the simplicial
   categories that serve as a model for (∞,1)-categories.  Lawvere observed
   that a category enriched over the non-negative extended reals ordered by
   ≥ under addition is exactly a generalized metric space: the hom-object is
   a distance, [ecompose] is the triangle inequality, and [eid] records that
   the self-distance is zero (Lawvere 1973).  This is the "generalized
   logic" reading, under which preorder- and quantale-enriched categories
   become systems of generalized truth values.  Any closed monoidal base is
   moreover enriched in itself through its internal hom, as
   Structure/Closed.v records.

   Enrichment is not the same as an internal category: an enriched
   hom-object lives IN K, one object per pair of external objects, whereas
   an internal category packs all objects and morphisms into two K-objects
   with structure maps, the two agreeing in good cases and diverging in
   general (nLab).

   Two of the dial settings are made literally computational here.
   [Category_is_Enriched_over_Set] is a definitional round trip over
   [Sets_Product_Monoidal]: a Sets-enriched category unfolds to an ordinary
   [Category] and back, [eid] at the unit point supplying the identity and
   [ecompose] on a pair (f, g) the composite, so enrichment over Set adds
   nothing, as it must; [Functor_is_Enriched_over_Set] does the same for
   [EnrichedFunctor].  Construction/Enriched/Two.v sharpens the slogan that
   a preorder is a category with at most one arrow per hom: a hom-object is a
   truth value, [eid] forces the diagonal (reflexivity), [ecompose] under
   meet forces transitivity, and the three coherence laws hold on their own
   because the base is thin, carrying at most one parallel arrow, so any two
   coincide ([Enriched_Two_preorder], [EnrichedFunctor_Two_monotone], both
   directions).  The surrounding structure sits alongside: the enriched
   natural transformations [EnrichedTransform]
   (Construction/Enriched/Natural.v) and their Sets-level recovery
   [EnrichedTransform_is_Transform] (Construction/Enriched/Sets.v), the
   identity and composite functors of Construction/Enriched/Compose.v, the
   ordinary functor category of Construction/Enriched/Fun.v, and the
   hand-built Ab-enriched example of Structure/Preadditive.v and
   Structure/Additive.v; Instance/Poset.v reads posets as truth-value
   enrichment. *)

Class Enriched (K : Category) `{@Monoidal K} := {
  eobj : Type;

  ehom : eobj → eobj → K where "a ⟿ b" := (ehom a b);

  eid {x} : I ~{K}~> (x ⟿ x);                                  (* identity j_x *)
  ecompose {x y z} : (y ⟿ z) ⨂ (x ⟿ y) ~{K}~> (x ⟿ z);        (* composition *)

  (* left unit: ecompose after eid on the codomain factor is unit_left *)
  eid_left  {x y} :
    ecompose ∘ eid ⨂ id << I ⨂ (x ⟿ y) ~~> (x ⟿ y) >> unit_left;
  (* right unit: ecompose after eid on the domain factor is unit_right *)
  eid_right {x y} :
    ecompose ∘ id ⨂ eid << (x ⟿ y) ⨂ I ~~> (x ⟿ y) >> unit_right;

  (* associativity: the two composition paths agree up to tensor_assoc *)
  ecompose_assoc {x y z w} :
    ecompose ∘ ecompose ⨂ id
      << ((z ⟿ w) ⨂ (y ⟿ z)) ⨂ (x ⟿ y) ~~> (x ⟿ w) >>
    ecompose ∘ id ⨂ ecompose ∘ tensor_assoc
}.

Infix "⟿" := ehom (at level 90, right associativity).

Coercion eobj : Enriched >-> Sortclass.

(** A K-enriched functor between K-categories. *)

(* nLab: https://ncatlab.org/nlab/show/enriched+functor
   Wikipedia: https://en.wikipedia.org/wiki/Enriched_category#Enriched_functors

   An object map efobj together with hom-object maps efmap : (x ⟿ y) ~>
   (efobj x ⟿ efobj y) in K, commuting with eid and ecompose. *)

Class EnrichedFunctor
      (K : Category) `{@Monoidal K}
      (C : Enriched K) (D : Enriched K) := {
  efobj : C → D;
  efmap {x y} : (x ⟿ y) ~{K}~> (efobj x ⟿ efobj y);

  (* preserves identity: efmap takes eid to eid *)
  efmap_id : ∀ x,
    efmap ∘ eid << I ~~> (efobj x ⟿ efobj x) >> eid;
  (* preserves composition: efmap commutes with ecompose *)
  efmap_comp : ∀ x y z,
    ecompose ∘ efmap ⨂ efmap
      << (y ⟿ z) ⨂ (x ⟿ y) ~~> (efobj x ⟿ efobj z) >>
    efmap ∘ ecompose
}.

Require Import Category.Instance.Sets.

Theorem Category_is_Enriched_over_Set : Enriched Sets ↔ Category.
Proof.
  split; intros.
  - unshelve refine
      {| obj     := eobj
       ; hom     := @ehom _ _ X
       ; homset  := @ehom _ _ X
       ; id      := fun x => @eid _ _ X x ttt
       ; compose := fun x y z f g => @ecompose _ _ X x y z (f, g) |}.
    + intros.
      proper.
      destruct X.
      simpl in *.
      destruct (ecompose0 x y z).
      simpl in *.
      now apply proper_morphism; simpl; auto.
    + intros.
      destruct X.
      simpl in *.
      now sapply (eid_left0 x y (ttt, f)).
    + intros.
      destruct X.
      simpl in *.
      now sapply (eid_right0 x y (f, ttt)).
    + intros.
      destruct X.
      simpl in *.
      symmetry.
      now sapply (ecompose_assoc0 x y z w ((f, g), h)).
    + intros.
      destruct X.
      simpl in *.
      now sapply (ecompose_assoc0 x y z w ((f, g), h)).
  - unshelve refine
      (@Build_Enriched Sets Sets_Product_Monoidal
          obj
          (fun x y : X => {| carrier := x ~> y |})
          (fun x => {| morphism := fun _ => id[x] |})
          (fun x y z => {| morphism := fun p => fst p ∘ snd p |})
          _ _ _).
    + now apply homset.
    + now proper.
    + proper; simpl.
      apply compose_respects;
      now match goal with
        [ H : _ ≈ _ |- _ ] => apply H
      end.
    + now simpl; intros; cat.
    + now simpl; intros; cat.
    + now simpl; intros; cat.
Defined.

Theorem Functor_is_Enriched_over_Set (C D : Category) :
  EnrichedFunctor
    Sets
    (snd Category_is_Enriched_over_Set C)
    (snd Category_is_Enriched_over_Set D)
    ↔ (C ⟶ D).
Proof.
  split; intros.
  - destruct X; simpl in *.
    construct.
    + now apply efobj0.
    + now apply efmap0.
    + proper.
      now apply efmap0.
    + now apply efmap_id0.
    + simpl in *.
      now srewrite (efmap_comp0 x y z (f, g)).
  - destruct X; simpl in *.
    construct.
    + now apply fobj.
    + construct.
      * now apply fmap.
      * proper.
        now apply fmap_respects.
    + now apply fmap_id.
    + simpl.
      symmetry.
      now apply fmap_comp.
Defined.
