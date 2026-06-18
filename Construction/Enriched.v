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
