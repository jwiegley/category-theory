Local Set Warnings "-notation-overridden". (* needed for Coq <8.16 *)

Require Import Coq.Classes.RelationClasses.
Require Import Coq.Setoids.Setoid.
Require Import Coq.Vectors.Fin.
Require Export Category.Lib.Foundation.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* nLab: https://ncatlab.org/nlab/show/setoid
   nLab: https://ncatlab.org/nlab/show/equivalence+relation
   Wikipedia: https://en.wikipedia.org/wiki/Setoid

   A setoid is a type [A] together with a distinguished equivalence relation
   [equiv] on it, written `≈`. Setoids stand in for quotient sets in a type
   theory that lacks quotient types: rather than identifying elements, one
   carries the equivalence explicitly and proves every operation respects it
   (the respectfulness/[Proper] discipline of Coq's generalized rewriting; see
   Coq.Classes.Morphisms). This is the foundational structure of the library:
   every hom is a setoid (a hom-setoid), so morphism equality throughout is the
   chosen `≈` rather than Coq's `=`. The relation lives in [crelation] (a
   [Type]-valued, hence proof-relevant, relation) so that equivalence proofs
   may carry computational content.

   The defining laws of [equiv], packaged as [Equivalence], are:
     reflexivity   x ≈ x
     symmetry      x ≈ y  ->  y ≈ x
     transitivity  x ≈ y  ->  y ≈ z  ->  x ≈ z *)
Class Setoid A := {
  equiv : crelation A;                  (* the equivalence ≈ on A *)
  setoid_equiv : Equivalence equiv      (* refl/symm/trans laws for ≈ *)
}.
#[export] Existing Instance setoid_equiv.

(* A setoid is in particular an [Equivalence], so its instance may be used
   wherever generalized rewriting expects one. *)
Coercion setoid_equiv : Setoid >-> Equivalence.

Notation "f ≈ g" := (equiv f g) (at level 79) : category_theory_scope.

(* Coq's [eq] is an equivalence relation; this is a universe-polymorphic
   repackaging of the standard-library proofs so that the setoids below can be
   built at an arbitrary universe level. *)
Definition eq_equivalence@{t u} {A : Type@{t}} : @Equivalence@{t u} A (@eq A) :=
  @Build_Equivalence@{t u} A
    (@eq A) (@eq_Reflexive A)
    (@eq_Symmetric A)
    (@eq_Transitive A).

(* A universe-polymorphic unit type. Used as the carrier of the terminal
   setoid (see Instance/One.v) where the polymorphism of the standard [unit]
   would be too restrictive. *)
Inductive poly_unit@{u} : Type@{u} := ttt.

(* The terminal/unit setoid: [poly_unit] under propositional equality. *)
Definition unit_setoid@{t u} : Setoid@{t u} poly_unit@{t} :=
  {| equiv := @eq poly_unit@{t}
   ; setoid_equiv := @eq_equivalence@{t u} poly_unit@{t} |}.

(* The discrete setoid on [A]: equivalence is just Coq's `=`. This is the
   tightest equivalence on a type and recovers ordinary (extensional) sets. *)
Definition eq_Setoid@{u} (A : Type@{u}) : Setoid@{u u} A :=
  Build_Setoid@{u _} A (λ f g, eq f g) eq_equivalence@{u u}.

(* The function setoid: two functions are equivalent when they agree
   pointwise up to the codomain's equivalence. This is extensional equality of
   functions, realised without the [funext] axiom by working up to `≈`. The
   low priority [| 9] keeps it from pre-empting more specific instances during
   resolution. *)
#[export]
Program Instance funext_Setoid
        {T : Type} (t : T → Type) (a b : T) `{Setoid (t b)} :
  Setoid (t a → t b) | 9 := {|
  equiv := λ f g, ∀ x, f x ≈ g x
|}.
Next Obligation.
  constructor; repeat intro.
  - reflexivity.
  - symmetry.
    now apply X.
  - now rewrite X, X0.
Qed.

(* The standard finite type [Fin.t n] as a discrete setoid under `=`. *)
#[export]
Program Instance Fin_Setoid {n} : Setoid (Fin.t n) := {|
  equiv := eq
|}.

(* Unique existence up to `≈`: a witness [unique_obj] satisfying [P], together
   with the proof [uniqueness] that any other witness is equivalent to it. This
   is the constructive content behind the `∃!` notation below and underlies the
   universal properties (limits, adjunctions) stated throughout the library. *)
Class Unique `{S : Setoid A} (P : A → Type) := {
  unique_obj : A;                          (* the witnessing element *)
  unique_property : P unique_obj;          (* it satisfies P *)
  uniqueness      : ∀ v : A, P v → unique_obj ≈ v;  (* and is unique up to ≈ *)
}.

Arguments unique_obj {_ _ _} _.
Arguments unique_property {_ _ _} _.
Arguments uniqueness {_ _ _} _.

Notation "∃! x .. y , P" := (Unique (fun x => .. (Unique (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity) : category_theory_scope.

(* Injectivity and surjectivity of a function between setoids, stated up to
   `≈` rather than `=`. The [not-a-class] warning is silenced because these
   single-field classes are used as plain propositions, not for instance
   resolution; it is restored immediately afterwards. *)
Local Set Warnings "-not-a-class".

(* [f] is injective when equal images force equivalent arguments. *)
Class injective {A : Type} `{Setoid A} {B : Type} `{Setoid B} (f : A -> B) :=
  { inj {x y} : f x ≈ f y -> x ≈ y }.

(* [f] is (split) surjective: every [y] has a chosen preimage up to `≈`. *)
Class surjective {A : Type} {B : Type} `{Setoid B} (f : A -> B) :=
  { surj {y} : { x & f x ≈ y} }.

Local Set Warnings "not-a-class".
