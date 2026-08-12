Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Coq.
Require Import Coq.Sets.Ensembles.

Generalizable All Variables.

(** * The category of ensembles *)

(* nLab: https://ncatlab.org/nlab/show/Set
   nLab: https://ncatlab.org/nlab/show/category+of+sets
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_sets

   "Ens" (from the French/Bourbaki "Ensembles") is a traditional name for the
   category Set. In the textbook category of sets the objects are sets and the
   morphisms are *arbitrary* functions between them; injective, surjective and
   bijective functions are then characterized as the monos, epis and isos.

   This file does NOT build that classical category directly. Its objects are
   Coq [Ensemble]s (predicates [T -> Prop], i.e. subsets [A ⊆ T] of a carrier
   type [T]), packaged as a dependent pair [∃ T : Type, Ensemble T]. A morphism
   from [A : Ensemble TA] to [B : Ensemble TB] is a function [f : TA -> TB] on
   the *carrier types* satisfying

       ∀ x : TA,  x ∈ A  ↔  f x ∈ B,

   that is, [A = f⁻¹(B)]: [f] both preserves membership ([x ∈ A → f x ∈ B]) and
   reflects it ([f x ∈ B → x ∈ A]). Note this is membership preservation-and-
   reflection, NOT injectivity: it places no constraint of the form
   [f a = f b → a = b]. Two morphisms are identified when they agree pointwise
   on the whole carrier type. Identity and composition are the identity function
   and ordinary function composition. *)

(* Cross-reference: Mac Lane's Ens_V — objects the members of a set V of sets,
   arrows ALL functions between them (CWM 2nd ed., §I.2, printed p. 11) — is a
   DIFFERENT construction from the two categories below, and it lives in
   Instance/EnsV.v. There an object is a code x : V decoded by El : V → Type,
   and a morphism x ~> y is an arbitrary function El x → El y with no side
   condition at all; here a morphism carries the constraint A = f⁻¹(B). Both are
   kept: [Ens] and [EnsT] record membership preservation-and-reflection, while
   [EnsV] records Mac Lane's set-sized sub-universe of the category of sets. *)

Program Definition Ens : Category := {|
  obj     := ∃ T : Type, Ensemble T;
  hom     := fun A B =>
    ∃ f : ``A → ``B, ∀ x : ``A, In _ (projT2 A) x ↔ In _ (projT2 B) (f x);
  homset  := fun P Q => {| equiv := fun f g => ∀ x, ``f x = ``g x |};
  id      := fun _ => (id; _);
  compose := fun _ _ _ f g =>  (λ x, ``f (``g x); _)
|}.
Next Obligation. equivalence; rewrite H, H0; reflexivity. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. proper; rewrite H, H0; reflexivity. Qed.

(* nLab: https://ncatlab.org/nlab/show/Set
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_sets

   [EnsT T] is the same construction restricted to a single fixed carrier type
   [T]: objects are the [Ensemble]s (subsets) of [T], and a morphism from [A] to
   [B] is an endofunction [f : T -> T] with [∀ x, x ∈ A ↔ f x ∈ B], i.e.
   [A = f⁻¹(B)]. As above this is membership preservation-and-reflection, not
   injectivity. Morphisms are compared pointwise on [T], with identity and
   composition the identity function and function composition. *)

Program Definition EnsT (T : Type) : Category := {|
  obj     := Ensemble T;
  hom     := fun A B =>
    ∃ f : T → T, ∀ x : T, In _ A x ↔ In _ B (f x);
  homset  := fun P Q => {| equiv := fun f g => ∀ x, ``f x = ``g x |};
  id      := fun _ => (id; _);
  compose := fun _ _ _ f g =>  (λ x, ``f (``g x); _)
|}.
Next Obligation. equivalence; rewrite H, H0; reflexivity. Qed.
Next Obligation. firstorder. Qed.
Next Obligation. proper; rewrite H, H0; reflexivity. Qed.
