Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.

Generalizable All Variables.

(** * Internal semigroups in a monoidal category, and the category Smgrp *)

(* nLab: https://ncatlab.org/nlab/show/semigroup
   nLab: https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.4, printed p. 144 (PDF p. 153) —
         maclane:VI.4:construction1

   Mac Lane opens §VI.4, from the page image: "A semigroup is a set S
   equipped with an associative binary operation ν: S × S → S", and he
   writes Smgrp for "the category of all small semigroups", with the
   forgetful functor G : Smgrp → Set.  This file states the definition
   internally, as Theory/Algebra/Monoid.v states monoids: a semigroup on
   an object X of a monoidal category (C, ⨂, I) is a multiplication
   smu : X ⨂ X ~> X with

     associativity  smu ∘ (smu ⨂ id) ≈ smu ∘ (id ⨂ smu) ∘ α

   (α = to tensor_assoc) and nothing more: no unit, so no unitor.
   [SemigroupHom] asks of f : x ~> y the multiplication square
   f ∘ smu ≈ smu ∘ (f ⨂ f) alone.  [Smgrp C] packages the semigroups and
   their homomorphisms with sigma objects and homs, arrows compared by
   their underlying arrows, exactly as Theory/Algebra/Monoid/Hom.v
   packages [Mon C]; [Smgrp_Forget] projects, faithfully by construction
   ([Smgrp_Forget_Faithful]).  [Mon_Smgrp] : Mon C ⟶ Smgrp C forgets the
   unit; after the two forgetful functors it is [Mon_Forget] on objects
   and on arrows at [eq_refl] ([Mon_Smgrp_Forget_obj],
   [Mon_Smgrp_Forget_map]).  Mac Lane's Smgrp is [Smgrp] at (Sets, ×),
   Instance/Smgrp.v's [SmgrpSets]; the free semigroup, the word monad W
   and the monadicity of Smgrp over Set are Instance/Smgrp.v and
   Instance/Smgrp/Word.v.

   NAMES.  The class [Semigroup] is the sibling of Theory/Algebra/
   Monoid.v's [Monoid], internal to an arbitrary monoidal category, and
   not of Structure/Monoid.v's cartesian [MonoidObject], from which
   Structure/Lattice.v builds its lattice objects.  It shares its short
   name with Theory/Coq/Semigroup.v's ops-only class, as [Monoid] shares
   its name with Theory/Coq/Monoid.v's; no file of the tree requires
   both.  No [PropEquiv] is asked (Lib/Setoid/Propositional.v's regime
   is that of the algebraic records CMon, Grp and the rest): [Mon] does
   not carry it either, and no adjoint functor theorem is involved here.

   STRENGTHS.  The two readbacks hold at [eq_refl], and
   Test/ProbeWord470.v restates them (C1, C2).  The laws of the category
   and of the two functors are the [Program] obligations of [Smgrp],
   [Smgrp_Forget] and [Mon_Smgrp], twelve, closed by the ambient tactic as
   in Theory/Algebra/Monoid/Hom.v; the four lemmas end [Qed], and no proof
   ends [Defined] (counted by token).  Nothing here is refused.

   UNIVERSES, read off [About].  [Smgrp@{u u0 u1 u2}],
   [Smgrp_Forget_Faithful] and the two readbacks have exactly the block of
   [Mon@{u u0 u1 u2}] (u0 < u2, u <= u1, u0 <= u1, with the caps of the
   standard library's sigma and pair projections), and [Smgrp_Forget],
   [Mon_Smgrp] and their six obligations that of [Mon_Forget] (u0 < u1,
   u <= u2, u0 <= u2, with those caps).  The class, the homomorphism
   record, their constructors and fields, the three homomorphism lemmas,
   [Monoid_Semigroup], [MonoidHom_SemigroupHom] and four of [Smgrp]'s six
   obligations bind @{u u0} with caps only; the other two bind @{u u0 u1}
   with u0 < u1.  No [Set] and no equation.  On Coq 8.20.1 every constant
   here has the same binder and the same constraints between bound
   levels; on Coq 8.19.2 so does every constant but the six obligations
   of [Smgrp], which bind one or two levels more (compared by script,
   the names of the standard library's caps differing by version).

   NOT DELIVERED.  Free semigroups, limits and colimits of semigroups in
   this generality; commutative semigroups; the semigroup of a lax
   monoidal functor; the unit-free variant of Structure/Lattice.v's
   lattice objects. *)

Section Semigroup.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class Semigroup (X : C) : Type := {
  smu : X ⨂ X ~> X;             (* multiplication ν : X ⨂ X ~> X *)

  (* associativity: smu ∘ (smu ⨂ id) ≈ smu ∘ (id ⨂ smu) ∘ α *)
  smu_assoc :
    smu ∘ bimap smu id[X]
      ≈ smu ∘ bimap id[X] smu ∘ to tensor_assoc
}.

End Semigroup.

Arguments smu {C M X _}.

Notation "'smu[' Sg ]" := (@smu _ _ _ Sg)
  (at level 9, format "'smu[' Sg ]") : morphism_scope.

Section SemigroupHom.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class SemigroupHom {x y : C} (Sx : Semigroup x) (Sy : Semigroup y)
      (f : x ~> y) : Type := {
  (* f preserves multiplication: f ∘ smu[Sx] ≈ smu[Sy] ∘ (f ⨂ f) *)
  shom_mu : f ∘ smu[Sx] ≈ smu[Sy] ∘ (f ⨂ f)
}.

(* The identity is a semigroup homomorphism. *)
Lemma SemigroupHom_id {x} (Sx : Semigroup x) : SemigroupHom Sx Sx id.
Proof. constructor; cat. Qed.

(* Semigroup homomorphisms compose: paste the two preservation squares,
   fusing (f ⨂ f) ∘ (g ⨂ g) into (f ∘ g) ⨂ (f ∘ g) by [bimap_comp]. *)
Lemma SemigroupHom_comp {x y z} {Sx : Semigroup x} {Sy : Semigroup y}
      {Sz : Semigroup z} {f : y ~> z} {g : x ~> y} :
  SemigroupHom Sy Sz f → SemigroupHom Sx Sy g → SemigroupHom Sx Sz (f ∘ g).
Proof.
  intros F G.
  constructor.
  rewrite <- comp_assoc.
  rewrite (@shom_mu _ _ _ _ _ G).
  rewrite comp_assoc.
  rewrite (@shom_mu _ _ _ _ _ F).
  rewrite <- comp_assoc.
  now rewrite <- bimap_comp.
Qed.

(* Being a semigroup homomorphism transports along ≈. *)
Lemma SemigroupHom_equiv {x y} {Sx : Semigroup x} {Sy : Semigroup y}
      {f g : x ~> y} :
  f ≈ g → SemigroupHom Sx Sy f → SemigroupHom Sx Sy g.
Proof.
  intros E F.
  constructor.
  rewrite <- E.
  apply (@shom_mu _ _ _ _ _ F).
Qed.

(* The category Smgrp(C) of internal semigroups in C, packaged with sigma
   objects and homs exactly as Theory/Algebra/Monoid/Hom.v packages Mon(C):
   morphism equivalence is equivalence of the underlying C-morphisms. *)
Program Definition Smgrp : Category := {|
  obj     := { x : C & Semigroup x };
  hom     := fun X Y => { f : `1 X ~> `1 Y & SemigroupHom `2 X `2 Y f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun X => (id; SemigroupHom_id `2 X);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; SemigroupHom_comp `2 f `2 g)
|}.

(* The forgetful functor Smgrp(C) ⟶ C projects out the underlying object
   and morphism. *)
Program Definition Smgrp_Forget : Smgrp ⟶ C := {|
  fobj := fun X => `1 X;
  fmap := fun _ _ f => `1 f
|}.

(* Faithful by construction, as [Mon_Forget_Faithful] is. *)
#[export] Instance Smgrp_Forget_Faithful : Faithful Smgrp_Forget.
Proof.
  constructor.
  intros X Y f g E.
  exact E.
Qed.

(* Every internal monoid is an internal semigroup: forget the unit. *)
Definition Monoid_Semigroup {x : C} (Mx : Monoid x) : Semigroup x :=
  {| smu := mu[Mx]; smu_assoc := @mu_assoc _ _ _ Mx |}.

(* Every monoid homomorphism is a semigroup homomorphism. *)
Definition MonoidHom_SemigroupHom {x y : C} {Mx : Monoid x} {My : Monoid y}
           {f : x ~> y} (H : MonoidHom Mx My f) :
  SemigroupHom (Monoid_Semigroup Mx) (Monoid_Semigroup My) f :=
  @Build_SemigroupHom _ _ (Monoid_Semigroup Mx) (Monoid_Semigroup My) f
    (@hom_mu _ _ _ _ _ _ _ H).

(* The functor Mon(C) ⟶ Smgrp(C) that forgets the unit. *)
Program Definition Mon_Smgrp : Mon C ⟶ Smgrp := {|
  fobj := fun X => (`1 X; Monoid_Semigroup `2 X);
  fmap := fun _ _ f => (`1 f; MonoidHom_SemigroupHom `2 f)
|}.

(* Forgetting the unit and then the multiplication is forgetting both. *)
Example Mon_Smgrp_Forget_obj (X : Mon C) :
  fobj[Smgrp_Forget] (fobj[Mon_Smgrp] X) = fobj[Mon_Forget] X := eq_refl.

Example Mon_Smgrp_Forget_map {X Y : Mon C} (f : X ~> Y) :
  fmap[Smgrp_Forget] (fmap[Mon_Smgrp] f) = fmap[Mon_Forget] f := eq_refl.

End SemigroupHom.

Arguments Smgrp C {M}.
