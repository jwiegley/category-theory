Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.

Generalizable All Variables.

(** * Monoid homomorphisms and the category of internal monoids *)

(* nLab: https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category

   Given internal monoids (x, mu[Mx], eta[Mx]) and (y, mu[My], eta[My]) in a
   monoidal category (C, ⨂, I), a morphism f : x ~> y is a monoid
   homomorphism when it commutes with the multiplications and units:

     multiplication square   f ∘ mu[Mx] ≈ mu[My] ∘ (f ⨂ f)
     unit triangle           f ∘ eta[Mx] ≈ eta[My]

   Monoid homomorphisms contain the identities and are closed under
   composition, so internal monoids and their homomorphisms form a category
   Mon(C), packaged here with sigma objects and homs — the same pattern as
   [Sub] in Construction/Subcategory.v, where morphism equivalence is
   equivalence of the underlying C-morphisms.  Projecting out the underlying
   object and morphism gives the forgetful functor Mon(C) ⟶ C, faithful by
   construction ([Mon_Forget_Faithful]). *)

Section MonoidHom.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class MonoidHom {x y : C} (Mx : Monoid x) (My : Monoid y) (f : x ~> y) :
  Type := {
  (* f preserves multiplication: f ∘ mu[Mx] ≈ mu[My] ∘ (f ⨂ f) *)
  hom_mu  : f ∘ mu[Mx] ≈ mu[My] ∘ (f ⨂ f);
  (* f preserves the unit: f ∘ eta[Mx] ≈ eta[My] *)
  hom_eta : f ∘ eta[Mx] ≈ eta[My]
}.

(* The identity is a monoid homomorphism. *)
Lemma MonoidHom_id {x} (Mx : Monoid x) : MonoidHom Mx Mx id.
Proof. split; cat. Qed.

(* Monoid homomorphisms are closed under composition: paste the two
   preservation squares, fusing (f ⨂ f) ∘ (g ⨂ g) into (f ∘ g) ⨂ (f ∘ g)
   by the interchange law [bimap_comp]. *)
Lemma MonoidHom_comp {x y z} {Mx : Monoid x} {My : Monoid y} {Mz : Monoid z}
      {f : y ~> z} {g : x ~> y} :
  MonoidHom My Mz f → MonoidHom Mx My g → MonoidHom Mx Mz (f ∘ g).
Proof.
  intros F G.
  split.
  - rewrite <- comp_assoc.
    rewrite (@hom_mu _ _ _ _ _ G).
    rewrite comp_assoc.
    rewrite (@hom_mu _ _ _ _ _ F).
    rewrite <- comp_assoc.
    now rewrite <- bimap_comp.
  - rewrite <- comp_assoc.
    rewrite (@hom_eta _ _ _ _ _ G).
    apply (@hom_eta _ _ _ _ _ F).
Qed.

(* Being a monoid homomorphism transports along ≈ (bimap respects ≈). *)
Lemma MonoidHom_equiv {x y} {Mx : Monoid x} {My : Monoid y} {f g : x ~> y} :
  f ≈ g → MonoidHom Mx My f → MonoidHom Mx My g.
Proof.
  intros E F.
  split.
  - rewrite <- E.
    apply (@hom_mu _ _ _ _ _ F).
  - rewrite <- E.
    apply (@hom_eta _ _ _ _ _ F).
Qed.

(* The category Mon(C) of internal monoids in C: objects are objects of C
   equipped with a monoid structure, morphisms are C-morphisms equipped with
   a proof of homomorphy, and equivalence is equivalence of the underlying
   morphisms — exactly the sigma packaging of [Sub] in
   Construction/Subcategory.v. *)
Program Definition Mon : Category := {|
  obj     := { x : C & Monoid x };
  hom     := fun X Y => { f : `1 X ~> `1 Y & MonoidHom `2 X `2 Y f };
  homset  := fun _ _ => {| equiv := fun f g => `1 f ≈ `1 g |};
  id      := fun X => (id; MonoidHom_id `2 X);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; MonoidHom_comp `2 f `2 g)
|}.

(* The forgetful functor Mon(C) ⟶ C projects out the underlying object and
   morphism; it is faithful by construction ([Mon_Forget_Faithful] below). *)
Program Definition Mon_Forget : Mon ⟶ C := {|
  fobj := fun X => `1 X;
  fmap := fun _ _ f => `1 f
|}.

(* Faithfulness is definitional: morphism equivalence in Mon(C) IS
   equivalence of the underlying C-morphisms, which is what [fmap] projects
   out. *)
#[export] Instance Mon_Forget_Faithful : Faithful Mon_Forget.
Proof.
  constructor.
  intros X Y f g E.
  exact E.
Qed.

End MonoidHom.

Arguments Mon C {M}.
