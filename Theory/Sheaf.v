Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Coq.Vectors.Vector.

Generalizable All Variables.

(* A C-valued presheaf on some category U.
  C is often taken to be Sets. *)
Definition Presheaf (U C : Category) := U^op ⟶ C.

(* The category of C-valued presheaves presheaves on a category U. *)
Definition Presheaves {U C : Category} := [U^op, C].

Definition Copresheaf (U C : Category) := U ⟶ C.

Definition Copresheaves {U C : Category} := [U, C].

(* Custom data type to express Forall propositions on vectors over Type. *)
Inductive ForallT {A : Type} (P : A → Type) :
  ∀ {n : nat}, t A n → Type :=
  | ForallT_nil : ForallT (nil A)
  | ForallT_cons (n : nat) (x : A) (v : t A n) :
    P x → ForallT v → ForallT (cons A x n v).

(* A coverage on a category C consists of a function assigning to each object
   U ∈ C a collection of families of morphisms { fᵢ : Uᵢ → U } (i∈I), called
   covering families, such that

   if { fᵢ : Uᵢ → U } (i∈I) is a covering family
   and g : V → U is a morphism,
   then there exists a covering family { hⱼ : Vⱼ → V }
   such that each composite g ∘ hⱼ factors through some fᵢ. *)

Class Site (C : Category) := {
  covering_family (u : C) :=
    ∃ I : nat, Vector.t (∃ v : C, v ~> u) I;

  coverage (u : C) : covering_family u;

  coverage_condition
    (u  : C) (fs : covering_family u)
    (v  : C) (g  : v ~> u) :
    ∃ (hs : covering_family v),
      ForallT
        (λ h : { w : C & w ~> v },
          ∃ (i : Fin.t (`1 fs)),
            let f := Vector.nth (`2 fs) i in
            ∃ (k : `1 h ~> `1 f),
              `2 f ∘ k ≈ g ∘ `2 h)
        (`2 hs)
}.

(* If { fᵢ : Uᵢ → U } (i∈I) is a family of morphisms with codomain U,
   a presheaf X : Cᵒᵖ → Set is called a sheaf for this family if:

   for any collection of elements xᵢ ∈ X(Uᵢ)
   such that,
     whenever g : V → Uᵢ and h : V → Uⱼ
     are such that fᵢ ∘ g = fⱼ ∘ h,
     we have X(g)(xᵢ) = X(h)(xⱼ),
   then there exists a unique x ∈ X(U)
   such that X(fᵢ)(x) = xᵢ for all i . *)

Class Sheaf {C : Category} `{@Site C} (X : Presheaf C Sets) := {
  restriction :
    ∀ u : C,
      let I := `1 (coverage u) in
      let f := `2 (coverage u) in
      ForallT
        (λ fᵢ : { v : C & v ~> u },
            ∀ (xᵢ : X (`1 fᵢ))
              (P : ∀ (v : C)
                     (g : v ~> `1 fᵢ)
                     (j : Fin.t I),
                  let fⱼ := Vector.nth f j in
                  ∀ (h : v ~> `1 fⱼ),
                    `2 fᵢ ∘ g ≈ `2 fⱼ ∘ h →
                    ∀ xⱼ : X (`1 fⱼ),
                      fmap[X] g xᵢ = fmap[X] h xⱼ),
              ∃! x : X u, fmap[X] (`2 fᵢ) x = xᵢ)
        f
}.
