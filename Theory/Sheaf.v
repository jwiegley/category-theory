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

Inductive ExistsT {A : Type} (P : A → Type) :
  ∀ {n : nat}, t A n → Type :=
  | ExistsT_cons_hd (m : nat) (x : A) (v : t A m) :
    P x → ExistsT (cons A x m v)
  | ExistsT_cons_tl (m : nat) (x : A) (v : t A m) :
    ExistsT v → ExistsT (cons A x m v).

(* A coverage on a category C consists of a function assigning to each object
   U ∈ C a collection of families of morphisms { fᵢ : Uᵢ → U } (i∈I), called
   covering families, such that

   if { fᵢ : Uᵢ → U } (i∈I) is a covering family
   and g : V → U is a morphism,
   then there exists a covering family { hⱼ : Vⱼ → V }
   such that each composite g ∘ hⱼ factors through some fᵢ. *)

Class Site (C : Category) := {
  covering_family (u : C) := sigT (Vector.t (∃ uᵢ, uᵢ ~> u));

  coverage (u : C) : covering_family u;

  coverage_condition
    (u  : C) (fs : covering_family u)
    (v  : C) (g  : v ~> u) :
    ∃ hs : covering_family v,
      ForallT (A := ∃ vⱼ, vⱼ ~> v) (λ '(vⱼ; hⱼ),
          ExistsT (A := ∃ uᵢ, uᵢ ~> u) (λ '(uᵢ; fᵢ),
              ∃ k : vⱼ ~> uᵢ, fᵢ ∘ k ≈ g ∘ hⱼ)
            (`2 fs))
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

Class Sheaf `{@Site C} (X : Presheaf C Sets) := {
  restriction :
    ∀ u : C,
      let '(i; f) := coverage u in
      ForallT
        (A := ∃ uᵢ, uᵢ ~> u)
        (λ '(uᵢ; fᵢ),
            ∀ xᵢ : X uᵢ,
              (∀ (v : C) (g : v ~> uᵢ),
                  ForallT
                    (A := ∃ uⱼ, uⱼ ~> u)
                    (λ '(uⱼ; fⱼ),
                      ∀ h : v ~> uⱼ,
                        fᵢ ∘ g ≈ fⱼ ∘ h →
                        ∀ xⱼ : X uⱼ,
                          fmap[X] g xᵢ = fmap[X] h xⱼ)
                    f) →
              ∃! x : X u, fmap[X] fᵢ x = xᵢ)
        f
}.
