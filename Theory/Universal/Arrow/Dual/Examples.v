Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Construction.Product.
Require Import Category.Construction.Comma.
Require Import Category.Functor.Product.Internal.
Require Import Category.Functor.Diagonal.
Require Import Category.Adjunction.Diagonal.Product.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

Set Universe Polymorphism.

Generalizable All Variables.

(* [=( c )] lives in functor_scope (Functor/Diagonal.v); this file does not
   import any module that opens it as a side effect, so it is opened here. *)
Open Scope functor_scope.

(** * A worked example of the couniversal-arrow assembly *)

(* This file is the mirror image of Adjunction/GAFT/Examples.v, and is meant to
   be read beside it.  There, a family of UNIVERSAL arrows into the product
   bifunctor ×(C) reconstructs the binary diagonal as a LEFT adjoint,

       diagonal_UA d : UniversalArrow d (×(C))     ⟹     F ⊣ ×(C),  F ≅ Δ.

   Here, a family of COUNIVERSAL arrows out of the binary diagonal
   Δ = Diagonal_Product C reconstructs the product bifunctor as a RIGHT
   adjoint,

       product_CUA p : CouniversalArrow p Δ        ⟹     Δ ⊣ R,   R ≅ ×(C).

   The same classical adjunction Δ ⊣ ×, approached from the two opposite
   sides -- which is the point of the exercise: it demonstrates
   [AdjunctionFromCouniversalArrows] end to end on a non-degenerate example
   rather than merely typechecking it.

   The example is the classical one, and Functor/Diagonal.v already quotes it
   verbatim (from Wikipedia, "Diagonal functor"): "a product a × b is a
   universal arrow from Δ to ⟨a, b⟩.  The arrow comprises the projection
   maps."  An arrow FROM a functor TO an object is Mac Lane's couniversal one,
   so that sentence is exactly [product_CUA] below.  The couniversal morphism
   is the PROJECTION PAIR (exl, exr), and the mediating factorization is
   [fork], so the entire universal-property content of
   [product_couniversal_unique] is [ump_products] (Structure/Cartesian.v) with
   nothing added.

   ONE STRENGTH DIFFERENCE FROM THE PRIMAL EXAMPLE, worth recording because it
   runs the other way.  [GAFT_from_initials] ends in [Qed], so the left adjoint
   the primal file produces is opaque and only PROVABLY the diagonal; that file
   must exhibit a natural isomorphism to say so.  The assembly here is
   transparent all the way down, so the object action of the produced right
   adjoint reduces to the product on the nose --
   [product_via_couniversal_obj] closes by [eq_refl].  The natural isomorphism
   to ×(C) is still supplied ([product_via_couniversal_is_product]), because
   the ARROW action is a chosen unique factorization and there is no reason for
   it to reduce to ×(C)'s [fmap]; but the object half needs no argument at all.

   The concrete instantiation at [Sets] closes the file, so the family is
   inhabited by something other than a variable. *)

Section CouniversalExample.

Context `{C : Category}.
Context `{@Cartesian C}.

(* The projection pair, typed as a morphism of C ∏ C out of the diagonal.
   The ascription is load-bearing: as a bare pair the elaborator cannot see
   which category's composition the couniversal equation is asking for. *)
Definition proj_pair (p : C ∏ C) :
  Diagonal_Product C (fst p × snd p) ~{C ∏ C}~> p :=
  (@exl C _ (fst p) (snd p), @exr C _ (fst p) (snd p)).

(* The couniversal mapping property of the projection pair, in the exact shape
   consumed by [couniversal_arrow_from_UMP]: for p : C ∏ C the object
   fst p × snd p together with (exl, exr) : Δ (fst p × snd p) ~> p is a
   couniversal arrow from Δ to p.  Any f : Δ d' ~> p -- that is, any pair of
   morphisms (f₁ : d' ~> fst p, f₂ : d' ~> snd p) -- factors uniquely through
   the projections, the factorization being the fork f₁ △ f₂. *)
#[local] Obligation Tactic := idtac.

Program Definition product_couniversal_unique (p : C ∏ C) (d' : C)
  (f : Diagonal_Product C d' ~{C ∏ C}~> p) :
  ∃! g : d' ~{C}~> (fst p × snd p),
    f ≈ proj_pair p ∘ fmap[Diagonal_Product C] g :=
  {| unique_obj := fst f △ snd f |}.
Next Obligation.
  (* existence: the fork factors both components through the projections *)
  intros p d' f; simpl; split.
  - now rewrite exl_fork.
  - now rewrite exr_fork.
Qed.
Next Obligation.
  (* uniqueness: any factorizer agrees with the fork, by [ump_products] *)
  intros p d' f v [Hv1 Hv2]; simpl in *.
  symmetry.
  apply ump_products; split.
  - now symmetry.
  - now symmetry.
Qed.

(* Packaged as a [CouniversalArrow]: Mac Lane's "a product is a couniversal
   arrow from the diagonal". *)
Definition product_CUA (p : C ∏ C) :
  CouniversalArrow p (Diagonal_Product C) :=
  couniversal_arrow_from_UMP p (Diagonal_Product C) (fst p × snd p)
    (proj_pair p)
    (product_couniversal_unique p).

(* The couniversal object is the product, and the couniversal arrow is the
   projection pair -- both by convertibility, since
   [couniversal_arrow_from_UMP] is [Defined]. *)
Corollary product_CUA_obj (p : C ∏ C) :
  coarrow_obj (product_CUA p) = (fst p × snd p).
Proof. reflexivity. Qed.

Corollary product_CUA_arrow (p : C ∏ C) :
  coarrow (product_CUA p) = proj_pair p.
Proof. reflexivity. Qed.

(** ** The terminal-object reading, exercised *)

(* [couniversal_arrow_terminal] applied to a real couniversal arrow: the
   product, with its projections, is a TERMINAL object of the comma category
   Δ ↓ =(p) -- Mac Lane's §III.1 Definition 3 read at his own example. *)
Definition product_terminal (p : C ∏ C) :
  @Terminal (Diagonal_Product C ↓ =(p)) :=
  couniversal_arrow_terminal (product_CUA p).

Corollary product_terminal_obj (p : C ∏ C) :
  `1 (@terminal_obj _ (product_terminal p)) = (fst p × snd p, ttt).
Proof. reflexivity. Qed.

(* ... and the passage back keeps both the object and the arrow. *)
Corollary product_terminal_round (p : C ∏ C) :
  coarrow (couniversal_arrow_of_terminal (product_terminal p))
    = coarrow (product_CUA p).
Proof. reflexivity. Qed.

(** ** The adjunction *)

(* Run [AdjunctionFromCouniversalArrows] on that family.  The result is a
   genuine adjunction Δ ⊣ R, produced entirely through the couniversal-arrow
   machinery of Theory/Universal/Arrow/Dual.v. *)
Definition product_via_couniversal_functor : C ∏ C ⟶ C :=
  RightAdjointFunctorFromCouniversalArrows (Diagonal_Product C) product_CUA.

Definition product_via_couniversal :
  Diagonal_Product C ⊣ product_via_couniversal_functor :=
  AdjunctionFromCouniversalArrows (Diagonal_Product C) product_CUA.

(* The object action of the produced right adjoint IS the product, on the nose
   -- the strength the primal GAFT example cannot state, its own functor being
   [Qed]-opaque. *)
Corollary product_via_couniversal_obj (p : C ∏ C) :
  fobj[product_via_couniversal_functor] p = (fst p × snd p).
Proof. reflexivity. Qed.

(* ... and its counit is the projection pair, up to `≈` (see the second
   boundary recorded in the header of Theory/Universal/Arrow/Dual.v: the
   transpose leaves a [fmap_id]/[id_right] residue). *)
Corollary product_via_couniversal_counit (p : C ∏ C) :
  @counit (C ∏ C) C (Diagonal_Product C) product_via_couniversal_functor
          product_via_couniversal p
    ≈ proj_pair p.
Proof. exact (counit_couniversal (Diagonal_Product C) product_CUA p). Qed.

(* The arrow action is a chosen unique factorization, so nothing forces it to
   reduce to ×(C)'s [fmap]; what does hold is that the two functors are
   naturally isomorphic, right adjoints to a fixed functor being unique up to
   natural isomorphism ([right_adjoint_iso], Theory/Adjunction.v).  Pitting the
   couniversally assembled adjunction against the concrete
   [Diagonal_Product_Adjunction] over their common left adjoint Δ delivers it,
   dually to [diagonal_product_via_gaft_is_diagonal]. *)
Definition product_via_couniversal_is_product :
  product_via_couniversal_functor ≈ ×(C) :=
  right_adjoint_iso (Diagonal_Product C)
    product_via_couniversal_functor (×(C))
    product_via_couniversal
    (Diagonal_Product_Adjunction C).

End CouniversalExample.

(** ** A concrete instantiation *)

(* The family above is inhabited by something other than a variable: [Sets] is
   cartesian, so every pair of setoids has its couniversal arrow from the
   diagonal, and the assembled adjunction is an adjunction of [Sets]. *)

Definition Sets_product_CUA (p : Sets ∏ Sets) :
  CouniversalArrow p (Diagonal_Product Sets) :=
  @product_CUA Sets Sets_Cartesian p.

Definition Sets_product_via_couniversal :
  Diagonal_Product Sets ⊣ @product_via_couniversal_functor Sets Sets_Cartesian :=
  @product_via_couniversal Sets Sets_Cartesian.

Corollary Sets_product_via_couniversal_obj (p : Sets ∏ Sets) :
  fobj[@product_via_couniversal_functor Sets Sets_Cartesian] p
    = @product_obj Sets Sets_Cartesian (fst p) (snd p).
Proof. reflexivity. Qed.
