Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Naturality.
Require Export Category.Structure.Monoidal.Braided.

Generalizable All Variables.

Section BalancedMonoidal.

Context {C : Category}.

(** Balanced monoidal category. *)

(* nLab: https://ncatlab.org/nlab/show/balanced+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Ribbon_category

   A balanced monoidal category is a braided monoidal category equipped with a
   natural isomorphism, the twist (or balancing),

       theta : x ≅ x                      ([twist]),

   self-natural (theta is a natural automorphism of the identity functor) and
   compatible with the braiding (beta = [braid]). The defining coherence law
   relates the twist on a tensor product to the double braiding. In the
   orientation of both sources, writing composition right to left,

       theta_{x⊗y} = beta_{y,x} ∘ beta_{x,y} ∘ (theta_x ⊗ theta_y)
                                          ([balanced_to_commutes]),

   together with the unit condition

       theta_I = id                       ([balanced_to], [balanced_from]).

   This file states the coherence law in the naturality-shifted form

       theta_{x⊗y} = beta_{y,x} ∘ (theta_y ⊗ theta_x) ∘ beta_{x,y},

   which is equal to the source form: naturality of [braid] gives
   beta_{x,y} ∘ (theta_x ⊗ theta_y) = (theta_y ⊗ theta_x) ∘ beta_{x,y}, so the
   factor (theta_y ⊗ theta_x) can be slid leftward across the inner braiding to
   recover the canonical statement. [balanced_from_commutes] is the same
   coherence for the inverse twist (theta⁻¹), the law obtained by inverting
   both sides; it is recorded as a field so the inverse direction need not be
   re-derived at each use.

   Every symmetric monoidal category is balanced with theta = id: when
   beta ∘ beta = id (see Structure/Monoidal/Symmetric.v) the law reduces to
   id = beta ∘ id ∘ beta. A balanced monoidal category that is additionally
   rigid (has duals whose twist is compatible with duality, theta on the dual
   of x being the dual of theta on x) is a ribbon, or tortile, category;
   rigidity is not required here. *)

Class BalancedMonoidal := {
  balanced_is_braided : @BraidedMonoidal C;

  (* The twist theta : x ≅ x, a natural automorphism of the identity. *)
  twist {x} : x ≅ x;
  twist_natural : natural (@twist);

  (* Unit condition theta_I = id, in both isomorphism directions. *)
  balanced_to   : to   (@twist I) ≈ id;
  balanced_from : from (@twist I) ≈ id;

  (* Twist/braiding coherence: theta on x ⊗ y is the double braiding wrapping
     theta ⊗ theta (naturality-shifted form; see the header). *)
  balanced_to_commutes {x y} :
    braid ∘ twist ⨂ twist ∘ braid
      << x ⨂ y ~~> x ⨂ y >>
    twist;

  (* The same coherence for the inverse twist theta⁻¹. *)
  balanced_from_commutes {x y} :
    braid ∘ twist⁻¹ ⨂ twist⁻¹ ∘ braid
      << x ⨂ y ~~> x ⨂ y >>
    twist⁻¹;
}.
#[export] Existing Instance balanced_is_braided.

Coercion balanced_is_braided : BalancedMonoidal >-> BraidedMonoidal.

End BalancedMonoidal.
