Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Export Category.Structure.Monoidal.Symmetric.

Generalizable All Variables.

Section TracedMonoidal.

Context {C : Category}.

(** Traced monoidal category. *)

(* nLab: https://ncatlab.org/nlab/show/traced+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Traced_monoidal_category

   A traced monoidal category is a (balanced or, as here, symmetric) monoidal
   category equipped with a trace, or "partial trace"/"feedback", operator

       Tr^u_{x,y} : Hom(x ⨂ u, y ⨂ u) → Hom(x, y)              ([trace]),

   that contracts the shared object u against itself, leaving x ~> y. Here u is
   left implicit and inferred from the morphism, so a single polymorphic
   [trace] stands for the whole family Tr^u_{x,y}. Writing the laws in this
   library's notation (composition reads right to left, ⨂ is the tensor on
   morphisms), the axioms are, following Joyal-Street-Verity:

       trace (f ∘ g ⨂ id)  ≈  trace f ∘ g       (naturality in x / left
                                                  tightening,
                                                  [trace_natural_in_x]),
       trace (g ⨂ id ∘ f)  ≈  g ∘ trace f       (naturality in y / right
                                                  tightening,
                                                  [trace_natural_in_y]),
       trace (id ⨂ g ∘ f)  ≈  trace (f ∘ id ⨂ g)
                                                 (dinaturality in u / sliding,
                                                  [trace_natural_in_u]),
       trace (unit_right⁻¹ ∘ f ∘ unit_right)  ≈  f
                                                 (vanishing I, [vanishing_unit]),
       trace f  ≈  trace (trace (tensor_assoc⁻¹ ∘ f ∘ tensor_assoc))
                                                 (vanishing ⨂, [vanishing_tensor]),
       trace (tensor_assoc⁻¹ ∘ id[c] ⨂ f ∘ tensor_assoc)  ≈  id[c] ⨂ trace f
                                                 (superposing, [superposing]),
       trace braid  ≈  id[x]                     (yanking, [yanking]).

   The unitor [unit_right] and associator [tensor_assoc] conjugations make the
   non-strict (coherent) statements of vanishing and superposing typecheck;
   under strictness they reduce to nLab's Tr^I(f) = f, Tr^{u⨂v}(f) =
   Tr^u(Tr^v(f)), and Tr^u(id_c ⨂ f) = id_c ⨂ Tr^u(f). Yanking uses the
   symmetry [braid] at {x, x}, recovering the identity by tracing the swap. *)

Class TracedMonoidal := {
  (* The underlying symmetric monoidal structure (braiding + symmetry). *)
  traced_is_symmetric : @SymmetricMonoidal C;

  (* Trace / partial trace: contracts the loop object u, Tr^u_{x,y}. *)
  trace {x y u} : x ⨂ u ~> y ⨂ u → x ~> y;

  (* Naturality in x (left tightening): precompose by g ⨂ id outside trace. *)
  trace_natural_in_x {x x' y u} {f : x ⨂ u ~> y ⨂ u} {g : x' ~> x} :
    trace (f ∘ g ⨂ id) ≈ trace f ∘ g;
  (* Naturality in y (right tightening): postcompose by g ⨂ id outside trace. *)
  trace_natural_in_y {x y y' u} {f : x ⨂ u ~> y ⨂ u} {g : y ~> y'} :
    trace (g ⨂ id ∘ f) ≈ g ∘ trace f;
  (* Dinaturality / sliding in u: a loop morphism g may slide around the loop. *)
  trace_natural_in_u {x y u u'} {f : x ⨂ u ~> y ⨂ u'} {g : u' ~> u} :
    trace (id ⨂ g ∘ f) ≈ trace (f ∘ id ⨂ g);

  (* Vanishing I: tracing over the unit object leaves f unchanged. *)
  vanishing_unit {x y} {f : x ~> y} :
    trace (unit_right⁻¹ ∘ f ∘ unit_right) ≈ f;
  (* Vanishing ⨂: a trace over u ⨂ v is two nested traces over u then v. *)
  vanishing_tensor {x y u v} {f : x ⨂ (u ⨂ v) ~> y ⨂ (u ⨂ v)} :
    trace f ≈ trace (trace (tensor_assoc⁻¹ ∘ f ∘ tensor_assoc));

  (* Superposing: an untraced factor c passes through the trace untouched. *)
  superposing {a b c u} {f : a ⨂ u ~> b ⨂ u} :
    trace (tensor_assoc⁻¹ ∘ id[c] ⨂ f ∘ tensor_assoc)
      ≈ id[c] ⨂ trace f;

  (* Yanking: tracing the braiding of x past itself yields the identity. *)
  yanking {x} : trace braid ≈ id[x];
}.
#[export] Existing Instance traced_is_symmetric.

Coercion traced_is_symmetric : TracedMonoidal >-> SymmetricMonoidal.

End TracedMonoidal.
