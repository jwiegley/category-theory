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

(* Feedback, fixed points, and the geometry of interaction

   nLab: https://ncatlab.org/nlab/show/traced+monoidal+category

   The trace operator axiomatizes feedback: a loop that plugs an output of
   type u back into an input of the same type, hiding an internal channel.
   Where a category has dual objects the loop comes for free — the u-wire
   bends around through the unit and counit of the duality, the [cc_unit]
   and [cc_counit] of Structure/Monoidal/CompactClosed.v, whose snake laws
   that file likewise annotates as "yanking" — and every compact closed
   category is canonically traced.  The definition of Joyal, Street and
   Verity ("Traced monoidal categories", Mathematical Proceedings of the
   Cambridge Philosophical Society 119(3) 1996) isolates the equational
   theory of that loop without demanding duals, so that categories with no
   dual objects — cartesian categories, pointed cpos, partial functions
   under coproduct — can still support feedback.  Their aim was to abstract
   the notion of trace shared by algebraic topology, knot theory, and
   theoretical computer science; their structure theorem shows the axiom
   set complete.  The Int construction — in their words "a glorification
   of the construction of the integers from the natural numbers" — embeds
   every traced monoidal category fully and faithfully in a tortile
   monoidal category Int(C) whose objects are pairs of a positive and a
   negative part and whose composition closes off the middle object with
   [trace]; Int is left biadjoint to the forgetful 2-functor from tortile
   to traced monoidal categories, with details refined in later
   literature.  A trace is therefore exactly the restriction of a genuine
   duality loop, and the seven axioms are the legal moves on a string
   diagram with a feedback loop (Selinger, "A survey of graphical
   languages for monoidal categories", Springer Lecture Notes in Physics
   813 2011).

   One operator carries three computational readings, keyed to the choice
   of tensor.  On finite-dimensional vector spaces [trace] is the partial
   matrix trace, summing over the loop index and recovering the classical
   trace when x and y are the unit.  On a cartesian category a trace is
   the same thing as a Conway fixed-point operator — a bijective
   correspondence found independently by Hasegawa and by Hyland (Hasegawa,
   "Recursion from Cyclic Sharing: Traced Monoidal Categories and Models
   of Cyclic Lambda Calculi", TLCA 1997), with equivalent observations
   predating the traced formulation in the iteration theories of Bloom and
   Ésik — so that [trace] computes parameterized least fixed points on
   pointed cpos and models letrec and cyclic sharing (Hasegawa, "Models of
   Sharing Graphs: A Categorical Semantics of let and letrec", Springer
   1999).  On partial functions with coproduct as tensor, [trace]
   iterates: run f, and feed the result back for as long as it lands in
   the loop summand u — the semantics of a while loop.

   A fourth reading is Girard's Geometry of Interaction ("Geometry of
   Interaction I: Interpretation of System F", Logic Colloquium '88,
   North-Holland 1989), which models cut-elimination in linear logic as
   tokens circulating through a proof net.  Abramsky ("Retracing some
   paths in Process Algebra", CONCUR 1996) identified traced monoidal
   categories as the common axiomatic core of its particle-style and
   wave-style formulations; in that tradition Int(C) is the GoI
   construction G(C), a morphism of which serves positive and negative
   channels while composition traces out the internal dialogue, and GoI
   situations over traced categories yield the linear combinatory
   algebras that capture the exponentials of linear logic (Abramsky,
   Haghverdi, Scott, "Geometry of Interaction and linear combinatory
   algebras", MSCS 12(5) 2002).

   In this library the balanced setting of the original definition —
   braided monoidal with a twist, of which the symmetric case bundled by
   [traced_is_symmetric] is the specialization with trivial twist — lives
   in Structure/Monoidal/Balanced.v.  Neither direction of the
   compact-closed connection is formalized in-tree: the canonical trace
   on a compact closed category and the Int construction are the natural
   follow-up developments, as is the Hasegawa–Hyland correspondence at
   the interface with Structure/Monoidal/Cartesian.v.  Theory/Recursion.v
   develops recursion in its universal-property form, through initial
   algebras and catamorphisms; a traced cartesian category is the
   operator form of the same idea.  Instance/Coq/Comonad/Traced.v is
   unrelated despite the name: it houses the traced (cowriter) comonad
   over a monoid. *)

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
