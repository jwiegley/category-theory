(** * Project-wide settings and core library re-exports.

   Establishes the global flags every file in the development inherits
   (primitive projections, universe polymorphism, uniform inductive
   parameters, the "!" single-goal selector, [Default Proof Using "Type"],
   opaque [Program] obligations, etc.) and re-exports the foundational
   datatypes.  Importing this module is what puts a file under the
   library's universe-polymorphic, setoid-based regime. *)

#[export] Set Primitive Projections.
#[export] Set Universe Polymorphism.
#[export] Set Uniform Inductive Parameters.
#[export] Set Default Proof Using "Type".
#[export] Set Default Goal Selector "!".
#[export] Unset Transparent Obligations.
#[export] Unset Intuition Negation Unfolding.
#[export] Unset Universe Minimization ToSet.
(* Rocq's variance-based minimization (rocq-prover/rocq#22721) keeps the universes
   bounded only from below; set them to their lower bound, as before *)
#[export] Set Universe Minimization Compat.

Require Export Category.Lib.Datatypes.
