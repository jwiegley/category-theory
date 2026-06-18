(** * The reflective categorical-equality solver (umbrella import).

   Re-exports the proof-by-reflection decision procedure for equalities of
   morphisms in a free category: [Reify] (Ltac that reflects a goal into
   abstract syntax), [Normal] (the free-category normal form and its
   denotation-preserving soundness), and [Decide] (the decision procedure
   and its soundness theorem).  Import this to get the [categorical] /
   [normalize] tactics. *)

Require Export Category.Solver.Reify.
Require Export Category.Solver.Normal.
Require Export Category.Solver.Decide.
