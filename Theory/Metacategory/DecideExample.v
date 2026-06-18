Require Import Coq.NArith.NArith.

Require Import Category.Lib.
Require Import Category.Lib.MapDecide.
Require Import Category.Theory.Metacategory.ArrowsOnly.

Generalizable All Variables.

Open Scope N_scope.

(** Worked examples for the arrows-only metacategory decision procedure *)

(* nLab: https://ncatlab.org/nlab/show/metacategory
   nLab: https://ncatlab.org/nlab/show/category

   These are not new results; they are a regression/demonstration suite tying
   together two pieces of machinery:

     - [Category.Theory.Metacategory.ArrowsOnly], which presents a category in
       Mac Lane's single-sorted ("arrows-only") form, with partial composition
       encoded as a finite map [pairs : M.t N] and a family of concrete finite
       metacategories built by [composable_pairs n] (the standard composable
       pairs of the n-object finite category, indexed via [triangular_number]);

     - [Category.Lib.MapDecide], a proof-by-reflection decision procedure for
       finite-map membership goals, exposed as the tactics [solve_map] and
       [map_decide] and the Gallina decider [formula_backward].

   The point of the examples is to exercise the decider on the very goals that
   arise when verifying that a [composable_pairs n] table really is a category:
   the associativity ("composition law") coherence between left- and
   right-associated composites. The interleaved timing comments contrast
   [map_decide] (reflective, fast) against the earlier brute-force tactic
   [destruct_maps; nomega], which blows up combinatorially as n grows. The
   examples are deliberately concrete and self-checking, so a regression in the
   decider surfaces as a build failure here rather than silently downstream. *)

(* Sanity check on the raw decider [formula_backward] (the Gallina kernel
   behind [map_decide]), bypassing the reflection wrapper. The reified formula
   is the tautology [P -> P] for one fixed [P], and the goal asserts that the
   decider lands in its [Proved] branch ([then True]) rather than [No]/[Uncertain]
   ([else False]); [vm_compute] runs the decision and [constructor] closes the
   resulting [True]. The [vars] environment supplies the free positives 1..4;
   the answer does not depend on [x y z w], which only confirms the result is
   independent of the particular variable assignment. *)
Example formula_backward_example (x y z w : N) :
  if formula_backward
       (Impl (Maps (Var 1%positive) (Var 2%positive) (Var 3%positive)
                   (Add (Value 1%N) (Value 1%N) (Var 4%positive) Empty))
             (Maps (Var 1%positive) (Var 2%positive) (Var 3%positive)
                   (Add (Value 1%N) (Value 1%N) (Var 4%positive) Empty)))
       {| vars := fun p =>
           if (p =? 1)%positive then x else
           if (p =? 2)%positive then y else
           if (p =? 3)%positive then z else
           if (p =? 4)%positive then w else 9%N |}
  then True else False.
Proof. vm_compute; constructor. Qed.

(* Smallest end-to-end use of the reflective tactic [solve_map]: the same
   two-element map appears as hypothesis and conclusion, so [MapsTo (x,y) f]
   follows trivially. This checks the reify/decide/reflect round trip closes a
   genuine (non-vacuous) membership goal. *)
Example map_decide_test  x y f :
  M.MapsTo (elt:=N) (x, y) f (M.add (0%N, 0%N) 0%N (M.add (1%N, 1%N) 1%N (M.empty _))) ->
  M.MapsTo (elt:=N) (x, y) f (M.add (0%N, 0%N) 0%N (M.add (1%N, 1%N) 1%N (M.empty _))).
Proof. solve_map. Qed.

(* The real content: the associativity coherence of [composable_pairs n].
   Following [ArrowsOnly]'s convention, [M.find (f, g) = Some fg] reads "g and
   f compose to fg" (i.e. [f ∘ g = fg]). So the hypotheses say [f ∘ g = fg],
   [g ∘ h = gh] and [fg ∘ h = fgh]; the conclusion says [f ∘ gh = fgh], i.e.
   the left- and right-associated composites of the triple agree. This is
   exactly the [composition_law] obligation discharged for [Three] in
   [ArrowsOnly], here stated directly against the composition table and closed
   by reflection. [vm_compute triangular_number] first normalises the index
   arithmetic so [map_decide] sees a ground map. The commented-out
   [destruct_maps; nomega] is the brute-force alternative, kept with its timing
   to document why reflection is used (0.016s vs 1.68s at n = 3). *)
Example problem3 : ∀ f g h fg gh fgh : N,
  let big := composable_pairs 3 in
  M.find (elt:=N) (f,  g)  big = Some fg ->
  M.find (elt:=N) (g,  h)  big = Some gh ->
  M.find (elt:=N) (fg, h)  big = Some fgh ->
  M.find (elt:=N) (f,  gh) big = Some fgh.
Proof.
  simpl; vm_compute triangular_number; intros.
(*
  destruct_maps; try nomega. (* takes 1.68s *)
  Undo.
*)
  map_decide.                (* takes 0.016s *)
Qed.

(* Same associativity goal at larger n, showing how the two approaches scale.
   Brute force grows combinatorially with the table size (timings noted below:
   30.15s at n = 4, 2501s at n = 5), while reflection stays in the tens of
   milliseconds; the [destruct_maps] lines are commented out so the file builds
   quickly. *)
Example problem4 : ∀ f g h fg gh fgh : N,
  let big := composable_pairs 4 in
  M.find (elt:=N) (f,  g)  big = Some fg ->
  M.find (elt:=N) (g,  h)  big = Some gh ->
  M.find (elt:=N) (fg, h)  big = Some fgh ->
  M.find (elt:=N) (f,  gh) big = Some fgh.
Proof.
  simpl; vm_compute triangular_number; intros.
  (* destruct_maps; try nomega. (* takes 30.15s *) *)
  (* Undo. *)
  map_decide.                (* takes 0.035s *)
Qed.

Example problem5 : ∀ f g h fg gh fgh : N,
  let big := composable_pairs 5 in
  M.find (elt:=N) (f,  g)  big = Some fg ->
  M.find (elt:=N) (g,  h)  big = Some gh ->
  M.find (elt:=N) (fg, h)  big = Some fgh ->
  M.find (elt:=N) (f,  gh) big = Some fgh.
Proof.
  simpl; vm_compute triangular_number; intros.
  (* destruct_maps; try nomega. (* takes 2501s *) *)
  (* Undo. *)
  map_decide.                (* takes 0.085s *)
Qed.

(* Largest instance exercised here. Despite the name, this uses
   [composable_pairs 10] (a 10-object table, the 100 alludes to the roughly
   hundred-entry map), and is the only case where reflection itself takes
   appreciable time (2.445s); brute force is not even attempted. *)
Example problem100 : ∀ f g h fg gh fgh : N,
  let big := composable_pairs 10 in
  M.find (elt:=N) (f,  g)  big = Some fg ->
  M.find (elt:=N) (g,  h)  big = Some gh ->
  M.find (elt:=N) (fg, h)  big = Some fgh ->
  M.find (elt:=N) (f,  gh) big = Some fgh.
Proof.
  simpl; vm_compute triangular_number; intros.
  (* destruct_maps; try nomega. *)
  (* Undo. *)
  map_decide.                (* takes 2.445s *)
Qed.
