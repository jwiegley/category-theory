Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Wedge.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** * Ends and coends *)

(* The END of a functor of mixed variance `F : C^op ∏ C ⟶ D`, written
   `∫_c F(c,c)`, is the UNIVERSAL (terminal) WEDGE: a wedge `(e, ω)` with apex
   `e : D` and legs `ω_x : e ~> F (x, x)` through which every other wedge
   factors uniquely. It is the dinatural analogue of a limit, and packages a
   family of legs constrained by the wedge (extranaturality) condition of
   Structure/Wedge.

   nLab:      https://ncatlab.org/nlab/show/end
   Wikipedia: https://en.wikipedia.org/wiki/End_(category_theory)

   Universal property (the end UMP), in this library's notation: for every
   wedge `W` (apex `wedge_obj[W]`, legs `wedge_map[W]`) there is a unique
   mediating morphism `u : W ~> e` (i.e. `wedge_obj[W] ~{D}~> e`) commuting with
   the legs,

     ∃! u : W ~> e, ∀ x : C, wedge_map[end_wedge] ∘ u ≈ wedge_map[W]

   so `u` runs from the arbitrary wedge's apex *to* the end (terminal direction)
   and recovers each leg of `W` by post-composition with the end's leg. This is
   the standard statement `β_x = ω_x ∘ u` (Wikipedia's `h : x → e`).

   The dual is the COEND `∫^c F(c,c)`, the universal (initial) cowedge; it is
   defined below by taking the end in the opposite categories. *)
Class End `(F : C^op ∏ C ⟶ D) := {
  end_wedge : Wedge F;                     (* the universal wedge `(e, ω)` *)

  (* the end UMP: every wedge `W` factors uniquely through `end_wedge`, with
     `u : W ~> end_wedge` mediating in `D` and `ω_x ∘ u ≈ wedge_map[W]` *)
  ump_ends : ∀ W : Wedge F, ∃! u : W ~> end_wedge, ∀ x : C,
    wedge_map[end_wedge] ∘ u ≈ @wedge_map _ _ _ W x
}.

Arguments End {_%_category _%_category} F%_functor.
Arguments end_wedge {_%_category _%_category} F%_functor {_}.

(* An end of `F` may be used directly as its apex object of `D` (and hence,
   transitively through `Wedge`'s own coercion, as that wedge). *)
Coercion wedge_obj `(F : C^op ∏ C ⟶ D) (E : End F) := @end_wedge _ _ _ E.

Require Import Category.Functor.Opposite.

(* The COEND `∫^c F(c,c)` is the universal (initial) cowedge, dual to the end.
   As with `Cowedge` in Structure/Wedge, it is obtained as an end in the
   opposite categories: a coend for `F` is literally an end for
   `F^op : (C^op)^op ∏ C^op ⟶ D^op`, so its legs `F (x, x) ~{D}~> d` are the
   reversed wedge legs and the UMP runs `d ~> x` out of the coend. *)
Definition Coend `(F : C^op ∏ C ⟶ D) := @End (C^op) (D^op) (F^op).
