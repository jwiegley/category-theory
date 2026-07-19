Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** * Category with a terminal object *)

(* nLab: https://ncatlab.org/nlab/show/terminal+object
   Wikipedia: https://en.wikipedia.org/wiki/Initial_and_terminal_objects

   A terminal object `1` in a category C is an object such that for every
   object `x` there is exactly one morphism `! : x ~> 1`. "Exactly one" splits
   into existence (the morphism [one]) and uniqueness (any two morphisms into
   `1` agree under `≈`, the law [one_unique]). Equivalently, every hom-setoid
   `x ~> 1` is contractible (a singleton up to `≈`). A terminal object is the
   dual of an initial object — it is initial in `C^op` — and is the limit of
   the empty diagram; see Structure/Initial.v, which derives initial objects
   from this file by duality. Terminal objects are unique up to (unique)
   isomorphism whenever they exist. *)

(* Where terminal objects come from, and what they are for

   nLab:  https://ncatlab.org/nlab/show/global+element
   nLab:  https://ncatlab.org/nlab/show/unit+type
   Paper: Samuel, "On universal mappings and free topological groups",
          Bulletin of the AMS 54(6), 1948
   Paper: Mac Lane, "Duality for groups", Bulletin of the AMS 56, 1950
   Paper: Lawvere, "An elementary theory of the category of sets",
          PNAS 52, 1964

   The terminal object is the simplest universal property.  Universal
   mapping properties enter mathematics with Samuel (1948), whose
   treatment of free topological groups the Bourbaki group then extended
   to free groups, tensor products and limits (the history is traced in
   Dubuc, "Categorías. Los 30 primeros años", arXiv:1404.6240, 2014);
   terminality is the nullary, degenerate case, a universal property with
   no auxiliary data whatsoever.  It follows that the contractibility of
   each hom-setoid `x ~> 1` is the prototype for every
   uniqueness-up-to-unique-isomorphism argument downstream, with
   [one_unique] as its entire content.  Mac Lane's duality program
   (1950), which recast group theory in terms of homomorphisms and
   composition so that reversing arrows would exchange paired notions,
   supplies the other half of the design: initial and terminal objects
   are the model dual pair, and Structure/Initial.v realizes the pairing
   literally — `Initial C` is notation for `Terminal (C^op)`, with
   [zero] and [zero_unique] mere projections of [one] and [one_unique],
   and [zero_comp] the dual reading of [one_comp].

   Terminality is also the shape to which every limit reduces.  The
   header's remark that `1` is the limit of the empty diagram is proved
   in both directions as [Terminal_Limit] in Structure/Limit/Terminal.v;
   conversely, a limit of any diagram is precisely a terminal object in
   its category of cones (Wikipedia, "Initial and terminal objects");
   [Limit_Cones] in Instance/Cones/Limit.v builds the limit from the
   terminal cone.  Even GAFT bottoms out here: Theory/WeaklyInitial.v
   builds its initial object as a [Build_Terminal] on the opposite
   category.

   The purpose the definition serves is to say "element" without
   mentioning elements.  A morphism `1 ~> x` is a global element of `x`
   — in the nLab's phrasing, a generalized element at stage of definition
   `1`: in Set it picks out an ordinary element, in Cat a functor from
   the terminal category singles out an object, and in a topos a global
   element of the subobject classifier is a truth value (nLab, "global
   element").  Lawvere's elementary theory of the category of sets
   (1964) rests on this reading: its categories are well-pointed,
   meaning `1` is a generator — two morphisms `a ~> b` agreeing on every
   global element of `a` already satisfy ≈ (nLab, "well-pointed topos").
   In this library the reading surfaces as [truth : 1 ~> Ω] in
   Structure/SubobjectClassifier.v and as the [Constant] class of
   Structure/Constant.v, a family of global elements embedding the
   values of a Coq type.

   Computationally, `1` is the unit type.  The nLab's unit-type article
   aligns the proposition "true", the singleton set, the terminal object
   and the unit type in a single row, the unit type being contractible
   exactly as the header describes the hom-setoids here.  In a category
   of types and pure functions there is one and only one function from
   any type to the unit type; Milewski's Bool counterexample — two
   distinct constant functions into Bool exist, so Bool is not terminal —
   shows the uniqueness half of the definition carrying all the weight
   (Milewski, "Products and Coproducts", 2015).  The computable witnesses
   are [Coq_Terminal] in Instance/Coq.v and [Sets_Terminal] in
   Instance/Sets.v; [const] below factors any constant map through `1`.

   Read in a monoidal category whose unit is terminal, [one] becomes the
   discard map and terminality becomes a causality principle.  Coecke
   and Lal define a causal category as a symmetric, partially monoidal
   category whose unit is terminal, and show that classical or quantum
   correlations force that terminality (Coecke, Lal, "Causal categories:
   relativistically interacting processes", Foundations of Physics 43,
   2013); Kissinger, Hoban and Coecke state the principle as process
   terminality — when the output of a process is discarded, the process
   itself may as well be discarded — and prove it equivalent to
   relativistic causal structure (Kissinger, Hoban, Coecke, "Equivalence
   of relativistic causal structure and process terminality", 2017).
   Concretely: probability distributions are normalized, quantum
   channels preserve trace, and [one_comp] is the slogan's algebraic
   kernel — discarding after computing is just discarding.
   Structure/Monoidal/Semicartesian/Terminal.v packages the
   correspondence as a [Terminal] structure with `one := eliminate`. *)

Section Terminal.

Context {C : Category}.

Class Terminal := {
  terminal_obj : C;                     (* the terminal object 1 *)
  one {x} : x ~> terminal_obj;          (* the morphism ! : x ~> 1 *)

  one_unique {x} (f g : x ~> terminal_obj) : f ≈ g  (* ! is unique up to ≈ *)
}.

End Terminal.

Notation "1" := terminal_obj : object_scope.

(* Precomposing the unique map collapses: ! ∘ f ≈ !, since both land in `1`. *)
Corollary one_comp `{@Terminal C} {x y : C} {f : x ~> y} :
  one ∘ f ≈ one.
Proof. intros; apply one_unique. Qed.

(* `one[x]` names the morphism `! : x ~> 1` at an explicit Terminal instance. *)
Notation "one[ C ]" := (@one _ _ C)
  (at level 9, format "one[ C ]") : morphism_scope.

(* A "constant" map `x ~> y` factoring through `1`: pick `f : 1 ~> y`, then
   precompose with `! : x ~> 1`, so the result ignores its argument's data. *)
Definition const `{@Terminal C} {x y : C} {f : 1 ~> y} := f ∘ one[x].
