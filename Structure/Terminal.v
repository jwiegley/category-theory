Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.

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
   isomorphism whenever they exist: [terminal_unique] below builds the
   isomorphism, [terminal_arrow_unique] shows it is the only arrow at all
   between the two objects, and [terminal_unique_up_to_unique_iso] packages
   the two as a single [Unique]. *)

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

(* Uniqueness of the terminal object (Mac Lane, CWM 2nd ed., §I.5, p. 20).

   Two [Terminal] structures on the same category need not choose the same
   object -- nothing in the class forces that -- but their chosen objects are
   canonically isomorphic. Each supplies the unique arrow into the other's
   object, and both round trips are arrows into a terminal object, so
   [one_unique] identifies them with the identity. This is the sense in which
   "the" terminal object is well defined, and it is what licenses the informal
   practice of speaking of *the* object `1`. *)
Program Definition terminal_unique {C : Category} (T1 T2 : @Terminal C) :
  @terminal_obj C T1 ≅ @terminal_obj C T2 := {|
  to   := @one C T2 (@terminal_obj C T1);
  from := @one C T1 (@terminal_obj C T2)
|}.
Next Obligation. apply (@one_unique C T2). Qed.
Next Obligation. apply (@one_unique C T1). Qed.

(* The isomorphism above is moreover the ONLY one, and indeed the only arrow
   at all between the two objects: every arrow into a terminal object is
   already pinned down by [one_unique]. Mac Lane states uniqueness of the
   object "up to a unique isomorphism"; this corollary is the "unique" half,
   and it makes [terminal_unique] canonical rather than merely one choice. *)
Corollary terminal_arrow_unique {C : Category} (T1 T2 : @Terminal C)
      (f g : @terminal_obj C T1 ~> @terminal_obj C T2) : f ≈ g.
Proof. apply (@one_unique C T2). Qed.

(* The object-level form of terminality (Riehl, CTiC, Def. 1.6.1).  The
   bundled [Terminal] class both *chooses* an object and asserts the
   universal property; when the object is already fixed -- as it is when
   terminality is used as a PREDICATE, e.g. to span a subcategory or to
   transport along an isomorphism -- the choice gets in the way.  Stated
   with [Unique] (Lib/Setoid.v), "there is exactly one arrow x ~> c" is
   literally "the hom-setoid x ~> c is contractible", the phrasing of the
   header of this file.  [Terminal_from_IsTerminalObj] and
   [IsTerminalObj_from_Terminal] convert in both directions, the latter
   landing on [terminal_obj] definitionally. *)
Definition IsTerminalObj {C : Category} (c : C) : Type :=
  ∀ x : C, Unique (fun _ : x ~> c => True).

(* The unique arrow x ~> c supplied by the predicate. *)
Definition is_terminal_one {C : Category} {c : C} (H : IsTerminalObj c)
  {x : C} : x ~> c := unique_obj (H x).

(* ... and its uniqueness, in the two-arrow form used by [one_unique]:
   both arrows agree with the chosen witness, hence with each other. *)
Lemma is_terminal_unique {C : Category} {c : C} (H : IsTerminalObj c)
  {x : C} (f g : x ~> c) : f ≈ g.
Proof.
  pose proof (uniqueness (H x) f I) as Hf.
  pose proof (uniqueness (H x) g I) as Hg.
  now rewrite <- Hf, <- Hg.
Qed.

(* Bundling: the predicate at c yields a [Terminal] structure choosing c. *)
Program Definition Terminal_from_IsTerminalObj {C : Category} {c : C}
  (H : IsTerminalObj c) : @Terminal C := {|
  terminal_obj := c;
  one := fun x => @is_terminal_one C c H x
|}.
Next Obligation. now apply (is_terminal_unique H). Qed.

(* ... and conversely, unbundling at the chosen object. *)
Program Definition IsTerminalObj_from_Terminal {C : Category}
  (T : @Terminal C) : IsTerminalObj (@terminal_obj C T) := fun x =>
  {| unique_obj := @one C T x
   ; unique_property := I |}.
Next Obligation. now apply (@one_unique C T). Qed.

(* Riehl, CTiC, Exercise 1.6.ii(i): terminality is isomorphism-invariant.
   Any object isomorphic to a terminal object is itself terminal.  The
   arrow into y is the arrow into 1 followed across the isomorphism, and
   uniqueness transports back: two arrows into y agree as soon as their
   [from i] translates agree, which they do by [one_unique].  The result
   chooses y ON THE NOSE -- see [Terminal_iso_obj] in Block B -- so this
   is a genuine transport of structure, not merely an existence claim. *)
Program Definition Terminal_iso {C : Category} (T : @Terminal C) (y : C)
  (i : @terminal_obj C T ≅ y) : @Terminal C := {|
  terminal_obj := y;
  one := fun x => to i ∘ @one C T x
|}.
Next Obligation.
  assert (Hf : to i ∘ (from i ∘ f) ≈ f)
    by (rewrite comp_assoc, iso_to_from; apply id_left).
  assert (Hg : to i ∘ (from i ∘ g) ≈ g)
    by (rewrite comp_assoc, iso_to_from; apply id_left).
  transitivity (to i ∘ (from i ∘ f)).
  - now symmetry.
  - now rewrite (@one_unique C T _ (from i ∘ f) (from i ∘ g)).
Qed.

(* Seven Sketches, Remark 3.85 ("unique up to unique isomorphism"), packaged as
   a single result rather than an existence lemma plus a separate appeal to
   [terminal_arrow_unique].

   The statement is [Unique] over the setoid [iso_setoid] of isomorphisms
   `1₁ ≅ 1₂`, whose equivalence [iso_equiv] compares BOTH the `to` and the
   `from` component.  So the three fields say, in order: such an isomorphism
   exists; the trivial predicate holds of it; and every isomorphism between
   the two objects is equal to it, in both directions.  Together that is
   exactly "there is exactly one isomorphism 1₁ ≅ 1₂" -- the predicate is
   [True] precisely so that the uniqueness clause quantifies over ALL
   isomorphisms and not merely over those satisfying some side condition. *)
Program Definition terminal_unique_up_to_unique_iso {C : Category}
  (T1 T2 : @Terminal C) :
  Unique (fun _ : @terminal_obj C T1 ≅ @terminal_obj C T2 => True) := {|
  unique_obj := terminal_unique T1 T2;
  unique_property := I
|}.
Next Obligation.
  split.
  - apply (@one_unique C T2).
  - apply (@one_unique C T1).
Qed.

(* The sharper fact behind it: not only is the isomorphism unique, the
   underlying morphism is the unique morphism of its hom-setoid.  This is
   [terminal_arrow_unique] packaged as a [Unique], and it implies the
   isomorphism statement above. *)
Program Definition terminal_hom_unique {C : Category} (T1 T2 : @Terminal C) :
  Unique (fun _ : @terminal_obj C T1 ~> @terminal_obj C T2 => True) := {|
  unique_obj := @one C T2 (@terminal_obj C T1);
  unique_property := I
|}.
Next Obligation. apply (@one_unique C T2). Qed.
