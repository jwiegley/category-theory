Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Theory.Size.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Limit.
Require Import Category.Functor.Hom.Continuous.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Comma.Creation.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.Representability.
Require Import Category.Adjunction.Representability.Sets.

Generalizable All Variables.

(** * Resizing a solution set

    nLab:      https://ncatlab.org/nlab/show/solution+set+condition
    nLab:      https://ncatlab.org/nlab/show/essentially+small+category
    nLab:      https://ncatlab.org/nlab/show/adjoint+functor+theorem
    Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors#General_adjoint_functor_theorem
    Riehl:     Category Theory in Context, §4.6 (the solution set condition)

    Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
    §V.7, book p. 128 (PDF p. 137), Lemma 2 (catalog id
    `maclane:V.7:lem2`), is the mathematical content this file makes
    expressible.  CITED BY LOCATION AND BY THE IN-TREE CATALOG
    (doc/plan/books/maclane/inventory/V.json); the printed text was not
    consulted and no sentence of it is reproduced here.

    ** What the file is for

    A [SolutionSet U d] (Adjunction/GAFT.v) and an [ElementSolutionSet K]
    (Adjunction/Representability/Sets.v) each carry an INDEX, a bare
    [Type@{i}] with no structure on it.  [GAFT] and
    [representability_theorem] then take limits over the DISCRETE category
    on that index, so they demand the index at the shape-object universe of
    the [Complete] they are handed.  Structure/Complete.v's SIZE NOTE is the
    authority on that chain and is not restated here; item 2(b) is the link
    that matters, and item 1 is why a naively-built index sits one universe
    too high.

    Mac Lane's answer, in the book, is Lemma 2: the family is a PROPER
    CLASS as first written, but the members are quotients of one fixed
    object, so a SET of representatives up to isomorphism suffices.  This
    file gives the three shapes in which that answer can be supplied, and
    the four maps that consume them.

    ** The three shapes, weakest premise last

    [SmallType] (Theory/Size.v) -- a Leibniz round trip onto a small
    carrier.  The strongest premise: it says the index ITSELF is small.

    [SmallCovering] -- a small type and a map into the index whose image
    still covers.  No round trip and no surjectivity onto the index: the
    small family need only remain a solution set.  This is literally a
    [SolutionSet] at the small index factored through the large one, and it
    is the honest minimum, since covering is the only thing the index is
    ever used for.

    [SmallUpToIso] -- for each large index a small one, an ISOMORPHISM of
    the two solution objects, and the compatibility of the two solution
    arrows.  This is Mac Lane's own "a small set of representatives up to
    isomorphism", and it is the shape a quotient presentation can actually
    supply: a quotient of a term model is isomorphic to, not equal to, an
    arbitrary spanning codomain.  [covering_of_iso] shows it implies
    [SmallCovering], so the three are ordered.

    ** THE BINDERS ARE THE THEOREM

    The point of every statement here is that the OUTPUT index universe is
    a DIFFERENT binder from the input's.  An earlier prototype of these
    constants left both to inference; the elaborator then identified them
    and the constants were resizings in name only -- they typechecked and
    said nothing.  Written with the input index [i] and the output index
    [w] declared separately, the constraint block says what was intended.
    Measured, [About] under [Set Printing Universes]:

      resize_solution_set@{i w dobj cobj h} :
        ∀ {C : Category@{cobj h h}} {D : Category@{dobj h h}} {U : C ⟶ D}
          {d : obj[D]} (S : SolutionSet@{i dobj cobj h} U d),
        SmallType@{w i} (sol_index S) → SolutionSet@{w dobj cobj h} U d
      (* i w dobj cobj h |= *)

    -- an EMPTY constraint block, so [i] and [w] are unrelated and [w] may
    be taken as low as the consumer needs.  The same for
    [resize_element_solution_set].  [resize_by_covering] and
    [resize_up_to_iso] cannot quite reach an empty block, because the small
    carrier's own universe [u] enters through the record field: they read
    [u <= w], which is the identification that says the output index is the
    carrier the premise supplied, and nothing more.

    A [@{w +}] annotation is a DECLARATION form only.  At a USE site the
    hypothesis is written unannotated and the identification is read off
    the [About]; there is no way to write [SmallCovering@{w +}] as an
    argument type.

    ** What is NOT delivered

    (1) NO SMALLNESS IS PROVED HERE.  Every constant takes its smallness as
    a hypothesis.  The one in-tree discharge is
    Instance/Mod/TensorAFT.v's [tensor_spanning_SmallUpToIso], Mac Lane's
    Lemma 2 at [RMod R]; [Instance/Variety/Spanning.v]'s
    [variety_solution_set] stays conditional, varieties having no
    [PropEquiv] on their term algebras.

    (2) NO TRUNCATION, hence no uniqueness.  [SmallType] is data (see its
    header in Theory/Size.v): two resizings of one index need not agree,
    and [resize_solution_set] applied to two of them gives two solution
    sets.  Nothing here says the resulting adjoint is independent of the
    choice, and the AFT's own output is only determined up to isomorphism
    in any case.

    (3) NO CONVERSE.  Nothing here says a solution set at a low index
    yields a [SmallType] of a high one, and nothing says an index that
    cannot be resized obstructs the theorem.
    Adjunction/GAFT/Necessity.v is the file about necessity and is
    untouched by this one.

    (4) NOTHING IS AN [Instance].  These are readings of a hypothesis, not
    structures resolution should search for. *)

(** ** Resizing along a Leibniz round trip *)

(** The index is replaced by the small carrier and every field is
    transported along [st_to].  The covering is the only field with
    content: a cover at a large index [i] is transported to the small
    representative [st_from H i] by destructing the round trip. *)
Definition resize_solution_set@{i w dobj cobj h +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  (S : SolutionSet@{i dobj cobj h} U d)
  (H : SmallType@{w i} (sol_index S)) : SolutionSet@{w dobj cobj h} U d.
Proof.
  unshelve refine
    {| sol_index := st_carrier H
     ; sol_obj := fun s => sol_obj S (st_to H s)
     ; sol_arr := fun s => sol_arr S (st_to H s) |}.
  intros c h.
  destruct (sol_covers S h) as [i [t e]].
  exists (st_from H i).
  destruct (st_to_from H i).
  exists t; exact e.
Defined.

(** The element-indexed twin.  [esol_covers] has no [Arguments] line, so
    the functor is explicit: it is [esol_covers K E x], not
    [esol_covers E x].  Outside [Adjunction/Representability/Sets.v]'s own
    section [ElementSolutionSet] takes FOUR universes, not one. *)
Definition resize_element_solution_set@{cobj h su i w}
  {C : Category@{cobj h h}} (K : C ⟶ Sets@{h su})
  (E : ElementSolutionSet@{cobj h su i} K)
  (H : SmallType@{w i} (esol_index E)) : ElementSolutionSet@{cobj h su w} K.
Proof.
  unshelve refine
    {| esol_index := st_carrier H
     ; esol_obj := fun s => esol_obj E (st_to H s)
     ; esol_elem := fun s => esol_elem E (st_to H s) |}.
  intros c x.
  destruct (esol_covers K E x) as [i [t e]].
  exists (st_from H i).
  destruct (st_to_from H i).
  exists t; exact e.
Defined.

(** ** The two weaker premises *)

(** [C] and [D] are written out rather than generalized: the records are
    declared at top level, so no section variable is in scope for them. *)

(** A small type whose image under [sc_to] still covers.  Nothing says the
    map is injective, surjective, or that the small carrier determines the
    index -- only that the covering survives. *)
Record SmallCovering@{w +} {C D : Category} {U : C ⟶ D} {d : D}
  (S : SolutionSet U d) := {
  sc_carrier : Type@{w};
  sc_to      : sc_carrier → sol_index S;
  sc_covers  : ∀ (c : C) (h : d ~> U c),
                 { s : sc_carrier
                 & { t : sol_obj S (sc_to s) ~> c
                   & fmap[U] t ∘ sol_arr S (sc_to s) ≈ h } }
}.

(** Mac Lane's shape: an ISO in the comma category rather than a Leibniz
    round trip.  For each large index a small representative, an
    isomorphism of the two solution objects, and the compatibility of the
    two solution arrows over it. *)
Record SmallUpToIso@{w +} {C D : Category} {U : C ⟶ D} {d : D}
  (S : SolutionSet U d) := {
  si_carrier : Type@{w};
  si_to      : si_carrier → sol_index S;
  si_rep     : ∀ i : sol_index S,
                 { s : si_carrier
                 & { phi : sol_obj S (si_to s) ≅ sol_obj S i
                   & fmap[U] (to phi) ∘ sol_arr S (si_to s) ≈ sol_arr S i } }
}.

Arguments SmallCovering {C D U d} S.
Arguments sc_carrier {C D U d S} _.
Arguments sc_to {C D U d S} _ _.
Arguments sc_covers {C D U d S} _ _ _.

Arguments SmallUpToIso {C D U d} S.
Arguments si_carrier {C D U d S} _.
Arguments si_to {C D U d S} _ _.
Arguments si_rep {C D U d S} _ _.

(** ** Resizing along the two weaker premises *)

(** With [SmallCovering] the resizing is a record literal: the premise IS
    the covering field. *)
Definition resize_by_covering@{w i dobj cobj h +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  (S : SolutionSet@{i dobj cobj h} U d) (H : SmallCovering S)
  : SolutionSet@{w dobj cobj h} U d :=
  {| sol_index := sc_carrier H
   ; sol_obj := fun s => sol_obj S (sc_to H s)
   ; sol_arr := fun s => sol_arr S (sc_to H s)
   ; sol_covers := fun c h => sc_covers H c h |}.

(** With [SmallUpToIso] the cover is transported ACROSS the isomorphism:
    a cover [t] of [h] through the large index [i] becomes [t ∘ to phi]
    through the representative, and the triangle closes by [fmap_comp]
    and the compatibility clause. *)
Definition resize_up_to_iso@{w i dobj cobj h +}
  {C : Category@{cobj h h}} {D : Category@{dobj h h}} {U : C ⟶ D} {d : D}
  (S : SolutionSet@{i dobj cobj h} U d) (H : SmallUpToIso S)
  : SolutionSet@{w dobj cobj h} U d.
Proof.
  unshelve refine
    {| sol_index := si_carrier H
     ; sol_obj := fun s => sol_obj S (si_to H s)
     ; sol_arr := fun s => sol_arr S (si_to H s) |}.
  intros c h.
  destruct (sol_covers S h) as [i [t e]].
  destruct (si_rep H i) as [s [phi Hphi]].
  exists s, (t ∘ to phi).
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite Hphi.
  exact e.
Defined.

(** ** The ordering of the three premises *)

(** Mac Lane's shape implies the minimum. *)
Definition covering_of_iso {C D : Category} {U : C ⟶ D} {d : D}
  (S : SolutionSet U d) (H : SmallUpToIso S) : SmallCovering S.
Proof.
  unshelve refine {| sc_carrier := si_carrier H ; sc_to := si_to H |}.
  intros c h.
  destruct (sol_covers S h) as [i [t e]].
  destruct (si_rep H i) as [s [phi Hphi]].
  exists s, (t ∘ to phi).
  rewrite fmap_comp, <- comp_assoc, Hphi.
  exact e.
Defined.

(** And so does the strongest. *)
Definition covering_of_smalltype {C D : Category} {U : C ⟶ D} {d : D}
  (S : SolutionSet U d) (H : SmallType (sol_index S)) : SmallCovering S.
Proof.
  unshelve refine {| sc_carrier := st_carrier H ; sc_to := st_to H |}.
  intros c h.
  destruct (sol_covers S h) as [i [t e]].
  exists (st_from H i).
  destruct (st_to_from H i).
  exists t; exact e.
Defined.

(** ** The consumer *)

(** [representability_theorem] accepts a resized element solution set at
    the universe it demands -- which is the whole purpose of the file.  The
    output index is written [h], the ambient hom level, because that is
    where item 2(b) of Structure/Complete.v's SIZE NOTE puts the shape
    universe of [Complete@{h h h cobj}]. *)
Definition representable_of_small@{cobj h su i +}
  {C : Category@{cobj h h}} (K : C ⟶ Sets@{h su})
  (comp : @Complete@{h h h cobj} C) (cont : @PreservesImageLimit C Sets K)
  (E : ElementSolutionSet@{cobj h su i} K)
  (H : SmallType@{h i} (esol_index E)) : Representable K :=
  representability_theorem K comp cont (resize_element_solution_set K E H).
