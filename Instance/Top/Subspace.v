Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.Strict.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.SlicedInverse.
Require Import Category.Structure.SlicedInverse.Strict.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Sets.Coequalizer.
Require Import Category.Instance.Top.Prop.

Generalizable All Variables.

(** * Subspace and quotient topologies as sliced adjoint inverses *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
     §V.9, read from the page images: the subspace construction, book
     pp. 132-133 (PDF pp. 141-142), the subspace topology as a
     right-adjoint-right-inverse of the sliced underlying-set functor
     (catalog id maclane:V.9:construction2); Proposition 1, book p. 133
     (PDF p. 142), which consumes it (maclane:V.9:prop1); the quotient
     construction, book pp. 133-134 (PDF pp. 142-143), the quotient
     topology as a left-adjoint-right-inverse of the cosliced one
     (maclane:V.9:construction3); and the sentence stating the dual of
     Proposition 1, book p. 134 (PDF p. 143), after which "This dual
     proposition and the above adjunction prove that Top has
     coequalizers" (the first clause of maclane:V.9:remark2, #458's
     catalog item).  The book numbers Proposition 1 and none of the
     constructions; the catalog ids are names, not book numbering.
   Fong and Spivak, "Seven Sketches in Compositionality", §7.3.2,
     Exercise 7.32, printed p. 236 (PDF p. 248): the subspace topology on
     a subset (7sketches:7.3.2:ex7.32), as the catalogue under
     doc/plan/books summarizes it (that book was not consulted)
   nLab:      https://ncatlab.org/nlab/show/subspace+topology
   nLab:      https://ncatlab.org/nlab/show/quotient+space
   nLab:      https://ncatlab.org/nlab/show/initial+topology
   nLab:      https://ncatlab.org/nlab/show/topological+concrete+category
   Wikipedia: https://en.wikipedia.org/wiki/Quotient_space_(topology)

   BACKGROUND.  The subspace topology on a subset of a space and the
   quotient topology on a set of equivalence classes are the basic
   induced topologies.  nLab's initial-topology page gives the general
   form: for functions f_i from a set S into spaces X_i, the coarsest
   topology on S making every f_i continuous, with the subspace topology
   the case of one injection; dually the finest topology making maps into
   S continuous, with the quotient topology the case of one surjection.
   nLab's topological concrete categories are the concrete categories
   with "nice features matching the ability to form weak and strong
   topologies in Top" (that page's Idea).  Mac Lane's §V.9 reads the
   one-map case, without the injection or the surjection, as an
   adjunction.  For a space X the underlying-set functor G induces a
   functor on slices,
       G ↓ X : (Top ↓ X) → (Set ↓ GX);
   its right adjoint L gives a set t : S → GX the topology whose opens
   are the preimages along t of the opens of X.  Mac Lane observes that
   G ↓ X after L is the identity and calls L a
   "right-adjoint-right-inverse" of G ↓ X; its counit is the identity,
   which is how Structure/SlicedInverse.v's record reads the name.  The
   book stresses that the universal property is about arbitrary spaces Y
   with arbitrary continuous maps into X, not only about subspaces.
   Dually,
       X ↓ G : (X ↓ Top) → (GX ↓ Set)
   has a left adjoint M giving t : GX → S the topology of the sets with
   open preimage, "with unit the identity map, so M is
   left-adjoint-right-inverse to X↓G".  Proposition 1 turns the first
   into equalizers (an element-free version of the equalizer as the set
   where two maps agree, with the subspace topology), and its dual turns
   the second into coequalizers.

   WHY THIS FILE IS OVER [PTopCat].  Over the tree's Type-valued [Top]
   neither adjunction is an [Adjunction] record.  That is measured at one
   universe assignment ([o < h], [h < so]; Instance/Top/Subspace/
   TypeValued.v's header quotes the refusals) and argued, not measured,
   at every other: [Top@{h o}] puts its homs strictly above its points,
   [o < h], because continuity quantifies over the opens of the codomain;
   a functor that builds spaces on the given point setoids must start
   from the slices of a [Sets] with homs at [o], while the sliced
   underlying-set functors land in the slices of one with homs at [h];
   and Theory/Adjunction.v's [Adjunction] identifies the hom levels of
   its two categories.  The subspace predicate, besides, quantifies over
   the opens of X and sits one universe above the points.
   Instance/Top/Prop.v's Prop-valued encoding removes both obstructions,
   and everything below is stated over it.  The readings that ARE
   formable over [Top] are Instance/Top/Subspace/TypeValued.v.

   WHAT IS HERE.
     - The subspace construction along an ARBITRARY setoid map
       [h : S → X], not only an inclusion.  [PSub X S h] has points [S]
       and the book's opens verbatim: [PSub_open] reads
       [POpen (PSub X S h) V] back as
       [ex (fun U => POpen X U /\ ∀ s, V s <-> U (h s))] at [eq_refl].
       [psub_universal] is the universal property over ARBITRARY spaces
       [Z] mapping in, both directions: a setoid map [g : Z → S] is
       continuous into [PSub X S h] if and only if [h ∘ g] is continuous.
       [psub_lift] is the book's form of it, a continuous [f : Z → X] with
       [f ≈ h ∘ g] making [g] a continuous map into the subspace.
     - Seven Sketches' Exercise 7.32 at a subset [Y ⊆ X] given by a
       predicate [P] ([ex732_Y], the sub-setoid, and [ex732_incl]).
       [ex732_def]: [A] is open iff [A = B ∩ Y] for an open [B] of [X], at
       [eq_refl].  [ex732_part1]: [Y] is open, [B] the whole of [X].
       [ex732_part2]: the three axioms of Definition 7.25, unions over an
       index type at any universe.  [ex732_part3]: the inclusion is
       continuous.
     - The quotient construction along an arbitrary setoid map
       [q : X → T].  [PQuot]'s opens are the [V] with
       [POpen X (fun x => V (q x))] AND respecting the equality of [T]
       ([PQuot_open], at [eq_refl]).  The second conjunct is the setoid
       discipline's addition to the book's predicate: the book's sets
       have an equality every predicate respects, and without it
       [popen_proper] could not hold at [T].  The tree already pairs such
       a respect-the-relation clause with the preimage condition, in
       Instance/Top.v's [CP_open] and Instance/Top/Wedge.v's
       [wedge_open].  [pquot_universal] is the universal property over
       arbitrary spaces [Z] mapping out; [pquot_desc] is the book's form.
     - The sliced functors.  [PForget_over X] (Mac Lane's G ↓ X) and
       [PForget_under X] (X ↓ G) are Structure/SlicedInverse.v's
       [Sliced PForget X] and [Cosliced PForget X] under local names:
       aliases, read back at [eq_refl] by [PForget_over_Sliced] and
       [PForget_under_Cosliced], so every adjunction below is an
       adjunction of the generic sliced functors.  An independent
       [Program] functor with the same actions would not do: in a scratch
       file its object action agrees with [Sliced PForget X] at
       [eq_refl], but the functor equation is refused ("cannot unify"),
       its obligations being [Qed] constants of its own.  [PSub_Functor
       X] (L) and [PQuot_Functor X] (M), and the adjunctions
       [psub_adjunction : PForget_over X ⊣ PSub_Functor X] and
       [pquot_adjunction : PQuot_Functor X ⊣ PForget_under X], each built
       by Theory/Adjunction.v's [Build_Adjunction'] from a hom-set
       bijection ([psub_adj_iso], [pquot_adj_iso]) that is the identity on
       underlying maps.  The object equations [psub_obj] and [pquot_obj]
       (G ↓ X after L, and X ↓ G after M, are the identity on objects) and
       the triangle facts [psub_counit] (the counit is [id_cast] of
       [psub_obj]) and [pquot_unit] (the unit is [id_cast] of the inverse
       of [pquot_obj]) are the convention of Adjunction/LeftInverse.v and
       Theory/Equivalence/Strict.v for "the counit (unit) is the
       identity".
     - The packaged constructions.  [subspace_RARI X :
       RightAdjointRightInverse (Sliced PForget X)] is the subspace
       construction in Structure/SlicedInverse.v's record, and
       [quotient_LARI X : LeftAdjointRightInverse (Cosliced PForget X)]
       the quotient construction in Theory/Equivalence/Strict.v's record,
       each the four facts above assembled ([subspace_RARI_right] and
       [quotient_LARI_left] read the adjoints back at [eq_refl]).
     - [PTop_HasEqualizers], Proposition 1 at [PForget]:
       Structure/SlicedInverse.v's [equalizers_from_sliced_RARI] fed
       [PForget_Faithful], [subspace_RARI] and the equalizers of [Sets]
       that Structure/Pullback/Reduction.v's
       [HasEqualizers_of_HasPullbacks_Terminal] builds from
       Instance/Sets/Pullback.v's [Sets_HasPullbacks] and Instance/Sets.v's
       [Sets_Terminal] -- the term of Adjunction/CokernelPair.v's
       [SetsEqualizers], restated so as not to require that file (see
       ROUTE AND COST).  [PTop_equalizer_obj] reads the equalizer of
       [f g : x ~> y] back at [eq_refl] as [PSub x S s], [s : S → x] the
       chosen [Sets] equalizer of the underlying maps, and
       [PTop_equalizer_arrow] reads its arrow as [psub_incl x S s]: the
       element-free form of the book's "take the set S of points x of X
       with fx = f'x and impose the subspace topology", with whatever
       equalizer the [Sets] donor chooses in place of that set.
     - [PTop_HasCoequalizers], the dual at [PForget]:
       Structure/SlicedInverse/Strict.v's [coequalizers_from_sliced_LARI]
       fed [PForget_Faithful], [quotient_LARI] and
       Instance/Sets/Coequalizer.v's [Sets_HasCoequalizers].
       [PTop_coequalizer_obj] reads the coequalizer back at [eq_refl] as
       [PQuot y (SetsCoeq Gf Gg) (sets_coeq_proj Gf Gg)], [Gf] and [Gg]
       the underlying maps: the quotient topology on the quotient of the
       points of [y] by the equivalence the pair generates; and
       [PTop_coequalizer_arrow] reads its arrow as [pquot_proj].
     - The two witnesses at concrete spaces, over Instance/Top/Prop.v's
       discrete [PPoint] and [PBool]: [PBool_subspace_RARI] and
       [PBool_quotient_LARI] are the two constructions at [PBool].
       [PBool_equalizer] is the equalizer of the identity and the
       constant map [pbool_true] on [PBool], two different maps
       ([pbool_maps_differ]); [PBool_equalizer_obj] reads it back at
       [eq_refl] as [PSub PBool] on the [Sets] equalizer of the
       underlying maps and [PBool_equalizer_rari] as the value of
       [rari_right PBool_subspace_RARI] there, and
       [PBool_equalizer_points] computes which points of [PBool] lie in
       it: exactly [true], so the equalizer is a proper, nonempty
       subspace.  [PBool_coequalizer] is the coequalizer of the two points
       [ppoint_false] and [ppoint_true] of [PBool], maps out of [PPoint]
       that differ ([ppoint_maps_differ]); [PBool_coequalizer_obj] reads
       it back at [eq_refl] as [PQuot PBool] on the [Sets] coequalizer and
       [PBool_coequalizer_lari] as the value of
       [lari_left PBool_quotient_LARI] there, and
       [PBool_coequalizer_points] identifies every point with [true] in
       it, while Instance/Top/Prop.v's [PBool_points_distinct] separates
       [false] from [true] in [PBool]: a proper quotient.

   STRENGTHS, measured strict first.
     - At [eq_refl]: [PSub_carrier], [PSub_open], [PQuot_carrier],
       [PQuot_open], [ex732_def], [psub_lift_map], [pquot_desc_map],
       [PForget_over_Sliced], [PForget_under_Cosliced],
       [PSub_Functor_obj], [PQuot_Functor_obj], the four transpose
       readbacks [psub_adj_to_map], [psub_adj_from_map],
       [pquot_adj_to_map], [pquot_adj_from_map], the object equations at
       an explicit pair, [psub_obj_pair] and [pquot_obj_pair],
       [subspace_RARI_right], [quotient_LARI_left], and the four
       (co)equalizer readbacks [PTop_equalizer_obj],
       [PTop_equalizer_arrow], [PTop_coequalizer_obj] and
       [PTop_coequalizer_arrow], and at the concrete spaces
       [PBool_equalizer_obj], [PBool_equalizer_rari],
       [PBool_coequalizer_obj] and [PBool_coequalizer_lari].
     - Leibniz, not [eq_refl] at a variable: [psub_obj] and [pquot_obj].
       Slice objects are stdlib [sigT] pairs, which have no eta, so at a
       variable [c] the equation takes a [destruct]; measured in a scratch
       file, the [eq_refl] at a variable is refused with "cannot unify" of
       the round trip and [c], while its first component is [eq_refl].
     - Four [Defined], each load-bearing, measured by closing it [Qed]
       alone in a scratch copy of this file.  [psub_obj] and [pquot_obj]:
       the triangle facts need the transport to reduce, and with either
       closed [Qed] the matching triangle fact is refused (Coq: Unable to
       unify "projT1 (id_cast (psub_obj (x; h))) t" with "t", and the
       [pquot_obj] twin).  [psub_adjunction] and [pquot_adjunction]: the
       counit and unit are computed through [Build_Adjunction'] from the
       hom-set bijection, and with either closed [Qed] the matching
       triangle fact is refused (Coq: Unable to unify "t" with "projT1
       counit t", and "projT1 unit t" for the quotient).
     - Up to [≈]: [psub_counit], [pquot_unit] (the record's convention),
       [psub_lift_comm], [pquot_desc_comm], and [PBool_coequalizer_points]
       in the coequalizer's setoid.
     - Propositional equivalences: [psub_universal], [pquot_universal],
       and [PBool_equalizer_points], whose "only if" is the fork equation
       and whose "if" is the equalizer's universal property at the point
       of [PPoint] picking [true].

   UNIVERSES, read by [About] under [Set Printing Universes].
     - [psub_open@{o}], [PSub@{o}], [psub_incl@{o}], [PQuot@{o}]: empty
       blocks.  [psub_universal], [psub_lift], [pquot_universal] and
       [pquot_desc] carry only the three [o <= compose.u*] caps of
       Instance/Sets.v's [setoid_morphism_compose].  [PSub] and [PQuot]
       are accepted at [PTop@{Set}] (scratch).
     - [ex732_Y@{o}] and the constants built on it carry [o <=
       Subset_projections.u0], the stdlib cap of [proj1_sig].
     - The sliced constants take [@{o so u}] (and one more universe for
       the adjunctions and the triangle facts), with [o < so] declared
       and [o < u] Construction/Slice.v's own strict bound of the hom
       level below a [Program] auxiliary universe.  [Set < so] is
       inherited from [PTopCat] and implied by [o < so]; [Set <
       Projections.u0] is implied by [so <= Projections.u0], the cap
       Construction/Slice.v's [Slice] carries on the object universe
       ([projT1]'s).  The adjunctions add the stdlib caps of
       [Build_Adjunction'] ([Logic_lemmas.equality], [prod_rect],
       [projections]), and [pquot_unit] and [quotient_LARI] add [so <=
       Logic_lemmas.equality.u0]: the stdlib [eq_sym] takes its type
       argument at that universe and is applied here to an equation
       between objects at [so], which is also why
       [LeftAdjointRightInverse]'s own block carries the cap on its
       second category's object universe.
     - [subspace_RARI@{o so u u0}] has type [∀ X,
       RightAdjointRightInverse@{so so o u0 u} (Sliced@{so o so o u0 u0
       so so} PForget@{o so} X)] and [quotient_LARI@{o so u u0}] has type
       [∀ X, LeftAdjointRightInverse@{so u0 u so o} (Cosliced@{so o so o
       u0 u0 so so} PForget@{o so} X)]: both slices' hom levels at the
       points' universe [o], and the two slice-auxiliary universes at one
       [u0], the identification Structure/SlicedInverse.v's header
       discloses.
     - [PTop_HasEqualizers@{o so u u0 u1 u2 u3} : HasEqualizers@{so o}
       PTopCat@{o so}] and [PTop_HasCoequalizers@{o so u u0 u1 u2 u3 u4} :
       HasCoequalizers@{so o} PTopCat@{o so}]: the structures sit at the
       category's own levels, and their blocks add only [<=] caps and
       strict bounds of [o] below auxiliary universes to the bounds
       above.
     - The witnesses at concrete spaces keep [o] and [so] throughout:
       [PBool_subspace_RARI@{o so u u0}] has type
       [RightAdjointRightInverse@{so so o u0 u} (Sliced@{so o so o u0 u0
       so so} PForget@{o so} PBool@{o})], [PBool_quotient_LARI@{o so u
       u0}] the cosliced dual; [PBool_equalizer@{o so u u0 u1 u2 u3}] and
       [PBool_coequalizer@{o so u u0 u1 u2 u3 u4}] are the (co)equalizers
       of [PTop_HasEqualizers] and [PTop_HasCoequalizers] at those
       instances, and each readback names them at [o] and [so] by an
       explicit instance, so that no [About] block carries a second copy
       of the two.  [pbool_true@{o}], [ppoint_false@{o}] and
       [ppoint_true@{o}] carry only [o <= Logic_lemmas.equality.u0], the
       cap Instance/Sets.v's [unit_setoid_object] and [bool_setoid_object]
       carry.
   No universe is pinned at [Set], and the only [Set] in any block is the
   two implied bounds above: over the [About] output of all 111 of this
   file's constants (its [Print Module] listing, obligations included),
   [Set < so] occurs in 68 blocks and [Set < Projections.u0] in 17, each
   of those 17 also carrying [so <= Projections.u0]; no block carries an
   equation.

   ROUTE AND COST.  Closure: 81 [Category.*] modules excluding this file
   ([Print Libraries] on a file requiring it).  Before the packaging it
   was 45; adding the Requires in turn, Structure/SlicedInverse.v costs
   12 (to 57), its satellite Structure/SlicedInverse/Strict.v 1 more
   (Theory/Equivalence/Strict.v was required already),
   Instance/Sets/Coequalizer.v 13 (to 71), and the equalizer route
   (Structure/Pullback/Reduction.v with Instance/Sets/Pullback.v) 10 (to
   81).  The equalizer donor was chosen on that measurement against the
   same list: Adjunction/GAFT/Sets.v's [Sets_HasEqualizers] or
   Adjunction/CokernelPair.v's [SetsEqualizers] would give 87, and
   Adjunction/Diagonal/Finite.v's [DiagSets_HasEqualizers] 98.  The
   packaging needs only Structure/SlicedInverse.v (57); the other 24
   modules are spent by [PTop_HasEqualizers], [PTop_HasCoequalizers] and
   their readbacks, which stay here, where #457's plan places them.

   NOT DELIVERED.  Initial and final topologies for FAMILIES of maps and
   the product topology (catalog maclane:V.9:remark1, #458's), and so no
   products, completeness or cocompleteness of [PTopCat]; any comparison
   of [PSub] or [PQuot] with the Type-valued constructions (Instance/Top/
   Presheaf.v's open subspaces, Instance/Top/Pushout.v's quotient,
   Instance/Top/Subspace/TypeValued.v's [TQuot]); any comparison of the
   [Sets] equalizer chosen here with the tree's other inhabitants of
   [HasEqualizers Sets]; the preservation corollaries
   ([equalizers_from_sliced_RARI_preserved] and its dual) restated at
   [PForget]; no uniqueness statement for L or M; and no witness whose
   topology is not discrete: at [PBool] the witnesses exhibit which
   points the equalizer and the coequalizer carry, and their opens are
   not computed here. *)

#[local] Obligation Tactic := idtac.

(** ** The subspace (initial) topology along a function *)

Section Subspace.

Universe o.

Context (X : PTop@{o}) (S : SetoidObject@{o o})
        (h : SetoidMorphism@{o o o} S X).

(* Mac Lane's predicate: V is open when it is the preimage along [h] of an
   open of X. *)
Definition psub_open (V : S → Prop) : Prop :=
  ex (fun U : X → Prop => POpen X U /\ ∀ s, V s <-> U (h s)).

Lemma psub_open_respects (U V : S → Prop) :
  (∀ s, U s <-> V s) → psub_open U → psub_open V.
Proof.
  intros HUV [B [HB HUB]]. exists B; split; [exact HB|].
  intro s; split.
  - intro v; exact (proj1 (HUB s) (proj2 (HUV s) v)).
  - intro b; exact (proj1 (HUV s) (proj2 (HUB s) b)).
Qed.

Lemma psub_open_proper (U : S → Prop) :
  psub_open U → ∀ s t : S, s ≈ t → U s → U t.
Proof.
  intros [B [HB HUB]] s t e u. apply (proj2 (HUB t)).
  exact (popen_proper X B HB (h s) (h t) (proper_morphism h s t e)
           (proj1 (HUB s) u)).
Qed.

(* The union of a family of subspace-opens is the preimage of the union of
   the family of ALL the opens of X witnessing a member: a Prop-valued
   family, so no choice of witnesses is made. *)
Lemma psub_open_union (F : (S → Prop) → Prop) :
  (∀ V, F V → psub_open V) →
  psub_open (fun s => ex (fun V => F V /\ V s)).
Proof.
  intro HF.
  exists (fun x => ex (fun U => (POpen X U /\
                                 ex (fun V => F V /\ ∀ s, V s <-> U (h s)))
                                /\ U x)).
  split.
  - apply popen_union. intros U [HU _]; exact HU.
  - intro s; split.
    + intros [V [FV v]]. destruct (HF V FV) as [U [HU HVU]].
      exists U. split; [split; [exact HU|]|].
      * exists V; split; [exact FV|exact HVU].
      * exact (proj1 (HVU s) v).
    + intros [U [[_ [V [FV HVU]]] u]].
      exists V; split; [exact FV|exact (proj2 (HVU s) u)].
Qed.

Lemma psub_open_whole : psub_open (fun _ => True).
Proof.
  exists (fun _ => True); split; [exact (popen_whole X)|].
  intro s; exact (iff_refl _).
Qed.

Lemma psub_open_inter (U V : S → Prop) :
  psub_open U → psub_open V → psub_open (fun s => U s /\ V s).
Proof.
  intros [A [HA HUA]] [B [HB HVB]].
  exists (fun x => A x /\ B x); split.
  - exact (popen_inter X A B HA HB).
  - intro s; split.
    + intros [u v]; exact (conj (proj1 (HUA s) u) (proj1 (HVB s) v)).
    + intros [a b]; exact (conj (proj2 (HUA s) a) (proj2 (HVB s) b)).
Qed.

Definition PSub : PTop@{o} := {|
  pt_carrier     := S;
  POpen          := psub_open;
  popen_respects := psub_open_respects;
  popen_proper   := psub_open_proper;
  popen_union    := psub_open_union;
  popen_whole    := psub_open_whole;
  popen_inter    := psub_open_inter
|}.

(* The subspace's points are [S] and its opens are the book's, verbatim. *)
Example PSub_carrier : pt_carrier PSub = S := eq_refl.

Example PSub_open (V : S → Prop) :
  POpen PSub V = ex (fun U : X → Prop => POpen X U /\ ∀ s, V s <-> U (h s))
  := eq_refl.

(* [h] is continuous out of the subspace. *)
Lemma psub_incl_cont : @PCont PSub X h.
Proof.
  intros U HU. exists U; split; [exact HU|].
  intro s; exact (iff_refl _).
Qed.

Definition psub_incl : PMor@{o} PSub X :=
  @Build_PMor PSub X h psub_incl_cont.

(* The universal property, over ARBITRARY spaces [Z] mapping in: a setoid
   map into the subspace is continuous exactly when its composite with [h]
   is. *)
Lemma psub_universal (Z : PTop@{o}) (g : SetoidMorphism@{o o o} Z S) :
  @PCont Z PSub g <-> @PCont Z X (setoid_morphism_compose h g).
Proof.
  split.
  - intros Hg U HU. exact (Hg _ (psub_incl_cont U HU)).
  - intros Hc V [U [HU HVU]].
    apply (popen_respects Z (fun z => U (h (g z)))).
    + intro z; exact (iff_sym (HVU (g z))).
    + exact (Hc U HU).
Qed.

(* The book's form: a continuous [f : Z → X] whose underlying function
   factors as [h ∘ g] has [g] continuous into the subspace. *)
Definition psub_lift (Z : PTop@{o}) (f : PMor@{o} Z X)
  (g : SetoidMorphism@{o o o} Z S) (Hfg : ∀ z, pmap f z ≈ h (g z)) :
  PMor@{o} Z PSub :=
  @Build_PMor Z PSub g
    (proj2 (psub_universal Z g)
       (pcont_respects (pmap f) (setoid_morphism_compose h g) Hfg (pcont f))).

Example psub_lift_map (Z : PTop@{o}) (f : PMor@{o} Z X)
  (g : SetoidMorphism@{o o o} Z S) (Hfg : ∀ z, pmap f z ≈ h (g z)) :
  pmap (psub_lift Z f g Hfg) = g := eq_refl.

Lemma psub_lift_comm (Z : PTop@{o}) (f : PMor@{o} Z X)
  (g : SetoidMorphism@{o o o} Z S) (Hfg : ∀ z, pmap f z ≈ h (g z)) :
  ∀ z, pmap (pcompose psub_incl (psub_lift Z f g Hfg)) z ≈ pmap f z.
Proof. intro z; symmetry; exact (Hfg z). Qed.

End Subspace.

(** ** Seven Sketches, Exercise 7.32: the subspace topology on a subset *)

Section Ex732.

Universe o.

Context (X : PTop@{o}) (P : X → Prop).

(* The subset [Y ⊆ X], with the equality of [X]. *)
Program Definition ex732_Y : SetoidObject@{o o} := {|
  carrier := { x : X | P x };
  is_setoid := {| equiv := fun a b => proj1_sig a ≈ proj1_sig b |}
|}.
Next Obligation.
  constructor.
  - intros a; reflexivity.
  - intros a b H; symmetry; exact H.
  - intros a b c H1 H2; transitivity (proj1_sig b); assumption.
Qed.

Program Definition ex732_incl : SetoidMorphism@{o o o} ex732_Y X := {|
  morphism := fun a => proj1_sig a
|}.
Next Obligation. intros a b H; exact H. Qed.

Definition ex732_Sub : PTop@{o} := PSub X ex732_Y ex732_incl.

(* The definition: [A ⊆ Y] is open iff [A = B ∩ Y] for some open [B] of
   [X]. *)
Example ex732_def (A : ex732_Y → Prop) :
  POpen ex732_Sub A
  = ex (fun B : X → Prop =>
          POpen X B /\ ∀ y : ex732_Y, A y <-> B (proj1_sig y)) := eq_refl.

(* Part 1: [Y] itself is open, [B] being the whole of [X]. *)
Lemma ex732_part1 :
  POpen X (fun _ => True)
  /\ (∀ y : ex732_Y, True <-> (fun _ : X => True) (proj1_sig y))
  /\ POpen ex732_Sub (fun _ => True).
Proof.
  split; [exact (popen_whole X)|split].
  - intro y; exact (iff_refl _).
  - exists (fun _ => True); split; [exact (popen_whole X)|].
    intro y; exact (iff_refl _).
Qed.

(* Part 2: the three axioms of Seven Sketches' Definition 7.25 -- the whole
   set, binary intersections, and unions of families indexed by any set [I],
   here any type at any universe. *)
Lemma ex732_part2 :
  POpen ex732_Sub (fun _ => True)
  /\ (∀ A B : ex732_Y → Prop, POpen ex732_Sub A → POpen ex732_Sub B →
        POpen ex732_Sub (fun y => A y /\ B y))
  /\ (∀ (I : Type) (A : I → ex732_Y → Prop), (∀ k, POpen ex732_Sub (A k)) →
        POpen ex732_Sub (fun y => ex (fun k => A k y))).
Proof.
  split; [exact (psub_open_whole X ex732_Y ex732_incl)|split].
  - exact (psub_open_inter X ex732_Y ex732_incl).
  - intros I A HA. exact (popen_union_indexed ex732_Sub I A HA).
Qed.

(* Part 3: the inclusion is continuous. *)
Lemma ex732_part3 : @PCont ex732_Sub X ex732_incl.
Proof. exact (psub_incl_cont X ex732_Y ex732_incl). Qed.

Definition ex732_incl_mor : PMor@{o} ex732_Sub X :=
  psub_incl X ex732_Y ex732_incl.

End Ex732.

(** ** The quotient (final) topology along a function *)

Section Quotient.

Universe o.

Context (X : PTop@{o}) (T : SetoidObject@{o o})
        (q : SetoidMorphism@{o o o} X T).

(* Mac Lane's predicate, V open when its preimage along [q] is, together
   with the setoid bookkeeping: V respects the equality of [T]. *)
Definition pquot_open (V : T → Prop) : Prop :=
  (∀ t t' : T, t ≈ t' → V t → V t') /\ POpen X (fun x => V (q x)).

Lemma pquot_open_respects (U V : T → Prop) :
  (∀ t, U t <-> V t) → pquot_open U → pquot_open V.
Proof.
  intros H [Hp Ho]; split.
  - intros t t' e v. apply (proj1 (H t')), (Hp t t' e), (proj2 (H t)), v.
  - exact (popen_respects X _ _ (fun x => H (q x)) Ho).
Qed.

Lemma pquot_open_proper (U : T → Prop) :
  pquot_open U → ∀ t t' : T, t ≈ t' → U t → U t'.
Proof. intros [Hp _]; exact Hp. Qed.

Lemma pquot_open_union (F : (T → Prop) → Prop) :
  (∀ V, F V → pquot_open V) →
  pquot_open (fun t => ex (fun V => F V /\ V t)).
Proof.
  intro HF; split.
  - intros t t' e [V [FV v]]. exists V; split; [exact FV|].
    exact (proj1 (HF V FV) t t' e v).
  - apply (popen_respects X
             (fun x => ex (fun U => ex (fun V => F V /\
                                          ∀ y, U y <-> V (q y)) /\ U x))).
    + intro x; split.
      * intros [U [[V [FV HUV]] u]]. exists V.
        split; [exact FV|exact (proj1 (HUV x) u)].
      * intros [V [FV v]]. exists (fun y => V (q y)).
        split; [|exact v]. exists V; split; [exact FV|].
        intro y; exact (iff_refl _).
    + apply popen_union. intros U [V [FV HUV]].
      apply (popen_respects X (fun y => V (q y))).
      * intro y; exact (iff_sym (HUV y)).
      * exact (proj2 (HF V FV)).
Qed.

Lemma pquot_open_whole : pquot_open (fun _ => True).
Proof. split; [intros; exact I|exact (popen_whole X)]. Qed.

Lemma pquot_open_inter (U V : T → Prop) :
  pquot_open U → pquot_open V → pquot_open (fun t => U t /\ V t).
Proof.
  intros [HpU HoU] [HpV HoV]; split.
  - intros t t' e [u v]; exact (conj (HpU t t' e u) (HpV t t' e v)).
  - exact (popen_inter X _ _ HoU HoV).
Qed.

Definition PQuot : PTop@{o} := {|
  pt_carrier     := T;
  POpen          := pquot_open;
  popen_respects := pquot_open_respects;
  popen_proper   := pquot_open_proper;
  popen_union    := pquot_open_union;
  popen_whole    := pquot_open_whole;
  popen_inter    := pquot_open_inter
|}.

Example PQuot_carrier : pt_carrier PQuot = T := eq_refl.

Example PQuot_open (V : T → Prop) :
  POpen PQuot V
  = ((∀ t t' : T, t ≈ t' → V t → V t') /\ POpen X (fun x => V (q x)))
  := eq_refl.

Lemma pquot_proj_cont : @PCont X PQuot q.
Proof. intros V HV; exact (proj2 HV). Qed.

Definition pquot_proj : PMor@{o} X PQuot :=
  @Build_PMor X PQuot q pquot_proj_cont.

(* The universal property, over ARBITRARY spaces [Z] mapping out: a setoid
   map out of the quotient is continuous exactly when its composite with
   [q] is. *)
Lemma pquot_universal (Z : PTop@{o}) (k : SetoidMorphism@{o o o} T Z) :
  @PCont PQuot Z k <-> @PCont X Z (setoid_morphism_compose k q).
Proof.
  split.
  - intros Hk W HW. exact (proj2 (Hk W HW)).
  - intros Hc W HW; split.
    + intros t t' e w.
      exact (popen_proper Z W HW (k t) (k t') (proper_morphism k t t' e) w).
    + exact (Hc W HW).
Qed.

(* The book's form: a continuous [f : X → Z] whose underlying function
   factors as [k ∘ q] has [k] continuous out of the quotient. *)
Definition pquot_desc (Z : PTop@{o}) (f : PMor@{o} X Z)
  (k : SetoidMorphism@{o o o} T Z) (Hfk : ∀ x, pmap f x ≈ k (q x)) :
  PMor@{o} PQuot Z :=
  @Build_PMor PQuot Z k
    (proj2 (pquot_universal Z k)
       (pcont_respects (pmap f) (setoid_morphism_compose k q) Hfk (pcont f))).

Example pquot_desc_map (Z : PTop@{o}) (f : PMor@{o} X Z)
  (k : SetoidMorphism@{o o o} T Z) (Hfk : ∀ x, pmap f x ≈ k (q x)) :
  pmap (pquot_desc Z f k Hfk) = k := eq_refl.

Lemma pquot_desc_comm (Z : PTop@{o}) (f : PMor@{o} X Z)
  (k : SetoidMorphism@{o o o} T Z) (Hfk : ∀ x, pmap f x ≈ k (q x)) :
  ∀ x, pmap (pcompose (pquot_desc Z f k Hfk) pquot_proj) x ≈ pmap f x.
Proof. intro x; symmetry; exact (Hfk x). Qed.

End Quotient.

(** ** The sliced forgetful functors and the sliced adjunctions *)

Section SliceAdjunctions.

Universes o so.
Constraint o < so.

Context (X : PTop@{o}).

Local Notation PT := PTopCat@{o so}.
Local Notation G := PForget@{o so}.

(* The forgetful functor sliced over [X], Mac Lane's [G ↓ X]: the generic
   [Sliced] of Structure/SlicedInverse.v at [PForget], under a local name.
   It is an alias, not a second functor, so the adjunction below is at
   once an adjunction of [Sliced G X] and Proposition 1 consumes it. *)
Definition PForget_over : @Slice PT X ⟶ @Slice Sets@{o so} (G X) :=
  Sliced G X.

(* The forgetful functor sliced under [X], Mac Lane's [X ↓ G]: the generic
   [Cosliced] at [PForget]. *)
Definition PForget_under : @Coslice PT X ⟶ @Coslice Sets@{o so} (G X) :=
  Cosliced G X.

Example PForget_over_Sliced : PForget_over = Sliced G X := eq_refl.

Example PForget_under_Cosliced : PForget_under = Cosliced G X := eq_refl.

(* Mac Lane's [L]: the subspace along each function into the points of
   [X]. *)
Program Definition PSub_Functor :
  @Slice Sets@{o so} (G X) ⟶ @Slice PT X := {|
  fobj := fun c => (PSub X (`1 c) (`2 c); psub_incl X (`1 c) (`2 c));
  fmap := fun c d m => ({| pmap := `1 m; pcont := _ |}; _)
|}.
Next Obligation.
  intros [S h] [S' h'] [m Hm]; simpl in *.
  apply (proj2 (psub_universal X S' h' (PSub X S h) m)).
  apply (@pcont_respects (PSub X S h) X h);
    [intro s; symmetry; exact (Hm s)|].
  exact (psub_incl_cont X S h).
Qed.
Next Obligation. intros [S h] [S' h'] [m Hm] s; simpl in *. exact (Hm s). Qed.
Next Obligation. intros c d m n H s; simpl in *. exact (H s). Qed.
Next Obligation. intros c s; simpl. reflexivity. Qed.
Next Obligation. intros c d e m n s; simpl. reflexivity. Qed.

Example PSub_Functor_obj (c : @Slice Sets@{o so} (G X)) :
  `1 (PSub_Functor c) = PSub X (`1 c) (`2 c) := eq_refl.

(* The hom-set bijection of [G ↓ X ⊣ L]: a map over [X] into the subspace
   IS its underlying map, continuity coming from [psub_universal]. *)
Program Definition psub_adj_iso (x : @Slice PT X)
  (y : @Slice Sets@{o so} (G X)) :
  @Isomorphism Sets
    {| carrier := @hom (@Slice Sets@{o so} (G X)) (PForget_over x) y
     ; is_setoid := @homset (@Slice Sets@{o so} (G X)) (PForget_over x) y |}
    {| carrier := @hom (@Slice PT X) x (PSub_Functor y)
     ; is_setoid := @homset (@Slice PT X) x (PSub_Functor y) |} := {|
  to   := {| morphism := fun k => ({| pmap := `1 k; pcont := _ |}; _) |};
  from := {| morphism := fun k => (pmap (`1 k); _) |}
|}.
Next Obligation.
  intros [Y g] [S h] [k Hk]; simpl in *.
  apply (proj2 (psub_universal X S h Y k)).
  apply (pcont_respects (pmap g)); [intro z; symmetry; exact (Hk z)|].
  exact (pcont g).
Qed.
Next Obligation. intros [Y g] [S h] [k Hk] z; simpl in *. exact (Hk z). Qed.
Next Obligation. intros x y k k' H z; simpl in *. exact (H z). Qed.
Next Obligation. intros [Y g] [S h] [k Hk] z; simpl in *. exact (Hk z). Qed.
Next Obligation. intros x y k k' H z; simpl in *. exact (H z). Qed.
Next Obligation. intros x y k z; simpl. reflexivity. Qed.
Next Obligation. intros x y k z; simpl. reflexivity. Qed.

(* Both transposes are the identity on underlying maps. *)
Example psub_adj_to_map (x : @Slice PT X) (y : @Slice Sets@{o so} (G X))
  (k : PForget_over x ~{@Slice Sets@{o so} (G X)}~> y) :
  pmap (`1 (to (psub_adj_iso x y) k)) = `1 k := eq_refl.

Example psub_adj_from_map (x : @Slice PT X) (y : @Slice Sets@{o so} (G X))
  (k : x ~{@Slice PT X}~> PSub_Functor y) :
  `1 (from (psub_adj_iso x y) k) = pmap (`1 k) := eq_refl.

Definition psub_adjunction : PForget_over ⊣ PSub_Functor.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ PForget_over PSub_Functor
                     psub_adj_iso).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(* [(G ↓ X) ∘ L = Id] on objects: Leibniz, after destructing the pair;
   [Defined], so that the [id_cast] below reduces. *)
Lemma psub_obj (c : @Slice Sets@{o so} (G X)) :
  PForget_over (PSub_Functor c) = c.
Proof. destruct c; reflexivity. Defined.

Example psub_obj_pair (S : SetoidObject@{o o})
  (h : S ~{Sets@{o so}}~> G X) :
  PForget_over (PSub_Functor (S; h)) = (S; h) := eq_refl.

(* The counit is the identity, transported along [psub_obj]. *)
Lemma psub_counit (c : @Slice Sets@{o so} (G X)) :
  @counit _ _ _ _ psub_adjunction c ≈ id_cast (psub_obj c).
Proof. destruct c; intro t; simpl. reflexivity. Qed.

(* Mac Lane's [M]: the quotient along each function out of the points of
   [X]. *)
Program Definition PQuot_Functor :
  @Coslice Sets@{o so} (G X) ⟶ @Coslice PT X := {|
  fobj := fun c => (PQuot X (`1 c) (`2 c); pquot_proj X (`1 c) (`2 c));
  fmap := fun c d m => ({| pmap := `1 m; pcont := _ |}; _)
|}.
Next Obligation.
  intros [T q] [T' q'] [m Hm]; simpl in *.
  apply (proj2 (pquot_universal X T q (PQuot X T' q') m)).
  apply (@pcont_respects X (PQuot X T' q') q'); [exact Hm|].
  exact (pquot_proj_cont X T' q').
Qed.
Next Obligation. intros [T q] [T' q'] [m Hm] x; simpl in *. exact (Hm x). Qed.
Next Obligation. intros c d m n H t; simpl in *. exact (H t). Qed.
Next Obligation. intros c t; simpl. reflexivity. Qed.
Next Obligation. intros c d e m n t; simpl. reflexivity. Qed.

Example PQuot_Functor_obj (c : @Coslice Sets@{o so} (G X)) :
  `1 (PQuot_Functor c) = PQuot X (`1 c) (`2 c) := eq_refl.

(* The hom-set bijection of [M ⊣ X ↓ G]: a map under [X] out of the
   quotient IS its underlying map, continuity coming from
   [pquot_universal]. *)
Program Definition pquot_adj_iso (x : @Coslice Sets@{o so} (G X))
  (y : @Coslice PT X) :
  @Isomorphism Sets
    {| carrier := @hom (@Coslice PT X) (PQuot_Functor x) y
     ; is_setoid := @homset (@Coslice PT X) (PQuot_Functor x) y |}
    {| carrier := @hom (@Coslice Sets@{o so} (G X)) x (PForget_under y)
     ; is_setoid := @homset (@Coslice Sets@{o so} (G X)) x
                      (PForget_under y) |} := {|
  to   := {| morphism := fun k => (pmap (`1 k); _) |};
  from := {| morphism := fun k => ({| pmap := `1 k; pcont := _ |}; _) |}
|}.
Next Obligation. intros [T q] [Y f] [k Hk] x; simpl in *. exact (Hk x). Qed.
Next Obligation. intros x y k k' H t; simpl in *. exact (H t). Qed.
Next Obligation.
  intros [T q] [Y f] [k Hk]; simpl in *.
  apply (proj2 (pquot_universal X T q Y k)).
  apply (pcont_respects (pmap f)); [exact Hk|].
  exact (pcont f).
Qed.
Next Obligation. intros [T q] [Y f] [k Hk] x; simpl in *. exact (Hk x). Qed.
Next Obligation. intros x y k k' H t; simpl in *. exact (H t). Qed.
Next Obligation. intros x y k t; simpl. reflexivity. Qed.
Next Obligation. intros x y k t; simpl. reflexivity. Qed.

Example pquot_adj_to_map (x : @Coslice Sets@{o so} (G X))
  (y : @Coslice PT X) (k : PQuot_Functor x ~{@Coslice PT X}~> y) :
  `1 (to (pquot_adj_iso x y) k) = pmap (`1 k) := eq_refl.

Example pquot_adj_from_map (x : @Coslice Sets@{o so} (G X))
  (y : @Coslice PT X)
  (k : x ~{@Coslice Sets@{o so} (G X)}~> PForget_under y) :
  pmap (`1 (from (pquot_adj_iso x y) k)) = `1 k := eq_refl.

Definition pquot_adjunction : PQuot_Functor ⊣ PForget_under.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ PQuot_Functor PForget_under
                     pquot_adj_iso).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(* [(X ↓ G) ∘ M = Id] on objects. *)
Lemma pquot_obj (c : @Coslice Sets@{o so} (G X)) :
  PForget_under (PQuot_Functor c) = c.
Proof. destruct c; reflexivity. Defined.

Example pquot_obj_pair (T : SetoidObject@{o o})
  (q : G X ~{Sets@{o so}}~> T) :
  PForget_under (PQuot_Functor (T; q)) = (T; q) := eq_refl.

(* The unit is the identity, transported along [pquot_obj]. *)
Lemma pquot_unit (c : @Coslice Sets@{o so} (G X)) :
  @unit _ _ _ _ pquot_adjunction c ≈ id_cast (eq_sym (pquot_obj c)).
Proof. destruct c; intro t; simpl. reflexivity. Qed.

(* The subspace construction packaged: [L] is a right-adjoint-right-inverse
   of [G ↓ X], in Structure/SlicedInverse.v's record, which is what
   Proposition 1 consumes. *)
Definition subspace_RARI : RightAdjointRightInverse (Sliced G X) := {|
  rari_right  := PSub_Functor;
  rari_adj    := psub_adjunction;
  rari_obj    := psub_obj;
  rari_counit := psub_counit
|}.

Example subspace_RARI_right : rari_right subspace_RARI = PSub_Functor :=
  eq_refl.

(* The quotient construction packaged: [M] is a left-adjoint-right-inverse
   of [X ↓ G], in Theory/Equivalence/Strict.v's record, which is what the
   dual of Proposition 1 consumes. *)
Definition quotient_LARI : LeftAdjointRightInverse (Cosliced G X) := {|
  lari_left := PQuot_Functor;
  lari_adj  := pquot_adjunction;
  lari_obj  := pquot_obj;
  lari_unit := pquot_unit
|}.

Example quotient_LARI_left : lari_left quotient_LARI = PQuot_Functor :=
  eq_refl.

End SliceAdjunctions.

(** ** Equalizers and coequalizers of spaces, by Proposition 1 and its dual *)

(* The downstairs equalizers: Structure/Pullback/Reduction.v's
   [HasEqualizers_of_HasPullbacks_Terminal] fed Instance/Sets/Pullback.v's
   [Sets_HasPullbacks] and Instance/Sets.v's [Sets_Terminal], the term of
   Adjunction/CokernelPair.v's [SetsEqualizers], written out here because
   requiring that file costs more (see the header). *)
#[local] Notation SetsEq :=
  (@HasEqualizers_of_HasPullbacks_Terminal Sets Sets_Terminal
     Sets_HasPullbacks).

(* Mac Lane's Proposition 1 at [PForget]: the equalizer of two continuous
   maps is the subspace on their equalizer in [Sets]. *)
Definition PTop_HasEqualizers@{o so + | o < so +} :
  @HasEqualizers PTopCat@{o so} :=
  @equalizers_from_sliced_RARI _ _ PForget@{o so} PForget_Faithful SetsEq
    subspace_RARI.

Example PTop_equalizer_obj@{o so + | o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (@equalizer _ PTop_HasEqualizers x y f g)
    = PSub x (`1 (@equalizer _ SetsEq _ _ (fmap[PForget] f) (fmap[PForget] g)))
        (`1 (`2 (@equalizer _ SetsEq _ _ (fmap[PForget] f) (fmap[PForget] g))))
  := eq_refl.

Example PTop_equalizer_arrow@{o so + | o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (`2 (@equalizer _ PTop_HasEqualizers x y f g))
    = psub_incl x
        (`1 (@equalizer _ SetsEq _ _ (fmap[PForget] f) (fmap[PForget] g)))
        (`1 (`2 (@equalizer _ SetsEq _ _ (fmap[PForget] f) (fmap[PForget] g))))
  := eq_refl.

(* The dual of Proposition 1 at [PForget], over Instance/Sets/Coequalizer.v's
   [Sets_HasCoequalizers]: the coequalizer of two continuous maps is the
   quotient topology on their coequalizer in [Sets], the quotient of the
   codomain's points by the equivalence the pair generates. *)
Definition PTop_HasCoequalizers@{o so + | o < so +} :
  @HasCoequalizers PTopCat@{o so} :=
  @coequalizers_from_sliced_LARI _ _ PForget@{o so} PForget_Faithful
    Sets_HasCoequalizers quotient_LARI.

Example PTop_coequalizer_obj@{o so + | o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (@coeq _ PTop_HasCoequalizers x y f g)
    = PQuot y (SetsCoeq (fmap[PForget] f) (fmap[PForget] g))
        (sets_coeq_proj (fmap[PForget] f) (fmap[PForget] g)) := eq_refl.

Example PTop_coequalizer_arrow@{o so + | o < so +} {x y : PTopCat@{o so}}
  (f g : x ~> y) :
  `1 (`2 (@coeq _ PTop_HasCoequalizers x y f g))
    = pquot_proj y (SetsCoeq (fmap[PForget] f) (fmap[PForget] g))
        (sets_coeq_proj (fmap[PForget] f) (fmap[PForget] g)) := eq_refl.

(** ** Applied at concrete spaces: an equalizer and a coequalizer of two
       different maps *)

(* The two constructions at the concrete two-point space [PBool] of
   Instance/Top/Prop.v, which the two witnesses below consume. *)
Definition PBool_subspace_RARI@{o so +| o < so +} :
  RightAdjointRightInverse (Sliced PForget@{o so} PBool@{o}) :=
  subspace_RARI PBool.

Definition PBool_quotient_LARI@{o so +| o < so +} :
  LeftAdjointRightInverse (Cosliced PForget@{o so} PBool@{o}) :=
  quotient_LARI PBool.

(* The constant map at [true] on [PBool]; it differs from the identity, at
   [false]. *)
Definition pbool_true@{o} : PMor@{o} PBool PBool :=
  pdisc_mor bool_setoid_object PBool (pconst bool_setoid_object PBool true).

Lemma pbool_maps_differ@{o so | o < so +} :
  pid PBool ≈[PTopCat@{o so}] pbool_true → False.
Proof. intro H; specialize (H false); simpl in H; discriminate H. Qed.

(* Proposition 1 at the pair (identity, constant [true]) on [PBool]: the
   subspace of [PBool] on the [Sets] equalizer of the underlying maps,
   which is the value of [rari_right PBool_subspace_RARI] there. *)
Definition PBool_equalizer@{o so +| o < so +} :=
  @equalizer PTopCat@{o so} PTop_HasEqualizers PBool PBool (pid PBool)
    pbool_true.

Example PBool_equalizer_obj@{o so +| o < so +} :
  `1 PBool_equalizer@{o so _ _ _ _ _}
    = PSub PBool
        (`1 (@equalizer _ SetsEq _ _ setoid_morphism_id
               (pconst bool_setoid_object PBool true)))
        (`1 (`2 (@equalizer _ SetsEq _ _ setoid_morphism_id
                   (pconst bool_setoid_object PBool true)))) := eq_refl.

Example PBool_equalizer_rari@{o so +| o < so +} :
  `1 PBool_equalizer@{o so _ _ _ _ _}
    = `1 (rari_right PBool_subspace_RARI@{o so _ _}
            (`1 (@equalizer _ SetsEq _ _ setoid_morphism_id
                   (pconst bool_setoid_object PBool true));
             `1 (`2 (@equalizer _ SetsEq _ _ setoid_morphism_id
                       (pconst bool_setoid_object PBool true))))) := eq_refl.

(* Which points of [PBool] lie in the equalizer: exactly [true], so the
   equalizer is a proper, nonempty subspace.  The "only if" is the fork
   equation, the "if" the universal property at the point picking
   [true]. *)
Lemma PBool_equalizer_points@{o so +| o < so +} (b : bool) :
  ex (fun e : pt_carrier (`1 PBool_equalizer@{o so _ _ _ _ _}) =>
        pmap (`1 (`2 PBool_equalizer@{o so _ _ _ _ _})) e = b)
  <-> b = true.
Proof.
  split.
  - intros [e He]. pose proof (fork_eq (`2 (`2 PBool_equalizer)) e) as F.
    simpl in F. rewrite <- He. exact F.
  - intros ->.
    pose (t := pdisc_mor unit_setoid_object PBool (pconst _ PBool true)
               : PPoint ~{PTopCat@{o so}}~> PBool).
    destruct (eq_desc (`2 (`2 PBool_equalizer@{o so _ _ _ _ _})) t
                (fun _ => eq_refl)) as [u Hu _].
    exists (pmap u ttt). exact (Hu ttt).
Qed.

(* The two points of [PBool], as maps out of the one-point space; they
   differ. *)
Definition ppoint_false@{o} : PMor@{o} PPoint PBool :=
  pdisc_mor unit_setoid_object PBool (pconst unit_setoid_object PBool false).

Definition ppoint_true@{o} : PMor@{o} PPoint PBool :=
  pdisc_mor unit_setoid_object PBool (pconst unit_setoid_object PBool true).

Lemma ppoint_maps_differ@{o so | o < so +} :
  ppoint_false ≈[PTopCat@{o so}] ppoint_true → False.
Proof. intro H; specialize (H ttt); simpl in H; discriminate H. Qed.

(* The dual of Proposition 1 at the pair ([false], [true]) out of the
   point: the quotient topology on the [Sets] coequalizer of the
   underlying maps, which is the value of [lari_left PBool_quotient_LARI]
   there. *)
Definition PBool_coequalizer@{o so +| o < so +} :=
  @coeq PTopCat@{o so} PTop_HasCoequalizers PPoint PBool ppoint_false
    ppoint_true.

Example PBool_coequalizer_obj@{o so +| o < so +} :
  `1 PBool_coequalizer@{o so _ _ _ _ _ _}
    = PQuot PBool
        (SetsCoeq (pconst unit_setoid_object PBool false)
                  (pconst unit_setoid_object PBool true))
        (sets_coeq_proj (pconst unit_setoid_object PBool false)
                        (pconst unit_setoid_object PBool true)) := eq_refl.

Example PBool_coequalizer_lari@{o so +| o < so +} :
  `1 PBool_coequalizer@{o so _ _ _ _ _ _}
    = `1 (lari_left PBool_quotient_LARI@{o so _ _}
            (SetsCoeq (pconst unit_setoid_object PBool false)
                      (pconst unit_setoid_object PBool true);
             sets_coeq_proj (pconst unit_setoid_object PBool false)
                            (pconst unit_setoid_object PBool true)))
  := eq_refl.

(* In the coequalizer every point is identified with [true], so the two
   points [PBool] separates ([PBool_points_distinct]) are glued: a proper
   quotient, to one point up to its equality. *)
Lemma PBool_coequalizer_points@{o so +| o < so +} (b : bool) :
  @equiv _ (`1 PBool_coequalizer@{o so _ _ _ _ _ _}) b true.
Proof.
  destruct b.
  - apply cq_base. reflexivity.
  - exact (cq_glue (pconst unit_setoid_object PBool false)
                   (pconst unit_setoid_object PBool true) ttt).
Qed.
