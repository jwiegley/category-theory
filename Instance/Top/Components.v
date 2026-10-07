Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Adjunction.Continuity.Equalizer.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Sets.Propositional.Full.
Require Import Category.Instance.Top.Prop.
Require Import Category.Instance.Top.Complete.
Require Import Category.Instance.Top.Cocomplete.
Require Import Category.Instance.Top.Separation.
Require Category.Theory.Concrete.
Require Import Coq.Arith.PeanoNat.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Classifier.OneLevel.

Generalizable All Variables.

(** * Connected components: Mac Lane §V.9 Exercise 1 *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
     read from the page images:
     - §V.9 Exercise 1, book p. 135 (PDF p. 144) (catalog id
       maclane:V.9:ex1):
       "For the full subcategory Lconn of locally connected spaces in Top,
       prove that D: Set → Lconn has a left adjoint C, assigning to each
       space X the set of its connected components, but show that this
       functor C can have no left adjoint (because of misbehavior on
       equalizers)."
     - D is the functor of §V.9, book p. 132 (PDF p. 141): the forgetful
       functor G : Top → Set "is faithful, and has a left adjoint D which
       assigns to each set S the discrete topology on S (i.e., all
       subsets of S are open)."  The book defines neither local
       connectedness nor the connected components of a space, and names
       no equalizer.
     - §IV.2 Exercise 9 (Smythe), book p. 90 (PDF p. 99): the functor
       O : Cat → Set of objects "has a left adjoint D which assigns to
       each set X the discrete category on X, and that D in turn has a
       left adjoint assigning to each category the set of its connected
       components"; Exercise 7(b) on the same page defines "the connected
       components of J" for a category J.  That is this exercise's twin
       for categories.
   Riehl, "Category Theory in Context", 2nd ed., §3.3, Example 3.3.2,
     printed pp. 99-100 (PDF pp. 119-120), read from the page images
     (catalog id riehl:3.3:example2, Riehl's Example 3.3.2):
     "Precomposing with the endpoint inclusions 0, 1 : ∗ ⇉ I defines a
     functor P : Top → Set^{•⇉•} that carries a space X to the parallel
     pair of functions Path(X) ≅ Top(I, X) ⇉ Top(∗, X) ≅ Point(X) that
     evaluate a path at its endpoints.  Their coequalizer [...] defines
     the set of path components of X, the quotient of the set of points
     in X by the relation that identifies any pair of points connected
     by a path.  Proposition 3.3.1 tells us that this coequalizer defines
     a functor, the path components functor π₀ := Top → Set^{•⇉•} →
     Set" (the two arrows labelled P and colim).  That is the
     PATH-components functor on all of Top, a different functor from
     Mac Lane's; it is the satellite Instance/Top/Components/Paths.v's,
     not this file's.
   nLab: https://ncatlab.org/nlab/show/Top
   nLab: https://ncatlab.org/nlab/show/locally+connected+space
   nLab: https://ncatlab.org/nlab/show/connected+space
   Wikipedia: https://en.wikipedia.org/wiki/Locally_connected_space

   BACKGROUND.  "It is not generally true that a topological space is the
   disjoint union space (coproduct in Top) of its connected components.
   The spaces such that this is true for all open subspaces are the
   locally connected topological spaces" (nLab), equivalently those in
   which "every point has a neighborhood basis of connected open subsets"
   (nLab's definition; Wikipedia's is the same).  In such a space every
   component is open, hence clopen, and nLab draws the consequence for
   the functors to sets: on locally connected spaces there is "an adjoint
   quadruple of adjoint functors Π₀ ⊣ Δ ⊣ Γ ⊣ ∇ : Set → LocConn", Π₀ the
   components, Δ the discrete space, Γ the points and ∇ the codiscrete
   space, "the adjunction structure as on a cohesive topos"; "the
   continuity of the unit X → ΔΠ₀X is immediate from a locally connected
   space's being the coproduct of its connected components."  Mac Lane's
   exercise is the leftmost adjunction of that quadruple and the reason
   it stops there: Π₀ does not preserve equalizers, so it is not a right
   adjoint.  Local connectedness is what the first half needs; below, the
   discrete functor on all spaces has no left adjoint at all.  The twin
   for categories, Mac Lane's §IV.2 Exercise 9, is Instance/Cat/
   Components.v's [Components_Disc_Adjunction : Pi0 ⊣ Cat_Disc], over
   Theory/Connected/Components.v's π₀ of a category.

   ENCODING.  Everything is over Instance/Top/Prop.v's [PTopCat], by the
   maintainer's decision for the §V.9 issues.  Over Instance/Top.v's
   Type-valued [Top] the wall is the functor, not the component relation.
   C must land among the point setoids, the objects of [Sets@{o so}], and
   a functor [Top@{h o} ⟶ Sets@{o so}] is refused ("Cannot enforce o = ...
   because o < h <= ..."): the homs of [Top] sit at [h], above the points,
   and a functor cannot lower the hom level, the reason
   Instance/Top/Forgetful.v's header gives for landing its underlying-set
   functor in [Sets@{h so}].  One universe up the functor is formable, and
   so is an [Adjunction] record between [Top] and [Sets@{h so}], but not
   one whose right adjoint is Forgetful.v's discrete functor [Top_Discrete
   : Sets@{o so} ⟶ Top@{h o}], whose domain must be the point setoids
   ("Cannot enforce ... = h because h < ...").  The relation itself is
   formable over [Top]: [comp_rel] restated there, with its neighbourhoods
   as [ex (fun O : X → Type@{o} => inhabited (IsOpen X O) /\ ...)], is a
   proposition, accepted under the closed universe list [@{o}] of the
   points' universe alone, and [About] reads back an empty constraint
   block on Rocq 9.1.  Only its Type-valued forms are refused at
   [Type@{o}], each with "universe inconsistency: Cannot enforce o < o
   because o = o": the sum over Type-valued subsets [{ W : X → Type@{o} &
   (W x * W y) }], the quasi-component form [∀ U : X → Type@{o}, IsOpen X
   U → U x → U y] and connectedness quantified over discrete targets [∀ (S
   : SetoidObject@{o o}) (g : X → S), ...]; all three are accepted at
   [Type@{h}] under [o < h].  Test/ProbeComponents462.v pins the functor
   as N1 and the adjunction as N2, each beside its control one universe
   up, the three Type-valued forms as N3, N4 and N5 beside theirs, and the
   Prop-valued relation as the control [tcomp_rel_prop].  Over [PTopCat]
   the homs sit at the points' universe (Instance/Top/Prop.v's [PMor]),
   every relation below is a proposition, and the components sit at the
   points' universe [o].

   MAC LANE'S SET: THE PROPOSITIONAL SETS, AND ALL OF [Sets] UNDER
   [Untruncate].  The tree's [Sets] has a Type-valued [≈], while
   continuity is a proposition and so is the component relation
   [comp_rel], and a proposition is not eliminated into a type.
   Extracting from [comp_rel X x y] a Type-valued witness is refused,
   and so is turning [inhabited (pmap g x ≈ pmap g y)] into
   [pmap g x ≈ pmap g y] ("Incorrect elimination of "HR" in the
   inductive type "inhabited": the return type has sort "Type" while it
   should be SProp or Prop"), Test/ProbeComponents462.v's N6 and N7;
   through a [PropEquiv] of the target it is accepted, Lib/Setoid/
   Propositional.v's [pequiv_elim_inhabited], that probe's control.
   The obstruction is not in the proof alone.
   [components_on_all_Sets_unsquashes]: ANY left adjoint of the discrete
   functor [LDisc : Sets ⟶ Lconn] yields
   [inhabited (∀ Q : Type@{o}, inhabited Q → Q)].  The unit at the
   indiscrete two-point space is continuous into a discrete space, so
   its two values are only merely equal, and transposing the identity
   into the two-point setoid whose [true ≈ false] is [Q] ([SquashSetoid],
   continuous as soon as [Q] is merely inhabited, [squash_id_cont])
   unsquashes [Q].  That principle is the truncation of
   Instance/Sets/Classifier/OneLevel.v's hypothesis [Untruncate@{o}],
   [∀ P : Type@{o}, Powerset_squash P → P]: each gives the other
   ([unsquash_Untruncate], [Untruncate_unsquash]), and
   [components_on_all_Sets_Untruncate] states the conclusion as
   [inhabited Untruncate@{o}]; [unsquash_choice] derives from the
   principle functional choice for relations between types at [o].
   The converse holds.  Under [Untruncate] a continuous map into a
   discrete space on ANY setoid is constant on components
   ([comp_respect_U]: the proposition carried along a connected subset
   is [Powerset_squash] of [≈]), and [components_left_adjoint_discrete_Sets
   U : components_functor_Sets ⊣ LDisc] is Mac Lane's adjunction with
   his Set read literally as all of [Sets], [components_functor_Sets]
   being C followed by the inclusion of [PSets].  So the literal
   statement holds under [Untruncate], and any adjunction of its shape
   makes [Untruncate] merely true: the truncation of the hypothesis is
   necessary.  [Untruncate] has no axiom-free inhabitant in the tree and
   follows from informative excluded middle (OneLevel.v's header and
   [untruncate_of_IEM]).  So Set is read unconditionally as [PSets], the
   full subcategory of [Sets] on the setoids whose equality is logically
   a proposition (Instance/Sets/Propositional.v's [PropEquivObj]), the
   reading the concrete algebraic categories take (the size note in
   Structure/Complete.v's header).  This is the one deviation from the
   book's statement beyond the [PTopCat] encoding (ENCODING above), and
   it is lifted at [Sets] under [Untruncate].
   CORRECTION (#1349): above, [SquashSetoid] is Instance/Sets/Propositional/
   Full.v's now, and [unsquash_Untruncate] and [Untruncate_unsquash]
   are derived from that file's [untr_of_choice] and [choice_of_untr],
   which #469 had stated in Instance/Pos/Monadicity.v.

   WHAT IS HERE.
     - Connectedness, Prop-valued.  [LocConstOn X W φ]: a Prop-valued [φ]
       is locally constant on [W]; [PConnectedSub X W]: every such [φ] is
       constant on [W]; [PConnected X]: the whole space is.  [PLocConn X]
       is nLab's and Wikipedia's definition: every open neighbourhood of a
       point contains a connected open one.  [comp_rel X x y]: x and y
       lie in a common connected subset, the relation whose classes are
       the connected components; it is an equivalence relation
       constructively ([point_connected]: a point is connected;
       [union_connected]: two connected subsets sharing a point have a
       connected union).  [CompSet X] is the set of components, the
       points under [comp_rel]; [comp_PropEquiv]: its equality is the
       proposition [comp_rel] itself.
     - The other forms.  [PConnectedSep]: two disjoint opens covering the
       space do not split it; [PConnectedBool]: every continuous map into
       [PBool] is constant.  [connected_no_separation] and
       [connected_bool_constant] derive both from [PConnectedSub] for a
       subset, [PConnected_Sep] and [PConnected_Bool] for the space.  The
       locally-constant form is the one the adjunction needs: its
       transpose takes φ z := [pequiv (g x) (g z)], a proposition, where
       a [bool]-valued indicator would need a decidable equality on the
       target.
     - [image_connected]: continuous images of connected subsets are
       connected; hence [comp_setoid_map] and [CompTop : PTopCat ⟶
       PSets], the components functor on ALL of [PTopCat], which needs no
       local connectedness.
     - The categories.  [PSets]: the [Sub] of [Sets] on [PropEquivObj]
       ([PSetsSub]).  [Lconn]: the [Sub] of [PTopCat] on [PLocConn]
       ([Lconn_Sub], Instance/Top/Separation.v's [PFullSub]).  Both are
       pinned by hand, as Instance/Top/Hausdorff.v pins [Haus].
       CORRECTION (#1349): #469 built the same category again, as
       Instance/Sets/Propositional/Full.v's [PropSets_sub] and
       [PropSets]; on the maintainer's decision to unify them,
       [PSetsSub] and [PSets] are now defined as those two, under
       #462's names, so the hand pin of [PSets] is that file's.
     - [components_functor : Lconn ⟶ PSets], Mac Lane's C, the issue's
       pinned name: [CompTop] after the inclusion.
     - D.  [LDisc : Sets ⟶ Lconn] is Instance/Top/Complete.v's [PDisc]
       corestricted to [Lconn], not a second discrete functor: its object
       and arrow parts ARE [PDisc]'s ([LDisc_PDisc_obj],
       [LDisc_PDisc_fmap]) and its three functor laws are [PDisc]'s,
       with [pdisc_locconn], a discrete space is locally connected.
       [PSetsDisc : PSets ⟶ Lconn], Mac Lane's D, is [LDisc] after the
       inclusion of [PSets].
     - [components_left_adjoint_discrete : components_functor ⊣
       PSetsDisc], the pinned name, by Theory/Adjunction.v's
       [Build_Adjunction'] from [comp_adj_iso], a hom-set bijection that
       is the identity on points both ways.  [comp_respect]: a continuous
       map into a discrete space on a propositional set is constant on
       components.  [comp_cont]: in a locally connected space a map
       constant on components is continuous into a discrete space, the
       preimage of an open being the union of the connected open sets
       that meet it.  Local connectedness is used once, at
       the whole space, for a connected open neighbourhood of each point
       (read off [comp_cont]'s proof), so the adjunction would hold on
       the larger class of spaces whose every point has a connected open
       neighbourhood; the book's class is kept.
     - Mac Lane's Set as all of [Sets], under [Untruncate] (MAC LANE'S
       SET above).  [components_functor_Sets : Lconn ⟶ Sets] is C
       followed by the inclusion of [PSets]; [comp_adj_iso_U] has
       [comp_adj_iso]'s two maps, with [comp_respect_U] for the
       respectfulness of the backward one; and
       [components_left_adjoint_discrete_Sets U :
       components_functor_Sets ⊣ LDisc].  The other direction is
       [components_on_all_Sets_unsquashes] with
       [components_on_all_Sets_Untruncate], [unsquash_Untruncate],
       [Untruncate_unsquash] and [unsquash_choice].
     - Exercise 1's second half, on a concrete equalizer.  [PZig], the
       points [zig_a], [zig_c], [zig_b] with [zig_a] and [zig_b] open and
       the whole space the only open set containing [zig_c], is connected
       ([PZig_connected], so [PZig_one_component]) and locally connected
       ([PZig_PLocConn]).  The pair [zig_f_map] (constant at [false]) and
       [zig_g_map] ([true] exactly at [zig_c]) into Instance/Top/
       Cocomplete.v's indiscrete two-point space [PTwoIndisc] has as its
       equalizer the discrete two-point space [PBool] on the two open
       points ([PTop_zig_equalizer] in [PTopCat], [Lconn_zig_equalizer]
       in [Lconn] by fullness).  [components_zig_not_preserved]: the
       image under C is not an equalizer, since C of the equalizing map
       identifies the two components of [PBool]
       ([pbool_two_components]) while an equalizing map is monic
       (Structure/Equalizer/Fork.v's [equalizer_monic]).
       [components_no_left_adjoint], the pinned name: every L with
       [L ⊣ components_functor] is refuted, by Adjunction/Continuity/
       Equalizer.v's [not_PreservesEqualizers_no_left_adjoint] on that
       equalizer.
     - For ANY left adjoint of D.  [discrete_left_adjoint_not_preserved]:
       every C with [C ⊣ PSetsDisc], whatever its definition, sends the
       same equalizer to a fork that is not one.  The unit at [PZig] is
       continuous into a discrete space, so it identifies the images of
       [zig_a], [zig_c] and [zig_b], and by naturality the images of the
       two points of [PBool], which the transpose of the identity of
       [PBool] separates.  [discrete_left_adjoint_no_left_adjoint]: no
       such C has a left adjoint.
     - A second witness.  [Lconn_swap_equalizer]: the identity and the
       swap [swap_L] of [PTwoIndisc] have the empty discrete space
       [LEmpty] (on Theory/Concrete.v's [empty_setoid_object]) as their
       equalizer in [Lconn].  [components_swap_not_preserved]: C sends it
       to a fork whose vertex is empty, while the one component of the
       two-point space forks the image pair.
     - What the restriction to [Lconn] buys.  [pconv_not_locconn]:
       Instance/Top/Complete.v's convergent sequence [PConv] is not
       locally connected, an isolated point [Some K] being relatively
       clopen in any open neighbourhood of the limit point.
       [discrete_no_left_adjoint_on_PTop]: D into all of [PTopCat]
       ([PSetsDiscTop], [PDisc] after the inclusion of [PSets]) has no
       left adjoint.  The unit at [PConv] is continuous into a discrete
       space, hence constant on a tail, and Complete.v's indicator
       [pconv_ind_mor N] of a point of that tail would factor through
       it.  [PDisc_no_left_adjoint]: the same for [PDisc : Sets ⟶
       PTopCat] itself, the open set being a truncation [inhabited]
       eliminated into the goal [False].  The book states only the
       [Lconn] half.

   STRENGTHS, measured strict first.
     - At [eq_refl]: [components_obj] (C X is [CompSet] of X's space),
       [components_equiv] (its equality IS [comp_rel]),
       [components_fmap] (C f is f on points), [LDisc_PDisc_obj],
       [LDisc_PDisc_fmap], [PSetsDisc_obj] (D S is the discrete space on
       S), [adj_to_points] and [adj_from_points] (both transposes are the
       identity on points), [components_unit_points] (the unit sends
       a point to itself, as a point of its component set), and
       [adj_Sets_to_points] and [adj_Sets_from_points] (the same two
       transposes for the reading into all of [Sets]).
     - Up to [≈]: the functor laws and the equalizers' universal
       properties.  The refutations are [… → False] statements and use
       no classical principle.
     - Eleven proofs end [Defined] (counted by token).  Ten are
       load-bearing, measured by closing each alone [Qed] in a scratch
       copy of this file and reading the first refusal:
       [comp_setoid_map] ([CompTop]'s obligations),
       [components_left_adjoint_discrete] ([adj_to_points]),
       [components_left_adjoint_discrete_Sets] ([adj_Sets_to_points]),
       [SquashSetoid] ([squash_id]), [squash_id] ([squash_id_cont]),
       [PZig] ([PZig_connected]), [zig_f_set], [zig_g_set] and
       [zig_e_set] ([PTop_zig_equalizer]), and [swap_set]
       ([Lconn_swap_equalizer]).  [empty_set_map] is [Defined] by the
       data convention only: closed [Qed], nothing in the file is
       refused.  56 [Qed], counted by token.  CORRECTION (#1349): ten
       [Defined] and 52 [Qed] now, by token.  [SquashSetoid] moved to
       Instance/Sets/Propositional/Full.v, where it is still [Defined]
       and still load-bearing for [squash_id] (that file's STRENGTHS),
       and [squash_sym] and [squash_trans] moved with it; and
       [unsquash_Untruncate] and [Untruncate_unsquash] are definitions
       by term.  The ten that remain, the nine others named above and
       [empty_set_map], are as measured above.
     - Every constant of the file is closed under the global context
       ([Print Assumptions] on each, obligations, the inductive, its
       constructors and its schemes included).

   UNIVERSES, read by [About] under [Set Printing Universes] on all
   125 constants of this file's [Print Module] listing (the fourteen
   [Program] obligations of [CompTop], [LDisc], [comp_adj_iso] and
   [comp_adj_iso_U], and the inductive [zig_pt] with its four schemes,
   among them; no record is declared).  CORRECTION (#1349): 121 now,
   the squash setoid's four having moved to Instance/Sets/Propositional/
   Full.v.  [About] in the trees before and after #1349 reads the same
   block for each of the 121 and for the four moved.
     - No universe is pinned at [Set] and no block carries [Set < o]: the
       points may be in [Set].  At [o := Set],
       [components_left_adjoint_discrete],
       [components_left_adjoint_discrete_Sets],
       [components_no_left_adjoint],
       [discrete_left_adjoint_no_left_adjoint],
       [components_on_all_Sets_unsquashes],
       [components_on_all_Sets_Untruncate],
       [discrete_no_left_adjoint_on_PTop], [PDisc_no_left_adjoint],
       [components_zig_not_preserved] and [components_swap_not_preserved]
       are accepted under [Set < so] and, where a hypothesis's
       adjunction brings its own object universe, [Set] below that one:
       Test/ProbeComponents462.v's ten controls named [p462_..._at_Set].
     - [Set < so] is carried by 61 blocks, the bound [PTopCat]
       records for [PTop]'s sort and [PSetsSub] for [PropEquivObj]'s
       (Instance/Sets/Propositional.v's [PropEquivObj@{u u0 u1}] has
       [Set < u]); [o < so] implies it.
     - [PSets@{o so} : Category@{so o o}] is [Sub@{so o so o so o so}]
       and [Lconn@{o so} : Category@{so o o}] is [Sub@{so o o o so o
       so}].  [PSetsSub]'s object predicate sits at [so], not [o]:
       placed at [o] it is accepted only with [Set < o] in its block
       (read by [About] in a scratch file requiring this one), and at
       [o := Set] it is refused ("Universe inconsistency. Cannot enforce
       Set < Set because Set = Set"), the sort of [PropEquivObj S] being
       at least [Set+1]: Test/ProbeComponents462.v's N8, beside the
       controls [p462_psets_sub_at_o] and [p462_psets_sub_Set].
       [components_functor], [components_functor_Sets], [PSetsDisc] and
       [PSetsDiscTop] pin Theory/Functor.v's [Compose@{u u0 u1 u2 u3}],
       whose own block is [u3 < u2], at [@{so so so so o}]: its
       auxiliary [u2] is [so].
     - [components_left_adjoint_discrete@{o so}] and
       [components_left_adjoint_discrete_Sets@{o so}]: the [Adjunction]
       record at [@{so o o so o o o o so o so}].  Their hom-isomorphisms
       live in [Sets@{o so}] ([comp_adj_iso], [comp_adj_iso_U]); the
       record's last slot, unconstrained in [Adjunction]'s own block
       (Instance/Top/Complete.v's [PDisc_PForget@{o so u u0}] leaves it
       free as [u0]), is pinned at [so].
     - The theorems that take an [Adjunction] as a hypothesis are bound
       [@{o so +| o < so +}], so they refute adjunctions at every
       universe instance: [components_on_all_Sets_unsquashes],
       [components_on_all_Sets_Untruncate],
       [components_no_left_adjoint], [discrete_left_adjoint_not_preserved],
       [discrete_no_left_adjoint_on_PTop] and [PDisc_no_left_adjoint]
       read back [@{o so u u0}] with [o < u], [u] the object universe of
       the hypothesis's hom-isomorphisms.
       [discrete_left_adjoint_no_left_adjoint@{o so ua ub u u0}] takes
       two adjunctions and names their object universes [ua] and [ub] in
       its binder, each above [o]; measured under the bare binder
       [@{o so +| o < so +}], minimization identified the two, reading
       back [@{o so u u0 u1}] with the one [u] in both hypotheses.
     - Strict stdlib caps.  [o < Projections.u0] is carried by
       nine blocks, first in dependency order by
       [comp_adj_iso_obligation_3], which projects [Lconn]'s objects,
       whose first component is a [PTop@{o}] at [o+1]; every one of them
       also carries [so <= Projections.u0] with [o < so], which imply it.
       [o < False_rect.u0] is carried by five blocks, [LEmpty],
       [Lconn_swap_equalizer], [components_swap_not_preserved],
       [empty_set_map] and [swap_e], from Instance/Sets.v's
       [False_Setoid@{u}], whose own block is [u < False_rect.u0],
       through Theory/Concrete.v's [empty_setoid_object@{t u}] (block
       [t < False_rect.u0], [t = u]).
     - Empty blocks: the connectedness predicates and lemmas
       ([LocConstOn], [PConnectedSub], [PConnected], [PLocConn],
       [comp_rel] and its three laws, [point_connected],
       [union_connected], [locconst_restrict], [connected_no_separation],
       [PConnectedSep], [PConnected_Sep]), [CompSetoid], [CompSet],
       [comp_PropEquiv], [comp_respect], [comp_cont], [pdisc_locconn],
       the squash setoid ([squash_rel], [squash_sym], [squash_trans],
       [SquashSetoid]), [unsquash_Untruncate], [Untruncate_unsquash] and
       [comp_respect_U].  CORRECTION (#1349): the squash setoid's four
       are Full.v's now, with these empty blocks, and the two
       [Untruncate] constants, now derived, keep theirs empty.  The rest
       of the [@{o}] constants, but [empty_set_map] above, carry stdlib
       caps only ([o <= Logic_lemmas.equality.u0], [eq_Setoid]'s and
       [bool_setoid_object]'s; the [eq_ind], [eq_ind_r] or [eq_rect_r]
       caps of some proofs; [unsquash_choice]'s
       [o <= Subset_projections.u0]).  [zig_pt], its constructors,
       [zig_pt_ind], [zig_pt_sind], [zig_g_fun], [zig_e_fun],
       [zig_lift_fun] and [negb_no_fixpoint] are [@{}]; [zig_pt_rect]
       and [zig_pt_rec] are [@{u}], the motive.

   ROUTE AND COST.  [Print Libraries] on a file requiring this one lists
   117 [Category.*] modules besides it; sixteen of them come with
   Instance/Sets/Powerset.v and Instance/Sets/Classifier/OneLevel.v,
   required for [Powerset_squash] and [Untruncate] (the same count
   without those two Requires is 101).  CORRECTION (#1349): 118 besides
   it now, the one more Instance/Sets/Propositional/Full.v, required for
   [PSets] and the squash setoid; sixteen still come with those two
   files (102 without them, measured the same way).  Theory/Concrete.v
   is required but not imported: it declares its own
   [bool_setoid_object], which would shadow Instance/Sets.v's, the one
   [PBool] and [PTwoIndisc] are built on.  Coq.Arith.PeanoNat serves the
   arguments at [PConv].

   NOT DELIVERED.
     - The converses of the connectedness bridges: [PConnectedSep] or
       [PConnectedBool] implying [PConnected] needs a decision of [φ] at
       each point (excluded middle, an informative one for the [bool]
       form); not attempted.  Classically the three forms agree.
     - The empty space: nLab's connected-space page does not regard it as
       connected, and [PConnectedSub] holds of the empty predicate,
       vacuously.  Immaterial to [comp_rel], whose subsets contain the
       points they relate.
     - An unconditional adjunction into all of [Sets]: any such
       adjunction makes [Untruncate] merely true
       ([components_on_all_Sets_Untruncate]), and [Untruncate] has no
       axiom-free inhabitant in the tree; the adjunction is delivered
       under it ([components_left_adjoint_discrete_Sets]).
     - Riehl's path-components functor is the satellite
       Instance/Top/Components/Paths.v's; no comparison of path
       components with connected components is delivered in either file.
       Such a comparison would also cross a difference of codomains: the
       satellite's [PPi0] lands in [Sets], its equality [colim_rel] being
       Type-valued, where C lands in [PSets] (and its reading into all
       of [Sets], [components_functor_Sets], is a left adjoint only under
       [Untruncate]).
     - Anything over the Type-valued [Top] beyond the refusals under
       ENCODING; no comparison of [PTopCat] with [Top].
     - The rest of nLab's quadruple (the points and the codiscrete space
       on [Lconn]) and C's preservation of finite products; the component
       of a point as a subspace, and a locally connected space as the sum
       of its components. *)

#[local] Obligation Tactic := idtac.

(** ** Connectedness, in the Prop-valued locally-constant form *)

(* A Prop-valued function [φ] is locally constant on the subset [W]: every
   point of [W] has an open neighbourhood on whose trace in [W] the value of
   [φ] does not change. *)
Definition LocConstOn@{o} (X : PTop@{o}) (W φ : X → Prop) : Prop :=
  ∀ z, W z → ex (fun O => POpen X O /\ O z /\
                           ∀ w, W w → O w → (φ w <-> φ z)).

(* [W] is connected: every Prop-valued function locally constant on [W] is
   constant on [W]. *)
Definition PConnectedSub@{o} (X : PTop@{o}) (W : X → Prop) : Prop :=
  ∀ φ, LocConstOn X W φ → ∀ a b, W a → W b → φ a → φ b.

(* The space is connected: the whole space is a connected subset. *)
Definition PConnected@{o} (X : PTop@{o}) : Prop :=
  PConnectedSub X (fun _ => True).

(* Local connectedness: every open neighbourhood of a point contains a
   connected open neighbourhood of it. *)
Definition PLocConn@{o} (X : PTop@{o}) : Prop :=
  ∀ x U, POpen X U → U x →
    ex (fun N => POpen X N /\ N x /\ (∀ y, N y → U y) /\ PConnectedSub X N).

(* Two points lie in a common connected subset: the relation whose classes
   are the connected components. *)
Definition comp_rel@{o} (X : PTop@{o}) (x y : X) : Prop :=
  ex (fun W => PConnectedSub X W /\ W x /\ W y).

Lemma locconst_restrict@{o} (X : PTop@{o}) (W W' φ : X → Prop) :
  (∀ z, W z → W' z) → LocConstOn X W' φ → LocConstOn X W φ.
Proof.
  intros HW H z wz.
  destruct (H z (HW z wz)) as [O [HO [Oz HOw]]].
  exists O; split; [exact HO|split; [exact Oz|]].
  intros w ww Ow; exact (HOw w (HW w ww) Ow).
Qed.

(* A point, as the subset of the points equal to it, is connected. *)
Lemma point_connected@{o} (X : PTop@{o}) (x : X) :
  PConnectedSub X (fun z => inhabited (x ≈ z)).
Proof.
  intros φ H a b [Ha] [Hb] pa.
  destruct (H a (inhabits Ha)) as [O [HO [Oa HOw]]].
  assert (Ob : O b).
  { apply (popen_proper X O HO a b); [|exact Oa].
    exact (transitivity (symmetry Ha) Hb). }
  exact (proj2 (HOw b (inhabits Hb) Ob) pa).
Qed.

Lemma comp_rel_of_equiv@{o} (X : PTop@{o}) (x y : X) :
  x ≈ y → comp_rel X x y.
Proof.
  intro H. exists (fun z => inhabited (x ≈ z)).
  split; [apply point_connected|].
  split; [exact (inhabits (reflexivity x))|exact (inhabits H)].
Qed.

Lemma comp_rel_sym@{o} (X : PTop@{o}) (x y : X) :
  comp_rel X x y → comp_rel X y x.
Proof. intros [W [HW [wx wy]]]; exists W; exact (conj HW (conj wy wx)). Qed.

(* Two connected subsets sharing a point have a connected union. *)
Lemma union_connected@{o} (X : PTop@{o}) (W1 W2 : X → Prop) (c : X) :
  PConnectedSub X W1 → PConnectedSub X W2 → W1 c → W2 c →
  PConnectedSub X (fun z => W1 z \/ W2 z).
Proof.
  intros H1 H2 c1 c2 φ H a b wa wb pa.
  pose proof (locconst_restrict X W1 _ φ (fun z w => or_introl w) H) as L1.
  pose proof (locconst_restrict X W2 _ φ (fun z w => or_intror w) H) as L2.
  destruct wa as [a1|a2]; destruct wb as [b1|b2].
  - exact (H1 φ L1 a b a1 b1 pa).
  - exact (H2 φ L2 c b c2 b2 (H1 φ L1 a c a1 c1 pa)).
  - exact (H1 φ L1 c b c1 b1 (H2 φ L2 a c a2 c2 pa)).
  - exact (H2 φ L2 a b a2 b2 pa).
Qed.

Lemma comp_rel_trans@{o} (X : PTop@{o}) (x y z : X) :
  comp_rel X x y → comp_rel X y z → comp_rel X x z.
Proof.
  intros [W1 [H1 [w1x w1y]]] [W2 [H2 [w2y w2z]]].
  exists (fun v => W1 v \/ W2 v).
  split; [exact (union_connected X W1 W2 y H1 H2 w1y w2y)|].
  exact (conj (or_introl w1x) (or_intror w2z)).
Qed.

(* The points under the component relation. *)
Definition CompSetoid@{o} (X : PTop@{o}) : Setoid@{o o} X := {|
  equiv := comp_rel X;
  setoid_equiv := {|
    Equivalence_Reflexive := fun x => comp_rel_of_equiv X x x (reflexivity x);
    Equivalence_Symmetric := comp_rel_sym X;
    Equivalence_Transitive := comp_rel_trans X |}
|}.

(* The set of connected components, at the points' universe. *)
Definition CompSet@{o} (X : PTop@{o}) : SetoidObject@{o o} :=
  {| carrier := pt_carrier X; is_setoid := CompSetoid X |}.

(* Its equality is a proposition, [comp_rel] itself. *)
Definition comp_PropEquiv@{o} (X : PTop@{o}) :
  PropEquiv@{o o} (is_setoid (CompSet X)) :=
  @PropEquiv_of_relation@{o o} _ (CompSetoid X) (comp_rel X)
    (fun _ _ h => h) (fun _ _ h => h).

(** ** The no-separation and two-point forms *)

(* No separation of the space by two disjoint open sets covering it. *)
Definition PConnectedSep@{o} (X : PTop@{o}) : Prop :=
  ∀ U V, POpen X U → POpen X V → (∀ z, U z \/ V z) →
    (∀ z, U z → V z → False) → ∀ a b, U a → U b.

(* Every continuous map into the discrete two-point space is constant. *)
Definition PConnectedBool@{o} (X : PTop@{o}) : Prop :=
  ∀ g : PMor@{o} X PBool@{o}, ∀ a b, pmap g a = pmap g b.

(* A connected subset lies in one side of every pair of disjoint opens
   covering it. *)
Lemma connected_no_separation@{o} (X : PTop@{o}) (W : X → Prop)
  (HW : PConnectedSub X W) (U V : X → Prop) :
  POpen X U → POpen X V → (∀ z, W z → U z \/ V z) →
  (∀ z, W z → U z → V z → False) →
  ∀ a b, W a → W b → U a → U b.
Proof.
  intros HU HV Hcov Hdis a b wa wb ua.
  refine (HW U _ a b wa wb ua).
  intros z wz. destruct (Hcov z wz) as [uz|vz].
  - exists U. split; [exact HU|split; [exact uz|]].
    intros w _ uw; split; intros _; assumption.
  - exists V. split; [exact HV|split; [exact vz|]].
    intros w ww vw; split; intro h.
    + destruct (Hdis w ww h vw).
    + destruct (Hdis z wz h vz).
Qed.

(* A continuous map into the discrete two-point space is constant on a
   connected subset. *)
Lemma connected_bool_constant@{o} (X : PTop@{o}) (W : X → Prop)
  (HW : PConnectedSub X W) (g : PMor@{o} X PBool@{o}) :
  ∀ a b, W a → W b → pmap g a = pmap g b.
Proof.
  intros a b wa wb.
  refine (HW (fun z => pmap g a = pmap g z) _ a b wa wb eq_refl).
  intros z _. exists (fun w => pmap g z = pmap g w).
  split; [|split; [reflexivity|]].
  - apply (pcont g (fun s => pmap g z = s)).
    intros s t e h; simpl in e; exact (eq_trans h e).
  - intros w _ e; split; intro h; congruence.
Qed.

Corollary PConnected_Sep@{o} (X : PTop@{o}) :
  PConnected X → PConnectedSep X.
Proof.
  intros H U V HU HV Hcov Hdis a b.
  exact (connected_no_separation X _ H U V HU HV (fun z _ => Hcov z)
           (fun z _ => Hdis z) a b I I).
Qed.

Corollary PConnected_Bool@{o} (X : PTop@{o}) :
  PConnected X → PConnectedBool X.
Proof. intros H g a b. exact (connected_bool_constant X _ H g a b I I). Qed.

(** ** Continuous images of connected sets are connected *)

Lemma image_connected@{o} {X Y : PTop@{o}} (f : PMor@{o} X Y)
  (W : X → Prop) :
  PConnectedSub X W →
  PConnectedSub Y (fun y => ex (fun x => W x /\ pmap f x = y)).
Proof.
  intros HW φ H a b [xa [wa ea]] [xb [wb eb]] pa.
  subst a b.
  refine (HW (fun x => φ (pmap f x)) _ xa xb wa wb pa).
  intros z wz.
  destruct (H (pmap f z) (ex_intro _ z (conj wz eq_refl)))
    as [O [HO [Oz HOw]]].
  exists (fun x => O (pmap f x)); split; [exact (pcont f O HO)|].
  split; [exact Oz|].
  intros w ww Ow.
  exact (HOw (pmap f w) (ex_intro _ w (conj ww eq_refl)) Ow).
Qed.

Lemma comp_rel_map@{o} {X Y : PTop@{o}} (f : PMor@{o} X Y) (x x' : X) :
  comp_rel X x x' → comp_rel Y (pmap f x) (pmap f x').
Proof.
  intros [W [HW [wx wx']]].
  exists (fun y => ex (fun x => W x /\ pmap f x = y)).
  split; [exact (image_connected f W HW)|].
  split; [exists x; exact (conj wx eq_refl)
         |exists x'; exact (conj wx' eq_refl)].
Qed.

(* A continuous map sends components into components. *)
Definition comp_setoid_map@{o} {X Y : PTop@{o}} (f : PMor@{o} X Y) :
  SetoidMorphism@{o o o} (CompSet X) (CompSet Y).
Proof.
  refine {| morphism := fun x => pmap f x |}.
  intros x x' H; exact (comp_rel_map f x x' H).
Defined.

(** ** The categories: propositional sets and locally connected spaces *)

(* Mac Lane's Set, read as the full subcategory of [Sets] on the setoids
   whose equality is a proposition.  Since #1349 it is
   Instance/Sets/Propositional/Full.v's [PropSets], under #462's names;
   [About] reads the same blocks for both names as before. *)
Definition PSetsSub@{o so | o < so +} : Subcategory@{so o so o} Sets@{o so} :=
  PropSets_sub@{o so}.

Definition PSets@{o so | o < so +} : Category@{so o o} :=
  PropSets@{o so}.

(* Mac Lane's Lconn: the full subcategory of [PTopCat] on the locally
   connected spaces. *)
Definition Lconn_Sub@{o so | o < so +} :
  Subcategory@{so o o o} PTopCat@{o so} :=
  PFullSub@{o so} PLocConn@{o}.

Definition Lconn@{o so | o < so +} : Category@{so o o} :=
  Sub@{so o o o so o so} PTopCat@{o so} Lconn_Sub@{o so}.

(** ** The components functor *)

(* On all of [PTopCat]: no local connectedness is needed for the functor. *)
Program Definition CompTop@{o so | o < so +} :
  PTopCat@{o so} ⟶ PSets@{o so} := {|
  fobj := fun X => (CompSet X; comp_PropEquiv X);
  fmap := fun X Y f => (comp_setoid_map f; I)
|}.
Next Obligation.
  intros X Y f g H x; simpl. apply comp_rel_of_equiv; exact (H x).
Qed.
Next Obligation. intros X x; simpl. apply comp_rel_of_equiv; reflexivity. Qed.
Next Obligation.
  intros X Y Z f g x; simpl. apply comp_rel_of_equiv; reflexivity.
Qed.

(* Mac Lane's C, on the locally connected spaces. *)
Definition components_functor@{o so | o < so +} :
  Lconn@{o so} ⟶ PSets@{o so} :=
  @Compose@{so so so so o} Lconn@{o so} PTopCat@{o so} PSets@{o so}
    CompTop@{o so} (Incl@{so o o o so so} PTopCat@{o so} Lconn_Sub@{o so}).

(** ** The discrete-space functor into [Lconn] *)

Lemma pdisc_locconn@{o} (S : SetoidObject@{o o}) : PLocConn (PDiscrete S).
Proof.
  intros x U HU ux.
  exists (fun y => inhabited (x ≈ y)).
  split; [|split; [exact (inhabits (reflexivity x))|split]].
  - intros a b e [h]. exact (inhabits (transitivity h e)).
  - intros y [h]. exact (HU x y h ux).
  - apply point_connected.
Qed.

(* Instance/Top/Complete.v's [PDisc], corestricted to [Lconn]: its object
   and arrow parts, and its three laws. *)
Program Definition LDisc@{o so | o < so +} : Sets@{o so} ⟶ Lconn@{o so} := {|
  fobj := fun S => (fobj[PDisc@{o so}] S; pdisc_locconn S);
  fmap := fun S T f => (fmap[PDisc@{o so}] f; I)
|}.
Next Obligation.
  intros S T f g H. exact (@fmap_respects _ _ PDisc@{o so} S T f g H).
Qed.
Next Obligation. intros S. exact (@fmap_id _ _ PDisc@{o so} S). Qed.
Next Obligation.
  intros S T U f g. exact (@fmap_comp _ _ PDisc@{o so} S T U f g).
Qed.

(* Mac Lane's D : Set → Lconn, at the propositional sets. *)
Definition PSetsDisc@{o so | o < so +} : PSets@{o so} ⟶ Lconn@{o so} :=
  @Compose@{so so so so o} PSets@{o so} Sets@{o so} Lconn@{o so}
    LDisc@{o so} (Incl@{so o so o so so} Sets@{o so} PSetsSub@{o so}).

(** ** Exercise 1, first half: C ⊣ D *)

(* Every continuous map into a discrete space on a propositional set is
   constant on each connected subset. *)
Lemma comp_respect@{o} (X : PTop@{o}) (S : SetoidObject@{o o})
  (P : PropEquiv@{o o} (is_setoid S)) (g : PMor@{o} X (PDiscrete S))
  (x y : X) :
  comp_rel X x y → pmap g x ≈ pmap g y.
Proof.
  intro H. apply (@pequiv_to _ _ P).
  destruct H as [W [HW [wx wy]]].
  refine (HW (fun z => @pequiv _ _ P (pmap g x) (pmap g z)) _ x y wx wy
            (pequiv_from _ _ (reflexivity _))).
  intros z wz.
  exists (fun w => @pequiv _ _ P (pmap g z) (pmap g w)).
  split; [|split].
  - apply (pcont g (fun s => @pequiv _ _ P (pmap g z) s)).
    intros s t e p. apply pequiv_from.
    exact (transitivity (pequiv_to _ _ p) e).
  - apply pequiv_from; reflexivity.
  - intros w ww p. split; intro q.
    + apply pequiv_from.
      exact (transitivity (pequiv_to _ _ q) (symmetry (pequiv_to _ _ p))).
    + apply pequiv_from.
      exact (transitivity (pequiv_to _ _ q) (pequiv_to _ _ p)).
Qed.

(* In a locally connected space every map constant on components is
   continuous into the discrete space: the components are open.  Local
   connectedness is used once, at the whole space. *)
Lemma comp_cont@{o} (X : PTop@{o}) (LC : PLocConn X) (S : SetoidObject@{o o})
  (h : SetoidMorphism@{o o o} (CompSet X) S) :
  @PCont X (PDiscrete S)
    {| morphism := fun x => h x;
       proper_morphism := fun x y e =>
         proper_morphism h x y (comp_rel_of_equiv X x y e) |}.
Proof.
  intros U HU.
  apply (popen_respects X
    (fun y => ex (fun N => (POpen X N /\ PConnectedSub X N /\
                            ex (fun x => N x /\ U (h x))) /\ N y))).
  - intro y; split.
    + intros [N [[_ [HN [x [nx ux]]]] ny]]; simpl.
      assert (Hc : comp_rel X x y) by (exists N; exact (conj HN (conj nx ny))).
      exact (HU (h x) (h y) (proper_morphism h x y Hc) ux).
    + simpl; intro uy.
      destruct (LC y (fun _ => True) (popen_whole X) I)
        as [N [HN [ny [_ Hc]]]].
      exists N. split; [|exact ny].
      split; [exact HN|split; [exact Hc|exists y; exact (conj ny uy)]].
  - apply popen_union. intros N [HN _]; exact HN.
Qed.

(* The hom-set bijection: both directions are the identity on points. *)
Program Definition comp_adj_iso@{o so | o < so +}
  (X : Lconn@{o so}) (S : PSets@{o so}) :
  @Isomorphism Sets@{o so}
    {| carrier := @hom PSets@{o so} (components_functor@{o so} X) S
     ; is_setoid := @homset PSets@{o so} (components_functor@{o so} X) S |}
    {| carrier := @hom Lconn@{o so} X (PSetsDisc@{o so} S)
     ; is_setoid := @homset Lconn@{o so} X (PSetsDisc@{o so} S) |} := {|
  to   := {| morphism := fun h =>
              (@Build_PMor (`1 X) (PDiscrete (`1 S)) _
                 (comp_cont (`1 X) (`2 X) (`1 S) (`1 h)); I) |};
  from := {| morphism := fun g =>
              ({| morphism := fun x => pmap (`1 g) x;
                  proper_morphism :=
                    comp_respect (`1 X) (`1 S) (`2 S) (`1 g) |}; I) |}
|}.
Next Obligation. intros X S h h' H x; exact (H x). Qed.
Next Obligation. intros X S g g' H x; exact (H x). Qed.
Next Obligation. intros X S g x; simpl; reflexivity. Qed.
Next Obligation. intros X S h x; simpl; reflexivity. Qed.

Definition components_left_adjoint_discrete@{o so | o < so +} :
  @Adjunction@{so o o so o o o o so o so} PSets@{o so} Lconn@{o so}
    components_functor@{o so} PSetsDisc@{o so}.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ components_functor PSetsDisc
                     comp_adj_iso).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

(** ** Readbacks *)

Example components_obj@{o so | o < so +} (X : Lconn@{o so}) :
  `1 (fobj[components_functor@{o so}] X) = CompSet (`1 X) := eq_refl.

Example components_equiv@{o so | o < so +} (X : Lconn@{o so})
  (x y : pt_carrier (`1 X)) :
  @equiv _ (is_setoid (`1 (fobj[components_functor@{o so}] X))) x y
    = comp_rel (`1 X) x y := eq_refl.

Example components_fmap@{o so | o < so +} {X Y : Lconn@{o so}}
  (f : X ~{Lconn@{o so}}~> Y) (x : pt_carrier (`1 X)) :
  `1 (fmap[components_functor@{o so}] f) x = pmap (`1 f) x := eq_refl.

Example LDisc_PDisc_obj@{o so | o < so +} (S : Sets@{o so}) :
  `1 (fobj[LDisc@{o so}] S) = fobj[PDisc@{o so}] S := eq_refl.

Example LDisc_PDisc_fmap@{o so | o < so +} {S T : Sets@{o so}}
  (f : S ~{Sets@{o so}}~> T) :
  `1 (fmap[LDisc@{o so}] f) = fmap[PDisc@{o so}] f := eq_refl.

Example PSetsDisc_obj@{o so | o < so +} (S : PSets@{o so}) :
  `1 (fobj[PSetsDisc@{o so}] S) = PDiscrete (`1 S) := eq_refl.

Example adj_to_points@{o so | o < so +} (X : Lconn@{o so}) (S : PSets@{o so})
  (h : components_functor@{o so} X ~{PSets@{o so}}~> S)
  (x : pt_carrier (`1 X)) :
  pmap (`1 (to (@adj _ _ _ _ components_left_adjoint_discrete@{o so} X S) h)) x
    = `1 h x := eq_refl.

Example adj_from_points@{o so | o < so +} (X : Lconn@{o so}) (S : PSets@{o so})
  (g : X ~{Lconn@{o so}}~> PSetsDisc@{o so} S) (x : pt_carrier (`1 X)) :
  `1 (from (@adj _ _ _ _ components_left_adjoint_discrete@{o so} X S) g) x
    = pmap (`1 g) x := eq_refl.

(* The unit sends each point to itself, its own component. *)
Example components_unit_points@{o so | o < so +} (X : Lconn@{o so})
  (x : pt_carrier (`1 X)) :
  pmap (`1 (@unit _ _ _ _ components_left_adjoint_discrete@{o so} X)) x = x
  := eq_refl.

(** ** Why Set is read as the propositional sets *)

(* The setoid on [bool] whose [true ≈ false] is a given type [Q] is
   Instance/Sets/Propositional/Full.v's [SquashSetoid], over its
   [squash_rel], [squash_sym] and [squash_trans]: #1349 moved the four
   there from this file, names, binders and proofs unchanged. *)

Definition squash_id@{o} (Q : Type@{o}) :
  SetoidMorphism@{o o o} PTwoIndisc@{o} (SquashSetoid Q).
Proof.
  refine {| morphism := fun b : bool => b |}.
  intros x y e; simpl in e; subst; left; reflexivity.
Defined.

(* Merely inhabited [Q] makes the identity continuous from the indiscrete
   two-point space into the discrete space on [SquashSetoid Q]. *)
Lemma squash_id_cont@{o} (Q : Type@{o}) (iq : inhabited Q) :
  @PCont PTwoIndisc@{o} (PDiscrete (SquashSetoid Q)) (squash_id Q).
Proof.
  intros U HU x y u. destruct iq as [q].
  apply (HU x y); [right; exact q|exact u].
Qed.

Lemma PTwoIndisc_connected@{o} : PConnected PTwoIndisc@{o}.
Proof.
  intros φ H a b _ _ pa.
  destruct (H a I) as [O [HO [Oa HOw]]].
  exact (proj2 (HOw b I (HO a b Oa)) pa).
Qed.

Lemma PTwoIndisc_PLocConn@{o} : PLocConn PTwoIndisc@{o}.
Proof.
  intros x U HU ux. exists (fun _ => True).
  split; [exact (popen_whole _)|split; [exact I|split]].
  - intros y _; exact (HU x y ux).
  - exact PTwoIndisc_connected.
Qed.

Definition LTwoIndisc@{o so | o < so +} : Lconn@{o so} :=
  (PTwoIndisc@{o}; PTwoIndisc_PLocConn@{o}).

(* A left adjoint of the discrete functor into ALL of [Sets] turns every
   merely inhabited type at the points' universe into an inhabitant. *)
Theorem components_on_all_Sets_unsquashes@{o so +| o < so +}
  (C' : Lconn@{o so} ⟶ Sets@{o so}) (A : C' ⊣ LDisc@{o so}) :
  inhabited (∀ Q : Type@{o}, inhabited Q → Q).
Proof.
  pose (eta := to (@adj _ _ _ _ A LTwoIndisc (C' LTwoIndisc)) id).
  (* the unit is continuous, so its two values are MERELY equal *)
  assert (He : inhabited (pmap (`1 eta) true ≈ pmap (`1 eta) false)).
  { pose proof (pcont (`1 eta)
                  (fun s => inhabited (pmap (`1 eta) true ≈ s))) as Hc.
    refine (Hc _ true false (inhabits (reflexivity _))).
    intros s t e [h]; exact (inhabits (transitivity h e)). }
  destruct He as [e]. constructor. intros Q iq.
  pose (g := ((@Build_PMor PTwoIndisc (PDiscrete (SquashSetoid Q)) (squash_id Q)
                (squash_id_cont Q iq)); I)
             : LTwoIndisc ~{Lconn@{o so}}~> LDisc (SquashSetoid Q)).
  pose (SQ := SquashSetoid Q).
  pose (gh := from (@adj _ _ _ _ A LTwoIndisc SQ) g).
  assert (Hg : ∀ b, squash_rel Q b (gh (pmap (`1 eta) b))).
  { intro b.
    pose proof (iso_to_from (@adj _ _ _ _ A LTwoIndisc SQ) g b) as E1.
    pose proof (@to_adj_nat_r _ _ _ _ A LTwoIndisc (C' LTwoIndisc) SQ
                  gh id b) as E2.
    pose proof (proper_morphism (to (@adj _ _ _ _ A LTwoIndisc SQ)) _ _
                  (id_right gh) b) as E3.
    simpl in E1, E2, E3.
    exact (squash_trans _ _ _ _ (squash_sym _ _ _ E1)
             (squash_trans _ _ _ _ (squash_sym _ _ _ E3) E2)). }
  pose proof (squash_trans _ _ _ _ (Hg true)
               (squash_trans _ _ _ _ (proper_morphism gh _ _ e)
                  (squash_sym _ _ _ (Hg false)))) as H.
  destruct H as [H|q]; [discriminate H|exact q].
Qed.

(* That principle gives functional choice for relations between types at
   the points' universe. *)
Lemma unsquash_choice@{o} (U : inhabited (∀ Q : Type@{o}, inhabited Q → Q))
  (A B : Type@{o}) (R : A → B → Prop) :
  (∀ a, ex (fun b => R a b)) → ex (fun f : A → B => ∀ a, R a (f a)).
Proof.
  intro H. destruct U as [u].
  exists (fun a => proj1_sig (u {b : B | R a b}
                                (let (b, r) := H a in inhabits (exist _ b r)))).
  intro a. exact (proj2_sig _).
Qed.

(** ** Mac Lane's Set as all of [Sets], under [Untruncate] *)

(* The unsquashing principle is Instance/Sets/Classifier/OneLevel.v's
   [Untruncate], truncated: each gives the other.  Since #1349 both are
   transparent definitions, derived from Instance/Sets/Propositional/
   Full.v's [untr_of_choice] (under [inhabited]) and [choice_of_untr],
   which write [Untruncate@{o}] out; the two forms convert. *)
Definition unsquash_Untruncate@{o} :
  inhabited (∀ Q : Type@{o}, inhabited Q → Q) → inhabited Untruncate@{o} :=
  fun H => match H with inhabits u => inhabits (untr_of_choice@{o} u) end.

Definition Untruncate_unsquash@{o} (U : Untruncate@{o}) (Q : Type@{o}) :
  inhabited Q → Q :=
  choice_of_untr@{o} U Q.

(* So a left adjoint of the discrete functor into all of [Sets] makes
   [Untruncate] merely true. *)
Corollary components_on_all_Sets_Untruncate@{o so +| o < so +}
  (C' : Lconn@{o so} ⟶ Sets@{o so}) (A : C' ⊣ LDisc@{o so}) :
  inhabited Untruncate@{o}.
Proof.
  exact (unsquash_Untruncate (components_on_all_Sets_unsquashes C' A)).
Qed.

(* Under [Untruncate], a continuous map into a discrete space on ANY
   setoid is constant on components: the proposition carried along the
   connected subset is the truncation [Powerset_squash] of [≈]. *)
Lemma comp_respect_U@{o} (U : Untruncate@{o}) (X : PTop@{o})
  (S : SetoidObject@{o o}) (g : PMor@{o} X (PDiscrete S)) (x y : X) :
  comp_rel X x y → pmap g x ≈ pmap g y.
Proof.
  intro H. apply U.
  destruct H as [W [HW [wx wy]]].
  refine (HW (fun z => Powerset_squash (pmap g x ≈ pmap g z)) _ x y wx wy
            (Powerset_squash_intro (reflexivity _))).
  intros z wz.
  exists (fun w => Powerset_squash (pmap g z ≈ pmap g w)).
  split; [|split].
  - apply (pcont g (fun s => Powerset_squash (pmap g z ≈ s))).
    intros s t e p Q k. apply p. intro h. exact (k (transitivity h e)).
  - exact (Powerset_squash_intro (reflexivity _)).
  - intros w ww p. split; intros q Q k.
    + apply q. intro h. apply p. intro h'.
      exact (k (transitivity h (symmetry h'))).
    + apply q. intro h. apply p. intro h'. exact (k (transitivity h h')).
Qed.

(* Mac Lane's C into all of [Sets]: [components_functor] followed by the
   inclusion of [PSets]. *)
Definition components_functor_Sets@{o so | o < so +} :
  Lconn@{o so} ⟶ Sets@{o so} :=
  @Compose@{so so so so o} Lconn@{o so} PSets@{o so} Sets@{o so}
    (Incl@{so o so o so so} Sets@{o so} PSetsSub@{o so})
    components_functor@{o so}.

(* The hom-set bijection into all of [Sets]: [comp_adj_iso]'s maps, with
   [comp_respect_U] for the backward map's respectfulness. *)
Program Definition comp_adj_iso_U@{o so | o < so +} (U : Untruncate@{o})
  (X : Lconn@{o so}) (S : Sets@{o so}) :
  @Isomorphism Sets@{o so}
    {| carrier := @hom Sets@{o so} (components_functor_Sets@{o so} X) S
     ; is_setoid := @homset Sets@{o so} (components_functor_Sets@{o so} X) S |}
    {| carrier := @hom Lconn@{o so} X (LDisc@{o so} S)
     ; is_setoid := @homset Lconn@{o so} X (LDisc@{o so} S) |} := {|
  to   := {| morphism := fun h =>
              (@Build_PMor (`1 X) (PDiscrete S) _
                 (comp_cont (`1 X) (`2 X) S h); I) |};
  from := {| morphism := fun g =>
              {| morphism := fun x => pmap (`1 g) x;
                 proper_morphism := comp_respect_U U (`1 X) S (`1 g) |} |}
|}.
Next Obligation. intros U X S h h' H x; exact (H x). Qed.
Next Obligation. intros U X S g g' H x; exact (H x). Qed.
Next Obligation. intros U X S g x; simpl; reflexivity. Qed.
Next Obligation. intros U X S h x; simpl; reflexivity. Qed.

(* Mac Lane's C ⊣ D with his Set read literally, as all of [Sets], under
   [Untruncate]. *)
Definition components_left_adjoint_discrete_Sets@{o so | o < so +}
  (U : Untruncate@{o}) :
  @Adjunction@{so o o so o o o o so o so} Sets@{o so} Lconn@{o so}
    components_functor_Sets@{o so} LDisc@{o so}.
Proof.
  unshelve eapply (@Build_Adjunction' _ _ components_functor_Sets LDisc
                     (comp_adj_iso_U U)).
  - intros x y z f g t; simpl. reflexivity.
  - intros x y z f g t; simpl. reflexivity.
Defined.

Example adj_Sets_to_points@{o so | o < so +} (U : Untruncate@{o})
  (X : Lconn@{o so}) (S : Sets@{o so})
  (h : components_functor_Sets@{o so} X ~{Sets@{o so}}~> S)
  (x : pt_carrier (`1 X)) :
  pmap (`1 (to (@adj _ _ _ _
                 (components_left_adjoint_discrete_Sets@{o so} U) X S) h)) x
    = h x := eq_refl.

Example adj_Sets_from_points@{o so | o < so +} (U : Untruncate@{o})
  (X : Lconn@{o so}) (S : Sets@{o so})
  (g : X ~{Lconn@{o so}}~> LDisc@{o so} S) (x : pt_carrier (`1 X)) :
  from (@adj _ _ _ _ (components_left_adjoint_discrete_Sets@{o so} U) X S)
    g x = pmap (`1 g) x := eq_refl.

(** ** Exercise 1, second half: a concrete equalizer C does not preserve *)

(* The three-point space: [zig_a] and [zig_b] are open points, and the only
   open set containing [zig_c] is the whole space. *)
Inductive zig_pt@{} : Set := zig_a | zig_c | zig_b.

Definition zig_setoid@{o} : SetoidObject@{o o} :=
  {| carrier := zig_pt; is_setoid := eq_Setoid zig_pt |}.

Definition zig_open@{o} (U : zig_setoid@{o} → Prop) : Prop :=
  U zig_c → U zig_a /\ U zig_b.

Definition PZig@{o} : PTop@{o}.
Proof.
  refine {| pt_carrier := zig_setoid@{o}; POpen := zig_open@{o} |}.
  - intros U V H HU v. pose proof (HU (proj2 (H zig_c) v)) as [a b].
    exact (conj (proj1 (H zig_a) a) (proj1 (H zig_b) b)).
  - intros U _ x y Hxy u. simpl in Hxy. subst. exact u.
  - intros F HF [U [FU u]]. destruct (HF U FU u) as [a b].
    split; exists U; split; assumption.
  - intros _. split; exact I.
  - intros U V HU HV [u v].
    destruct (HU u), (HV v). split; split; assumption.
Defined.

Lemma PZig_connected@{o} : PConnected PZig@{o}.
Proof.
  intros φ H a b _ _ pa.
  destruct (H zig_c I) as [O [HO [Oc HOw]]].
  destruct (HO Oc) as [Oa Ob].
  assert (Hall : ∀ z : zig_pt, O z) by (intros []; assumption).
  exact (proj2 (HOw b I (Hall b)) (proj1 (HOw a I (Hall a)) pa)).
Qed.

(* It has one component. *)
Corollary PZig_one_component@{o} (x y : zig_pt) : comp_rel PZig@{o} x y.
Proof. exists (fun _ => True). exact (conj PZig_connected (conj I I)). Qed.

Lemma PZig_PLocConn@{o} : PLocConn PZig@{o}.
Proof.
  intros x U HU u.
  destruct x.
  - exists (fun y => inhabited (@equiv _ PZig@{o} zig_a y)).
    split; [|split; [exact (inhabits eq_refl)|split]].
    + intros [h]; discriminate h.
    + intros y [h]; simpl in h; subst; exact u.
    + apply point_connected.
  - exists (fun _ => True).
    split; [intros _; split; exact I|split; [exact I|split]].
    + destruct (HU u) as [a b]. intros [] _; assumption.
    + exact PZig_connected.
  - exists (fun y => inhabited (@equiv _ PZig@{o} zig_b y)).
    split; [|split; [exact (inhabits eq_refl)|split]].
    + intros [h]; discriminate h.
    + intros y [h]; simpl in h; subst; exact u.
    + apply point_connected.
Qed.

(* The parallel pair into the indiscrete two-point space: constant at
   [false], and [true] exactly at [zig_c]. *)
Definition zig_g_fun@{} (z : zig_pt) : bool :=
  match z with zig_c => true | _ => false end.

Definition zig_f_set@{o} :
  SetoidMorphism@{o o o} zig_setoid@{o} bool_setoid_object@{o o}.
Proof.
  refine {| morphism := fun _ : zig_pt => false |}.
  intros x y _; reflexivity.
Defined.

Definition zig_g_set@{o} :
  SetoidMorphism@{o o o} zig_setoid@{o} bool_setoid_object@{o o}.
Proof.
  refine {| morphism := zig_g_fun |}.
  intros x y e; simpl in e; subst; reflexivity.
Defined.

Definition zig_f_map@{o} : PMor@{o} PZig@{o} PTwoIndisc@{o} :=
  pindisc_mor bool_setoid_object@{o o} PZig@{o} zig_f_set@{o}.

Definition zig_g_map@{o} : PMor@{o} PZig@{o} PTwoIndisc@{o} :=
  pindisc_mor bool_setoid_object@{o o} PZig@{o} zig_g_set@{o}.

(* Their equalizer: the two open points, as the discrete two-point space. *)
Definition zig_e_fun@{} (b : bool) : zig_pt := if b then zig_a else zig_b.

Definition zig_e_set@{o} :
  SetoidMorphism@{o o o} bool_setoid_object@{o o} zig_setoid@{o}.
Proof.
  refine {| morphism := zig_e_fun |}.
  intros x y e; simpl in e; subst; reflexivity.
Defined.

Definition zig_e_map@{o} : PMor@{o} PBool@{o} PZig@{o} :=
  pdisc_mor bool_setoid_object@{o o} PZig@{o} zig_e_set@{o}.

Definition zig_lift_fun@{} (z : zig_pt) : bool :=
  match z with zig_a => true | zig_b => false | zig_c => true end.

Lemma PTop_zig_equalizer@{o so | o < so +} :
  @IsEqualizer PTopCat@{o so} PZig@{o} PTwoIndisc@{o}
    zig_f_map@{o} zig_g_map@{o} PBool@{o} zig_e_map@{o}.
Proof.
  unshelve econstructor.
  - intros [|]; reflexivity.
  - intros W k Hk.
    assert (Hnc : ∀ w, pmap k w <> zig_c).
    { intros w Hw. pose proof (Hk w) as H. simpl in H.
      rewrite Hw in H. discriminate H. }
    unshelve eexists.
    + unshelve refine (Build_PMor W PBool
        {| morphism := fun w => zig_lift_fun (pmap k w) |} _).
      * intros w1 w2 Hw. simpl. f_equal.
        exact (proper_morphism (pmap k) _ _ Hw).
      * intros V HV.
        apply (popen_respects W
                 (fun w => (fun z => match z with
                                     | zig_a => V true | zig_b => V false
                                     | zig_c => False end) (pmap k w))).
        -- intro w. simpl. pose proof (Hnc w) as Hn.
           destruct (pmap k w); simpl; try tauto; contradiction.
        -- exact (pcont k (fun z => match z with
                                      | zig_a => V true | zig_b => V false
                                      | zig_c => False end)
                        (fun H => False_ind _ H)).
    + intro w. simpl. pose proof (Hnc w) as Hn.
      destruct (pmap k w); simpl; try reflexivity; contradiction.
    + intros v Hv w. simpl. pose proof (Hv w) as H. simpl in H.
      destruct (pmap v w), (pmap k w); simpl in *; congruence.
Qed.

(* The same fork in [Lconn], by fullness. *)
Definition LZig@{o so | o < so +} : Lconn@{o so} :=
  (PZig@{o}; PZig_PLocConn@{o}).

Definition LBool@{o so | o < so +} : Lconn@{o so} :=
  (PBool@{o}; pdisc_locconn bool_setoid_object@{o o}).

Definition zig_f@{o so | o < so +} :
  LZig@{o so} ~{Lconn@{o so}}~> LTwoIndisc@{o so} := (zig_f_map@{o}; I).

Definition zig_g@{o so | o < so +} :
  LZig@{o so} ~{Lconn@{o so}}~> LTwoIndisc@{o so} := (zig_g_map@{o}; I).

Definition zig_e@{o so | o < so +} :
  LBool@{o so} ~{Lconn@{o so}}~> LZig@{o so} := (zig_e_map@{o}; I).

Lemma Lconn_zig_equalizer@{o so | o < so +} :
  @IsEqualizer Lconn@{o so} LZig@{o so} LTwoIndisc@{o so}
    zig_f@{o so} zig_g@{o so} LBool@{o so} zig_e@{o so}.
Proof.
  pose proof PTop_zig_equalizer@{o so} as E.
  unshelve econstructor.
  - exact (fork_eq E).
  - intros W k Hk.
    destruct (eq_desc E (`1 k) Hk) as [u Hu Huniq].
    exists (u; I).
    + exact Hu.
    + intros v Hv. exact (Huniq (`1 v) Hv).
Qed.

(* The discrete two-point space has two components. *)
Lemma pbool_two_components@{o} : comp_rel PBool@{o} true false → False.
Proof.
  intros [W [HW [wt wf]]].
  assert (L : LocConstOn PBool W (fun b => b = true)).
  { intros z _. exists (fun w => w = z). split; [|split; [reflexivity|]].
    - intros x y e h; simpl in e; subst; reflexivity.
    - intros w _ e; subst; tauto. }
  discriminate (HW _ L true false wt wf eq_refl).
Qed.

(* The one-point propositional set. *)
Definition PSetsOne@{o so | o < so +} : PSets@{o so} :=
  (unit_setoid_object@{o o}; unit_PropEquiv@{o o}).

(* C does not preserve the equalizer: C of the three-point space is one
   component, so C of the equalizing map identifies the two components of
   [PBool] and is not monic. *)
Theorem components_zig_not_preserved@{o so | o < so +} :
  @IsEqualizer PSets@{o so} _ _
    (fmap[components_functor@{o so}] zig_f@{o so})
    (fmap[components_functor@{o so}] zig_g@{o so})
    (components_functor@{o so} LBool@{o so})
    (fmap[components_functor@{o so}] zig_e@{o so}) → False.
Proof.
  intro HE.
  pose proof (equalizer_monic _ _ HE) as M.
  pose (k1 := ({| morphism := fun _ : unit_setoid_object@{o o} => true;
                  proper_morphism := fun _ _ _ => reflexivity _ |}; I)
              : PSetsOne@{o so} ~{PSets@{o so}}~>
                  components_functor@{o so} LBool@{o so}).
  pose (k2 := ({| morphism := fun _ : unit_setoid_object@{o o} => false;
                  proper_morphism := fun _ _ _ => reflexivity _ |}; I)
              : PSetsOne@{o so} ~{PSets@{o so}}~>
                  components_functor@{o so} LBool@{o so}).
  assert (Hk : fmap[components_functor@{o so}] zig_e@{o so} ∘ k1
                 ≈ fmap[components_functor@{o so}] zig_e@{o so} ∘ k2).
  { intro t. exact (PZig_one_component zig_a zig_b). }
  exact (pbool_two_components (@monic _ _ _ _ M _ k1 k2 Hk ttt)).
Qed.

(* Hence C has no left adjoint: a right adjoint preserves the equalizer. *)
Theorem components_no_left_adjoint@{o so +| o < so +}
  (L : PSets@{o so} ⟶ Lconn@{o so}) (B : L ⊣ components_functor@{o so}) :
  False.
Proof.
  exact (not_PreservesEqualizers_no_left_adjoint _ _ _ _
           Lconn_zig_equalizer@{o so} components_zig_not_preserved@{o so}
           L B).
Qed.

(* The same for ANY left adjoint of D, whatever its definition: the unit
   at the three-point space is continuous into a discrete space, so it
   identifies the two images of the equalizer. *)
Theorem discrete_left_adjoint_not_preserved@{o so +| o < so +}
  (C : Lconn@{o so} ⟶ PSets@{o so}) (A : C ⊣ PSetsDisc@{o so}) :
  @IsEqualizer PSets@{o so} _ _ (fmap[C] zig_f@{o so}) (fmap[C] zig_g@{o so})
    (C LBool@{o so}) (fmap[C] zig_e@{o so}) → False.
Proof.
  intro EC.
  pose proof (equalizer_monic _ _ EC) as M.
  pose (etaX := @unit _ _ _ _ A LZig).
  pose (etaE := @unit _ _ _ _ A LBool).
  assert (Hconn : ∀ z, inhabited (pmap (`1 etaX) z ≈ pmap (`1 etaX) zig_c)).
  { intro z.
    pose proof (pcont (`1 etaX)
                  (fun s => inhabited (s ≈ pmap (`1 etaX) zig_c))) as Hc.
    assert (Ho : POpen (PDiscrete (`1 (C LZig)))
                   (fun s => inhabited (s ≈ pmap (`1 etaX) zig_c))).
    { intros a b Hab [Ha]. constructor.
      exact (transitivity (symmetry Hab) Ha). }
    specialize (Hc Ho). simpl in Hc.
    destruct z.
    - exact (proj1 (Hc (inhabits (reflexivity _)))).
    - exact (inhabits (reflexivity _)).
    - exact (proj2 (Hc (inhabits (reflexivity _)))). }
  destruct (Hconn zig_a) as [Ha], (Hconn zig_b) as [Hb].
  assert (Nat : etaX ∘ zig_e ≈ fmap[PSetsDisc] (fmap[C] zig_e) ∘ etaE).
  { unfold etaX, etaE, unit.
    rewrite <- (@to_adj_nat_l _ _ _ _ A).
    rewrite <- (@to_adj_nat_r _ _ _ _ A).
    exact (to_adj_respects (H := A) _ _
             (transitivity (id_left _) (symmetry (id_right _)))). }
  assert (Hid : pmap (`1 etaE) true ≈ pmap (`1 etaE) false).
  { pose (k1 := ({| morphism := fun _ : unit_setoid_object@{o o} =>
                                  pmap (`1 etaE) true;
                    proper_morphism := fun _ _ _ => reflexivity _ |}; I)
                : PSetsOne@{o so} ~{PSets@{o so}}~> fobj[C] LBool).
    pose (k2 := ({| morphism := fun _ : unit_setoid_object@{o o} =>
                                  pmap (`1 etaE) false;
                    proper_morphism := fun _ _ _ => reflexivity _ |}; I)
                : PSetsOne@{o so} ~{PSets@{o so}}~> fobj[C] LBool).
    assert (Hk : fmap[C] zig_e ∘ k1 ≈ fmap[C] zig_e ∘ k2).
    { intro t. simpl.
      transitivity (pmap (`1 etaX) zig_a); [symmetry; exact (Nat true)|].
      transitivity (pmap (`1 etaX) zig_c); [exact Ha|].
      transitivity (pmap (`1 etaX) zig_b); [symmetry; exact Hb|].
      exact (Nat false). }
    exact (@monic _ _ _ _ M _ k1 k2 Hk ttt). }
  pose (BoolP := (bool_setoid_object@{o o}; eq_PropEquiv bool)
                 : PSets@{o so}).
  pose (sep := (pdisc_mor bool_setoid_object@{o o}
                  (PDiscrete bool_setoid_object@{o o})
                  setoid_morphism_id; I)
               : LBool ~{Lconn@{o so}}~> PSetsDisc BoolP).
  pose (hsep := from (@adj _ _ _ _ A LBool BoolP) sep).
  assert (Hs : ∀ b, `1 hsep (pmap (`1 etaE) b) ≈ b).
  { intro b.
    pose proof (@to_adj_unit _ _ _ _ A _ _ hsep) as T.
    pose proof (from_adj_comp_law (H := A) sep) as T2.
    exact (transitivity (symmetry T) T2 b). }
  pose proof (proper_morphism (`1 hsep) _ _ Hid) as H3.
  assert (Hbad : @equiv _ bool_setoid_object@{o o} true false).
  { exact (transitivity (symmetry (Hs true)) (transitivity H3 (Hs false))). }
  discriminate Hbad.
Qed.

Theorem discrete_left_adjoint_no_left_adjoint@{o so ua ub +| o < so +}
  (C : Lconn@{o so} ⟶ PSets@{o so})
  (A : @Adjunction@{so o o so o o o o ua o _} PSets@{o so} Lconn@{o so}
         C PSetsDisc@{o so})
  (L : PSets@{o so} ⟶ Lconn@{o so})
  (B : @Adjunction@{so o o so o o o o ub o _} Lconn@{o so} PSets@{o so}
         L C) : False.
Proof.
  exact (not_PreservesEqualizers_no_left_adjoint _ _ _ _
           Lconn_zig_equalizer@{o so}
           (discrete_left_adjoint_not_preserved C A) L B).
Qed.

(** ** A second witness: the swap of the indiscrete two-point space *)

(* The empty space, discrete. *)
Definition LEmpty@{o so | o < so +} : Lconn@{o so} :=
  LDisc@{o so} Concrete.empty_setoid_object@{o o}.

Definition swap_set@{o} :
  SetoidMorphism@{o o o} bool_setoid_object@{o o} bool_setoid_object@{o o}.
Proof.
  refine {| morphism := negb |}.
  intros x y e; simpl in e; subst; reflexivity.
Defined.

Definition swap_map@{o} : PMor@{o} PTwoIndisc@{o} PTwoIndisc@{o} :=
  pindisc_mor bool_setoid_object@{o o} PTwoIndisc@{o} swap_set@{o}.

Definition empty_set_map@{o} :
  SetoidMorphism@{o o o} Concrete.empty_setoid_object@{o o} PTwoIndisc@{o}.
Proof.
  refine {| morphism := fun x : False => match x with end |}.
  intros x; destruct x.
Defined.

Definition swap_L@{o so | o < so +} :
  LTwoIndisc@{o so} ~{Lconn@{o so}}~> LTwoIndisc@{o so} := (swap_map@{o}; I).

Definition swap_e@{o so | o < so +} :
  LEmpty@{o so} ~{Lconn@{o so}}~> LTwoIndisc@{o so} :=
  (pdisc_mor Concrete.empty_setoid_object@{o o} PTwoIndisc@{o}
     empty_set_map@{o}; I).

Lemma negb_no_fixpoint@{} (b : bool) : b = negb b → False.
Proof. destruct b; discriminate. Qed.

(* The equalizer of the identity and the swap is the empty space. *)
Lemma Lconn_swap_equalizer@{o so | o < so +} :
  @IsEqualizer Lconn@{o so} LTwoIndisc@{o so} LTwoIndisc@{o so}
    id swap_L@{o so} LEmpty@{o so} swap_e@{o so}.
Proof.
  unshelve econstructor.
  - intro x; destruct x.
  - intros z h Hh.
    assert (Hno : ∀ p : pt_carrier (`1 z), False).
    { intro p. apply (negb_no_fixpoint (pmap (`1 h) p)). exact (Hh p). }
    unshelve refine {| unique_obj := _ |}.
    + unshelve refine (_; I).
      unshelve refine (@Build_PMor (`1 z)
                         (PDiscrete Concrete.empty_setoid_object@{o o})
                         {| morphism := fun p => match Hno p with end |} _).
      * intros p; destruct (Hno p).
      * intros U HU. apply (popen_respects _ (fun _ => False)).
        -- intro p; destruct (Hno p).
        -- apply popen_empty.
    + intro p; destruct (Hno p).
    + intros v _ p; destruct (Hno p).
Qed.

(* C does not preserve it: the one component of the two-point space is a
   fork into the empty set. *)
Theorem components_swap_not_preserved@{o so | o < so +} :
  @IsEqualizer PSets@{o so} _ _ (fmap[components_functor@{o so}] id)
    (fmap[components_functor@{o so}] swap_L@{o so})
    (components_functor@{o so} LEmpty@{o so})
    (fmap[components_functor@{o so}] swap_e@{o so}) → False.
Proof.
  intro HE.
  pose (k := ({| morphism := fun _ : unit_setoid_object@{o o} => true;
                 proper_morphism := fun _ _ _ => reflexivity _ |}; I)
             : PSetsOne@{o so} ~{PSets@{o so}}~>
                 components_functor@{o so} LTwoIndisc@{o so}).
  assert (Hk : fmap[components_functor@{o so}] id ∘ k
                 ≈ fmap[components_functor@{o so}] swap_L@{o so} ∘ k).
  { intro t. exists (fun _ => True).
    exact (conj PTwoIndisc_connected (conj I I)). }
  destruct (eq_desc HE k Hk) as [v _ _].
  exact (`1 v ttt).
Qed.

(** ** Outside [Lconn]: D on all of [PTopCat] has no left adjoint *)

(* The convergent sequence is not locally connected at its limit point: the
   isolated point [Some K] is relatively clopen in every neighbourhood of
   it. *)
Lemma pconv_not_locconn@{o} : PLocConn PConv@{o} → False.
Proof.
  intro LC.
  destruct (LC None (fun _ => True) (popen_whole _) I)
    as [N [HN [nN [_ HC]]]].
  destruct (HN nN) as [K HK].
  assert (L : LocConstOn PConv N (fun z => z = Some K)).
  { intros z _. destruct z as [m|].
    - exists (fun w => w = Some m). split; [|split; [reflexivity|]].
      + intro H; discriminate H.
      + intros w _ e; subst; tauto.
    - exists (fun w => match w with
                       | None => True
                       | Some m => (S K <= m)%nat end).
      split; [|split; [exact I|]].
      + intros _. exists (S K). intros m Hm; exact Hm.
      + intros w _ Hw. destruct w as [m|]; [|tauto].
        split; intro e; [injection e as e; subst; exfalso;
                          exact (Nat.nle_succ_diag_l _ Hw)|discriminate]. }
  discriminate (HC _ L (Some K) None (HK K (le_n K)) nN eq_refl).
Qed.

(* D into all of [PTopCat], from the propositional sets. *)
Definition PSetsDiscTop@{o so | o < so +} : PSets@{o so} ⟶ PTopCat@{o so} :=
  @Compose@{so so so so o} PSets@{o so} Sets@{o so} PTopCat@{o so}
    PDisc@{o so} (Incl@{so o so o so so} Sets@{o so} PSetsSub@{o so}).

Theorem discrete_no_left_adjoint_on_PTop@{o so +| o < so +}
  (C' : PTopCat@{o so} ⟶ PSets@{o so}) (A : C' ⊣ PSetsDiscTop@{o so}) :
  False.
Proof.
  pose (Q := C' PConv).
  pose (eta := to (@adj _ _ _ _ A PConv Q) id).
  pose (P := `2 Q).
  (* continuity of the unit at the propositional singleton of eta None *)
  assert (Hopen : POpen PConv
            (fun z => @pequiv _ _ P (pmap eta z) (pmap eta None))).
  { apply (pcont eta (fun s => @pequiv _ _ P s (pmap eta None))).
    intros s t e p. apply pequiv_from.
    exact (transitivity (symmetry e) (pequiv_to _ _ p)). }
  destruct (Hopen (pequiv_from _ _ (reflexivity _))) as [N HN].
  pose (BoolP := (bool_setoid_object@{o o}; eq_PropEquiv bool)
                 : PSets@{o so}).
  pose (f := pconv_ind_mor@{o} N
             : PConv ~{PTopCat@{o so}}~> PSetsDiscTop BoolP).
  pose (g := from (@adj _ _ _ _ A PConv BoolP) f).
  assert (Hf : ∀ z, pmap f z = (`1 g) (pmap eta z)).
  { intro z.
    pose proof (iso_to_from (@adj _ _ _ _ A PConv BoolP) f z) as E1.
    pose proof (@to_adj_nat_r _ _ _ _ A PConv Q BoolP g id z) as E2.
    pose proof (proper_morphism (to (@adj _ _ _ _ A PConv BoolP)) _ _
                  (id_right g) z) as E3.
    simpl in E1, E2, E3.
    exact (eq_trans (eq_sym E1) (eq_trans (eq_sym E3) E2)). }
  pose proof (Hf (Some N)) as HN1. pose proof (Hf None) as HN0.
  pose proof (proper_morphism (`1 g) _ _
                (pequiv_to _ _ (HN N (le_n N)))) as Hg.
  simpl in HN1, HN0, Hg.
  rewrite Nat.eqb_refl in HN1.
  rewrite <- HN1, <- HN0 in Hg. discriminate Hg.
Qed.

(* The same with all of [Sets]: Instance/Top/Complete.v's [PDisc] has no
   left adjoint.  The open set is now a truncation, eliminated into the
   goal [False]. *)
Theorem PDisc_no_left_adjoint@{o so +| o < so +}
  (C' : PTopCat@{o so} ⟶ Sets@{o so}) (A : C' ⊣ PDisc@{o so}) : False.
Proof.
  pose (Q := C' PConv).
  pose (eta := to (@adj _ _ _ _ A PConv Q) id).
  assert (Hopen : POpen PConv
            (fun z => inhabited (pmap eta z ≈ pmap eta None))).
  { apply (pcont eta (fun s => inhabited (s ≈ pmap eta None))).
    intros s t e [p]. exact (inhabits (transitivity (symmetry e) p)). }
  destruct (Hopen (inhabits (reflexivity _))) as [N HN].
  pose (f := pconv_ind_mor@{o} N
             : PConv ~{PTopCat@{o so}}~> PDisc bool_setoid_object@{o o}).
  pose (g := from (@adj _ _ _ _ A PConv bool_setoid_object@{o o}) f).
  assert (Hf : ∀ z, pmap f z = g (pmap eta z)).
  { intro z.
    pose proof (iso_to_from (@adj _ _ _ _ A PConv bool_setoid_object) f z)
      as E1.
    pose proof (@to_adj_nat_r _ _ _ _ A PConv Q bool_setoid_object g id z)
      as E2.
    pose proof (proper_morphism (to (@adj _ _ _ _ A PConv bool_setoid_object))
                  _ _ (id_right g) z) as E3.
    simpl in E1, E2, E3.
    exact (eq_trans (eq_sym E1) (eq_trans (eq_sym E3) E2)). }
  destruct (HN N (le_n N)) as [e].
  pose proof (Hf (Some N)) as HN1. pose proof (Hf None) as HN0.
  pose proof (proper_morphism g _ _ e) as Hg.
  simpl in HN1, HN0, Hg.
  rewrite Nat.eqb_refl in HN1.
  rewrite <- HN1, <- HN0 in Hg. discriminate Hg.
Qed.
