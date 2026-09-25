Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Coequalizer.Wide.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Parallel.Wide.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Coproduct.
Require Import Category.Instance.Top.Homotopy.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Top.Quotient.

Generalizable All Variables.

(** * The category of pairs, and X/A as a left adjoint *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
     §V.9, book pp. 134-135 (PDF pp. 143-144), read from the page images:
     "If we consider the category Top^(2) whose objects are pairs ⟨X, A⟩
     (a space X with a subset A) and whose arrows ⟨X, A⟩ → ⟨X', A'⟩ are
     continuous maps X → X' sending A to A', then the definition of X/A,
     for Y a pointed topological space, reads:
         Top_*(X/A, Y) = Top^(2)(⟨X, A⟩, ⟨Y, *⟩).
     Thus ⟨X, A⟩ ↦ X/A is left adjoint to the functor Y ↦ ⟨Y, *⟩ which
     sends each pointed space to the pair ⟨Y, *⟩." (catalog id
     maclane:V.9:construction6; the book numbers it not)
   nLab:      https://ncatlab.org/nlab/show/Top
   nLab:      https://ncatlab.org/nlab/show/pointed+object
   Wikipedia: https://en.wikipedia.org/wiki/Quotient_space_(topology)
   Book:      A. Hatcher, "Algebraic Topology", Cambridge University Press
              (2002), Proposition 2.22 (good pairs)

   BACKGROUND.  Pairs of spaces are where relative homology lives, and
   the quotient is how it is computed: for a good pair (X, A) the
   quotient map induces isomorphisms from the relative homology of
   (X, A) to the reduced homology of X/A (Hatcher, Proposition 2.22).
   Mac Lane's paragraph turns the collapse into a functor on pairs and
   reads its defining property as a hom-set bijection, so that
   ⟨X, A⟩ ↦ X/A is a left adjoint.  The target is the category of pointed
   spaces, the tree's [Top_pointed] (Instance/Top/Homotopy.v).  The nLab
   page on pointed objects records the simplest case: the forgetful
   functor from pointed objects has a left adjoint, adjoining a disjoint
   basepoint, X ↦ X₊ = X ⊔ *.  That is Mac Lane's adjunction at the empty
   subset, since every continuous map carries ∅ into the basepoint.

   AT A = ∅ THE BOOK LEAVES A CHOICE, AND ONE READING MAKES ITS TWO
   CONSTRUCTIONS AGREE.  Mac Lane defines the coequalizer of a pair
   elementarily (book p. 64, PDF p. 73, display (6): an arrow u : b → e
   with uf = ug, universal), reads it as a universal arrow to Δ (p. 65,
   PDF p. 74: "just a universal arrow from ⟨f, g⟩ to the functor Δ"),
   and says coequalizers of any set of maps "are defined in the same
   way", all read from the page images.  The two forms agree on every
   nonempty set; at the empty set the universal arrow is a ⊔ b and the
   elementary form b.  Read as the universal arrow, the reading p. 135
   needs since Top_*(X/A, Y) takes X/A pointed, his X/∅ is X ⊔ * and
   Constructions 5 and 6 agree at every A
   ([pquot_wide_coequalizer_colimit]); read elementarily, as
   Structure/Coequalizer/Wide.v's header reads it, X/∅ is X and they
   part there.  The universal arrow is a colimit over the shape that has
   the domain * as a vertex, Wide.v's [WideCoequalizer]: a cocone has a
   leg out of * as well as one out of X, so no point of A is needed, and
   at the empty family the leg out of * is unconstrained, which gives
   the X₊ of the nLab's adjoint above.  The refutations below are about
   the elementary reading.

   This file defines X/A uniformly as (X ⊔ {∗})/(A ∼ ∗): the points are
   [option X], [None] the new point, [Some x] identified with [None]
   exactly when x lies in A ([pquot_rel]), with the quotient topology
   [TQuot] of Instance/Top/Subspace/TypeValued.v along [Some]
   ([pquot_space]).  No case split on whether A is empty, which is not
   decidable here, is needed.  What is proved about it:
     - It IS the coequalizer of the point-inclusions of A read as the
       universal arrow, for every A, the empty one included, with no
       point of A ([pquot_wide_coequalizer_colimit]: a [WideCoequalizer]
       of exactly Construction 5's family [collapse_sub_family], at the
       type of Instance/Top/Quotient.v's [collapse_colimit]).  Its apex
       is [pquot_space X], its leg out of X is [pquot_in X], and its leg
       out of * sends the one point to the left adjoint's basepoint, all
       at [eq_refl] ([pquot_wide_coequalizer_colimit_apex],
       [pquot_wide_coequalizer_colimit_in],
       [pquot_wide_coequalizer_colimit_base]); and the left adjoint's
       underlying space at every pair IS that apex, at [eq_refl]
       ([pquot_wide_coequalizer_colimit_quotient]), so under that reading
       Mac Lane's two constructions give one space.  Every colimit of
       that family has a point, the image of * ([collapse_colimit_point]).
     - It is the pushout X ⊔_A ∗ in [Top] ([pquot_pushout]), of the
       inclusion of the points of A with the discrete topology
       ([pair_sub_space], [pair_sub_incl]) against the map to the point;
       the apex is [pquot_space X] at [eq_refl] ([pquot_pushout_apex]).
       The colimit above descends through the pushout's mediator
       [pquot_po_med]: a cocone's two legs are a map out of X and a point
       absorbing A.  The discrete topology is a choice: the subspace
       topology is not formable at the points' universe (the header of
       Instance/Top/Subspace/TypeValued.v), and since neither the cocone
       condition nor the mediator's continuity consults the topology of
       A, any topology making the inclusion continuous gives the same
       pushout (argued, not formalized).
     - Given a point [a0] of A, X ~> X/A is also an ELEMENTARY wide
       coequalizer of the point-inclusions of A ([pquot_coequalizer]),
       the record [IsWideCoequalizer] of Structure/Coequalizer/Wide.v
       that Instance/Top/Quotient.v's [collapse_coequalizer] meets for
       every A; so the two readings of X/A are isomorphic in [Top] when A
       has a point ([pquot_collapse_iso], by [wide_coequalizer_unique]),
       the iso being x ↦ [Some x] one way and [Some x] ↦ x, [None] ↦ a0
       the other, at [eq_refl] ([pquot_collapse_iso_to],
       [pquot_collapse_iso_from_some], [pquot_collapse_iso_from_none]).
       They are isomorphic as POINTED spaces as well: Construction 5's
       X/A pointed at [a0] ([collapse_pointed]) is isomorphic in
       [Top_pointed] to the left adjoint's value [fobj[PairQuotient] X]
       ([pquot_collapse_iso_pointed]).
     - X/∅ is X₊: [pquot_empty_sum_iso] identifies [pquot_space] of
       ⟨X, ∅⟩ ([empty_pair]) with Instance/Top/Coproduct.v's
       [Sum_Top X Point_Top] in [Top], [Some x] ↦ [inl x] and
       [None] ↦ [inr ttt] at [eq_refl] ([pquot_empty_sum_iso_some],
       [pquot_empty_sum_iso_none]), an isomorphism, refused at [eq_refl] as
       an equation of spaces (Test/ProbeCollapse459.v's N16); the new
       point is new ([pquot_empty_new_point]).  So, read as the universal
       arrow, the coequalizer of the empty family is X ⊔ *
       ([pquot_wide_coequalizer_colimit_empty], the colimit's apex at
       ⟨X, ∅⟩ against [Sum_Top X Point_Top]).

   THE ELEMENTARY READING AT A = ∅.  [IsWideCoequalizer], book p. 64's
   display (6) extended to a set of maps, states a coequalizer as an
   arrow out of X alone.  At the empty family its condition is vacuous
   and it pins down X itself (Instance/Top/Quotient.v's
   [collapse_empty_iso], X/∅ ≅ X), where the colimit is X ⊔ *: the gap
   between the two forms that the header of Structure/Coequalizer/Wide.v
   records ([wide_coround_trip_needs_point]).  At X = ∅ no elementary
   wide coequalizer of the empty family has a point, whatever its
   construction (Quotient.v's [empty_wide_coequalizer_pointless]).  The
   refutations here are statements about that elementary reading, under
   which Constructions 5 and 6 part at A = ∅, a case the book does not
   treat: no pointed space's underlying space is an elementary wide
   coequalizer of the empty family at ∅
   ([no_pointed_coequalizer_at_empty]); so no assignment of a pointed
   space to each pair, a functor or any other function on objects, makes
   every underlying space an elementary wide coequalizer of the
   point-inclusions ([no_pointed_elementary_coequalizers]); this file's
   X/A at ⟨∅, ∅⟩ is not one, so [pquot_coequalizer]'s point of A cannot
   be dropped ([pquot_empty_not_coequalizer],
   [pquot_coequalizer_needs_point]); and at ⟨∅, ∅⟩ no colimit's apex
   carries one ([empty_colimit_not_elementary]), the two forms parting
   there at [Top] as that header says they part in general.  None uses
   the uniqueness of left adjoints or an initial object of [Top_pointed].

   THE CATEGORY OF PAIRS.  [PairTop]: a space with a Type-valued
   predicate on its points that respects their equality
   ([pair_sub_proper]).  [PairMap]: a continuous map carrying the subset
   into the subset; the hom-setoid is [Top]'s own read on the underlying
   maps, as Instance/Top/Homotopy.v's [PointedMap_Setoid] is, so
   [Top_pairs] has [Top_pointed]'s shape.  What bears on the two choices
   is pinned in Test/ProbeCollapse459.v, which carries this file's import
   list.
     - Type, not Prop, is forced by ⟨Y, *⟩.  The book's ⟨Y, *⟩ is the
       predicate y ≈ y0, whose values are the Type-valued equality of a
       space's points; read as a Prop-valued predicate it is refused,
       "The term "y ≈ ptop_pt Y" has type "Type" while it is expected to
       have type "Prop"" (the probe's N10).  As a Prop it must be
       squashed, [inhabited (y ≈ y0)], and the transpose needs it
       unsquashed ([pquot_from_map]'s case [Some x] ∼ [None]); unsquashing
       is refused, "Incorrect elimination of "H" in the inductive type
       "inhabited": the return type has sort "Type" while it should be
       SProp or Prop" (N11).  Control: the elimination into
       [inhabited (y ≈ y0)] is accepted.
     - The respect field is a design choice, not a necessity.  A subset
       of a setoid is taken closed under the points' equality, the setoid
       reading of Mac Lane's "subset": points equal in the space are one
       point of it.  The alternative is to drop the field and saturate A
       inside the identification, as Instance/Top/Quotient.v's
       [collapse_image] does: the same four-case relation over [option X]
       with the saturation of A, the points equal to a point of A, in
       place of A is an equivalence with no field (Test/ProbeCollapse459.v's
       [p459_sat_rel_Equivalence], closed under the global context).
       What is measured about the field concerns the UNSATURATED relation
       [pquot_rel] only: without the field it is not transitive, on [bool]
       with the total equality and A := (= true), [Some false] ∼
       [Some true] ∼ [None] while [Some false] ≁ [None] (the probe's
       [p459_unsat_rel_not_transitive], closed under the global context).

   THE ADJUNCTION.  [PointPair] sends Y to ⟨Y, *⟩; [PairQuotient] sends
   ⟨X, A⟩ to X/A pointed at [None], and a map f to [Some x] ↦ [Some (f x)],
   [None] ↦ [None].  [pairs_quotient_iso X Y] is the book's display as an
   [Isomorphism] in [Sets]; its "=" is refused at [eq_refl] as an
   equation of hom types (Test/ProbeCollapse459.v's N12).  [pquot_to]
   restricts along [Some], [pquot_from] extends by sending [None] to the
   basepoint, its continuity from [TQuot]'s universal property.
   [pairs_quotient_adjunction] (the issue's pinned name) is
   [Build_Adjunction'] on it, both naturality squares pointwise
   reflexivity; the unit is x ↦ [Some x], the counit [Some y] ↦ y and
   [None] ↦ the basepoint.  It is an [Adjunction] record in [Top], where
   Instance/Top/Subspace/TypeValued.v's sliced quotient adjunction is
   refused, because [Adjunction] identifies the hom levels of its two
   categories (Theory/Adjunction.v, About: [h1 = h2]) and here both
   [Top_pointed@{h o}] and [Top_pairs@{h o}] have their homs at [h].

   THE REALS.  [Top_pointed] lives in Instance/Top/Homotopy.v, which
   requires the stdlib reals and opens [R_scope]; this file reaches them
   through that import, as Instance/Top/Wedge.v does, and every constant
   here still prints "Closed under the global context".  The relation
   [pquot_rel] is written under [%type] for that reason.  Moving
   [PointedTop] and [Top_pointed] to a file free of the reals is left to
   the maintainer.

   STRENGTHS.  At [eq_refl]: [PointPair_sub], [pquot_space_carrier],
   [pquot_basepoint], [pquot_space_open], [pquot_to_eval],
   [pquot_from_eval_some], [pquot_from_eval_none],
   [pairs_quotient_unit_eval], [pairs_quotient_counit_some],
   [pairs_quotient_counit_none], [pairs_quotient_adj_is] (the adjunction's
   hom-set isomorphism IS [pairs_quotient_iso]), [pquot_pushout_apex],
   the four readbacks of the colimit [pquot_wide_coequalizer_colimit]
   (its apex, its two legs and the left adjoint's underlying space), the
   three [pquot_collapse_iso] readbacks and the two [pquot_empty_sum_iso]
   readbacks.  Up to [≈]: the category and functor
   laws, the isomorphism laws, the naturality squares and the universal
   properties.  Eleven [Defined], counted by token, every one
   load-bearing: each closed [Qed] alone in a scratch copy leaves a
   named constant refused — [point_pair_map] ([PointPair]'s first
   obligation), [pquot_fmap_map] ([pquot_fmap_cont]), [pquot_to]
   ([pairs_quotient_iso]'s first obligation), [pquot_from_map]
   ([pquot_from]), [pairs_quotient_adjunction]
   ([pairs_quotient_unit_eval], "cannot unify "unit x" and "Some x""),
   [pquot_po_map] ([pquot_po_med]), [pquot_pushout]
   ([pquot_pushout_apex]), [pquot_coequalizer]
   ([pquot_collapse_iso_from_some]), [pquot_empty_sum_to] and
   [pquot_empty_sum_from] ([pquot_empty_sum_iso]), [pquot_empty_sum_iso]
   ([pquot_empty_sum_iso_some]).

   UNIVERSES, read by [About] under [Set Printing Universes] on all 100
   constants of this file's [Print Module] listing (the two records,
   their constructors and projections, and the fourteen [Program]
   obligations included).  Binder order: [@{h o ...}], the order of
   [Top@{h o}], except for the constants that restate Construction 5's
   wide-coequalizer vocabulary, which keep Instance/Top/Quotient.v's
   [@{o h ...}] and so instantiate like the constants they read (the
   colimit form, [pquot_wide_legs] through
   [pquot_wide_coequalizer_colimit_quotient] and
   [pquot_wide_coequalizer_colimit_empty], with
   [collapse_colimit_point]; [pquot_coequalizer], [pquot_collapse_iso]
   with its three readbacks and [pquot_collapse_iso_pointed]; and the
   refutations [pquot_empty_not_coequalizer],
   [pquot_coequalizer_needs_point], [no_pointed_coequalizer_at_empty],
   [no_pointed_elementary_coequalizers] and
   [empty_colimit_not_elementary]).
     - The constants that mention no arrow of [Top] ([PairTop], its
       constructor and projections, [point_pair], [pquot_rel] through
       [pquot_pointed], [pquot_space_open], [pair_sub_setoid] and its
       [Equivalence], [pair_sub_space], [pair_sub_incl_map],
       [empty_pair], [pquot_empty_new_point], [pquot_empty_sum_to],
       [pquot_empty_sum_from] and [collapse_pointed]): [@{o}], with no
       constraint beyond stdlib caps; X/A is a [TopSpace@{o}], at the
       universe of X.
     - [PairMap], [Top_pairs], [PointPair], [PairQuotient] and the maps
       between them, the section constants [pquot_po_map] and
       [pquot_po_med] and [pquot_empty_sum_iso] with its two readbacks
       among them: [@{h o}] with [o < h] and stdlib caps;
       [Top_pairs@{h o} : Category@{h h h}], the shape of
       [Top_pointed@{u u0}] (About: [Category@{u u u}], [u0 < u]).
     - The colimit form ([pquot_wide_legs], [pquot_wide_legs_coherence],
       [pquot_wide_cocone], [pquot_wide_ump],
       [pquot_wide_coequalizer_colimit] with its four readbacks and
       [pquot_wide_coequalizer_colimit_empty], and
       [collapse_colimit_point]): [@{o h}] with [o < h] and stdlib caps;
       the colimit is a [WideCoequalizer@{h h}] of
       [AWide@{h h h h h} (collapse_sub_family@{o h} X (pair_sub X))],
       the instance of Instance/Top/Quotient.v's [collapse_colimit@{o h}]
       at A := [pair_sub X] (both About).
     - [pairs_quotient_iso@{h o u}]: [o < h] and [h < u], an
       [Isomorphism] in [Sets@{h u}], whose objects, the hom-setoids at
       [h], sit at [u].  [pairs_quotient_adjunction@{h o u v}]: the same
       two bounds, and [v] in no constraint.  [v] is [Adjunction]'s own
       binder [sp] of [Adjunction@{o1 h1 p1 o2 h2 p2 o3 p3 so sh sp}],
       which occurs in no constraint of that record's About block.  The
       statement is written [Adjunction@{h h h h h h h h u h v}]: the same
       [Build_Adjunction'] term stated through the notation [⊣] under the
       closed binder, [v] named in it, is refused at the statement,
       "Universe <1> (...) is unbound" (Test/ProbeCollapse459.v's N13),
       while the finished constant reads through [⊣] once the binder
       names [v] and is refused when it does not (N14 and its control).
     - [pquot_coequalizer], [pquot_empty_not_coequalizer],
       [pquot_coequalizer_needs_point], [no_pointed_coequalizer_at_empty],
       [no_pointed_elementary_coequalizers] and
       [empty_colimit_not_elementary]: [@{o h i}] with [o < h] and
       [o <= i], the flexible index of Instance/Top/Quotient.v's header
       (its W-c).  [pquot_collapse_iso@{o h u}] and
       [pquot_collapse_iso_pointed@{o h u}]: [u] is
       [wide_coequalizer_unique]'s own binder, as in that file; with [u]
       dropped the body of [pquot_collapse_iso] is refused, "Universe <1>
       (...) is unbound" (N15).
     - The five refutations [pquot_empty_not_coequalizer],
       [pquot_coequalizer_needs_point], [no_pointed_coequalizer_at_empty],
       [no_pointed_elementary_coequalizers] and
       [empty_colimit_not_elementary] carry the file's only STRICT stdlib
       cap, [o < False_rect.u0], which is [Empty_Top]'s own (its About:
       [u < False_rect.u0]).
     - No constraint block carries an equation or mentions [Set].  [Set]
       occurs in the statements of nine constants, thirteen times by a
       word count over the About output of all 100 under
       Test/ProbeCollapse459.v's import list: eleven times in eight
       constants of the colimit form, and twice in the refutation
       [empty_colimit_not_elementary] ([colimit_apex@{Set h h h} L], in
       the binder of [e] and in the negated [IsWideCoequalizer]).  Each
       time it is at the slot of the shape's objects in an instance of
       the colimit vocabulary ([Cocone], [cocone_inj], [colimit_apex],
       [colimit_inj], [colimit_is_acolimit]): the objects of the wide
       shape are Instance/Parallel.v's [ParObj : Set].

   NOT DELIVERED.  A Prop-valued subset (refused as above); [Top^(2)] as
   a comma category, a Grothendieck construction or a displayed category
   over [Top]; the pushout for other topologies on A (argued above); an
   initial object of [Top_pointed], and the argument that a left adjoint
   must send the initial pair ⟨∅, ∅⟩ to it (not formalized, and not
   needed: the value of the adjoint built here at every pair is read
   directly as the coequalizer in the universal-arrow reading,
   [pquot_wide_coequalizer_colimit_quotient]); the uniqueness of left
   adjoints applied to [PairQuotient]; X/A, and its colimit form, for a
   pair whose subset is not closed under the points' equality, which the
   saturated relation above would give; any homotopy-theoretic use,
   relative homology among them; and the relocation of [Top_pointed]
   away from the reals. *)

#[local] Obligation Tactic := idtac.

(** ** The category of pairs [Top^(2)] *)

(* A space with a subset of its points; the subset is a Type-valued
   predicate that respects the points' equality. *)
Record PairTop@{o} := {
  pair_space :> TopSpace@{o};
  pair_sub : carrier (top_carrier pair_space) → Type@{o};
  pair_sub_proper : ∀ x y, x ≈ y → pair_sub x → pair_sub y
}.

(* A map of pairs: a continuous map carrying the subset into the subset. *)
Record PairMap@{h o | o < h +} (X Y : PairTop@{o}) := {
  pair_map :> pair_space X ~{Top@{h o}}~> pair_space Y;
  pair_carries : ∀ x, pair_sub X x → pair_sub Y (pair_map x)
}.

Arguments pair_map {X Y} _.
Arguments pair_carries {X Y} _ _ _.

(* The hom-setoid is [Top]'s own, read on the underlying maps, as
   Instance/Top/Homotopy.v's [PointedMap_Setoid] is. *)
Lemma PairMap_equiv_Equivalence@{h o | o < h +} {X Y : PairTop@{o}} :
  Equivalence (fun p q : PairMap@{h o} X Y => pair_map p ≈ pair_map q).
Proof.
  constructor.
  - intro p; reflexivity.
  - intros p q Hpq; symmetry; exact Hpq.
  - intros p q r Hpq Hqr.
    transitivity (pair_map q); [ exact Hpq | exact Hqr ].
Qed.

#[export]
Instance PairMap_Setoid@{h o | o < h +} {X Y : PairTop@{o}} :
  Setoid@{h h} (PairMap@{h o} X Y) := {|
  equiv := fun p q => pair_map p ≈ pair_map q;
  setoid_equiv := PairMap_equiv_Equivalence@{h o}
|}.

Definition pair_id@{h o | o < h +} {X : PairTop@{o}} : PairMap@{h o} X X :=
  @Build_PairMap@{h o} X X (@id Top@{h o} (pair_space X)) (fun x a => a).

Definition pair_compose@{h o | o < h +} {X Y Z : PairTop@{o}}
  (p : PairMap@{h o} Y Z) (q : PairMap@{h o} X Y) : PairMap@{h o} X Z :=
  @Build_PairMap@{h o} X Z (pair_map p ∘[Top@{h o}] pair_map q)
    (fun x a => pair_carries p _ (pair_carries q x a)).

Lemma pair_compose_respects@{h o | o < h +} {X Y Z : PairTop@{o}} :
  Proper (equiv ==> equiv ==> equiv) (@pair_compose@{h o} X Y Z).
Proof.
  intros p p' Hp q q' Hq x; simpl.
  transitivity (pair_map p (pair_map q' x)).
  - apply proper_morphism; exact (Hq x).
  - exact (Hp (pair_map q' x)).
Qed.

(* Mac Lane's [Top^(2)].

       objects: pairs ⟨X, A⟩         (a space with a subset of its points)
        arrows: maps carrying A into A'
      identity: the identity map
   composition: composition of continuous maps *)
Program Definition Top_pairs@{h o | o < h +} : Category@{h h h} := {|
  obj     := PairTop@{o};
  hom     := PairMap@{h o};
  homset  := @PairMap_Setoid@{h o};
  id      := @pair_id@{h o};
  compose := @pair_compose@{h o};

  compose_respects := @pair_compose_respects@{h o}
|}.
Next Obligation. intros X Y f x; simpl. reflexivity. Qed.
Next Obligation. intros X Y f x; simpl. reflexivity. Qed.
Next Obligation. intros X Y Z W f g k x; simpl. reflexivity. Qed.
Next Obligation. intros X Y Z W f g k x; simpl. reflexivity. Qed.

(** ** The underlying pair of a pointed space *)

(* ⟨Y, *⟩: the subset is the basepoint, up to the points' equality. *)
Definition point_pair@{o} (Y : PointedTop@{o}) : PairTop@{o} :=
  @Build_PairTop@{o} (ptop_space Y) (fun y => y ≈ ptop_pt Y)
    (fun x y e h => transitivity (symmetry e) h).

Definition point_pair_map@{h o | o < h +} {X Y : PointedTop@{o}}
  (p : X ~{Top_pointed@{h o}}~> Y) :
  point_pair X ~{Top_pairs@{h o}}~> point_pair Y.
Proof.
  refine (@Build_PairMap@{h o} (point_pair X) (point_pair Y) (ptop_map p) _).
  intros x Hx; simpl in *.
  transitivity (ptop_map p (ptop_pt X)).
  - apply proper_morphism; exact Hx.
  - exact (ptop_preserves p).
Defined.

(* Y ↦ ⟨Y, *⟩. *)
Program Definition PointPair@{h o | o < h +} :
  Top_pointed@{h o} ⟶ Top_pairs@{h o} := {|
  fobj := point_pair@{o};
  fmap := @point_pair_map@{h o}
|}.
Next Obligation. intros X Y f g Hfg x; simpl. exact (Hfg x). Qed.
Next Obligation. intros X x; simpl. reflexivity. Qed.
Next Obligation. intros X Y Z f g x; simpl. reflexivity. Qed.

(** ** The quotient X/A of a pair: (X ⊔ {∗}) / (A ∼ ∗) *)

(* The points are those of X and one new point [None]; a point of X is
   identified with [None] exactly when it lies in A. *)
Definition pquot_rel@{o} (X : PairTop@{o})
  (u v : option (carrier (top_carrier (pair_space X)))) : Type@{o} :=
  match u, v with
  | Some x, Some y => ((x ≈ y) + (pair_sub X x ∧ pair_sub X y))%type
  | Some x, None => pair_sub X x
  | None, Some y => pair_sub X y
  | None, None => poly_unit@{o}
  end.

Lemma pquot_rel_Equivalence@{o} (X : PairTop@{o}) :
  Equivalence (pquot_rel X).
Proof.
  constructor.
  - intros [x|]; simpl; [left; reflexivity | exact ttt].
  - intros [x|] [y|] H; simpl in *; try exact H.
    destruct H as [H|[H1 H2]]; [left; now symmetry | right; exact (H2, H1)].
  - intros [x|] [y|] [z|] H1 H2; simpl in *; try exact ttt.
    + destruct H1 as [H1|[H1 H1']], H2 as [H2|[H2 H2']].
      * left; now transitivity y.
      * right; split;
          [ exact (pair_sub_proper X _ _ (symmetry H1) H2) | exact H2' ].
      * right; split; [ exact H1 | exact (pair_sub_proper X _ _ H2 H1') ].
      * right; exact (H1, H2').
    + destruct H1 as [H1|[H1 H1']].
      * exact (pair_sub_proper X _ _ (symmetry H1) H2).
      * exact H1.
    + right; exact (H1, H2).
    + exact H1.
    + destruct H2 as [H2|[H2 H2']].
      * exact (pair_sub_proper X _ _ H2 H1).
      * exact H2'.
    + exact H2.
Qed.

Definition pquot_setoid@{o} (X : PairTop@{o}) :
  Setoid@{o o} (option (carrier (top_carrier (pair_space X)))) := {|
  equiv := pquot_rel X;
  setoid_equiv := pquot_rel_Equivalence X
|}.

Definition pquot_carrier@{o} (X : PairTop@{o}) : SetoidObject@{o o} := {|
  carrier := option (carrier (top_carrier (pair_space X)));
  is_setoid := pquot_setoid X
|}.

Definition pquot_some@{o} (X : PairTop@{o}) :
  SetoidMorphism@{o o o} (top_carrier (pair_space X)) (pquot_carrier X) :=
  @Build_SetoidMorphism _ (is_setoid (top_carrier (pair_space X))) _
    (pquot_setoid X) (@Some _)
    (fun x y (e : x ≈ y) => (inl e : pquot_rel X (Some x) (Some y))).

(* X/A: the quotient topology of Instance/Top/Subspace/TypeValued.v along
   [Some], so an open is a predicate respecting the identification whose
   restriction to X is open. *)
Definition pquot_space@{o} (X : PairTop@{o}) : TopSpace@{o} :=
  TQuot (pair_space X) (pquot_carrier X) (pquot_some X).

Definition pquot_pointed@{o} (X : PairTop@{o}) : PointedTop@{o} :=
  @Build_PointedTop@{o} (pquot_space X) None.

Definition pquot_in@{h o | o < h +} (X : PairTop@{o}) :
  pair_space X ~{Top@{h o}}~> pquot_space X :=
  tquot_proj (pair_space X) (pquot_carrier X) (pquot_some X).

(** ** The functor ⟨X, A⟩ ↦ X/A *)

Definition pquot_fmap_map@{h o | o < h +} {X Y : PairTop@{o}}
  (f : X ~{Top_pairs@{h o}}~> Y) :
  SetoidMorphism@{o o o} (pquot_carrier X) (pquot_carrier Y).
Proof.
  unshelve notypeclasses refine
    (@Build_SetoidMorphism _ (pquot_setoid X) _ (pquot_setoid Y)
       (fun u => match u with
                 | Some x => Some (pair_map f x)
                 | None => None
                 end) _).
  intros [x|] [y|] H; simpl in *; try exact H.
  - destruct H as [H|[H1 H2]].
    + left; apply proper_morphism; exact H.
    + right; exact (pair_carries f _ H1, pair_carries f _ H2).
  - exact (pair_carries f _ H).
  - exact (pair_carries f _ H).
Defined.

Lemma pquot_fmap_cont@{h o | o < h +} {X Y : PairTop@{o}}
  (f : X ~{Top_pairs@{h o}}~> Y) :
  Continuous (pquot_space X) (pquot_space Y) (pquot_fmap_map f).
Proof.
  intros V [HVp HVo]; split.
  - intros u v e w.
    exact (HVp _ _ (proper_morphism (pquot_fmap_map f) u v e) w).
  - exact (continuity (pair_map f) _ HVo).
Qed.

Definition pquot_fmap@{h o | o < h +} {X Y : PairTop@{o}}
  (f : X ~{Top_pairs@{h o}}~> Y) :
  pquot_pointed X ~{Top_pointed@{h o}}~> pquot_pointed Y :=
  @Build_PointedMap@{h o} (pquot_pointed X) (pquot_pointed Y)
    (@Build_ContinuousMorphism@{h o} (pquot_space X) (pquot_space Y)
       (pquot_fmap_map f) (pquot_fmap_cont f))
    ttt.

Program Definition PairQuotient@{h o | o < h +} :
  Top_pairs@{h o} ⟶ Top_pointed@{h o} := {|
  fobj := pquot_pointed@{o};
  fmap := @pquot_fmap@{h o}
|}.
Next Obligation.
  intros X Y f g Hfg [x|]; simpl; [ left; exact (Hfg x) | exact ttt ].
Qed.
Next Obligation. intros X [x|]; simpl; [ left; reflexivity | exact ttt ]. Qed.
Next Obligation.
  intros X Y Z f g [x|]; simpl; [ left; reflexivity | exact ttt ].
Qed.

(** ** The hom-set bijection Top_*(X/A, Y) ≅ Top^(2)(⟨X, A⟩, ⟨Y, *⟩) *)

(* Restrict a based map out of X/A along [Some]. *)
Definition pquot_to@{h o | o < h +} (X : PairTop@{o}) (Y : PointedTop@{o})
  (p : pquot_pointed X ~{Top_pointed@{h o}}~> Y) :
  X ~{Top_pairs@{h o}}~> point_pair Y.
Proof.
  refine (@Build_PairMap@{h o} X (point_pair Y)
            (ptop_map p ∘[Top@{h o}] pquot_in X) _).
  intros x Hx; simpl.
  transitivity (ptop_map p None).
  - apply (proper_morphism (continuous_map (ptop_map p)) (Some x) None).
    exact Hx.
  - exact (ptop_preserves p).
Defined.

(* Extend a map of pairs by sending the new point to the basepoint. *)
Definition pquot_from_map@{h o | o < h +} (X : PairTop@{o})
  (Y : PointedTop@{o}) (g : X ~{Top_pairs@{h o}}~> point_pair Y) :
  SetoidMorphism@{o o o} (pquot_carrier X) (top_carrier (ptop_space Y)).
Proof.
  unshelve notypeclasses refine
    (@Build_SetoidMorphism _ (pquot_setoid X) _
       (is_setoid (top_carrier (ptop_space Y)))
       (fun u => match u with
                 | Some x => pair_map g x
                 | None => ptop_pt Y
                 end) _).
  intros [x|] [y|] H; simpl in *.
  - destruct H as [H|[H1 H2]].
    + apply proper_morphism; exact H.
    + transitivity (ptop_pt Y).
      * exact (pair_carries g _ H1).
      * symmetry; exact (pair_carries g _ H2).
  - exact (pair_carries g _ H).
  - symmetry; exact (pair_carries g _ H).
  - reflexivity.
Defined.

Definition pquot_from@{h o | o < h +} (X : PairTop@{o}) (Y : PointedTop@{o})
  (g : X ~{Top_pairs@{h o}}~> point_pair Y) :
  pquot_pointed X ~{Top_pointed@{h o}}~> Y :=
  @Build_PointedMap@{h o} (pquot_pointed X) Y
    (tquot_desc (pair_space X) (pquot_carrier X) (pquot_some X)
       (ptop_space Y) (pair_map g) (pquot_from_map X Y g)
       (fun x => reflexivity _))
    (reflexivity _).

Program Definition pairs_quotient_iso@{h o u | o < h, h < u +}
  (X : PairTop@{o}) (Y : PointedTop@{o}) :
  @Isomorphism Sets@{h u}
    {| carrier := @hom Top_pointed@{h o} (PairQuotient@{h o} X) Y;
       is_setoid := @homset Top_pointed@{h o} (PairQuotient@{h o} X) Y |}
    {| carrier := @hom Top_pairs@{h o} X (PointPair@{h o} Y);
       is_setoid := @homset Top_pairs@{h o} X (PointPair@{h o} Y) |} := {|
  to   := {| morphism := pquot_to@{h o} X Y |};
  from := {| morphism := pquot_from@{h o} X Y |}
|}.
Next Obligation. intros X Y p q H x; exact (H (Some x)). Qed.
Next Obligation.
  intros X Y p q H [x|]; simpl; [ exact (H x) | reflexivity ].
Qed.
Next Obligation. intros X Y g x; reflexivity. Qed.
Next Obligation.
  intros X Y p [x|]; simpl;
    [ reflexivity | symmetry; exact (ptop_preserves p) ].
Qed.

(* Construction 6: ⟨X, A⟩ ↦ X/A is left adjoint to Y ↦ ⟨Y, *⟩. *)
Definition pairs_quotient_adjunction@{h o u v | o < h, h < u +} :
  @Adjunction@{h h h h h h h h u h v} Top_pointed@{h o} Top_pairs@{h o}
    PairQuotient@{h o} PointPair@{h o}.
Proof.
  unshelve eapply (@Build_Adjunction' Top_pointed@{h o} Top_pairs@{h o}
                     PairQuotient@{h o} PointPair@{h o}
                     pairs_quotient_iso@{h o u}).
  - intros X Y Z f g x; reflexivity.
  - intros X Y Z f g x; reflexivity.
Defined.

(** ** Readbacks *)

Example PointPair_sub@{h o | o < h +} (Y : PointedTop@{o})
  (y : carrier (top_carrier (ptop_space Y))) :
  pair_sub (fobj[PointPair@{h o}] Y) y = (y ≈ ptop_pt Y) := eq_refl.

Example pquot_space_carrier@{h o | o < h +} (X : PairTop@{o}) :
  carrier (top_carrier (ptop_space (fobj[PairQuotient@{h o}] X)))
    = option (carrier (top_carrier (pair_space X))) := eq_refl.

Example pquot_basepoint@{h o | o < h +} (X : PairTop@{o}) :
  ptop_pt (fobj[PairQuotient@{h o}] X) = None := eq_refl.

Example pquot_space_open@{o} (X : PairTop@{o})
  (V : pquot_carrier X → Type@{o}) :
  IsOpen (pquot_space X) V
    = tquot_open (pair_space X) (pquot_carrier X) (pquot_some X) V
  := eq_refl.

Example pquot_to_eval@{h o | o < h +} (X : PairTop@{o}) (Y : PointedTop@{o})
  (p : pquot_pointed X ~{Top_pointed@{h o}}~> Y)
  (x : carrier (top_carrier (pair_space X))) :
  continuous_map (pair_map (pquot_to X Y p)) x
    = continuous_map (ptop_map p) (Some x) := eq_refl.

Example pquot_from_eval_some@{h o | o < h +} (X : PairTop@{o})
  (Y : PointedTop@{o}) (g : X ~{Top_pairs@{h o}}~> point_pair Y)
  (x : carrier (top_carrier (pair_space X))) :
  continuous_map (ptop_map (pquot_from X Y g)) (Some x)
    = continuous_map (pair_map g) x := eq_refl.

Example pquot_from_eval_none@{h o | o < h +} (X : PairTop@{o})
  (Y : PointedTop@{o}) (g : X ~{Top_pairs@{h o}}~> point_pair Y) :
  continuous_map (ptop_map (pquot_from X Y g)) None = ptop_pt Y := eq_refl.

Example pairs_quotient_unit_eval@{h o u v | o < h, h < u +}
  (X : PairTop@{o}) (x : carrier (top_carrier (pair_space X))) :
  continuous_map
    (pair_map (@unit _ _ _ _ pairs_quotient_adjunction@{h o u v} X)) x
    = Some x := eq_refl.

Example pairs_quotient_counit_some@{h o u v | o < h, h < u +}
  (Y : PointedTop@{o}) (y : carrier (top_carrier (ptop_space Y))) :
  continuous_map
    (ptop_map (@counit _ _ _ _ pairs_quotient_adjunction@{h o u v} Y)) (Some y)
    = y := eq_refl.

Example pairs_quotient_counit_none@{h o u v | o < h, h < u +}
  (Y : PointedTop@{o}) :
  continuous_map
    (ptop_map (@counit _ _ _ _ pairs_quotient_adjunction@{h o u v} Y)) None
    = ptop_pt Y := eq_refl.

Example pairs_quotient_adj_is@{h o u v | o < h, h < u +} (X : PairTop@{o})
  (Y : PointedTop@{o}) :
  @adj _ _ _ _ pairs_quotient_adjunction@{h o u v} X Y
    = pairs_quotient_iso@{h o u} X Y := eq_refl.

(** ** X/A is the pushout X ⊔_A ∗ *)

(* The points of A, with the equality of X, as a discrete space. *)
Lemma pair_sub_equiv_Equivalence@{o} (X : PairTop@{o}) :
  Equivalence (fun a b : collapse_sub_points (pair_space X) (pair_sub X) =>
                 projT1 a ≈ projT1 b).
Proof.
  constructor.
  - intro a; reflexivity.
  - intros a b H; symmetry; exact H.
  - intros a b c H1 H2; transitivity (projT1 b); assumption.
Qed.

Definition pair_sub_setoid@{o} (X : PairTop@{o}) : SetoidObject@{o o} := {|
  carrier := collapse_sub_points (pair_space X) (pair_sub X);
  is_setoid := {| equiv := fun a b => projT1 a ≈ projT1 b;
                  setoid_equiv := pair_sub_equiv_Equivalence X |}
|}.

Definition pair_sub_space@{o} (X : PairTop@{o}) : TopSpace@{o} :=
  Discrete_Top (pair_sub_setoid X).

Definition pair_sub_incl_map@{o} (X : PairTop@{o}) :
  SetoidMorphism@{o o o} (pair_sub_setoid X) (top_carrier (pair_space X)) :=
  @Build_SetoidMorphism _ (is_setoid (pair_sub_setoid X)) _
    (is_setoid (top_carrier (pair_space X))) (@projT1 _ _)
    (fun a b (e : projT1 a ≈ projT1 b) => e).

Definition pair_sub_incl@{h o | o < h +} (X : PairTop@{o}) :
  pair_sub_space X ~{Top@{h o}}~> pair_space X :=
  @Build_ContinuousMorphism@{h o} (pair_sub_space X) (pair_space X)
    (pair_sub_incl_map X)
    (out_of_discrete_continuous _ (pair_space X) (pair_sub_incl_map X)).

(* The new point, as a map from the one-point space. *)
Definition pquot_base@{h o | o < h +} (X : PairTop@{o}) :
  Point_Top@{o} ~{Top@{h o}}~> pquot_space X :=
  top_point@{h o} (pquot_space X) None.

Section Pushout.

Universes h o.
Constraint o < h.

Context (X : PairTop@{o}) {Q : Top@{h o}}
  (q1 : pair_space X ~{Top@{h o}}~> Q) (q2 : Point_Top@{o} ~{Top@{h o}}~> Q)
  (Hq : q1 ∘ pair_sub_incl X ≈ q2 ∘ top_one (pair_sub_space X)).

Definition pquot_po_map : SetoidMorphism@{o o o} (pquot_carrier X) Q.
Proof using X Q q1 q2 Hq.
  unshelve notypeclasses refine
    (@Build_SetoidMorphism _ (pquot_setoid X) _ (is_setoid (top_carrier Q))
       (fun u => match u with
                 | Some x => continuous_map q1 x
                 | None => continuous_map q2 ttt
                 end) _).
  assert (HA : ∀ x, pair_sub X x → q1 x ≈ q2 ttt).
  { intros x Hx. exact (Hq (x; Hx)). }
  intros [x|] [y|] H; simpl in *.
  - destruct H as [H|[H1 H2]].
    + apply proper_morphism; exact H.
    + transitivity (q2 ttt); [ exact (HA x H1) | symmetry; exact (HA y H2) ].
  - exact (HA x H).
  - symmetry; exact (HA y H).
  - reflexivity.
Defined.

Definition pquot_po_med : pquot_space X ~{Top@{h o}}~> Q :=
  tquot_desc (pair_space X) (pquot_carrier X) (pquot_some X) Q q1
    pquot_po_map (fun x => reflexivity _).

End Pushout.

Definition pquot_pushout@{h o | o < h +} (X : PairTop@{o}) :
  IsPushout (C := Top@{h o}) (pair_sub_incl X) (top_one (pair_sub_space X)).
Proof.
  unshelve refine (@Build_Pullback (Top@{h o}^op) _ _ _
                     (pair_sub_incl X) (top_one (pair_sub_space X))
                     (pquot_space X) (pquot_in X) (pquot_base X) _ _).
  - intro a; simpl. exact (projT2 a).
  - intros Q q1 q2 Hq.
    unshelve eapply Build_Unique.
    + exact (pquot_po_med X q1 q2 Hq).
    + split.
      * intro x; simpl. reflexivity.
      * intro t; simpl. destruct t. reflexivity.
    + intros v [Hv1 Hv2] [x|]; simpl.
      * symmetry; exact (Hv1 x).
      * symmetry; exact (Hv2 ttt).
Defined.

Example pquot_pushout_apex@{h o | o < h +} (X : PairTop@{o}) :
  pushout_apex (pquot_pushout@{h o} X) = pquot_space X := eq_refl.

(** ** X/A is the universal-arrow coequalizer of the point-inclusions *)

(* Read as a universal arrow to the diagonal functor (book pp. 64-65), the
   coequalizer of a set of maps a → b is a colimit over the shape that has
   a as a vertex, Structure/Coequalizer/Wide.v's [WideCoequalizer]; read
   elementarily (p. 64's display (6)), it is that file's
   [IsWideCoequalizer], and the two agree on every nonempty set of maps.
   The colimit's cocones have a leg out of * as well as one out of X, so
   no point of A is needed: the leg out of * is the new point. *)
Definition pquot_wide_legs@{o h | o < h +} (X : PairTop@{o}) (p : ParObj) :
  fobj[AWide@{h h h h h} (C := Top@{h o})
         (collapse_sub_family (pair_space X) (pair_sub X))] p
    ~{Top@{h o}}~> pquot_space X :=
  match p return
    fobj[AWide@{h h h h h} (C := Top@{h o})
           (collapse_sub_family (pair_space X) (pair_sub X))] p
      ~{Top@{h o}}~> pquot_space X with
  | ParX => pquot_base X
  | ParY => pquot_in X
  end.

Lemma pquot_wide_legs_coherence@{o h | o < h +} (X : PairTop@{o}) :
  ∀ (a b : ParObj)
    (k : b ~{WideParallel@{h h}
               (collapse_sub_points (pair_space X) (pair_sub X))}~> a),
    pquot_wide_legs X a
      ∘ fmap[AWide@{h h h h h} (C := Top@{h o})
               (collapse_sub_family (pair_space X) (pair_sub X))] k
    ≈ pquot_wide_legs X b.
Proof.
  intros a b k.
  destruct a, b; simpl in *.
  - intro t; simpl. exact ttt.
  - destruct k.
  - intro t; simpl. exact (projT2 k).
  - intro t; simpl. left; reflexivity.
Qed.

Definition pquot_wide_cocone@{o h | o < h +} (X : PairTop@{o}) :
  Cocone (AWide@{h h h h h} (C := Top@{h o})
            (collapse_sub_family (pair_space X) (pair_sub X))) :=
  @Build_Cone
    ((WideParallel@{h h}
        (collapse_sub_points (pair_space X) (pair_sub X)))^op)
    (Top@{h o}^op)
    ((AWide@{h h h h h} (C := Top@{h o})
        (collapse_sub_family (pair_space X) (pair_sub X)))^op)
    (pquot_space X)
    (@Build_ACone
       ((WideParallel@{h h}
           (collapse_sub_points (pair_space X) (pair_sub X)))^op)
       (Top@{h o}^op) (pquot_space X)
       ((AWide@{h h h h h} (C := Top@{h o})
           (collapse_sub_family (pair_space X) (pair_sub X)))^op)
       (pquot_wide_legs X) (pquot_wide_legs_coherence X)).

(* A cocone's two legs are a map out of X and a point absorbing A: the
   data of the pushout, whose mediator [pquot_po_med] is the one here. *)
Lemma pquot_wide_ump@{o h | o < h +} (X : PairTop@{o})
  (N : Cocone (AWide@{h h h h h} (C := Top@{h o})
                 (collapse_sub_family (pair_space X) (pair_sub X)))) :
  ∃! u : pquot_space X ~{Top@{h o}}~> vertex_obj[N],
    ∀ p : ParObj, u ∘ pquot_wide_legs X p ≈ cocone_inj N p.
Proof.
  assert (Hq : cocone_inj N ParY ∘ pair_sub_incl X
               ≈ cocone_inj N ParX ∘ top_one (pair_sub_space X)).
  { intro a.
    exact (cocone_inj_coherence N (a : ParX ~{WideParallel _}~> ParY) ttt). }
  unshelve eapply Build_Unique.
  - exact (pquot_po_med X (cocone_inj N ParY) (cocone_inj N ParX) Hq).
  - intros p; destruct p; intro t; simpl.
    + destruct t; reflexivity.
    + reflexivity.
  - intros v Hv [x|]; simpl.
    + symmetry; exact (Hv ParY x).
    + symmetry; exact (Hv ParX ttt).
Qed.

(* Construction 5 read as the universal arrow, for EVERY pair, the empty
   subset included: the colimit of the point-inclusions of A, the type of
   Instance/Top/Quotient.v's [collapse_colimit], with no point of A. *)
Definition pquot_wide_coequalizer_colimit@{o h | o < h +}
  (X : PairTop@{o}) :
  WideCoequalizer (AWide@{h h h h h} (C := Top@{h o})
                     (collapse_sub_family (pair_space X) (pair_sub X))) :=
  {| limit_cone := pquot_wide_cocone X;
     ump_limits := fun N => pquot_wide_ump X N |}.

Example pquot_wide_coequalizer_colimit_apex@{o h | o < h +}
  (X : PairTop@{o}) :
  colimit_apex (pquot_wide_coequalizer_colimit@{o h} X) = pquot_space X
  := eq_refl.

Example pquot_wide_coequalizer_colimit_in@{o h | o < h +}
  (X : PairTop@{o}) :
  colimit_inj (colimit_is_acolimit (pquot_wide_coequalizer_colimit@{o h} X))
    ParY = pquot_in X := eq_refl.

(* The leg out of * picks the left adjoint's basepoint. *)
Example pquot_wide_coequalizer_colimit_base@{o h | o < h +}
  (X : PairTop@{o}) :
  continuous_map
    (colimit_inj (colimit_is_acolimit (pquot_wide_coequalizer_colimit@{o h} X))
       ParX) ttt
    = ptop_pt (fobj[PairQuotient@{h o}] X) := eq_refl.

(* The left adjoint's value at every pair IS that colimit's apex. *)
Example pquot_wide_coequalizer_colimit_quotient@{o h | o < h +}
  (X : PairTop@{o}) :
  ptop_space (fobj[PairQuotient@{h o}] X)
    = colimit_apex (pquot_wide_coequalizer_colimit@{o h} X) := eq_refl.

(* Every colimit of the point-inclusions of a subset has a point, the image
   of * under its leg out of *, whether or not the subset has one. *)
Definition collapse_colimit_point@{o h | o < h +} (X : TopSpace@{o})
  (A : X → Type@{o})
  (L : WideCoequalizer (AWide@{h h h h h} (C := Top@{h o})
                          (collapse_sub_family X A))) :
  top_carrier (colimit_apex L) :=
  continuous_map (colimit_inj (colimit_is_acolimit L) ParX) ttt.

(** ** The elementary record, given a point of A *)

(* With a point [a0] of A in hand, X ~> X/A IS an elementary wide
   coequalizer of the point-inclusions of A. *)
Definition pquot_coequalizer@{o h i | o < h, o <= i +} (X : PairTop@{o})
  (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family (pair_space X) (pair_sub X))
    (pquot_space X) (pquot_in X).
Proof.
  unshelve econstructor.
  - intros [a Ha] [b Hb] t; simpl; right; exact (Ha, Hb).
  - intros Z k Hk.
    unshelve eapply Build_Unique.
    + refine (pquot_po_med X k (k ∘ top_point (pair_space X) (projT1 a0)) _).
      intro a; simpl. exact (Hk a a0 ttt).
    + intro x; reflexivity.
    + intros v Hv [x|]; simpl.
      * symmetry; exact (Hv x).
      * transitivity (continuous_map v (Some (projT1 a0))).
        -- symmetry; exact (Hv (projT1 a0)).
        -- apply (proper_morphism (continuous_map v) (Some (projT1 a0)) None).
           exact (projT2 a0).
Defined.

(* The two readings of X/A are isomorphic in [Top], by the identity on the
   points of X. *)
Definition pquot_collapse_iso@{o h u | o < h, h < u +} (X : PairTop@{o})
  (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  Top_collapse_sub (pair_space X) (pair_sub X) ≅[Top@{h o}] pquot_space X :=
  wide_coequalizer_unique _
    (collapse_coequalizer@{o h o} (pair_space X) (pair_sub X))
    (pquot_coequalizer@{o h o} X a0).

Example pquot_collapse_iso_to@{o h u | o < h, h < u +} (X : PairTop@{o})
  (a0 : collapse_sub_points (pair_space X) (pair_sub X))
  (x : carrier (top_carrier (pair_space X))) :
  continuous_map (to (pquot_collapse_iso X a0)) x = Some x := eq_refl.

Example pquot_collapse_iso_from_some@{o h u | o < h, h < u +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X))
  (x : carrier (top_carrier (pair_space X))) :
  continuous_map (from (pquot_collapse_iso X a0)) (Some x) = x := eq_refl.

Example pquot_collapse_iso_from_none@{o h u | o < h, h < u +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  continuous_map (from (pquot_collapse_iso X a0)) None = projT1 a0
  := eq_refl.

(* Construction 5's X/A, pointed at the point [a0] of A. *)
Definition collapse_pointed@{o} (X : PairTop@{o})
  (a0 : collapse_sub_points (pair_space X) (pair_sub X)) : PointedTop@{o} :=
  @Build_PointedTop@{o} (Top_collapse_sub (pair_space X) (pair_sub X))
    (projT1 a0).

(* The comparison as POINTED spaces: the value of the left adjoint at
   ⟨X, A⟩ is Construction 5's X/A pointed at [a0], up to isomorphism in
   [Top_pointed].  Both basepoint conditions hold by the readbacks above:
   [a0] goes to [Some (projT1 a0)], which lies with [None] because a0 is in
   A, and [None] goes back to [projT1 a0] itself. *)
Definition pquot_collapse_iso_pointed@{o h u | o < h, h < u +}
  (X : PairTop@{o}) (a0 : collapse_sub_points (pair_space X) (pair_sub X)) :
  collapse_pointed X a0 ≅[Top_pointed@{h o}] fobj[PairQuotient@{h o}] X :=
  @Build_Isomorphism Top_pointed@{h o} (collapse_pointed X a0)
    (fobj[PairQuotient@{h o}] X)
    (@Build_PointedMap@{h o} (collapse_pointed X a0)
       (fobj[PairQuotient@{h o}] X) (to (pquot_collapse_iso@{o h u} X a0))
       (projT2 a0))
    (@Build_PointedMap@{h o} (fobj[PairQuotient@{h o}] X)
       (collapse_pointed X a0) (from (pquot_collapse_iso@{o h u} X a0))
       (inl (reflexivity (projT1 a0))))
    (iso_to_from (pquot_collapse_iso@{o h u} X a0))
    (iso_from_to (pquot_collapse_iso@{o h u} X a0)).

(** ** The empty subset: X/∅ ≅ X₊; no pointed elementary coequalizer *)

Definition empty_pair@{o} (X : TopSpace@{o}) : PairTop@{o} :=
  @Build_PairTop@{o} X (fun _ => False) (fun _ _ _ f => f).

(* The collapse at ∅ has a genuinely new point ... *)
Lemma pquot_empty_new_point@{o} (X : TopSpace@{o})
  (x : carrier (top_carrier X)) :
  pquot_rel (empty_pair X) (Some x) None → False.
Proof. exact (fun f => f). Qed.

(* ... and is X with a disjoint point added, X₊ = X + 1. *)
Definition pquot_empty_sum_to@{o} (X : TopSpace@{o}) :
  SetoidMorphism@{o o o} (pquot_carrier (empty_pair X))
    (sum_carrier X Point_Top@{o}).
Proof.
  unshelve notypeclasses refine
    (@Build_SetoidMorphism _ (pquot_setoid (empty_pair X)) _
       (is_setoid (sum_carrier X Point_Top@{o}))
       (fun u => match u with
                 | Some x => Datatypes.inl x
                 | None => Datatypes.inr ttt
                 end) _).
  intros [x|] [y|] H; simpl in *.
  - destruct H as [H|[H _]]; [ exact H | destruct H ].
  - destruct H.
  - destruct H.
  - reflexivity.
Defined.

Definition pquot_empty_sum_from@{o} (X : TopSpace@{o}) :
  SetoidMorphism@{o o o} (sum_carrier X Point_Top@{o})
    (pquot_carrier (empty_pair X)).
Proof.
  unshelve notypeclasses refine
    (@Build_SetoidMorphism _ (is_setoid (sum_carrier X Point_Top@{o})) _
       (pquot_setoid (empty_pair X))
       (fun w => match w with
                 | Datatypes.inl x => Some x
                 | Datatypes.inr _ => None
                 end) _).
  intros [x|a] [y|b] H; simpl in *.
  - left; exact H.
  - destruct H.
  - destruct H.
  - exact ttt.
Defined.

Definition pquot_empty_sum_iso@{h o | o < h +} (X : TopSpace@{o}) :
  pquot_space (empty_pair X) ≅[Top@{h o}] Sum_Top X Point_Top@{o}.
Proof.
  unshelve refine (@Build_Isomorphism Top@{h o}
            (pquot_space (empty_pair X)) (Sum_Top X Point_Top@{o})
            (@Build_ContinuousMorphism@{h o} (pquot_space (empty_pair X))
               (Sum_Top X Point_Top@{o}) (pquot_empty_sum_to X) _)
            (@Build_ContinuousMorphism@{h o} (Sum_Top X Point_Top@{o})
               (pquot_space (empty_pair X)) (pquot_empty_sum_from X) _)
            _ _).
  - apply (snd (tquot_universal (pair_space (empty_pair X))
                  (pquot_carrier (empty_pair X)) (pquot_some (empty_pair X))
                  (Sum_Top X Point_Top@{o}) (pquot_empty_sum_to X))).
    exact (continuity (Top_inl X Point_Top@{o})).
  - intros V [_ HV]; split.
    + exact HV.
    + exact (open_const Point_Top@{o} (V None)).
  - intros [x|a]; simpl.
    + reflexivity.
    + destruct a; reflexivity.
  - intros [x|]; simpl.
    + left; reflexivity.
    + exact ttt.
Defined.

Example pquot_empty_sum_iso_some@{h o | o < h +} (X : TopSpace@{o})
  (x : carrier (top_carrier X)) :
  continuous_map (to (pquot_empty_sum_iso@{h o} X)) (Some x) = Datatypes.inl x
  := eq_refl.

Example pquot_empty_sum_iso_none@{h o | o < h +} (X : TopSpace@{o}) :
  continuous_map (to (pquot_empty_sum_iso@{h o} X)) None = Datatypes.inr ttt
  := eq_refl.

(* So, read as the universal arrow, the coequalizer of the empty family of
   point-inclusions, the colimit above at ⟨X, ∅⟩, is X ⊔ ∗. *)
Definition pquot_wide_coequalizer_colimit_empty@{o h | o < h +}
  (X : TopSpace@{o}) :
  colimit_apex (pquot_wide_coequalizer_colimit@{o h} (empty_pair X))
    ≅[Top@{h o}] Sum_Top X Point_Top@{o} :=
  pquot_empty_sum_iso@{h o} X.

(* The elementary record at ⟨∅, ∅⟩ is not met by this X/A ... *)
Lemma pquot_empty_not_coequalizer@{o h i | o < h, o <= i +} :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family (pair_space (empty_pair Empty_Top@{o}))
       (pair_sub (empty_pair Empty_Top@{o})))
    (pquot_space (empty_pair Empty_Top@{o}))
    (pquot_in (empty_pair Empty_Top@{o})) → False.
Proof.
  intro E.
  destruct (wcoeq_desc E (@id Top@{h o} Empty_Top@{o})
              (fun i => match projT2 i with end)) as [u _ _].
  exact (continuous_map u None).
Qed.

(* ... so [pquot_coequalizer]'s point of A cannot be dropped. *)
Lemma pquot_coequalizer_needs_point@{o h i | o < h, o <= i +} :
  (∀ X : PairTop@{o},
     IsWideCoequalizer@{i h h} (C := Top@{h o})
       (collapse_sub_family (pair_space X) (pair_sub X))
       (pquot_space X) (pquot_in X)) → False.
Proof.
  intro H.
  exact (pquot_empty_not_coequalizer@{o h i} (H (empty_pair Empty_Top@{o}))).
Qed.

(** ** The elementary record and the colimit part at the empty subset *)

(* No pointed space's underlying space is an elementary wide coequalizer
   of the empty family of point-inclusions at the empty space: its
   basepoint would be a point of it, which Instance/Top/Quotient.v's
   [empty_wide_coequalizer_pointless] refutes. *)
Lemma no_pointed_coequalizer_at_empty@{o h i | o < h, o <= i +}
  (Q : PointedTop@{o}) (e : Empty_Top@{o} ~{Top@{h o}}~> ptop_space Q) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family Empty_Top@{o} (fun _ => False)) (ptop_space Q) e →
  False.
Proof.
  intro E.
  exact (empty_wide_coequalizer_pointless@{o h i} (ptop_space Q) e E
           (ptop_pt Q)).
Qed.

(* Hence no assignment of a pointed space to each pair, a functor or any
   other function on objects, makes every underlying space an elementary
   wide coequalizer of the point-inclusions: at ⟨∅, ∅⟩ there is none.  The
   colimit form is met by [PairQuotient] at every pair
   ([pquot_wide_coequalizer_colimit_quotient]). *)
Lemma no_pointed_elementary_coequalizers@{o h i | o < h, o <= i +}
  (L : PairTop@{o} → PointedTop@{o}) :
  (∀ X : PairTop@{o}, ∃ e : pair_space X ~{Top@{h o}}~> ptop_space (L X),
     IsWideCoequalizer@{i h h} (C := Top@{h o})
       (collapse_sub_family (pair_space X) (pair_sub X)) (ptop_space (L X)) e)
  → False.
Proof.
  intro H.
  destruct (H (empty_pair Empty_Top@{o})) as [e E].
  exact (no_pointed_coequalizer_at_empty@{o h i} _ e E).
Qed.

(* At the empty family the two forms part: no colimit's apex carries an
   elementary wide coequalizer of the family at ∅, since the colimit has a
   point ([collapse_colimit_point]) and the elementary one has none. *)
Lemma empty_colimit_not_elementary@{o h i | o < h, o <= i +}
  (L : WideCoequalizer (AWide@{h h h h h} (C := Top@{h o})
                          (collapse_sub_family Empty_Top@{o}
                             (fun _ => False))))
  (e : Empty_Top@{o} ~{Top@{h o}}~> colimit_apex L) :
  IsWideCoequalizer@{i h h} (C := Top@{h o})
    (collapse_sub_family Empty_Top@{o} (fun _ => False)) (colimit_apex L) e →
  False.
Proof.
  intro E.
  exact (empty_wide_coequalizer_pointless@{o h i} (colimit_apex L) e E
           (collapse_colimit_point Empty_Top@{o} (fun _ => False) L)).
Qed.
