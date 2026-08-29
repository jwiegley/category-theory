Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Quotient.
Require Import Category.Structure.Discrete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Groupoid.Connected.
Require Import Category.Instance.Zero.
Require Import Category.Instance.One.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Roof.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

(** * Connected components: π₀ of a category *)

(* nLab:      https://ncatlab.org/nlab/show/connected+category
   nLab:      https://ncatlab.org/nlab/show/connected+component
   nLab:      https://ncatlab.org/nlab/show/full+subcategory
   Wikipedia: https://en.wikipedia.org/wiki/Connected_category
   Book:      Riehl, "Category Theory in Context", Dover 2016, §1.5,
              printed p. 35 (the running definition of a connected
              category) and Proposition 1.5.13, printed pp. 35-36
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, §I.5, printed p. 20 (the remark following Definition 9)

   A category is CONNECTED when any two of its objects are joined by a
   finite zig-zag of morphisms.  The relation "there is a zig-zag from x to
   y" is an equivalence relation on the objects, and the quotient by it is
   the SET OF CONNECTED COMPONENTS, written π₀.  Classically every category
   is the disjoint union of its components, each of which is connected;
   that is the sense in which connectedness is not a restriction but a
   decomposition.  Only the second half of that sentence is proved below
   ([Component_Connected]); see the NOT-delivered list for the first.

   This file builds π₀ and the components.  It does NOT build the zig-zag
   relation: that already exists. *)

(** ** What is consumed, and the correction that goes with it

   [ZigZag], [Connected] and the whole zig-zag calculus are CONSUMED from
   Structure/Groupoid/Connected.v.  Nothing below redeclares them.  What is
   there, checked against that file rather than taken on report:

     [ZigZag] (:122)          the inductive chain, with constructors
                              [zz_nil], [zz_fwd] and [zz_bwd]
     [Connected] (:133)       ∀ x y : C, ZigZag x y
     [hom_zigzag] (:137)      a single arrow as a one-step chain
     [arrow_connected] (:140) the one-arrow form implies the zig-zag form
     [zigzag_trans] (:147)    chains compose end to end
     [zigzag_sym] (:158)      chains reverse
     [Fence] (:170)           the strictly alternating form, with
                              [fence_zigzag] (:180) and [zigzag_fence]
                              (:190) converting both ways
     [zigzag_hom] (:203)      collapse to one arrow in a groupoid
     [connected_arrow] (:211) and [connected_iso] (:216)
     [WideDeloop] (:339)      with [WideDeloop_Connected] (:380)
     [Roof_Connected] (:431)  a connected category that is not a groupoid
     [Two_Discrete_zigzag_endpoints] (:507) and
     [Two_Discrete_not_connected] (:516)

   Three further files consume [Connected] already:
   Structure/Groupoid/Basepoint.v (:319, as a section hypothesis),
   Construction/Deloop/Transform.v (:987, :1012) and
   Instance/Top/FundamentalGroupoid.v, which declares [PathConnected]
   (:1092) and [pathconnected_Connected] (:1094).

   THE SOURCE ISSUE'S "Current state" IS STALE, AND IN THE STRONGEST WAY:
   it reports that a whole-tree search for the identifier [Connected]
   returns no hits and that "there is no π₀, no zig-zag relation on
   objects", and proposes building the relation together with its
   reflexivity, symmetry and transitivity from scratch.  Searching the `.v`
   files: [ZigZag] occurs in exactly ONE, the file that declares it; the
   word [Connected] occurs in FIVE, of which one declares it, three use it
   in statements (Structure/Groupoid/Basepoint.v:319,
   Construction/Deloop/Transform.v:987 and :1012,
   Instance/Top/FundamentalGroupoid.v:1095, :1434, :1496) and one —
   Structure/Groupoid.v:55, :91 — matches only because the file PATH
   `Structure/Groupoid/Connected.v` appears in a comment there.  So the
   issue's item 1, and the reflexivity/symmetry/transitivity HALF of its
   item 2, were already discharged before this file was written, and
   re-declaring them here would have produced a second, incompatible
   zig-zag type.  Item 2's OTHER half — "and that it is preserved by every
   functor" — was NOT discharged, and is [zigzag_fmap] below; the next
   paragraph says exactly that, and an earlier draft of this one claimed
   the whole of item 2 was already done, contradicting it.

   What that same search shows to be genuinely ABSENT is narrower and is
   what this file supplies:

     - no action of a functor on zig-zags: [ZigZag] is named nowhere
       outside its own file, so no such action can exist under any name
       that mentions it, and no statement of the shape "F carries a chain
       to a chain" occurs;
     - no π₀ OF A CATEGORY, and no components construction on a category.
       The nearest prior art is Instance/FinSet/Pushout.v:275's
       [components], a union-find fold over a LIST OF EDGES on [Fin.t N]
       computing the connected components of a finite graph, used to build
       pushouts in skeletal FinSet.  Its input is an edge list and not a
       category, its output is an idempotent labelling — a chosen
       representative per class, whose fibres are the components — rather
       than a coarsened setoid, and it decides class membership through
       [fin_eqb], which nothing below can do.  The other declared names in
       the tree matching `component` are the components of natural
       transformations and of isomorphisms, together with
       Instance/Comp.v:462's [Component] and that file's [component_id] and
       [component_compose], and the [components_*] lemmas about the fold
       just described; none of them is π₀;
     - no subcategory spanned by a zig-zag class. *)

(* Why the principal construction is called [pi0]

   The quotient built below is a SET — an object of [Sets], one point per
   component.  Calling it [Components] would suggest a collection of
   subcategories, which is a different object and is what
   [ConnectedComponent] names in the fourth section.  π₀ is the universal
   name for the set, is unambiguous, and keeps the two apart.  There is no
   in-tree collision: before this file no `pi0`, `Pi0` or
   [ConnectedComponent] was declared anywhere.  [Instance/Comp.v:462] does
   declare a [Component] — a SOFTWARE component, a map from required
   interfaces to provided ones — which is
   why the category below is [ConnectedComponent] and not [Component]; the
   two would otherwise collide in the single scope the [print-assumptions]
   target audits in. *)

(* Universes, measured in the constraint blocks

   THE EXPLICIT BINDERS ARE LOAD-BEARING IN THREE PLACES, and in each the
   measurement is discriminating: the same body without them is strictly
   worse and nothing else about it changes.

   (1) [zigzag_fmap].  Written unannotated the fixpoint elaborates at
   [∀ {C : Category@{u0 u1 u1}} {D : Category@{u u1 u1}}] — the two
   categories' HOM universes IDENTIFIED, on an empty constraint block, so
   reading the block alone would report no identification at all.  The
   annotated form's block is literally [hc <= hd], which is [Functor]'s
   own constraint, and it applies to a functor between categories whose hom
   universes are declared strictly apart.  The identification was
   minimization, not content, and it propagates: with it [pi0_fmap] carries
   [hc = hd]; without it, [hc <= hd] together with [hc <= o] and [hd <= o] —
   those being the constraints that bear on the point rather than the whole
   block, which also carries [o < so] and five bounds against stdlib
   donors.

   (2) [pi0_proj].  Unannotated the same body elaborates at
   [∀ C : Category@{u u u}] — ALL THREE of C's universes identified — and
   is then rejected at a category declared with its homs strictly below its
   objects, with "Cannot enforce vh = vo".  Annotated, [h <= o] is the only
   constraint relating C's own two levels that
   survives, and [pi0_proj Sets] is formable: [Sets@{o so}] IS
   [Category@{so o o}] and so has exactly the shape the unannotated form
   rejects.

   (3) [ObjSetoid] takes FOUR binders rather than three, so that the
   setoid's relation universe is not C's proof universe.  Two comparisons,
   both with an otherwise identical body: taking the setoid packaged from
   Lib/Setoid.v:65's [eq_Setoid] returns [SetoidObject@{o o}] — carrier and
   relation identified — because [eq_Setoid@{u}] carries one binder and
   returns [Setoid@{u u}], where Lib/Setoid.v:47's [eq_equivalence@{o q}]
   carries two; and reusing C's own proof universe in place of the fresh
   fourth one makes [pi0_coarser] elaborate with [o = h] where the shipped
   form leaves [h <= o].  So the binder, not merely the annotation on
   [pi0_proj], is doing the work.

   THE SAME CAUSE FORCES AN IDENTIFICATION, AND IT HIDES IN A BINDER — the
   very trap this block names two paragraphs up, met here by this file's own
   [pi0_fmap].  Its binder reads
   [{C : Category@{o hc hc}} {D : Category@{o hd hd}}]: the level [o] is
   written TWICE, so the two categories' OBJECT universes are IDENTIFIED,
   while its constraint block contains no equation at all — a reader who
   checks only the block concludes there is none and is wrong.  [Pi0]
   inherits it.  It is FORCED rather than a minimization accident, and that
   is measured rather than assumed: restating the same body with the object
   universes declared apart puts [oc = od] INTO the constraint block.  The
   cause is the one named next.

   WHAT DOES NOT GO AWAY, and is not this file's doing: both endpoints of a
   morphism of [Sets] live in [obj[Sets@{o so}]], which is
   [SetoidObject@{o o}] — a setoid's carrier universe identified with its
   relation universe.  [ZigZag@{o h}] lands at [Type@{max(o, h)}], so every
   [Sets]-level statement here — [pi0_proj], [pi0_fmap], [Pi0] — carries
   [h <= o]: the homs of the categories it speaks about sit at or below
   their objects.  That is [Sets]' own object type, the restriction
   Structure/Kernel/Universal.v records from the other side, and no route
   around it is attempted here.  It is a BOUND and not an identification,
   and [pi0] itself, which never mentions [Sets], restricts C not at all:
   [pi0@{u u0 u1 u2} : Category@{u u2 u2} → SetoidObject@{u u0}] with
   [u <= u0] and [u2 <= u0] and no equation.

   TWO INHERITED IDENTIFICATIONS are named rather than repaired, and
   neither is claimed unavoidable.  [ZigZag@{u u0}] is declared over
   [Category@{u u0 u0}], identifying C's hom and proof universes; that is
   the donor's, and everything below inherits it.  And [eso_connected]
   keeps [hc = hd] even annotated, which is [EssentiallySurjective]'s
   doing — its instance there is [EssentiallySurjective@{od oc hc}], using
   C's hom universe where D's arrows live.  By contrast
   [connected_image@{k oc od hc hd}] IDENTIFIES neither object universe with
   anything — its whole block is [oc <= k], [hc <= k], [hc <= hd], so one
   object universe is BOUNDED and the other unconstrained; "free of any
   identification" is the accurate reading, not "bounds the homs only" —
   and neither [zigzag_fmap], [ConnectedComponent]
   nor [ConnectedNonempty] contains a universe equation. *)

(* Strengths, measured [eq_refl] first

   HELD.  None is [t = t] with a notation expanded on one side.  Seven name
   the constant they are about against a DONOR constant; the other two,
   [pi0_proj_at] and [pi0_fmap_at], name it against a bound variable
   (applied, in the second case), which is equally not a tautology but is a
   different shape that the earlier blanket phrasing did not cover:

     [zigzag_fmap_hom]     the image of a one-step chain is the one-step
                           chain on the image arrow
     [pi0_carrier]         carrier (pi0 C) = obj[C]
     [pi0_equiv]           the quotient's `≈` IS [ZigZag]
     [pi0_proj_at]         the projection is the identity on objects
     [pi0_fmap_at]         the induced map IS the object action of F
     [Pi0_obj]             fobj[Pi0] C = pi0 C
     [component_sobj]      the selected objects ARE the zig-zag class
     [component_obj_type]  obj[ConnectedComponent C x] = ∃ y, ZigZag x y
     [Component_Incl_obj]  the inclusion IS the first projection

   MEASURED AND REJECTED, not guarded here — this file carries no [Fail],
   a probe being the place for that:

     [zigzag_fmap Id[C] s = s] at a VARIABLE chain [s].  [zigzag_fmap]
     recurses on the chain, so at a variable it is stuck and rebuilds
     nothing.  The conversion [fobj[Id[C]] x = x] DOES hold and the
     statement DOES close by [eq_refl] at [zz_nil x], which locates the
     failure at the recursion rather than at [Id].  Proved by induction as
     [zigzag_fmap_id].

     [zigzag_fmap (G ◯ F) s = zigzag_fmap G (zigzag_fmap F s)] likewise: at
     a variable chain rejected, at [zz_nil x] accepted, proved by induction
     as [zigzag_fmap_compose].

     The [proper_morphism] field of [pi0_fmap] supplied as a record-literal
     assignment [proper_morphism := @zigzag_fmap C D F].  The two types are
     CONVERTIBLE and the very same certificate is accepted when supplied by
     a one-step script, so what is rejected is unification through [Proper]
     and [respectful], not the term — the shape
     Instance/Sets/Quotient.v:243-248 records at [sets_quot_proj]. *)

(* STATUS: axiom-free.  95 constants — 80 named, 12 [Program] obligations,
   the two projections [cn_obj] and [cn_zigzag], and the constructor
   [Build_ConnectedNonempty] — each measured separately by [Print
   Assumptions] at its fully qualified name, all 95 reporting "Closed under
   the global context".  READ THE GRADE: that is a ONE-TIME measurement of
   all 95; the [make print-assumptions] gate carries FORTY of them
   permanently, the other 55 being measured once here.  [Print Module] lists
   94 of them, omitting only the constructor, and renders the [Qed] results
   as opaque declarations, a display convention and not an axiom.  Note
   that it WRAPS the [Record] line, so a line-anchored sweep of its output
   reports 93 and misses [ConnectedNonempty] — the counting hazard this
   tree records elsewhere for universe instances, met here at a record. *)

(* What is NOT delivered

     - NO DECISION PROCEDURE.  [ZigZag] is proof-relevant data, and nothing
       here decides whether two objects are joined; the negative results
       below each go through an invariant of the ambient category, never
       through an analysis of chains.

     - NO NORMAL FORM for zig-zags.  [zigzag_fmap_id] and
       [zigzag_fmap_compose] are proved by induction and not by any
       canonical-form argument, and no two chains between the same pair of
       objects are ever identified.

     - NO DISJOINT-UNION THEOREM.  Every object lies in the component of
       itself and every component is connected ([Component_Connected]), but
       nothing here exhibits C as a coproduct of its components in the
       sense of Construction/Coproduct/Indexed.v: that would need the
       components indexed by [carrier (pi0 C)], which is a family of
       categories over a setoid, and no such indexing is built.

     - NO π₀ OF A GROUPOID as a set of isomorphism classes, and no
       comparison with Theory/Skeleton.v.

     - NO LEFT ADJOINT.  [Pi0 : Cat ⟶ Sets] is built, but the discrete
       functor [Sets ⟶ Cat] and the adjunction π₀ ⊣ discrete are not.

     - NO CONNECTED LIMITS.  The reason connected index categories matter —
       that a connected limit of a diagram of a certain shape is computed
       from any one component — is not touched.

     - NO REFLECTION.  Nothing says that a functor with any property
       carries [Connected D] back to [Connected C]; only the forward
       direction is treated.  And the surjectivity hypothesis of
       [eso_connected] is not merely convenient: dropping it makes the
       statement FALSE, which [image_connected_not_connected] witnesses.
       Whether some weaker hypothesis than essential surjectivity suffices
       is neither proved nor refuted.

     - NO ISOMORPHISM OF COMPONENTS.  [Component_reindex_equiv] relates the
       components at two joined representatives by an EQUIVALENCE only, and
       the obstruction is described where it is built; no statement in
       [StrictCat] is attempted.

     - NO NATURALITY OF THE PROJECTION.  [pi0_proj] is built pointwise in
       C; [ObjSetoid] is not exhibited as a functor [Cat ⟶ Sets], so the
       projection is not a natural transformation to [Pi0].

     - NO INVARIANCE OF π₀ UNDER EQUIVALENCE.  [equivalence_connected]
       transports CONNECTEDNESS along an equivalence, but nothing here
       states [C ≃ D → pi0 C ≅ pi0 D], which is the first thing a reader
       handed [Pi0 : Cat ⟶ Sets] will look for.  Nor is [pi0 C] compared
       with [pi0 (C^op)], and the [DiscreteCat bool] witness gets only
       [pi0_bool_separates] (two points are distinct) rather than "exactly
       two components".

     - NO [Fence] ANALOGUE.  Everything below is stated with [ZigZag]; the
       alternating form is never used, though the donor's conversions make
       every statement transportable to it. *)

(** ** Functors carry zig-zags to zig-zags *)

(* A functor sends each step of a chain to a step of the same direction.
   This is the piece that was missing: the donor file has the chain, its
   composition and its reversal, but no action of a functor on it.

   The recursion is on the chain and nothing else — no functor law is
   consumed, only [fmap] itself.  In particular this holds for an arbitrary
   functor, with no fullness, faithfulness or surjectivity hypothesis.

   The universe binders are spelled out because minimization identifies the
   two categories' hom universes here, and that identification propagates
   to [pi0_fmap] downstream; see the universe block in the header, where
   the two forms are compared. *)
Fixpoint zigzag_fmap@{oc od hc hd} {C : Category@{oc hc hc}}
  {D : Category@{od hd hd}} (F : C ⟶ D) {x y : C}
  (s : ZigZag@{oc hc} x y) : ZigZag@{od hd} (F x) (F y) :=
  match s in ZigZag a b return ZigZag@{od hd} (F a) (F b) with
  | zz_nil w    => zz_nil (F w)
  | zz_fwd f s' => zz_fwd (fmap[F] f) (zigzag_fmap F s')
  | zz_bwd f s' => zz_bwd (fmap[F] f) (zigzag_fmap F s')
  end.

(* The image of a one-step chain is the one-step chain on the image arrow,
   ON THE NOSE.  Both sides mention [zigzag_fmap] and [hom_zigzag], so the
   statement is not [t = t] with the notation expanded on one side. *)
Example zigzag_fmap_hom {C D : Category} (F : C ⟶ D) {x y : C} (f : x ~> y) :
  zigzag_fmap F (hom_zigzag f) = hom_zigzag (fmap[F] f) := eq_refl.

(* Functoriality of the action.  These are NOT [eq_refl]: [zigzag_fmap]
   recurses on its chain argument, so at a variable chain it is stuck.
   Both statements were measured at [eq_refl] and REJECTED (measured and
   rejected, not guarded here — no [Fail] appears in this file), and both
   DO close by [eq_refl] at the empty chain [zz_nil x], which is what
   locates the failure at the recursion: the conversions
   [fobj[Id[C]] x = x] and [fobj[G ◯ F] x = fobj[G] (fobj[F] x)] both
   hold, and it is only the rebuilding of a variable chain that does not
   reduce. *)
Lemma zigzag_fmap_id {C : Category} {x y : C} (s : ZigZag x y) :
  zigzag_fmap Id[C] s = s.
Proof.
  induction s; simpl; [ reflexivity | f_equal; exact IHs | f_equal; exact IHs ].
Qed.

Lemma zigzag_fmap_compose {C D E : Category} (G : D ⟶ E) (F : C ⟶ D)
  {x y : C} (s : ZigZag x y) :
  zigzag_fmap (G ◯ F) s = zigzag_fmap G (zigzag_fmap F s).
Proof.
  induction s; simpl; [ reflexivity | f_equal; exact IHs | f_equal; exact IHs ].
Qed.

(* The action is compatible with the donor's two chain operations. *)
Lemma zigzag_fmap_trans {C D : Category} (F : C ⟶ D) {x y z : C}
  (s : ZigZag x y) (t : ZigZag y z) :
  zigzag_fmap F (zigzag_trans s t)
    = zigzag_trans (zigzag_fmap F s) (zigzag_fmap F t).
Proof.
  induction s; simpl; [ reflexivity | f_equal; apply IHs | f_equal; apply IHs ].
Qed.

Lemma zigzag_fmap_sym {C D : Category} (F : C ⟶ D) {x y : C}
  (s : ZigZag x y) :
  zigzag_fmap F (zigzag_sym s) = zigzag_sym (zigzag_fmap F s).
Proof.
  induction s; simpl.
  - reflexivity.
  - rewrite zigzag_fmap_trans, IHs; reflexivity.
  - rewrite zigzag_fmap_trans, IHs; reflexivity.
Qed.

(* What a functor out of a connected category gives, stated at exactly the
   strength it has: any two objects IN THE IMAGE are joined.  Read the
   quantifier carefully — [x] and [y] range over C, not over D, so this
   says nothing about objects of D outside the image, and it is NOT
   [Connected D].  The gap is real and is witnessed below by
   [image_connected_not_connected]: the point category is connected, the
   two-element discrete category is not, and there is a functor from the
   first to the second. *)
Definition connected_image@{k oc od hc hd} {C : Category@{oc hc hc}}
  {D : Category@{od hd hd}} (F : C ⟶ D) (K : Connected@{k oc hc} C)
  (x y : C) : ZigZag@{od hd} (F x) (F y) := zigzag_fmap F (K x y).

(* Surjectivity is what closes the gap, and essential surjectivity is
   enough: an object of D is joined to the image of its chosen preimage by
   the one-step chain on the isomorphism, and the two images are joined by
   [connected_image]. *)
Definition eso_connected@{k l oc od hc hd} {C : Category@{oc hc hc}}
  {D : Category@{od hd hd}} (F : C ⟶ D)
  (E : EssentiallySurjective F) (K : Connected@{k oc hc} C) :
  Connected@{l od hd} D :=
  fun d e =>
    zz_bwd (to (eso_iso d))
      (zigzag_trans (connected_image F K (eso_obj d) (eso_obj e))
                    (zz_fwd (to (eso_iso e)) (zz_nil e))).

(* Hence connectedness is invariant under equivalence of categories.  The
   only field of [EquivalenceOfCategories] consumed is its essential
   surjectivity. *)
Definition equivalence_connected {C D : Category} (F : C ⟶ D)
  (E : EquivalenceOfCategories F) (K : Connected C) : Connected D :=
  eso_connected F (Equivalence_EssSurj E) K.

(** ** π₀ as a setoid *)

(* The three chain operations of the donor file are exactly the three
   fields of an equivalence relation.  [zz_nil] is reflexivity, [zigzag_sym]
   is symmetry and [zigzag_trans] is transitivity, each passed through
   unchanged: this constant introduces no proof content of its own. *)
Definition zigzag_Equivalence (C : Category) : Equivalence (@ZigZag C) :=
  {| Equivalence_Reflexive  := @zz_nil C
   ; Equivalence_Symmetric  := @zigzag_sym C
   ; Equivalence_Transitive := @zigzag_trans C |}.

(* The object type of C as a setoid under Leibniz equality — the finest
   equality on it, so that the quotient below genuinely coarsens.

   THE FOURTH UNIVERSE BINDER IS LOAD-BEARING AND WAS MEASURED, NOT
   GUESSED, in two separate comparisons.  (i) Building the same object from
   Lib/Setoid.v:65's [eq_Setoid] returns [SetoidObject@{o o}], IDENTIFYING
   the carrier universe with the universe of the equality proofs, because
   [eq_Setoid@{u}] carries a single binder and returns [Setoid@{u u}];
   Lib/Setoid.v:47's [eq_equivalence@{o q}] carries two.  The two bodies
   differ only in whether the setoid is taken packaged or spelled out over
   that donor, so the difference is attributable to it.  (ii) Reusing C's
   OWN proof universe [p] in place of a fresh [q] — a three-binder variant
   with an otherwise identical body — makes [pi0_coarser] below elaborate
   with [o = h], where the four-binder form leaves [h <= o].  So the extra
   binder, and not merely the annotation on [pi0_proj], is what lets these
   constructions reach a category whose homs sit strictly below its
   objects. *)
Definition ObjSetoid@{o h p q} (C : Category@{o h p}) : SetoidObject@{o q} :=
  {| carrier   := obj[C]
   ; is_setoid := {| equiv        := @eq obj[C]
                   ; setoid_equiv := @eq_equivalence@{o q} obj[C] |} |}.

(* π₀ of C: the objects of C with "joined by a zig-zag" as the equality.

   This is Instance/Sets/Quotient.v:232's [SetsQuotient] applied directly —
   [ZigZag] is already a [crelation] on [obj[C]], so no encoding step
   intervenes.  Per the house discipline of that file the CARRIER IS
   UNTOUCHED and only `≈` is coarsened; the two readbacks below record
   that. *)
Definition pi0 (C : Category) : SetoidObject :=
  SetsQuotient (ObjSetoid C) (@ZigZag C) (zigzag_Equivalence C).

(* The carrier of π₀ IS the object type, and its equality IS the zig-zag
   relation, both by conversion.  Neither statement is a tautology: each
   names [pi0] on one side and a donor constant on the other. *)
Example pi0_carrier (C : Category) : carrier (pi0 C) = obj[C] := eq_refl.

Example pi0_equiv (C : Category) (x y : C) :
  @equiv _ (pi0 C) x y = ZigZag x y := eq_refl.

(* Leibniz-equal objects are joined, by the empty chain.  This is the
   [SetoidCoarser] hypothesis of Instance/Sets/Quotient.v:181, and it is
   the only thing the projection needs beyond the equivalence. *)
Definition pi0_coarser@{o h} (C : Category@{o h h}) :
  SetoidCoarser@{o o o o} (A:=ObjSetoid@{o h h o} C) (@ZigZag@{o h} C) :=
  fun x y (e : x = y) =>
    match e in _ = z return ZigZag x z with eq_refl => zz_nil x end.

(* The projection sending an object to its component, as a morphism of
   [Sets].

   THE EXPLICIT BINDERS HERE ARE LOAD-BEARING, MEASURED AS FOLLOWS.
   Written without them the same body elaborates at
   [∀ C : Category@{u u u}, ...] — all three of C's universes identified —
   and is then REJECTED at a category declared with its homs strictly below
   its objects, with "Cannot enforce vh = vo".  With the binders written
   out only [h <= o] survives, and [pi0_proj Sets] is formable, [Sets@{o so}]
   being [Category@{so o o}].  The identification was therefore
   MINIMIZATION and not content.  What does NOT go away is [h <= o]: the
   source and target of a [Sets]-morphism are both [SetoidObject@{o o}], so
   the relation universe is forced down to the carrier's, and [ZigZag]
   lands at [max(o, h)].  That constraint is [Sets]' own object type, not
   this file's, and no attempt is made here to route around it. *)
Definition pi0_proj@{o so h} (C : Category@{o h h}) :
  ObjSetoid@{o h h o} C ~{Sets@{o so}}~> pi0@{o o o h} C :=
  sets_quot_proj@{so o} (ObjSetoid@{o h h o} C) (@ZigZag@{o h} C)
    (zigzag_Equivalence@{o o h} C) (pi0_coarser@{o h} C).

(* ... and it is the identity on underlying objects, by conversion. *)
Example pi0_proj_at (C : Category) (x : C) : pi0_proj C x = x := eq_refl.

(* π₀ is functorial, and [zigzag_fmap] is exactly the respectfulness
   clause: a map on components is a map on objects that carries joined
   objects to joined objects.

   The certificate is supplied by a one-step script rather than as a field
   of the record literal, for the reason Instance/Sets/Quotient.v:243-248
   records at [sets_quot_proj]: [Proper (equiv ==> equiv) fobj[F]] is
   CONVERTIBLE with the type of [zigzag_fmap F] but the elaborator does not
   unfold [Proper] and [respectful] during unification, so the field
   assignment is rejected.  (Measured here too, at exactly that spot.) *)
Definition pi0_fmap@{o so hc hd} {C : Category@{o hc hc}}
  {D : Category@{o hd hd}} (F : C ⟶ D) :
  pi0@{o o o hc} C ~{Sets@{o so}}~> pi0@{o o o hd} D.
Proof.
  unshelve refine {| morphism := fobj[F] |}.
  intros x y s; exact (zigzag_fmap F s).
Defined.

(* Its underlying map is the object action of F, by conversion. *)
Example pi0_fmap_at {C D : Category} (F : C ⟶ D) (x : C) :
  pi0_fmap F x = F x := eq_refl.

(* Naturally isomorphic functors induce the same map on components: the
   component of the isomorphism at x is a one-step chain from F x to G x.
   Only the [to] direction and none of the coherence is consumed, which is
   why the same proof would work for a bare pointwise family of arrows. *)
Lemma pi0_fmap_respects {C D : Category} (F G : C ⟶ D) (H : F ≈ G) :
  pi0_fmap F ≈ pi0_fmap G.
Proof. intro x; exact (hom_zigzag (to (`1 H x))). Qed.

(* Connectedness read off π₀.  Both directions are NEAR-DEFINITIONAL —
   [equiv] on [pi0 C] IS [ZigZag] by [pi0_equiv] above — and they are
   recorded because the π₀ phrasing is the one a consumer will reach for,
   not because either carries an argument.  Read [pi0_subsingleton] as "π₀
   has at most one point"; the "exactly one" reading needs the
   inhabitedness clause, and is [connected_nonempty_iff_pi0_singleton] in
   the section on the two readings below. *)
Definition pi0_subsingleton (C : Category) : Type :=
  ∀ x y : carrier (pi0 C), x ≈ y.

Definition connected_pi0_subsingleton {C : Category} (K : Connected C) :
  pi0_subsingleton C := K.

Definition pi0_subsingleton_connected {C : Category}
  (H : pi0_subsingleton C) : Connected C := H.

Theorem connected_iff_pi0_subsingleton (C : Category) :
  Connected C ↔ pi0_subsingleton C.
Proof.
  split; [ exact (@connected_pi0_subsingleton C)
         | exact (@pi0_subsingleton_connected C) ].
Defined.

(** ** π₀ as a functor Cat ⟶ Sets *)

(* The three functor laws are free.  [fmap_respects] is [pi0_fmap_respects];
   [fmap_id] and [fmap_comp] ask for a chain between two objects that are
   Leibniz-equal, and [zz_nil] supplies it — so no property of [Id] or of
   [Compose] is consumed at all, and in particular [zigzag_fmap_id] and
   [zigzag_fmap_compose] are NOT used here.  They are the stronger,
   Leibniz-level statements; these obligations only need `≈` in [Sets],
   which on components is inhabitation of [ZigZag].

   [Cat]'s hom-setoid is natural isomorphism (Instance/Cat.v), which is
   exactly why [pi0_fmap_respects] is what [fmap_respects] wants; a functor
   into [Sets] out of a strict category of categories would be a different
   statement and is not built. *)
Program Definition Pi0 : Cat ⟶ Sets := {|
  fobj := pi0;
  fmap := fun _ _ F => pi0_fmap F
|}.
Next Obligation. intros F G H. exact (pi0_fmap_respects F G H). Defined.
Next Obligation. exact (zz_nil _). Defined.
Next Obligation. exact (zz_nil _). Defined.

Example Pi0_obj (C : Cat) : fobj[Pi0] C = pi0 C := eq_refl.

(** ** The connected component of an object, as a full subcategory *)

(* The objects joined to x, with EVERY morphism of C between them.  The
   selected-morphism family is the universe-polymorphic unit, so the two
   closure fields are discharged by the ambient obligation tactic and the
   subcategory is full by construction. *)
Program Definition ComponentSub (C : Category) (x : C) : Subcategory C := {|
  sobj := fun y => ZigZag x y;
  shom := fun _ _ _ _ _ => poly_unit
|}.

Example component_sobj (C : Category) (x y : C) :
  sobj C (ComponentSub C x) y = ZigZag x y := eq_refl.

Definition ConnectedComponent (C : Category) (x : C) : Category :=
  Sub C (ComponentSub C x).

Example component_obj_type (C : Category) (x : C) :
  obj[ConnectedComponent C x] = (∃ y : C, ZigZag x y) := eq_refl.

Definition Component_Incl (C : Category) (x : C) :
  ConnectedComponent C x ⟶ C := Incl C (ComponentSub C x).

Example Component_Incl_obj (C : Category) (x : C)
  (y : ConnectedComponent C x) : Component_Incl C x y = `1 y := eq_refl.

Definition ComponentSub_Full (C : Category) (x : C) :
  Category.Construction.Subcategory.Full C (ComponentSub C x) :=
  fun _ _ _ _ _ => ttt.

Definition Component_Incl_Faithful (C : Category) (x : C) :
  Faithful (Component_Incl C x) := Incl_Faithful C (ComponentSub C x).

Definition Component_Incl_Full (C : Category) (x : C) :
  Functor.Full (Component_Incl C x) :=
  Full_Implies_Full_Functor C (ComponentSub C x) (ComponentSub_Full C x).

(* Every arrow of C between two selected objects is an arrow of the
   component, the selection witness being [ttt]. *)
Definition component_arr {C : Category} {x : C} {a b : C}
  (sa : ZigZag x a) (sb : ZigZag x b) (f : a ~> b) :
  (a; sa) ~{ConnectedComponent C x}~> (b; sb) := (f; ttt).

(* Membership is DATA, so one object of C sitting in the component by two
   different chains gives two DIFFERENT objects of the subcategory.  They
   are canonically isomorphic, by the identity of C in both directions.
   (Construction/Subcategory.v:133's [Full_membership_iso] proves the same
   thing generically; it is not used, the direct construction being two
   lines because [shom] here is [poly_unit] and the hom-setoid of [Sub]
   compares first projections.) *)
Program Definition component_iso (C : Category) (x y : C)
  (s t : ZigZag x y) :
  @Isomorphism (ConnectedComponent C x) (y; s) (y; t) := {|
  to := (id[y]; ttt) ; from := (id[y]; ttt)
|}.

(* A chain in C starting inside the component lifts to a chain in the
   component.  This is what makes each component connected, and it is the
   one genuinely recursive construction of this section: each intermediate
   object of the chain has to be SHOWN to lie in the component, by
   extending the chain that got us to the previous one, and the target
   membership proof is carried along as an explicit argument so that the
   chain may end at whichever proof the caller holds.

   The [zz_nil] branch is where the proof-relevance is paid for: the two
   membership proofs there need not agree, so the empty chain of C becomes
   a ONE-step chain of the component, on the identity arrow. *)
Fixpoint component_lift {C : Category} {x : C} {y z : C}
  (sy : ZigZag x y) (s : ZigZag y z) :
  ∀ sz : ZigZag x z, @ZigZag (ConnectedComponent C x) (y; sy) (z; sz) :=
  match s in ZigZag a b
        return ∀ (sa : ZigZag x a) (sb : ZigZag x b),
               @ZigZag (ConnectedComponent C x) (a; sa) (b; sb) with
  | zz_nil w    => fun sa sb => hom_zigzag (component_arr sa sb (id[w]))
  | zz_fwd f s' => fun sa sb =>
      zz_fwd (component_arr sa (zigzag_trans sa (hom_zigzag f)) f)
             (component_lift (zigzag_trans sa (hom_zigzag f)) s' sb)
  | zz_bwd f s' => fun sa sb =>
      zz_bwd (component_arr (zigzag_trans sa (zz_bwd f (zz_nil _))) sa f)
             (component_lift (zigzag_trans sa (zz_bwd f (zz_nil _))) s' sb)
  end sy.

(* Each component is connected — the half of "C is the disjoint union of
   its connected components" that is a theorem here.  The chain from a to b
   is built in C by going back to x and out again, then lifted. *)
Definition Component_Connected (C : Category) (x : C) :
  Connected (ConnectedComponent C x).
Proof.
  intros [a sa] [b sb].
  exact (component_lift sa (zigzag_trans (zigzag_sym sa) sb) sb).
Defined.

(* ... and each is inhabited, by its own representative. *)
Definition Component_obj (C : Category) (x : C) : ConnectedComponent C x :=
  (x; zz_nil x).

(* A connected category is its own single component, up to equivalence: the
   inclusion is fully faithful always, and connectedness makes it
   surjective on objects on the nose, so the witnessing isomorphism is
   [iso_id]. *)
Definition Component_Incl_ESO (C : Category) (x : C) (K : Connected C) :
  EssentiallySurjective (Component_Incl C x) :=
  @Build_EssentiallySurjective _ _ (Component_Incl C x)
    (fun d => ((d; K x d) : ConnectedComponent C x)) (fun d => iso_id).

Definition connected_Component_equiv (C : Category) (x : C)
  (K : Connected C) : EquivalenceOfCategories (Component_Incl C x) :=
  @FF_ESO_Equivalence _ _ (Component_Incl C x)
    (Component_Incl_Full C x) (Component_Incl_Faithful C x)
    (Component_Incl_ESO C x K).

(* The component does not depend on which representative names it.  The
   object and arrow actions are elaborated as plain definitions first,
   because writing them inline in a [Program Definition] makes Program
   destructure the sigma and insert [eq_rect] transports that no ordinary
   case analysis discharges — the hazard Functor/Construction/Postcompose.v
   records for indexed arrow actions, met here through [sigT]. *)
Definition component_reindex_obj {C : Category} {x x' : C} (z : ZigZag x x')
  (y : ConnectedComponent C x) : ConnectedComponent C x' :=
  (`1 y; zigzag_trans (zigzag_sym z) `2 y).

Definition component_reindex_map {C : Category} {x x' : C} (z : ZigZag x x')
  {a b : ConnectedComponent C x} (f : a ~> b) :
  component_reindex_obj z a
    ~{ConnectedComponent C x'}~> component_reindex_obj z b := (`1 f; ttt).

Program Definition Component_reindex {C : Category} {x x' : C}
  (z : ZigZag x x') :
  ConnectedComponent C x ⟶ ConnectedComponent C x' := {|
  fobj := component_reindex_obj z ; fmap := @component_reindex_map C x x' z
|}.

Definition Component_reindex_Faithful (C : Category) (x x' : C)
  (z : ZigZag x x') : Faithful (Component_reindex z).
Proof. construct; simpl in *; auto. Defined.

Definition Component_reindex_Full (C : Category) (x x' : C)
  (z : ZigZag x x') : Functor.Full (Component_reindex z).
Proof.
  construct.
  - exact (`1 g; ttt).
  - simpl; reflexivity.
Defined.

Definition Component_reindex_ESO (C : Category) (x x' : C)
  (z : ZigZag x x') : EssentiallySurjective (Component_reindex z).
Proof.
  unshelve refine (@Build_EssentiallySurjective _ _ _ _ _).
  - intro d; exact ((`1 d; zigzag_trans z `2 d) : ConnectedComponent C x).
  - intros [w s]; simpl.
    exact (component_iso C x' w _ s).
Defined.

(* Only an EQUIVALENCE is claimed, and that is not a shortfall of the proof
   but of the objects: reindexing changes the membership proof each object
   carries, so the object [(w; s)] of the target is reached from
   [(w; zigzag_trans z s)] and comes back as
   [(w; zigzag_trans (zigzag_sym z) (zigzag_trans z s))], a DIFFERENT chain
   from [s].  The two index isomorphic objects, which is what
   [component_iso] supplies and what the essential-surjectivity witness
   above uses. *)
Definition Component_reindex_equiv (C : Category) (x x' : C)
  (z : ZigZag x x') :
  EquivalenceOfCategories (Component_reindex z) :=
  @FF_ESO_Equivalence _ _ (Component_reindex z)
    (Component_reindex_Full C x x' z) (Component_reindex_Faithful C x x' z)
    (Component_reindex_ESO C x x' z).

(** ** Two readings of "connected", separated *)

(* THE SOURCE ISSUE AND THE DONOR FILE DO NOT DEFINE THE SAME PREDICATE,
   AND THE DIFFERENCE IS EXACTLY THE EMPTY CATEGORY.  The issue asks for
   "INHABITED, and any two objects are joined by a zig-zag"; the in-tree
   [Connected] (Structure/Groupoid/Connected.v:133) is the second clause
   alone.  The usual convention — the nLab entry cited at the head of this
   file states it — includes inhabitedness, precisely so that "a category
   is the disjoint union of its connected components" has no empty
   summand — so this is a genuine discrepancy and not a matter of taste.

   [ConnectedNonempty] below is the stronger reading, with the extra datum
   as its own field so that neither direction is hidden: [cn_zigzag]
   forgets it and [Build_ConnectedNonempty] supplies it. *)
Record ConnectedNonempty (C : Category) : Type := {
  cn_obj    : C;
  cn_zigzag : Connected C
}.

Arguments cn_obj {C} _.
Arguments cn_zigzag {C} _.
Arguments Build_ConnectedNonempty {C} _ _.

Definition connected_of_nonempty {C : Category} (K : ConnectedNonempty C) :
  Connected C := cn_zigzag K.

Definition nonempty_connected {C : Category} (c : C) (K : Connected C) :
  ConnectedNonempty C := Build_ConnectedNonempty c K.

(* The empty category satisfies the in-tree reading VACUOUSLY: there is no
   pair of objects to join, so the function is defined by zero clauses. *)
Definition Zero_Connected : Connected _0.
Proof. intros x; destruct x. Defined.

(* ... and fails the issue's reading, since it has no object at all. *)
Theorem Zero_not_ConnectedNonempty : ConnectedNonempty _0 → False.
Proof. intro K; destruct (cn_obj K). Qed.

(* The separation, packaged: the two readings are not the same predicate,
   and [_0] is a witness.  This is what makes the discrepancy above a
   proved fact rather than an observation. *)
Definition connected_readings_differ :
  Connected _0 * (ConnectedNonempty _0 → False) :=
  (Zero_Connected, Zero_not_ConnectedNonempty).

(* Every component satisfies the stronger reading, its representative
   supplying the object.  So the decomposition of C into components has no
   empty summand — which is the reason the stronger reading is the
   conventional one. *)
Definition Component_ConnectedNonempty (C : Category) (x : C) :
  ConnectedNonempty (ConnectedComponent C x) :=
  Build_ConnectedNonempty (Component_obj C x) (Component_Connected C x).

(* The π₀ phrasing of the stronger reading: π₀ has exactly one point.  Like
   the subsingleton statement above this is near-definitional, the carrier
   of [pi0 C] being [obj[C]] and its `≈` being [ZigZag]. *)
Theorem connected_nonempty_iff_pi0_singleton (C : Category) :
  ConnectedNonempty C ↔ (carrier (pi0 C) * pi0_subsingleton C).
Proof.
  split.
  - intro K; exact (cn_obj K, cn_zigzag K).
  - intros [c H]; exact (Build_ConnectedNonempty c H).
Defined.

(** ** Categories that are connected, and one that is not *)

(* A terminal object joins every pair: out to 1 and back.  Both the bundled
   class and the object-level predicate of Structure/Terminal.v are
   covered, the latter because terminality is often available only as a
   property. *)
Definition terminal_connected {C : Category} (T : @Terminal C) :
  Connected C :=
  fun x y => zz_fwd (@one C T x) (zz_bwd (@one C T y) (zz_nil y)).

Definition is_terminal_connected {C : Category} {c : C}
  (H : IsTerminalObj c) : Connected C :=
  fun x y => zz_fwd (is_terminal_one H (x:=x))
                    (zz_bwd (is_terminal_one H (x:=y)) (zz_nil y)).

Definition terminal_ConnectedNonempty {C : Category} (T : @Terminal C) :
  ConnectedNonempty C :=
  Build_ConnectedNonempty (@terminal_obj C T) (terminal_connected T).

(* Dually for an initial object: in to 0 and back out.  Note that these are
   written out rather than obtained from the terminal case at [C^op],
   because a chain in [C^op] is not a chain in C on the nose — the two
   constructors exchange — and no transport between them is built here. *)
Definition initial_connected {C : Category} (I : @Initial C) :
  Connected C :=
  fun x y => zz_bwd (@zero C I x) (zz_fwd (@zero C I y) (zz_nil y)).

Definition is_initial_connected {C : Category} {c : C}
  (H : IsInitialObj c) : Connected C :=
  fun x y => zz_bwd (is_initial_zero H (x:=x))
                    (zz_fwd (is_initial_zero H (x:=y)) (zz_nil y)).

Definition initial_ConnectedNonempty {C : Category} (I : @Initial C) :
  ConnectedNonempty C :=
  Build_ConnectedNonempty (@initial_obj C I) (initial_connected I).

(* The point category, directly: its single hom is the one-step chain. *)
Definition One_Connected : Connected _1 :=
  fun x y => @hom_zigzag _1 x y ttt.

Definition One_ConnectedNonempty : ConnectedNonempty _1 :=
  @Build_ConnectedNonempty _1 ttt One_Connected.

(* In a discrete category a chain cannot leave the object it starts at:
   every arrow forces its endpoints Leibniz-equal, and an induction over
   the chain accumulates those equalities.  Stated over
   Structure/Discrete.v's [Discrete] PREDICATE rather than over
   Instance/Discrete.v's construction, so it applies to any category shown
   discrete.  (Structure/Groupoid/Connected.v:507 proves the same statement
   for the one two-object discrete category it needed; this is the general
   form, and that one is not used below.) *)
Lemma discrete_zigzag_eq {C : Category} (D : Discrete C) {x y : C}
  (s : ZigZag x y) : x = y.
Proof.
  induction s as [ w | a b c f s' IH | a b c f s' IH ].
  - reflexivity.
  - transitivity b; [ exact `1 (D _ _ f) | exact IH ].
  - transitivity b; [ symmetry; exact `1 (D _ _ f) | exact IH ].
Qed.

Definition discrete_connected_eq {C : Category} (D : Discrete C)
  (K : Connected C) (x y : C) : x = y := discrete_zigzag_eq D (K x y).

(* Hence a discrete category is connected exactly when it has at most one
   object, and satisfies the stronger reading exactly when it has exactly
   one.  The backward directions are immediate: in [DiscreteCat A] a
   morphism IS an equality proof, so [x = y] already names an arrow. *)
Theorem DiscreteCat_connected_iff (A : Type) :
  Connected (DiscreteCat A) ↔ (∀ x y : A, x = y).
Proof.
  split.
  - intros K x y.
    exact (discrete_connected_eq (DiscreteCat_Discrete A) K x y).
  - intros H x y.
    exact (hom_zigzag (H x y : x ~{DiscreteCat A}~> y)).
Defined.

Theorem DiscreteCat_ConnectedNonempty_iff (A : Type) :
  ConnectedNonempty (DiscreteCat A) ↔ (A * (∀ x y : A, x = y)).
Proof.
  split.
  - intro K.
    exact (cn_obj K,
           fun x y => discrete_connected_eq (DiscreteCat_Discrete A)
                        (cn_zigzag K) x y).
  - intros [a H].
    exact (@Build_ConnectedNonempty (DiscreteCat A) a
             (snd (DiscreteCat_connected_iff A) H)).
Defined.

(* For a GROUPOID the zig-zag form and the one-arrow form agree.  This is
   PURE ASSEMBLY of two constants of the donor file —
   Structure/Groupoid/Connected.v:211's [connected_arrow] forward and :140's
   [arrow_connected] back — and introduces no argument of its own; it is
   recorded because the biconditional is the shape a consumer wants and the
   donor states only the two halves.  The forward half is where the
   groupoid hypothesis is spent, through :203's [zigzag_hom]. *)
Theorem groupoid_connected_iff_arrow {C : Category} (G : IsGroupoid C) :
  Connected C ↔ (∀ x y : C, x ~> y).
Proof.
  split; [ exact (connected_arrow G) | exact (@arrow_connected C) ].
Defined.

(** ** Witnesses *)

(* The walking parallel pair is connected: its two objects are joined by
   either of its two non-identity arrows, and the chain uses one of them
   forwards or backwards according to direction. *)
Definition Parallel_Connected : Connected Parallel.
Proof.
  intros x y.
  destruct x, y.
  - exact (@zz_nil Parallel ParX).
  - exact (hom_zigzag ((true; ParOne) : ParX ~{Parallel}~> ParY)).
  - exact (@zz_bwd Parallel ParY ParX ParX
             ((true; ParOne) : ParX ~{Parallel}~> ParY)
             (@zz_nil Parallel ParX)).
  - exact (@zz_nil Parallel ParY).
Defined.

Definition Parallel_ConnectedNonempty : ConnectedNonempty Parallel :=
  @Build_ConnectedNonempty Parallel ParX Parallel_Connected.

Definition pi0_Parallel_subsingleton : pi0_subsingleton Parallel :=
  Parallel_Connected.

(* [Roof] is the sharper witness and it is CITED, not reproved:
   Structure/Groupoid/Connected.v:431's [Roof_Connected] already exhibits
   the walking span as connected, and :457's [Roof_no_arrow_neg_pos] shows
   it is not arrow-connected.  So π₀ of it is a SUBSINGLETON — which is
   what the constant below says; [Roof] is inhabited, so "exactly one
   point" is also true there, but it needs the inhabitedness clause and is
   not what is delivered — even though two
   of its three objects have an empty hom-set between them in BOTH
   directions — Instance/Roof.v:70 and :75 supply the two emptiness
   lemmas.  That is the case in which π₀ says strictly more than the
   one-arrow reading would. *)
Definition pi0_Roof_subsingleton : pi0_subsingleton Roof := Roof_Connected.

(* The two-element discrete category is NOT connected. *)
Theorem DiscreteCat_bool_not_connected :
  Connected (DiscreteCat bool) → False.
Proof.
  intro K.
  pose proof (fst (DiscreteCat_connected_iff bool) K true false) as H.
  discriminate H.
Qed.

(* ... and π₀ of it genuinely separates its two objects, which is what
   makes the construction non-vacuous: the quotient does not collapse
   everything.  The argument does not read the chain and conclude False
   from its shape — no analysis of chains could, a chain being data with
   three constructors and no contradictory one; it runs the endpoint
   invariant [discrete_zigzag_eq] (itself an induction over the chain, but
   one whose conclusion is an EQUALITY) and then discriminates that
   equality in [bool]. *)
Theorem pi0_bool_separates :
  @equiv _ (pi0 (DiscreteCat bool)) true false → False.
Proof.
  intro s.
  pose proof (discrete_zigzag_eq (DiscreteCat_Discrete bool) s) as H.
  discriminate H.
Qed.

(* The component of [true] excludes [false], by the same invariant. *)
Theorem component_bool_excludes_false :
  sobj (DiscreteCat bool) (ComponentSub (DiscreteCat bool) true) false
    → False.
Proof.
  intro s.
  pose proof (discrete_zigzag_eq (DiscreteCat_Discrete bool) s) as H.
  discriminate H.
Qed.

(* A functor from a connected category to a disconnected one.  This is what
   makes [connected_image] the honest statement of the first section: its
   conclusion holds here, while [Connected (DiscreteCat bool)] is
   refutable.  So the implication "C is connected and there is a functor
   C ⟶ D, therefore D is connected" is FALSE, and the surjectivity
   hypothesis of [eso_connected] cannot simply be dropped.  The witness is
   sharp in the sense that matters: that hypothesis genuinely FAILS here
   ([One_to_bool_not_ESO] below).  It is not sharp in any finer sense —
   whether some hypothesis weaker than essential surjectivity would do is
   left open, and nothing is claimed about this functor's fullness or
   faithfulness. *)
Program Definition One_to_bool : _1 ⟶ DiscreteCat bool := {|
  fobj := fun _ => true;
  fmap := fun _ _ _ => eq_refl
|}.

Definition image_connected_not_connected :
  (∀ x y : _1, ZigZag (One_to_bool x) (One_to_bool y))
    * (Connected (DiscreteCat bool) → False) :=
  (connected_image One_to_bool One_Connected, DiscreteCat_bool_not_connected).

(* ... and the hypothesis of [eso_connected] genuinely fails at it: an
   essential-surjectivity witness would supply an isomorphism
   [true ≅ false] in [DiscreteCat bool], whose forward leg is an equality
   of booleans. *)
Theorem One_to_bool_not_ESO :
  EssentiallySurjective One_to_bool → False.
Proof.
  intro E.
  pose proof (to (@eso_iso _ _ One_to_bool E false)) as H.
  discriminate H.
Qed.
