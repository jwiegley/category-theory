Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Theory.Diagram.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * Cones and limits over a diagram of graph shape *)

(* Book:    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
            Springer GTM 5, 1998, Section III.4, printed p. 71
   Catalog: maclane:III.4:def8  ("diagram of graph shape and its limit")
            maclane:III.4:remark6 ("graph-shaped limits reduce to functor
            limits via the free category"), both in
            doc/plan/books/maclane/inventory/III.json
   nLab:    https://ncatlab.org/nlab/show/cone
   nLab:    https://ncatlab.org/nlab/show/free+category

   CITED BY LOCATION; the printed text was not consulted.  Everything
   attributed to Mac Lane below paraphrases the CATALOG'S summaries, which
   are themselves paraphrases and not the book's wording.

   WHAT WAS ALREADY IN TREE, AND WHAT IS ADDED HERE.  A DIAGRAM OF GRAPH
   SHAPE -- a graph morphism D : G -> U C into the underlying graph of C --
   is Theory/Diagram.v:151's [Diagram G C := QuiverHomomorphism G
   (QuiverOfCat C)], and this file adds no second definition of it; nor does
   it reprove the FACTORIZATION half of remark 6, which is
   Construction/Free/Quiver.v:529's [UniversalArrowQuiverCat] (every D
   factors through the unit as a functor on the free category, uniquely up
   to [StrictCat]'s hom-equivalence) together with Theory/Diagram.v:240's
   [FunctorOfDiagram], :246's [DiagramOfFunctor] and the two round trips at
   :284 and :299 -- all cited, none restated.  What was missing is the rest
   of def 8: the CONE over a graph diagram and its LIMIT, and then remark
   6's clause that limits and limiting cones for the two presentations
   "correspond exactly".

   THE ABSENCE, SCOPED TO WHAT WAS SEARCHED, AND MEASURED BEFORE THIS FILE
   EXISTED.  [grep -icE 'cone|limit'] returned 0 on
   Construction/Free/Quiver.v and on each of the five siblings that were
   then under Construction/Free/Quiver/ (Concrete.v, Constructions.v,
   Coproduct.v, Examples.v, Presented.v), and Theory/Diagram.v's three hits
   are all inside comments (:94, :95, :209).  A shape search
   [rg -g '*.v' 'GraphCone|graph_cone|gvertex'] over the whole tree returned
   nothing.  The claim is scoped to those two searches: no cone over a
   quiver homomorphism was found anywhere by them.

   NO FUNCTORIALITY IS NEEDED, AND THIS FILE SHOWS EXACTLY WHERE THAT SHOWS
   UP.  Mac Lane's cone assigns to each NODE i of G an arrow mu_i : c -> D i,
   subject to one equation per graph EDGE h : i -> j, namely
   D h ∘ mu_i = mu_j; the catalog's own summary calls it "a natural
   transformation from the constant, using composition in C but not in the
   domain".  A graph has no composition and no identities, so there is
   nothing further for the cone to respect.  In [AGraphCone] below that is
   the single field [gcone_coherence], quantified over [edges x y] -- ONE
   TRIANGLE PER EDGE.  Contrast [ACone] (Structure/Cone.v:24), whose
   [cone_coherence] is quantified over [x ~{J}~> y]; over a free category
   those morphisms are PATHS of every length, so a functor cone carries ONE
   TRIANGLE PER ARROW.  The two witnesses below make that gap concrete.

   THE CORRESPONDENCE, AND WHICH HALF COSTS ANYTHING.  Passing a functor cone
   DOWN to a graph cone ([AGraphCone_of_ACone]) is RESTRICTION to one-edge
   paths: instantiate the functor cone's coherence at [tlist_singleton e]
   (Lib/TList.v:87) and remove the one identity a singleton path contributes.
   Passing a graph cone UP ([ACone_of_AGraphCone]) is EXTENSION ALONG PATHS,
   and it is the file's only induction over a path: [gcone_dpath] proves
   [dpath D p ∘ mu_x ≈ mu_y] for a path of ARBITRARY length by induction on
   the [tlist], each step spending one instance of [gcone_coherence] and one
   [comp_assoc].

   STRENGTHS, MEASURED RATHER THAN GUESSED.

   (1) APEXES AND LEGS SURVIVE BOTH PASSAGES ON THE NOSE.  Pinned by the four
       [eq_refl] Examples [gcone_apex_fwd], [gcone_leg_fwd],
       [gcone_apex_bwd], [gcone_leg_bwd], and by the two round-trip Examples
       [gcone_round_graph] and [gcone_round_cone].  Neither passage touches
       the leg family; each rebuilds only the coherence field.

   (2) THE WHOLE-RECORD ROUND TRIPS ARE REFUTED AT [eq_refl].  All FOUR
       records involved ([AGraphCone], [GraphCone], [ACone], [Cone]) --
       an earlier draft wrote "both" -- have primitive projections with
       eta, so record equality reduces to
       field equality -- and the coherence fields do not converge, [≈] being
       [crelation]-valued here, so those fields are DATA and the rebuilt
       proof is a different term.  Measured for [AGraphCone_of_ACone
       (ACone_of_AGraphCone N)], for [ACone_of_AGraphCone
       (AGraphCone_of_ACone N)] and for [GraphCone_of_Cone
       (Cone_of_GraphCone N)].  A FOURTH, [Cone_of_GraphCone
       (GraphCone_of_Cone N)], is refuted the same way and was omitted from
       that list; it is covered obliquely by the [≈]-level
       [Cone_of_GraphCone_round].  This file ships no [Fail] probe, so all
       four are stated as measurements and pinned nowhere -- and
       Test/ProbeQuiverLimit332.v, which accompanies this issue, does not
       pin them either and says so.  What IS
       delivered is the [≈]-level [Cone_of_GraphCone_round], through
       Structure/Cone.v:37's [AConeEquiv], which compares legs only.

   (3) AT THE LIMIT LEVEL THE CORRESPONDENCE COSTS NOTHING.  [graph_limitcone]
       and [limitcone_graph_limit] are supplied by [:=] with NO TACTIC and no
       obligation: the two [∃!] statements are CONVERTIBLE, because apex and
       every leg agree on the nose and [obj[FreeOnQuiver G]] IS [nodes G].
       All the proof content of remark 6 sits in the cone-level passages, and
       none of it in the limit-level ones.

   (4) [dpath D p] IS NOT [fmap[FunctorOfDiagram D] p] AT A VARIABLE PATH.
       Measured, and the cause is that [dpath] (Theory/Diagram.v:163) is a
       [Fixpoint] while [InducedFunctor]'s arrow action
       (Construction/Free/Quiver.v:475) is elaborated as a [tlist'_rect], so
       the two are different terms; Theory/Diagram.v:251's [dpath_fmap]
       relates them at [≈], and that is what [ACone_of_AGraphCone] and
       [AGraphCone_of_ACone] both consume.  At a ONE-EDGE path they DO agree
       definitionally, pinned here as [dpath_singleton_is_fmap].

   NON-VACUITY: TWO WITNESSES MAKING TWO DIFFERENT POINTS, both over quivers
   that ALREADY EXIST in Theory/Diagram.v -- no new shape is drawn.

   (a) A REAL LIMIT.  Over [TriangleQuiver] (Theory/Diagram.v:650) -- three
       nodes with edges X->Y, Y->Z and X->Z -- take the diagram whose direct
       edge is LITERALLY the composite, [TriangleDiagram u v (v ∘ u)].  Then
       the apex [p] with legs [id], [u], [v ∘ u] is a graph cone
       ([TriangleGraphCone]) and [triangle_graph_limit] proves it a LIMITING
       one, over an ARBITRARY category and arbitrary [u] and [v]: the
       mediator out of a competing graph cone is that cone's own leg at
       [TrX], its three triangles are [id_left] together with the coherence
       instances at the edges X->Y and X->Z, and uniqueness is [id_left]
       again.  The coherence instance at Y->Z is never spent.

   (b) THE NO-FUNCTORIALITY POINT, EXHIBITED.  The triangle shape has TWO
       DISTINCT parallel arrows X->Z in its free category -- [tri_via_Y] of
       length two and [tri_direct] of length one, proved distinct by
       Theory/Diagram.v:662's [tri_via_Y_neq_direct], cited and not
       reproved.  READ THE TWO DIFFERENTLY, and an earlier draft of this
       paragraph did not: [tri_via_Y] is the GENUINE no-functoriality
       instance -- it is a composite, no cone field mentions it, and its
       triangle is reached only by the induction in [gcone_dpath].
       [tri_direct] is a SINGLETON path on an actual edge of the shape, so
       the cone's own [gcone_coherence] field at that edge IS its triangle,
       modulo the one [id_left] that [dpath] leaves on a one-edge path --
       which is exactly what paragraph (a) above spends at the X->Z edge,
       and what the limit proof spends.  The earlier draft said a graph
       cone "states a triangle for NEITHER of them", which contradicts
       paragraph (a) and is false of [tri_direct].  Both
       [tri_gcone_at_via_Y] and [tri_gcone_at_direct] are nonetheless
       routed uniformly through [gcone_leg_dpath], hence [gcone_dpath];
       for [tri_direct] that route is not the cheapest one.  The walking
       loop (Theory/Diagram.v:772) sharpens this to the extreme case:
       [loop_gcone] builds a graph cone from the SINGLE
       equation [e ∘ psi ≈ psi], and [loop_gcone_every_path] then discharges
       the triangle at [loop_path n] for EVERY [n], those paths being
       pairwise distinct arrows of the free category
       ([loop_paths_distinct]).  One field, one triangle for each of
       infinitely many arrows.

   (c) COMPUTATION.  The triangle witness is instantiated in [Coq]
       (Instance/Coq.v) at [u := S] and [v := Nat.even]: the apex, the three
       legs, and the mediator out of a probe cone all reduce, pinned by
       [eq_refl] ([coq_tri_apex] through [coq_probe_Y]).

   WHAT IS NOT DELIVERED, scoped to this file.

     * No dual.  There is no graph cocone and no colimit of a graph diagram;
       nothing here is stated at [C^op].
     * No category of graph cones, hence no rendering of the limit as a
       terminal object, and no setoid on [AGraphCone] mirroring
       Structure/Cone.v:37's [AConeEquiv].  Consequently there is no
       essential-uniqueness statement for graph limits: no "any two limiting
       graph cones are canonically isomorphic", with or without legs.
     * No preservation, reflection or creation of graph limits, and no
       analogue of Structure/Limit/Preservation.v's [PreservesLimit].
     * [graph_limit_IsALimit] is offered only as the apex-only READING of the
       cone-level statement.  It is the weaker of the two -- its legs are
       unconstrained -- and NO separation between them is proved here, so
       "strictly weaker" is not claimed.
     * Nothing connects to Theory/Diagram.v:212's [Commutative], which is
       never invoked below, and no commutativity theorem of that file is
       consumed.  The triangle witness does draw a commuting triangle -- its
       direct edge is the composite BY DEFINITION, and that choice is what
       makes the apex a limit -- but it is used as a definitional unfolding,
       never through the predicate.
     * The loop witness exhibits the no-functoriality point but NOT a limit:
       the limit of a loop diagram is the equalizer of [e] and [id], and no
       equalizer is constructed here.
     * The computing witnesses at the end of the file are the sole reason
       this module Requires Category.Instance.Coq, which pulls that file's
       own closure (Theory.Monad, Functor.Strong, Structure.BiCCC and so
       on) into this module's.  Nothing but the probe Requires this file,
       so the weight is contained; it is disclosed rather than split, and
       the precedent for splitting on exactly this ground is the
       Structure/Limit/Power.v / Power/Hom.v division.
     * No [GraphLimit] instance is produced for any category from a
       completeness hypothesis; there is no "C complete implies every graph
       diagram over C has a graph limit".
     * No universe measurement is offered IN THIS FILE.  Nothing below
       claims which levels these constants identify or leave free.  Scope
       that precisely: the companion Test/ProbeQuiverLimit332.v DOES make
       one measurement, that [Diagram] identifies C's hom and proof
       universes (which is why [AGraphCone] displays them identified where
       the [ACone] it mirrors displays them apart).  That pin is the
       DONOR's -- Theory/Diagram.v:143-151 opens its section with an
       unannotated [Context {C : Category}], so it is a minimization
       artifact of the kind Construction/Free/Quiver/Examples.v's header
       records, repairable upstream with explicit binders, and NOT
       inherent content of this development. *)

(** ** Graph cones *)

(* Mac Lane's def 8, apex parameterized: a leg at every NODE, and one
   triangle at every EDGE.  There is no clause for composites or identities,
   because the shape [G] has neither. *)
Class AGraphCone {G : Quiver} {C : Category} (D : Diagram G C)
  (c : obj[C]) := {
  (* The leg at the node [x]: an arrow from the apex into the label of [x]. *)
  gvertex_map (x : G) : c ~{C}~> D x;
  (* One triangle for each drawn edge, and no other condition. *)
  gcone_coherence {x y : G} (e : edges x y) :
    dedge D e ∘ gvertex_map x ≈ gvertex_map y
}.

(* The bundled form, mirroring Structure/Cone.v:51's [Cone]. *)
Class GraphCone {G : Quiver} {C : Category} (D : Diagram G C) := {
  gvertex_obj : obj[C];                    (* the apex *)
  gconeFrom : AGraphCone D gvertex_obj     (* its legs, with coherence *)
}.

Coercion gvertex_obj : GraphCone >-> obj.
#[export] Existing Instance gconeFrom.

Notation "gvertex_obj[ N ]" := (@gvertex_obj _ _ _ N)
  (at level 9, format "gvertex_obj[ N ]") : category_scope.

(* The leg of a bundled graph cone at a node, as a first-class function --
   the covariant accessor, mirroring Structure/Limit/Preservation.v:108's
   [cone_leg]. *)
Definition gcone_leg {G : Quiver} {C : Category} {D : Diagram G C}
  (N : GraphCone D) (x : G) : gvertex_obj[N] ~{C}~> D x :=
  @gvertex_map G C D (@gvertex_obj G C D N) (@gconeFrom G C D N) x.

Section Bridge.

Context {G : Quiver}.
Context {C : Category}.
Context {D : Diagram G C}.

(** ** Extension along paths *)

(* THE induction.  The coherence field speaks only of edges; this extends it
   to a path of arbitrary length, one [gcone_coherence] and one [comp_assoc]
   per step.  It is what makes a graph cone a cone over the free category,
   and it is the only place in this file where a path is inducted over. *)
Lemma gcone_dpath {c : obj[C]} (N : AGraphCone D c) {x y : G}
  (p : tlist edges x y) : dpath D p ∘ gvertex_map x ≈ gvertex_map y.
Proof.
  induction p as [ | i m e p IH ]; simpl.
  - now rewrite id_left.
  - rewrite <- comp_assoc, gcone_coherence.
    exact IH.
Qed.

(* The same statement read off a bundled cone. *)
Lemma gcone_leg_dpath (N : GraphCone D) {x y : G} (p : tlist edges x y) :
  dpath D p ∘ gcone_leg N x ≈ gcone_leg N y.
Proof. exact (gcone_dpath (@gconeFrom G C D N) p). Qed.

(** ** The correspondence with cones over the extending functor *)

(* Up: a graph cone IS a cone over [FunctorOfDiagram D].  The legs are
   carried across unchanged; the work is [gcone_dpath], routed through
   Theory/Diagram.v:251's [dpath_fmap]. *)
Definition ACone_of_AGraphCone {c : obj[C]} (N : AGraphCone D c) :
  ACone c (FunctorOfDiagram D).
Proof.
  unshelve eapply Build_ACone.
  - exact (fun x => @gvertex_map G C D c N x).
  - intros x y p; simpl.
    rewrite <- (dpath_fmap D p).
    exact (gcone_dpath N p).
Defined.

(* Down: restriction to one-edge paths.  The singleton path denotes
   [id ∘ dedge D e], so exactly one [id_left] is removed. *)
Definition AGraphCone_of_ACone {c : obj[C]}
  (N : ACone c (FunctorOfDiagram D)) : AGraphCone D c.
Proof.
  unshelve eapply Build_AGraphCone.
  - exact (fun x => @vertex_map _ _ c (FunctorOfDiagram D) N x).
  - intros x y e.
    pose proof (@cone_coherence _ _ c _ N x y (tlist_singleton e)) as H.
    rewrite <- (dpath_fmap D (tlist_singleton e)) in H.
    simpl in H.
    now rewrite id_left in H.
Defined.

Definition Cone_of_GraphCone (N : GraphCone D) : Cone (FunctorOfDiagram D) :=
  {| vertex_obj := gvertex_obj[N]
   ; coneFrom  := ACone_of_AGraphCone (@gconeFrom G C D N) |}.

Definition GraphCone_of_Cone (N : Cone (FunctorOfDiagram D)) : GraphCone D :=
  {| gvertex_obj := @vertex_obj _ _ _ N
   ; gconeFrom   := AGraphCone_of_ACone (@coneFrom _ _ _ N) |}.

(* Apexes and legs cross both ways ON THE NOSE. *)
Example gcone_apex_fwd (N : GraphCone D) :
  vertex_obj[Cone_of_GraphCone N] = gvertex_obj[N] := eq_refl.

Example gcone_leg_fwd (N : GraphCone D) (x : G) :
  cone_leg (Cone_of_GraphCone N) x = gcone_leg N x := eq_refl.

Example gcone_apex_bwd (N : Cone (FunctorOfDiagram D)) :
  gvertex_obj[GraphCone_of_Cone N] = vertex_obj[N] := eq_refl.

Example gcone_leg_bwd (N : Cone (FunctorOfDiagram D)) (x : G) :
  gcone_leg (GraphCone_of_Cone N) x = cone_leg N x := eq_refl.

(* ... and so do the legs of both round trips.  The whole RECORDS do not:
   see measurement (2) of the header. *)
Example gcone_round_graph (N : GraphCone D) (x : G) :
  gcone_leg (GraphCone_of_Cone (Cone_of_GraphCone N)) x = gcone_leg N x
  := eq_refl.

Example gcone_round_cone (N : Cone (FunctorOfDiagram D)) (x : G) :
  cone_leg (Cone_of_GraphCone (GraphCone_of_Cone N)) x = cone_leg N x
  := eq_refl.

(* The cone-side round trip at the strength the library's cone setoid
   supports: legs only, [AConeEquiv] ignoring the coherence proof. *)
Lemma Cone_of_GraphCone_round (N : Cone (FunctorOfDiagram D)) :
  @coneFrom _ _ _ (Cone_of_GraphCone (GraphCone_of_Cone N))
    ≈ @coneFrom _ _ _ N.
Proof. intro j; reflexivity. Qed.

(* Where [dpath] and the extending functor's [fmap] DO agree definitionally.
   At a variable path they do not; measurement (4) of the header. *)
Example dpath_singleton_is_fmap {x y : G} (e : edges x y) :
  dpath D (tlist_singleton e) = fmap[FunctorOfDiagram D] (tlist_singleton e)
  := eq_refl.

(** ** Limits of a graph diagram *)

(* Def 8's "a limit for the diagram D is a universal such cone", at CONE
   level: the factorization is required to commute with the legs OF N, which
   is what the apex-only reading cannot say.  This is the graph-shaped mirror
   of Structure/Limit/Preservation.v:166's [IsLimitCone]. *)
Definition IsLimitGraphCone (N : GraphCone D) : Type :=
  ∀ M : GraphCone D, ∃! u : gvertex_obj[M] ~{C}~> gvertex_obj[N],
    ∀ x : G, gcone_leg N x ∘ u ≈ gcone_leg M x.

(* Remark 6's "limits and limiting cones correspond exactly", both
   directions, each a term with no tactic: the two statements are
   convertible. *)
Definition graph_limitcone (N : GraphCone D) (H : IsLimitGraphCone N) :
  IsLimitCone (Cone_of_GraphCone N) :=
  fun M => H (GraphCone_of_Cone M).

Definition limitcone_graph_limit (N : GraphCone D)
  (H : IsLimitCone (Cone_of_GraphCone N)) : IsLimitGraphCone N :=
  fun M => H (Cone_of_GraphCone M).

Definition graph_limit_iff_limitcone (N : GraphCone D) :
  IsLimitGraphCone N ↔ IsLimitCone (Cone_of_GraphCone N) :=
  (graph_limitcone N, limitcone_graph_limit N).

(* The same passage starting from an arbitrary limiting cone over the
   extending functor, rather than from one already in the image. *)
Definition graph_limit_of_limitcone (N : Cone (FunctorOfDiagram D))
  (H : IsLimitCone N) : IsLimitGraphCone (GraphCone_of_Cone N) :=
  fun M => H (Cone_of_GraphCone M).

(* The apex-only READING.  Weaker than the cone-level statement -- its legs
   are unconstrained -- and no separation between the two is proved here. *)
Definition graph_limit_IsALimit (N : GraphCone D) (H : IsLimitGraphCone N) :
  IsALimit (FunctorOfDiagram D) gvertex_obj[N] :=
  limitcone_isalimit (graph_limitcone N H).

(* The bundled limit of a graph diagram, mirroring Structure/Limit.v:113. *)
Class GraphLimit := {
  graph_limit_cone : GraphCone D;
  graph_ump_limits : IsLimitGraphCone graph_limit_cone
}.

Definition Limit_of_GraphLimit (L : GraphLimit) : Limit (FunctorOfDiagram D) :=
  limitcone_limit (Cone_of_GraphCone (@graph_limit_cone L))
    (graph_limitcone _ (@graph_ump_limits L)).

Definition GraphLimit_of_Limit (L : Limit (FunctorOfDiagram D)) : GraphLimit :=
  {| graph_limit_cone := GraphCone_of_Cone (@limit_cone _ _ _ L)
   ; graph_ump_limits := graph_limit_of_limitcone _ (limit_limitcone L) |}.

Example graph_limit_round (L : GraphLimit) (x : G) :
  gcone_leg (@graph_limit_cone (GraphLimit_of_Limit (Limit_of_GraphLimit L))) x
  = gcone_leg (@graph_limit_cone L) x := eq_refl.

(** ** The mediating morphism *)

Definition graph_limit_med {N : GraphCone D} (H : IsLimitGraphCone N)
  (M : GraphCone D) : gvertex_obj[M] ~{C}~> gvertex_obj[N] :=
  unique_obj (H M).

Lemma graph_limit_med_commutes {N : GraphCone D} (H : IsLimitGraphCone N)
  (M : GraphCone D) (x : G) :
  gcone_leg N x ∘ graph_limit_med H M ≈ gcone_leg M x.
Proof. exact (unique_property (H M) x). Qed.

Lemma graph_limit_med_unique {N : GraphCone D} (H : IsLimitGraphCone N)
  (M : GraphCone D) (m : gvertex_obj[M] ~{C}~> gvertex_obj[N]) :
  (∀ x : G, gcone_leg N x ∘ m ≈ gcone_leg M x) → graph_limit_med H M ≈ m.
Proof. intro Hm; exact (uniqueness (H M) m Hm). Qed.

Lemma graph_limit_med_eq {N : GraphCone D} (H : IsLimitGraphCone N)
  (M : GraphCone D) (m m' : gvertex_obj[M] ~{C}~> gvertex_obj[N]) :
  (∀ x : G, gcone_leg N x ∘ m ≈ gcone_leg M x) →
  (∀ x : G, gcone_leg N x ∘ m' ≈ gcone_leg M x) → m ≈ m'.
Proof.
  intros Hm Hm'.
  transitivity (graph_limit_med H M).
  - symmetry; exact (graph_limit_med_unique H M m Hm).
  - exact (graph_limit_med_unique H M m' Hm').
Qed.

End Bridge.

Arguments GraphLimit {G C} D.

(** ** Witness one: a limiting graph cone over the walking triangle *)

(* The shape is Theory/Diagram.v:650's [TriangleQuiver]; the diagram is that
   file's [TriangleDiagram] with its direct edge taken to be LITERALLY the
   composite, so no commutation hypothesis is needed and none is used. *)
Section TriangleLimit.

Context {C : Category}.
Context {p q r : C} (u : p ~{C}~> q) (v : q ~{C}~> r).

Notation TriD := (TriangleDiagram u v (v ∘ u)).

Definition tri_lim_legs (i : TriNode) : p ~{C}~> TriD i :=
  match i as i0 return p ~{C}~> TriD i0 with
  | TrX => id
  | TrY => u
  | TrZ => v ∘ u
  end.

Definition tri_lim_acone : AGraphCone TriD p.
Proof.
  unshelve eapply Build_AGraphCone.
  - exact tri_lim_legs.
  - intros i j e.
    destruct i, j; simpl in e; try destruct e; simpl;
      rewrite ?id_right; reflexivity.
Defined.

Definition TriangleGraphCone : GraphCone TriD :=
  {| gvertex_obj := p ; gconeFrom := tri_lim_acone |}.

(* Every arrow into the apex induces a competing graph cone. *)
Definition tri_gcone_of_arrow {c : obj[C]} (f : c ~{C}~> p) : GraphCone TriD.
Proof.
  unshelve eapply Build_GraphCone; [ exact c | ].
  unshelve eapply Build_AGraphCone.
  - exact (fun i => match i as i0 return c ~{C}~> TriD i0 with
                    | TrX => f
                    | TrY => u ∘ f
                    | TrZ => (v ∘ u) ∘ f
                    end).
  - intros i j e.
    destruct i, j; simpl in e; try destruct e; simpl;
      rewrite ?comp_assoc; reflexivity.
Defined.

(* The apex [p] is the limit, over an arbitrary category and arbitrary
   [u], [v].  The mediator is the competing cone's leg at [TrX]; the
   coherence instance at the edge Y->Z is never spent. *)
Theorem triangle_graph_limit : IsLimitGraphCone TriangleGraphCone.
Proof.
  intro M.
  unshelve eapply Build_Unique.
  - exact (gcone_leg M TrX).
  - intro i; destruct i; simpl.
    + apply id_left.
    + exact (@gcone_coherence _ _ _ _ (@gconeFrom _ _ _ M) TrX TrY tt).
    + exact (@gcone_coherence _ _ _ _ (@gconeFrom _ _ _ M) TrX TrZ tt).
  - intros m Hm.
    pose proof (Hm TrX) as H; simpl in H.
    rewrite id_left in H.
    now symmetry.
Defined.

Example tri_med_is_arrow {c : obj[C]} (f : c ~{C}~> p) :
  graph_limit_med triangle_graph_limit (tri_gcone_of_arrow f) = f := eq_refl.

(** *** No functoriality: the triangles at the two parallel X->Z arrows *)

(* [tri_via_Y] and [tri_direct] are DISTINCT morphisms of the free category
   (Theory/Diagram.v:662's [tri_via_Y_neq_direct]), and a graph cone states a
   triangle for neither.  Both are consequences of the edge conditions,
   through [gcone_dpath]. *)
Lemma tri_gcone_at_via_Y (M : GraphCone TriD) :
  dpath TriD tri_via_Y ∘ gcone_leg M TrX ≈ gcone_leg M TrZ.
Proof. exact (gcone_leg_dpath M tri_via_Y). Qed.

Lemma tri_gcone_at_direct (M : GraphCone TriD) :
  dpath TriD tri_direct ∘ gcone_leg M TrX ≈ gcone_leg M TrZ.
Proof. exact (gcone_leg_dpath M tri_direct). Qed.

End TriangleLimit.

Example tri_via_Y_len : tlist_length tri_via_Y = 2%nat := eq_refl.
Example tri_direct_len : tlist_length tri_direct = 1%nat := eq_refl.

(** ** Witness two: the walking loop, one field against infinitely many
       arrows *)

Fixpoint loop_path (n : nat) : tlist (@edges LoopQuiver) LpX LpX :=
  match n with
  | O   => tnil
  | S k => tcons LpX (tt : @edges LoopQuiver LpX LpX) (loop_path k)
  end.

Lemma loop_path_length (n : nat) : tlist_length (loop_path n) = n.
Proof.
  induction n as [ | k IH ]; simpl; [ reflexivity | ].
  apply f_equal; exact IH.
Qed.

(* The paths are pairwise distinct arrows of the free category, so the
   endo-hom at the single node is infinite. *)
Lemma loop_paths_distinct (n m : nat) :
  (loop_path n ≈[FreeOnQuiver LoopQuiver] loop_path m) → n = m.
Proof.
  intro H.
  pose proof (tlist'_equiv_lengths LoopQuiver LpX LpX LpX
                (loop_path n) (loop_path m) eq_refl H) as Hl.
  now rewrite !loop_path_length in Hl.
Qed.

Section LoopCone.

Context {C : Category}.
Context {a : C} (e : a ~{C}~> a).

(* A graph cone over the loop diagram is EXACTLY an arrow [psi] with
   [e ∘ psi ≈ psi]: one datum, one equation. *)
Definition loop_gcone {c : obj[C]} (psi : c ~{C}~> a) (H : e ∘ psi ≈ psi) :
  GraphCone (LoopDiagram e).
Proof.
  unshelve eapply Build_GraphCone; [ exact c | ].
  unshelve eapply Build_AGraphCone.
  - exact (fun i => match i as i0 return c ~{C}~> LoopDiagram e i0 with
                    | LpX => psi
                    end).
  - intros i j w; destruct i, j; simpl; exact H.
Defined.

Example loop_gcone_leg {c : obj[C]} (psi : c ~{C}~> a) (H : e ∘ psi ≈ psi) :
  gcone_leg (loop_gcone psi H) LpX = psi := eq_refl.

Lemma loop_gcone_fix (N : GraphCone (LoopDiagram e)) :
  e ∘ gcone_leg N LpX ≈ gcone_leg N LpX.
Proof. exact (@gcone_coherence _ _ _ _ (@gconeFrom _ _ _ N) LpX LpX tt). Qed.

(* ... and that one equation discharges the triangle at EVERY path, hence at
   every arrow of the free category, by [gcone_dpath] alone. *)
Theorem loop_gcone_every_path (N : GraphCone (LoopDiagram e)) (n : nat) :
  dpath (LoopDiagram e) (loop_path n) ∘ gcone_leg N LpX ≈ gcone_leg N LpX.
Proof. exact (gcone_leg_dpath N (loop_path n)). Qed.

End LoopCone.

(** ** Witness three: the triangle limit computing in [Coq] *)

Definition coq_u : nat ~{Coq}~> nat := S.
Definition coq_v : nat ~{Coq}~> bool := Nat.even.

Definition CoqTriDiagram : Diagram TriangleQuiver Coq :=
  TriangleDiagram coq_u coq_v (coq_v ∘ coq_u).

Definition CoqTriCone : GraphCone CoqTriDiagram :=
  TriangleGraphCone coq_u coq_v.

Example coq_tri_apex : gvertex_obj[CoqTriCone] = nat := eq_refl.
Example coq_tri_X : gcone_leg CoqTriCone TrX 3%nat = 3%nat := eq_refl.
Example coq_tri_Y : gcone_leg CoqTriCone TrY 3%nat = 4%nat := eq_refl.
Example coq_tri_Z : gcone_leg CoqTriCone TrZ 3%nat = true := eq_refl.
Example coq_tri_Z' : gcone_leg CoqTriCone TrZ 4%nat = false := eq_refl.

Definition coq_probe : bool ~{Coq}~> nat := fun b => if b then 1%nat else 0%nat.

Definition CoqProbeCone : GraphCone CoqTriDiagram :=
  tri_gcone_of_arrow coq_u coq_v coq_probe.

Example coq_probe_med :
  graph_limit_med (triangle_graph_limit coq_u coq_v) CoqProbeCone = coq_probe
  := eq_refl.

Example coq_probe_med_true :
  graph_limit_med (triangle_graph_limit coq_u coq_v) CoqProbeCone true = 1%nat
  := eq_refl.

Example coq_probe_Z_t : gcone_leg CoqProbeCone TrZ true = true := eq_refl.
Example coq_probe_Z_f : gcone_leg CoqProbeCone TrZ false = false := eq_refl.
Example coq_probe_Y : gcone_leg CoqProbeCone TrY true = 2%nat := eq_refl.
