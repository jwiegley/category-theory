From Coq Require Import Lia.
Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.PreorderReflection.

Generalizable All Variables.

(** * Diagrams and commutativity *)

(* nLab: https://ncatlab.org/nlab/show/commutative+diagram

   A DIAGRAM in a category [C] over a quiver (directed multigraph) [G] is a
   labelling of the vertices of [G] by objects of [C] and of its edges by
   morphisms of [C], respecting sources and targets.  That is exactly a quiver
   homomorphism [G ⇨ QuiverOfCat C] (Construction/Free/Quiver.v:205 for the
   class [QuiverHomomorphism], :54 for [Quiver]), which is how [Diagram] is
   defined below.

   A PATH in [G] is a finite composable chain of edges, i.e. an inhabitant of
   [tlist edges x y] (Lib/TList.v); it is also, definitionally, a morphism
   [x ~> y] of the free category [FreeOnQuiver G] (Construction/Free/Quiver.v:431).
   [dpath] denotes such a path by composing its edge labels in [C], and
   [Commutative D] asserts that ANY two paths sharing a source and a target
   denote [≈]-equal morphisms.  The quantification is over all pairs of
   vertices and all pairs of parallel paths of arbitrary length; no diagram
   shape is privileged.

   The bridge to the free category runs both ways.  [FunctorOfDiagram] sends a
   diagram to the functor [FreeOnQuiver G ⟶ C] extending it (this is
   Quiver.v's [InducedFunctor]), [DiagramOfFunctor] restricts a functor along
   the unit [UnitQuiverCatAdjunction] back to a diagram, and the two round
   trips are proved: [functor_of_diagram_of_functor] in the hom-setoid of
   StrictCat and [diagram_of_functor_of_diagram] in [QuiverCategory].  Under
   that correspondence [Commutative D] is precisely [CommutativeShape] of the
   extending functor, i.e. the functor sends every parallel pair of the free
   category to a single morphism ([commutative_iff_shape],
   [shape_iff_commutative]).

   SCOPE of "correspondence": both directions are maps of the underlying
   types, and both round trips are proved pointwise.  Respectfulness of the
   two maps for the two equivalences, and naturality in [G] and [C], are NOT
   established here, so nothing below asserts an isomorphism of hom-setoids.
   What IS proved is that the two maps are mutually inverse up to [≈],
   pointwise; that is weaker than a bijection of the underlying types, since
   the round trips are up to [≈] rather than up to [=], and weaker than a
   bijection of the setoid quotients, since without respectfulness the maps do
   not descend to them.
   The universal property that would package them is already in the tree --
   Construction/Free/Quiver.v:518's [UniversalArrowQuiverCat] and :550's
   [FreeForgetfulAdjunction].  The two round trips below are NOT derived from
   it: each is proved directly by induction.  They carry the same content its
   existence and uniqueness halves would give, but that agreement is not
   itself proved here.

   Instances: the walking square and the walking triangle are built as quivers
   here, and for each the general predicate is proved EQUIVALENT to the single
   familiar two-composite equation ([square_commutative_iff],
   [triangle_commutative_iff]).  The naturality square of a natural
   transformation is such a commuting square
   ([naturality_square_commutative_iff]).  A faithful functor reflects
   commutativity ([faithful_reflects_commutative]) and every functor preserves
   it ([functor_preserves_commutative]); both also hold in the
   diagram-as-functor formulation, for an arbitrary indexing category
   ([faithful_reflects_commutative_shape],
   [functor_preserves_commutative_shape]). *)

(* Diagrams and commutation: sources and in-tree connections

   Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          Springer GTM 5, 1998, §I.1 "Axioms for Categories", printed p. 8
          (PDF p. 18), the third numbered definition of that section.
   Book:  Fong and Spivak, "Seven Sketches in Compositionality", CUP 2019,
          §3.3.4 Definition 3.51, printed p. 95 (PDF p. 107).
   Book:  Riehl, "Category Theory in Context", 2nd ed., §1.1, printed
          pp. 3-4 (PDF pp. 23-24); §1.6, printed p. 39 (PDF p. 59);
          Lemma 1.6.20, printed p. 46 (PDF p. 66).
   nLab:  https://ncatlab.org/nlab/show/commutative+diagram

   The three books are cited BY LOCATION only.  Their printed text was not
   consulted while writing this file, so nothing here quotes or paraphrases
   them; the locations record where each result is stated, and the Coq
   statements below stand on their own.  The attributions follow the issue
   that requested this file (jwiegley/category-theory#216), which supplies
   those locations.

   Why this file exists.  Commutativity is the working language of category
   theory, and the reusable in-tree statements of it each fix a single FIGURE
   with a fixed number of sides: [Construction/Sq.v:50] fixes a square
   ([dsq := fun a b c d h u v k => k ∘ u ≈ v ∘ h]), [Structure/Cone.v:30]'s
   [cone_coherence] fixes the apex triangle of a cone leg, and
   [Theory/Morphisms/Stability.v:55]'s [is_pullback_commutes] fixes the
   pullback square.  Each of the three ranges over arbitrary MORPHISMS -- so
   its sides may themselves be long composites -- but each pins the figure,
   and none quantifies over PAIRS OF PARALLEL PATHS in a shape.  That last
   quantification is what [Commutative] adds, and it is what makes the
   predicate independent of any drawing.  Issue #216's coverage pass reports
   that elsewhere in the tree commutativity appears only as an ad hoc [≈]
   equation between two named composites; that survey is the issue's, and is
   not re-verified here.

   Relation to the solver.  [Solver/Expr.v:65] reifies composite morphisms as
   an untyped term grammar [Term ::= Ident | Morph nat | Comp Term Term],
   and its own header comment (Solver/Expr.v:58-64) records that this grammar
   "is exactly a term of the free category on the quiver whose edges are the
   variables [arrs]".  The typed in-tree counterpart of that grammar is
   [Mor ::= Ident | Morph edge | Comp] of Construction/Free/Quiver.v:559,
   normalised to a path by [morDA] (:564).  [dterm] below interprets [Mor] in
   [C] with the same reading of [Comp] that Solver/Denote.v uses (there,
   "[Comp f g] denotes [f ∘ g]"), and [dterm_dpath] proves that interpreting a
   term agrees with denoting its normal-form path.  [commutative_dterm] is the
   consequence a solver would want: over a commutative diagram, ALL parallel
   terms are interchangeable, not merely the ones a normaliser can identify.

   The Seven Sketches footnote packaging -- that a diagram commutes exactly
   when it factors through the preorder reflection of its indexing category --
   is proved below in both directions ([commutative_shape_factors],
   [factors_commutative_shape], [factors_commutative_shape'],
   [commutative_factors]) and packaged as the single biconditional
   [commutes_iff_factors], over Construction/PreorderReflection.v.  The
   forward factorization is moreover an equality of FUNCTORS in StrictCat's
   hom-setoid ([shape_factor_functor]), not merely a pointwise agreement.
   That file needed no new machinery: Construction/Quotient.v already
   quotients a category by a hom-congruence, and the preorder reflection is
   that quotient at the total congruence; what it adds is the universal
   property [ThinLift], which makes it THE universal thin quotient rather than
   a quotient that happens to be thin.

   SCOPE.  What Construction/PreorderReflection.v supplies is the construction
   and its thinness only.  The remaining parts of
   jwiegley/category-theory#803 -- the truncated object preorder, functoriality
   of the reflection on [Cat], and the adjunction with the inclusion of
   preorders -- are NOT built, and nothing below depends on them. *)

#[local] Existing Instance edgeset.

(** ** Diagrams, path denotation, and the commutativity predicate *)

Section DiagramCore.

Context {G : Quiver}.
Context {C : Category}.

(* A diagram in [C] of shape [G]: vertices go to objects, edges to morphisms
   between the labels of their endpoints.  Source and target preservation is
   automatic because a [Quiver]'s edges are indexed by their endpoints. *)
Definition Diagram : Type := QuiverHomomorphism G (QuiverOfCat C).

Context (D : Diagram).

(* The morphism labelling an edge.  [fnodes] is a coercion, so [D x] is the
   object labelling the vertex [x]. *)
Definition dedge {x y : G} (e : edges x y) : D x ~{C}~> D y :=
  @fedgemap G (QuiverOfCat C) D x y e.

(* Denotation of a path: compose the edge labels along it.  The empty path
   denotes the identity; [e ::: p] denotes [dpath p ∘ dedge e], the edge first
   because a path runs source-to-target while [∘] is written right-to-left. *)
Fixpoint dpath {x y : G} (p : tlist edges x y) : D x ~{C}~> D y :=
  match p in tlist' _ i return D i ~{C}~> D y with
  | tnil            => id
  | tcons _ e rest  => dpath rest ∘ dedge e
  end.

(* Path denotation turns concatenation into composition. *)
Lemma dpath_app {x y z : G} (p : tlist edges x y) (q : tlist edges y z) :
  dpath (p +++ q) ≈ dpath q ∘ dpath p.
Proof.
  induction p as [ | i m e p IH ].
  - rewrite tlist_app_tnil_l; simpl.
    now rewrite id_right.
  - rewrite <- tlist_app_comm_cons; simpl.
    rewrite IH.
    now rewrite comp_assoc.
Qed.

(* Mac Lane's condition: any two paths with the same source and the same
   target have the same composite.  Both vertices and both paths are
   universally quantified, and paths carry no length bound, so this covers
   every diagram shape at once rather than a fixed square or triangle.

   The EMPTY path counts as a path, so taking [q := tnil] forces every
   endo-path to denote [id]: over a shape with a loop [e : x -> x],
   [Commutative] therefore requires [dedge D e ≈ id], and a diagram drawing a
   non-identity endomorphism is not [Commutative].  That is the intended
   reading and it matches the functor formulation, whose quantification over
   parallel pairs likewise includes the identity; [commutative_iff_shape]
   proves the two agree.

   That consequence is not left as prose: [loop_commutative_iff] below proves
   it in both directions over the walking loop, and
   Theory/Diagram/Examples.v exhibits a concrete diagram that draws a
   non-identity endomorphism and is therefore not [Commutative].

   CARE IS NEEDED STATING WHAT THIS SEPARATES.  It is NOT that the
   figure-fixing statements cannot express a loop condition: Construction/
   Sq.v:50's [dsq a b c d h u v k := k ∘ u ≈ v ∘ h] quantifies over arbitrary
   OBJECTS, so all four corners may be instantiated to one object [X], making
   [h : X ~> X] an endo-path; [dsq X X X X e id id id] then reduces to
   [id ∘ id ≈ id ∘ e], which is exactly [e ≈ id].  The real distinction is
   about who supplies the condition.  [Commutative] FORCES [e ≈ id] from the
   SHAPE alone, with no choice of instantiation: the empty path is always
   available as a competitor to any endo-path.  [dsq] can be INSTANTIATED to
   state that equation but never forces it, and the degenerate instantiation
   is not what any of its in-tree uses does.  For [cone_coherence] and
   [is_pullback_commutes] the point is different again -- each is a FIELD of a
   record, so it cannot be freely instantiated at all. *)
Definition Commutative : Type :=
  ∀ (x y : G) (p q : tlist edges x y), dpath p ≈ dpath q.

End DiagramCore.

Arguments Diagram : clear implicits.
Arguments dedge {G C} D {x y} e.
Arguments dpath {G C} D {x y} p.
Arguments Commutative {G C} D.

(** ** The diagram-as-functor form of the predicate *)

(* The Seven Sketches formulation: a diagram is a functor out of an indexing
   category, and it commutes when every parallel pair of the indexing category
   has a single image.  For an indexing category that is free on a quiver this
   is the same condition as [Commutative], proved below. *)
Definition CommutativeShape {J C : Category} (F : J ⟶ C) : Type :=
  ∀ (x y : J) (f g : x ~{J}~> y), fmap[F] f ≈ fmap[F] g.

(** ** The bridge to the free category *)

Section DiagramBridge.

Context {G : Quiver}.
Context {C : Category}.

(* A diagram extends to a functor on the free category: this is Quiver.v's
   [InducedFunctor], named here for the correspondence. *)
Definition FunctorOfDiagram (D : Diagram G C) : FreeOnQuiver G ⟶ C :=
  InducedFunctor G D.

(* ... and a functor on the free category restricts to a diagram, by
   composing with the unit of the free/forgetful adjunction, which sends an
   edge to the one-edge path. *)
Definition DiagramOfFunctor (F : FreeOnQuiver G ⟶ C) : Diagram G C :=
  QuiverComp (UnitQuiverCatAdjunction G)
             (QuiverHomomorphismOfFunctor (FreeOnQuiver G) C F).

(* Path denotation is the extending functor's action on morphisms. *)
Lemma dpath_fmap (D : Diagram G C) {x y : G} (p : tlist edges x y) :
  dpath D p ≈ fmap[FunctorOfDiagram D] p.
Proof.
  induction p as [ | i m e p IH ]; simpl; [ reflexivity | ].
  now rewrite IH.
Qed.

(* Denoting a path in the restricted diagram is applying the original functor
   to that path, viewed as a morphism of the free category.  Proved for paths
   of arbitrary length, by induction. *)
Lemma dpath_of_functor (F : FreeOnQuiver G ⟶ C) {x y : G} (p : tlist edges x y) :
  dpath (DiagramOfFunctor F) p ≈ fmap[F] p.
Proof.
  induction p as [ | i m e p IH ]; simpl.
  - change (@tnil _ _ y) with (@id (FreeOnQuiver G) y).
    now rewrite fmap_id.
  - (* [≈], not [=]: [tlist_app_cons] (Lib/TList.v:199) is proved by
       [destruct], so the two sides are not the same term and the
       Functor/Bifunctor.v:42-45 exception does not apply.  This mirrors the
       [RW] step of Construction/Free/Quiver.v:532. *)
    assert (Hsplit : @equiv _ (@homset (FreeOnQuiver G) i y) (e ::: p)
                       (@compose (FreeOnQuiver G) _ _ _ p (tlist_singleton e)))
      by (unfold tlist_singleton; simpl; now rewrite <- tlist_app_cons).
    rewrite Hsplit, fmap_comp.
    apply compose_respects; [ exact IH | reflexivity ].
Qed.

(* Round trip one: extending the restriction of a functor gives that functor
   back.  The equivalence used is [Functor_StrictEq_Setoid]
   (Theory/Functor.v:508), which is exactly the hom-setoid of the strict
   category of categories (Instance/StrictCat.v:59): objects agree on the nose
   -- here by [eq_refl], since the two functors have the same object map by
   definition -- and the transported morphism maps agree up to [≈]. *)
Lemma functor_of_diagram_of_functor (F : FreeOnQuiver G ⟶ C) :
  @equiv _ (@Functor_StrictEq_Setoid (FreeOnQuiver G) C)
         (FunctorOfDiagram (DiagramOfFunctor F)) F.
Proof.
  exists (fun _ => eq_refl).
  intros x y p.
  change (fmap[FunctorOfDiagram (DiagramOfFunctor F)] p ≈ fmap[F] p).
  transitivity (dpath (DiagramOfFunctor F) p);
    [ symmetry; apply dpath_fmap | apply dpath_of_functor ].
Qed.

(* Round trip two: restricting the extension of a diagram gives that diagram
   back, as morphisms of [QuiverCategory].  The vertex maps agree definitionally
   ([eq_refl]); on edges the round trip inserts one identity, removed by
   [id_left]. *)
Lemma diagram_of_functor_of_diagram (D : Diagram G C) :
  DiagramOfFunctor (FunctorOfDiagram D) ≈[QuiverCategory] D.
Proof.
  exists (fun _ => eq_refl).
  intros x y e; simpl.
  now rewrite id_left.
Qed.

(* Commutativity of a diagram is exactly the statement that its extending
   functor identifies parallel morphisms of the free category.  This is the
   agreement of Mac Lane's quiver-and-paths formulation with the Seven
   Sketches diagram-as-functor formulation: morphisms of [FreeOnQuiver G] ARE
   the paths of [G], so the two quantifications range over the same pairs. *)
Theorem commutative_iff_shape (D : Diagram G C) :
  Commutative D ↔ CommutativeShape (FunctorOfDiagram D).
Proof.
  split; intros H x y p q.
  - transitivity (dpath D p); [ symmetry; apply dpath_fmap | ].
    transitivity (dpath D q); [ apply H | apply dpath_fmap ].
  - transitivity (fmap[FunctorOfDiagram D] p); [ apply dpath_fmap | ].
    transitivity (fmap[FunctorOfDiagram D] q);
      [ apply H | symmetry; apply dpath_fmap ].
Qed.

(* The same correspondence read from the functor side. *)
Theorem shape_iff_commutative (F : FreeOnQuiver G ⟶ C) :
  CommutativeShape F ↔ Commutative (DiagramOfFunctor F).
Proof.
  split; intros H x y p q.
  - transitivity (fmap[F] p); [ apply dpath_of_functor | ].
    transitivity (fmap[F] q); [ apply H | symmetry; apply dpath_of_functor ].
  - transitivity (dpath (DiagramOfFunctor F) p);
      [ symmetry; apply dpath_of_functor | ].
    transitivity (dpath (DiagramOfFunctor F) q);
      [ apply H | apply dpath_of_functor ].
Qed.

End DiagramBridge.

(** ** Terms over a diagram *)

Section DiagramTerms.

Context {G : Quiver}.
Context {C : Category}.
Context (D : Diagram G C).

(* Interpret a formal composite (Construction/Free/Quiver.v:559) in [C].  The
   reading of [Comp f g] as [f ∘ g] is the one Solver/Denote.v documents for
   the untyped [Term] of Solver/Expr.v:65. *)
Fixpoint dterm {x y : G} (t : Mor x y) : D x ~{C}~> D y :=
  match t in @Mor _ x0 y0 return D x0 ~{C}~> D y0 with
  | Ident      => id
  | Morph e    => dedge D e
  | Comp f g   => dterm f ∘ dterm g
  end.

(* Interpreting a term agrees with denoting the path it normalises to. *)
Lemma dterm_dpath {x y : G} (t : Mor x y) : dterm t ≈ dpath D (morDA t).
Proof.
  induction t as [ x | x y e | x y z f IHf g IHg ]; simpl.
  - reflexivity.
  - now rewrite id_left.
  - rewrite dpath_app.
    now rewrite IHf, IHg.
Qed.

(* Over a commutative diagram every pair of parallel terms is interchangeable,
   whatever their shapes or lengths. *)
Corollary commutative_dterm (Hc : Commutative D) {x y : G} (s t : Mor x y) :
  dterm s ≈ dterm t.
Proof.
  rewrite (dterm_dpath s), (dterm_dpath t).
  now apply Hc.
Qed.

End DiagramTerms.

Arguments dterm {G C} D {x y} t.

(** ** Transporting a diagram along a functor *)

Section DiagramFunctorial.

Context {G : Quiver}.
Context {C E : Category}.

(* The image of a diagram under a functor, again a diagram. *)
Definition PostcomposeDiagram (U : C ⟶ E) (D : Diagram G C) : Diagram G E :=
  QuiverComp D (QuiverHomomorphismOfFunctor C E U).

(* The functor commutes with path denotation, for paths of arbitrary length. *)
Lemma dpath_postcompose (U : C ⟶ E) (D : Diagram G C)
      {x y : G} (p : tlist edges x y) :
  dpath (PostcomposeDiagram U D) p ≈ fmap[U] (dpath D p).
Proof.
  induction p as [ | i m e p IH ]; simpl.
  - now rewrite fmap_id.
  - transitivity (fmap[U] (dpath D p) ∘ fmap[U] (dedge D e)).
    + apply compose_respects; [ exact IH | reflexivity ].
    + symmetry; apply fmap_comp.
Qed.

(* Every functor preserves commutativity. *)
Theorem functor_preserves_commutative (U : C ⟶ E) (D : Diagram G C) :
  Commutative D -> Commutative (PostcomposeDiagram U D).
Proof.
  intros Hc x y p q.
  transitivity (fmap[U] (dpath D p)); [ apply dpath_postcompose | ].
  transitivity (fmap[U] (dpath D q));
    [ apply fmap_respects, Hc | symmetry; apply dpath_postcompose ].
Qed.

(* Riehl, Lemma 1.6.20: a FAITHFUL functor reflects commutativity.  If the
   image diagram commutes then the diagram already commutes.  The proof is by
   [fmap_inj] (Theory/Functor.v:343) applied to the two path denotations, and
   holds for parallel paths of arbitrary length because [dpath_postcompose]
   does. *)
Theorem faithful_reflects_commutative (U : C ⟶ E) `{@Faithful C E U}
        (D : Diagram G C) :
  Commutative (PostcomposeDiagram U D) -> Commutative D.
Proof.
  intros Hc x y p q.
  apply fmap_inj.
  transitivity (dpath (PostcomposeDiagram U D) p);
    [ symmetry; apply dpath_postcompose | ].
  transitivity (dpath (PostcomposeDiagram U D) q);
    [ apply Hc | apply dpath_postcompose ].
Qed.

End DiagramFunctorial.

(* The same two facts in the diagram-as-functor formulation, where they need
   no quiver at all: they hold for a diagram indexed by ANY category. *)
Theorem functor_preserves_commutative_shape {J C E : Category}
        (U : C ⟶ E) (F : J ⟶ C) :
  CommutativeShape F -> CommutativeShape (U ◯ F).
Proof.
  intros Hc x y f g; simpl.
  now apply fmap_respects, Hc.
Qed.

Theorem faithful_reflects_commutative_shape {J C E : Category}
        (U : C ⟶ E) `{@Faithful C E U} (F : J ⟶ C) :
  CommutativeShape (U ◯ F) -> CommutativeShape F.
Proof.
  intros Hc x y f g.
  apply fmap_inj.
  exact (Hc x y f g).
Qed.

(** ** The walking square *)

(* Four vertices and four edges,

        A --u--> B
        |        |
        h        v
        |        |
        v        v
        C --k--> D

   with no edge out of D and no edge into A. *)
Inductive SqNode : Set := SqA | SqB | SqC | SqD.

Definition sq_edge (i j : SqNode) : Type :=
  match i, j with
  | SqA, SqB => unit
  | SqA, SqC => unit
  | SqB, SqD => unit
  | SqC, SqD => unit
  | _  , _   => Empty_set
  end.

Definition SquareQuiver : Quiver := Build_Quiver_Standard_Eq SqNode sq_edge.

(* Sanity: the edge sets are the intended ones. *)
Example sq_edge_AB : @edges SquareQuiver SqA SqB = unit := eq_refl.
Example sq_edge_BD : @edges SquareQuiver SqB SqD = unit := eq_refl.
Example sq_edge_DA : @edges SquareQuiver SqD SqA = Empty_set := eq_refl.

(* The two paths from A to D. *)
Definition sq_via_B : tlist (@edges SquareQuiver) SqA SqD :=
  tcons SqA (tt : @edges SquareQuiver SqA SqB)
    (tcons SqB (tt : @edges SquareQuiver SqB SqD) tnil).

Definition sq_via_C : tlist (@edges SquareQuiver) SqA SqD :=
  tcons SqA (tt : @edges SquareQuiver SqA SqC)
    (tcons SqC (tt : @edges SquareQuiver SqC SqD) tnil).

(* This quiver genuinely has a parallel pair: the two paths are DISTINCT
   morphisms of the free category, since they pass through different vertices
   and [SqB = SqC] is refutable.  Without this the commutativity predicate
   would be vacuous on this shape. *)
Lemma sq_via_B_neq_via_C :
  (sq_via_B ≈[FreeOnQuiver SquareQuiver] sq_via_C) -> False.
Proof.
  intro Hbc.
  unfold sq_via_B, sq_via_C in Hbc; simpl in Hbc.
  destruct Hbc as [Hq _ _].
  discriminate Hq.
Qed.

(* ACYCLICITY, proved rather than asserted.  Ranking the vertices so that every
   edge strictly increases the rank bounds the length of any path by the rank
   difference; an endo-path has rank difference zero, hence length zero, hence
   is [tnil].  This is what makes the endo-path clause of [Commutative] inert
   on this shape -- NOT the emptiness of the self-edge sets, which alone would
   leave a directed cycle of length two or more possible. *)
Definition sq_rank (i : SqNode) : nat :=
  match i with SqA => 0 | SqB => 1 | SqC => 1 | SqD => 2 end.

Lemma sq_len_rank (i j : SqNode) (p : tlist (@edges SquareQuiver) i j) :
  (sq_rank i + tlist_length p <= sq_rank j)%nat.
Proof.
  induction p as [ | i m e p IH ]; simpl.
  - lia.
  - destruct i, m; simpl in e; try contradiction; simpl in *; lia.
Qed.

Lemma sq_endo_paths_are_nil (i : SqNode)
      (p : tlist (@edges SquareQuiver) i i) : tlist_length p = 0%nat.
Proof. pose proof (sq_len_rank i i p); lia. Qed.

Section WalkingSquare.

Context {C : Category}.
Context {a b c d : C} (u : a ~> b) (v : b ~> d) (h : a ~> c) (k : c ~> d).

Definition sq_obj (i : SqNode) : C :=
  match i with SqA => a | SqB => b | SqC => c | SqD => d end.

Definition sq_edgemap (i j : SqNode) : sq_edge i j -> sq_obj i ~> sq_obj j :=
  match i, j return sq_edge i j -> sq_obj i ~> sq_obj j with
  | SqA, SqB => fun _ => u
  | SqA, SqC => fun _ => h
  | SqB, SqD => fun _ => v
  | SqC, SqD => fun _ => k
  | _  , _   => fun e => match e with end
  end.

Program Definition SquareDiagram : Diagram SquareQuiver C :=
  {| fnodes := sq_obj ; fedgemap := sq_edgemap |}.

(* The edge labels are the four given morphisms.  The equality is Leibniz (=)
   rather than [≈] because the two sides are the very same term; this is the
   convention documented at Functor/Bifunctor.v:42-45. *)
Example sq_label_u : dedge SquareDiagram (tt : @edges SquareQuiver SqA SqB) = u
  := eq_refl.
Example sq_label_k : dedge SquareDiagram (tt : @edges SquareQuiver SqC SqD) = k
  := eq_refl.

(* The composite denoted by each of the two paths. *)
Example sq_denote_via_B : dpath SquareDiagram sq_via_B ≈ v ∘ u.
Proof. simpl; now rewrite id_left. Qed.

Example sq_denote_via_C : dpath SquareDiagram sq_via_C ≈ k ∘ h.
Proof. simpl; now rewrite id_left. Qed.

(* The specification of every path of the square, by its endpoints.  [False]
   marks the vertex pairs joined by no path at all.  Read as: assuming the
   square commutes, a path's denotation is determined by its endpoints. *)
Definition sq_spec (i j : SqNode) : (sq_obj i ~{C}~> sq_obj j) -> Type :=
  match i, j return (sq_obj i ~{C}~> sq_obj j) -> Type with
  | SqA, SqA => fun f => f ≈ id
  | SqB, SqB => fun f => f ≈ id
  | SqC, SqC => fun f => f ≈ id
  | SqD, SqD => fun f => f ≈ id
  | SqA, SqB => fun f => f ≈ u
  | SqA, SqC => fun f => f ≈ h
  | SqA, SqD => fun f => f ≈ v ∘ u
  | SqB, SqD => fun f => f ≈ v
  | SqC, SqD => fun f => f ≈ k
  | _  , _   => fun _ => False
  end.

Lemma sq_paths (Hsq : v ∘ u ≈ k ∘ h) (i j : SqNode)
      (p : tlist (@edges SquareQuiver) i j) :
  sq_spec i j (dpath SquareDiagram p).
Proof.
  induction p as [ | i m e p IH ].
  - destruct j; simpl; reflexivity.
  - (* Closed explicitly rather than with [cat]: every component of [cat]
       (Lib/Tactics.v:134) always succeeds, so [cat] can never report a
       missing step; and exactly one of these goals -- [k ∘ h ≈ v ∘ u] -- is
       the one place [Hsq] is used, so it is discharged by name.  The [ [> ... ] ]
       selector pins that to EXACTLY one remaining goal: without it, an edit
       that made [try reflexivity] close every goal would leave the chain
       running on none, silently succeeding with [Hsq] unused -- the same class
       of quiet-success defect the [cat] removal above is about.  This matches
       [tri_paths] below. *)
    destruct i, m; simpl in e; try destruct e;
      destruct j; simpl in *; try contradiction;
      rewrite IH; rewrite ?id_left; try reflexivity; [> symmetry; exact Hsq ].
Qed.

(* The one equation implies the general predicate over ALL parallel pairs. *)
Theorem square_commutes (Hsq : v ∘ u ≈ k ∘ h) : Commutative SquareDiagram.
Proof.
  intros x y p q.
  pose proof (sq_paths Hsq _ _ p) as Hp.
  pose proof (sq_paths Hsq _ _ q) as Hq.
  destruct x, y; simpl in Hp, Hq; try contradiction;
    now rewrite Hp, Hq.
Qed.

(* ... and conversely, instantiating the predicate at the two paths from A to
   D recovers the equation. *)
Theorem square_commutes_inv : Commutative SquareDiagram -> v ∘ u ≈ k ∘ h.
Proof.
  intro Hc.
  pose proof (Hc SqA SqD sq_via_B sq_via_C) as Heq.
  unfold sq_via_B, sq_via_C in Heq; simpl in Heq.
  now rewrite !id_left in Heq.
Qed.

(* So on the square shape the general predicate carries exactly the content of
   the familiar two-composite equation: nothing more, nothing less.  The
   informal reason usually given -- that this shape has just one pair of
   distinct parallel paths -- is a statement about paths up to equality and is
   NOT proved here; what is proved is the [↔] itself, semantically, via
   [sq_paths]. *)
Theorem square_commutative_iff :
  Commutative SquareDiagram ↔ v ∘ u ≈ k ∘ h.
Proof.
  split; [ apply square_commutes_inv | apply square_commutes ].
Qed.

End WalkingSquare.

(** ** The walking triangle *)

(* Three vertices, with a direct edge and a two-step route:

        X --w------------> Z
         \                ^
          u              /
           \            /
            > Y --v----/

   (the two-step route is [u] then [v]; [w] is the direct edge). *)
Inductive TriNode : Set := TrX | TrY | TrZ.

Definition tri_edge (i j : TriNode) : Type :=
  match i, j with
  | TrX, TrY => unit
  | TrY, TrZ => unit
  | TrX, TrZ => unit
  | _  , _   => Empty_set
  end.

Definition TriangleQuiver : Quiver := Build_Quiver_Standard_Eq TriNode tri_edge.

Definition tri_via_Y : tlist (@edges TriangleQuiver) TrX TrZ :=
  tcons TrX (tt : @edges TriangleQuiver TrX TrY)
    (tcons TrY (tt : @edges TriangleQuiver TrY TrZ) tnil).

Definition tri_direct : tlist (@edges TriangleQuiver) TrX TrZ :=
  tcons TrX (tt : @edges TriangleQuiver TrX TrZ) tnil.

(* Again a genuine parallel pair: the two-step route and the direct edge are
   distinct morphisms of the free category, since their first edges land on
   different vertices and [TrY = TrZ] is refutable. *)
Lemma tri_via_Y_neq_direct :
  (tri_via_Y ≈[FreeOnQuiver TriangleQuiver] tri_direct) -> False.
Proof.
  intro Hxy.
  unfold tri_via_Y, tri_direct in Hxy; simpl in Hxy.
  destruct Hxy as [Hq _ _].
  discriminate Hq.
Qed.

(* Acyclicity of the triangle, by the same rank argument. *)
Definition tri_rank (i : TriNode) : nat :=
  match i with TrX => 0 | TrY => 1 | TrZ => 2 end.

Lemma tri_len_rank (i j : TriNode) (p : tlist (@edges TriangleQuiver) i j) :
  (tri_rank i + tlist_length p <= tri_rank j)%nat.
Proof.
  induction p as [ | i m e p IH ]; simpl.
  - lia.
  - destruct i, m; simpl in e; try contradiction; simpl in *; lia.
Qed.

Lemma tri_endo_paths_are_nil (i : TriNode)
      (p : tlist (@edges TriangleQuiver) i i) : tlist_length p = 0%nat.
Proof. pose proof (tri_len_rank i i p); lia. Qed.

Section WalkingTriangle.

Context {C : Category}.
Context {x y z : C} (u : x ~> y) (v : y ~> z) (w : x ~> z).

Definition tri_obj (i : TriNode) : C :=
  match i with TrX => x | TrY => y | TrZ => z end.

Definition tri_edgemap (i j : TriNode) : tri_edge i j -> tri_obj i ~> tri_obj j :=
  match i, j return tri_edge i j -> tri_obj i ~> tri_obj j with
  | TrX, TrY => fun _ => u
  | TrY, TrZ => fun _ => v
  | TrX, TrZ => fun _ => w
  | _  , _   => fun e => match e with end
  end.

Program Definition TriangleDiagram : Diagram TriangleQuiver C :=
  {| fnodes := tri_obj ; fedgemap := tri_edgemap |}.

Definition tri_spec (i j : TriNode) : (tri_obj i ~{C}~> tri_obj j) -> Type :=
  match i, j return (tri_obj i ~{C}~> tri_obj j) -> Type with
  | TrX, TrX => fun f => f ≈ id
  | TrY, TrY => fun f => f ≈ id
  | TrZ, TrZ => fun f => f ≈ id
  | TrX, TrY => fun f => f ≈ u
  | TrY, TrZ => fun f => f ≈ v
  | TrX, TrZ => fun f => f ≈ w
  | _  , _   => fun _ => False
  end.

Lemma tri_paths (Htri : v ∘ u ≈ w) (i j : TriNode)
      (p : tlist (@edges TriangleQuiver) i j) :
  tri_spec i j (dpath TriangleDiagram p).
Proof.
  induction p as [ | i m e p IH ].
  - destruct j; simpl; reflexivity.
  - destruct i, m; simpl in e; try destruct e;
      destruct j; simpl in *; try contradiction;
      rewrite IH; rewrite ?id_left; try reflexivity; [> exact Htri ].
Qed.

Theorem triangle_commutes (Htri : v ∘ u ≈ w) : Commutative TriangleDiagram.
Proof.
  intros i j p q.
  pose proof (tri_paths Htri _ _ p) as Hp.
  pose proof (tri_paths Htri _ _ q) as Hq.
  destruct i, j; simpl in Hp, Hq; try contradiction;
    now rewrite Hp, Hq.
Qed.

Theorem triangle_commutes_inv : Commutative TriangleDiagram -> v ∘ u ≈ w.
Proof.
  intro Hc.
  pose proof (Hc TrX TrZ tri_via_Y tri_direct) as Heq.
  unfold tri_via_Y, tri_direct in Heq; simpl in Heq.
  now rewrite !id_left in Heq.
Qed.

Theorem triangle_commutative_iff :
  Commutative TriangleDiagram ↔ v ∘ u ≈ w.
Proof.
  split; [ apply triangle_commutes_inv | apply triangle_commutes ].
Qed.

End WalkingTriangle.

(** ** The walking loop: the empty path carries content *)

(* One vertex, one loop edge.

        X --e--> X   (a single edge from X to itself)

   Both shapes above are ACYCLIC, so in each of them the endo-path clause of
   [Commutative] is instantiated only at [tnil] and says nothing; this shape is
   the one that exercises it.  Note that "every [edges i i] is [Empty_set]"
   would NOT by itself establish that -- a directed cycle of length two or more
   produces an endo-path with no self-edge anywhere in it.  What actually
   rules cycles out is that the edges strictly increase a rank, which is proved
   below as [sq_endo_paths_are_nil] and [tri_endo_paths_are_nil] rather than
   asserted. *)
Inductive LoopNode : Set := LpX.

Definition loop_edge (i j : LoopNode) : Type :=
  match i, j with LpX, LpX => unit end.

Definition LoopQuiver : Quiver := Build_Quiver_Standard_Eq LoopNode loop_edge.

Example loop_edge_XX : @edges LoopQuiver LpX LpX = unit := eq_refl.

Section WalkingLoop.

Context {C : Category}.
Context {a : C}.
Context (e : a ~> a).

Definition loop_obj (i : LoopNode) : C := a.

Definition loop_edgemap (i j : LoopNode)
  : loop_edge i j -> loop_obj i ~> loop_obj j :=
  match i, j with LpX, LpX => fun _ => e end.

(* As with [SquareDiagram] and [TriangleDiagram], the [fedgemap_respects]
   obligation here is discharged by the file-global [Obligation Tactic]
   (Lib/Tactics.v:225's [cat_simpl]).  That is wide automation of exactly the
   kind this file argues against for LOAD-BEARING steps, so it is worth being
   explicit that these three are not load-bearing: each edge map is a constant
   or a match on a finite enumeration, and the obligation resolves to
   [CMorphisms.reflexive_proper]. *)
Program Definition LoopDiagram : Diagram LoopQuiver C :=
  {| fnodes := loop_obj ; fedgemap := loop_edgemap |}.

(* Every path in this shape denotes an iterate of [e]; under [e ≈ id] they all
   denote [id]. *)
Lemma loop_paths (He : e ≈ id) (i j : LoopNode)
      (p : tlist (@edges LoopQuiver) i j) :
  dpath LoopDiagram p ≈ id.
Proof.
  induction p as [ | i m ed p IH ].
  - reflexivity.
  - simpl; rewrite IH, id_left; destruct i, m; exact He.
Qed.

(* The forward direction is the empty-path argument itself: compare the
   one-edge path against [tnil]. *)
Theorem loop_commutes_inv : Commutative LoopDiagram -> e ≈ id.
Proof.
  intro Hc.
  pose proof (Hc LpX LpX
                (tcons LpX (tt : @edges LoopQuiver LpX LpX) tnil) tnil) as H.
  simpl in H.
  now rewrite id_left in H.
Qed.

Theorem loop_commutes (He : e ≈ id) : Commutative LoopDiagram.
Proof.
  intros i j p q.
  now rewrite (loop_paths He _ _ p), (loop_paths He _ _ q).
Qed.

(* So on the walking loop, commutativity is exactly the statement that the
   drawn endomorphism is the identity.  This is the header claim about [tnil],
   proved rather than asserted. *)
Theorem loop_commutative_iff : Commutative LoopDiagram ↔ e ≈ id.
Proof.
  split.
  - apply loop_commutes_inv.
  - apply loop_commutes.
Qed.

End WalkingLoop.

(** ** The naturality square as a commuting diagram *)

Section NaturalitySquare.

Context {C D : Category}.
Context {F G : C ⟶ D}.
Context (alpha : F ⟹ G).

(* The naturality square at [f : p ~> q], as a diagram of shape
   [SquareQuiver]:

        F p --fmap[F] f--> F q
         |                  |
       alpha p            alpha q
         |                  |
         v                  v
        G p --fmap[G] f--> G q                                            *)
Definition NaturalitySquareDiagram {p q : C} (f : p ~> q)
  : Diagram SquareQuiver D :=
  SquareDiagram (fmap[F] f) (@transform _ _ _ _ alpha q)
                (@transform _ _ _ _ alpha p) (fmap[G] f).

(* It commutes, by naturality.  [naturality_sym] (Theory/Natural/Transformation.v)
   is literally the equation [square_commutes] asks for. *)
Theorem naturality_square_commutes {p q : C} (f : p ~> q) :
  Commutative (NaturalitySquareDiagram f).
Proof.
  apply square_commutes.
  apply naturality_sym.
Qed.

(* And commutativity of that diagram gives naturality back, so for this shape
   the diagrammatic condition and the naturality equation are the same
   statement. *)
Theorem naturality_of_commutative_square {p q : C} (f : p ~> q) :
  Commutative (NaturalitySquareDiagram f) ->
  @transform _ _ _ _ alpha q ∘ fmap[F] f
    ≈ fmap[G] f ∘ @transform _ _ _ _ alpha p.
Proof.
  apply square_commutes_inv.
Qed.

Theorem naturality_square_commutative_iff {p q : C} (f : p ~> q) :
  Commutative (NaturalitySquareDiagram f)
    ↔ @transform _ _ _ _ alpha q ∘ fmap[F] f
        ≈ fmap[G] f ∘ @transform _ _ _ _ alpha p.
Proof.
  apply square_commutative_iff.
Qed.

End NaturalitySquare.


(** ** Commutativity as factorization through the preorder reflection *)

(* Fong and Spivak, Seven Sketches in Compositionality, §3.3.4, the footnote to
   Definition 3.51 (cited by location; see the header): a diagram commutes
   exactly when it factors through the preorder reflection of its indexing
   category.  Construction/PreorderReflection.v builds that reflection as the
   quotient of a category by the total hom-congruence.

   The intuition is that the reflection destroys precisely the information
   commutativity asks a diagram to ignore.  In [PreorderReflect J] all parallel
   morphisms are identified, so a functor out of it CANNOT distinguish two
   parallel paths -- it commutes for want of the ability to do otherwise -- and
   conversely a functor that already identifies parallel morphisms descends
   through the quotient. *)

(* (=>) A shape-commuting functor factors through the reflection, and the
   factorization reproduces it on the nose.  The mediating functor is
   [QuotientLift] at the total congruence, whose hypothesis is exactly
   [CommutativeShape]. *)
Definition ShapeFactor {J C : Category} (F : J ⟶ C) (Hc : CommutativeShape F)
  : PreorderReflect J ⟶ C :=
  @QuotientLift J (TotalRel J) _ C F (fun x y f g _ => Hc x y f g).

Theorem commutative_shape_factors {J C : Category} (F : J ⟶ C)
        (Hc : CommutativeShape F) :
  ∀ (x y : J) (f : x ~> y),
    fmap[ShapeFactor F Hc] (fmap[Reflect J] f) = fmap[F] f.
Proof.
  intros. exact (@QuotientLift_proj J (TotalRel J) _ C F _ x y f).
Qed.

(* The Leibniz [=] here is the library's same-term exception, not a lapse from
   [≈]: Construction/Quotient.v:322's [QuotientLift_proj] is proved by
   [reflexivity], the two sides being the same term, exactly as at
   Functor/Bifunctor.v:42-45. *)

(* (<=) Anything of the form [K ◯ Reflect J] commutes, whatever [K] is. *)
Theorem factors_commutative_shape {J C : Category}
        (K : PreorderReflect J ⟶ C) :
  CommutativeShape (K ◯ Reflect J).
Proof.
  intros x y f g; simpl; apply fmap_respects; exact I.
Qed.

(* The converse in the form that matches the forward direction: a functor that
   merely AGREES with such a composite -- pointwise up to [≈], with object maps
   equal on the nose, which is how Construction/Quotient.v states its
   uniqueness -- is itself shape-commuting. *)
Theorem factors_commutative_shape' {J C : Category} (F : J ⟶ C)
        (K : PreorderReflect J ⟶ C)
        (Hobj : ∀ x : J, fobj[K] x = fobj[F] x)
        (Hfac : ∀ (x y : J) (f : x ~> y),
                   hom_cast (Hobj x) (Hobj y)
                     (fmap[K] (fmap[Reflect J] f)) ≈ fmap[F] f) :
  CommutativeShape F.
Proof.
  intros x y f g.
  rewrite <- (Hfac x y f), <- (Hfac x y g).
  apply hom_cast_respects.
  apply fmap_respects.
  exact I.
Qed.

(* And hence for Mac Lane's quiver form of the predicate, through
   [commutative_iff_shape]: a commuting diagram factors through the preorder
   reflection of its FREE category. *)
Theorem commutative_factors {G : Quiver} {C : Category} (D : Diagram G C)
        (Hc : Commutative D) :
  ∀ (x y : FreeOnQuiver G) (f : x ~> y),
    fmap[ShapeFactor (FunctorOfDiagram D) (fst (commutative_iff_shape D) Hc)]
        (fmap[Reflect _] f)
      = fmap[FunctorOfDiagram D] f.
Proof.
  intros. apply commutative_shape_factors.
Qed.

(* The two directions above are usually quoted as a single biconditional, so
   state it.  "Factors through the reflection" is packaged as the data of a
   functor out of [PreorderReflect J] agreeing with [F], in exactly the form
   Construction/Quotient.v:334 uses for its own uniqueness statement: object
   maps equal on the nose, morphism maps agreeing up to [≈] after conjugating
   by [hom_cast] along those equalities. *)
Definition FactorsThroughReflection {J C : Category} (F : J ⟶ C) : Type :=
  { K : PreorderReflect J ⟶ C &
  { Hobj : ∀ x : J, fobj[K] x = fobj[F] x &
    ∀ (x y : J) (f : x ~> y),
      hom_cast (Hobj x) (Hobj y)
        (fmap[K] (fmap[Reflect J] f)) ≈ fmap[F] f }}.

(* The factorization is moreover an equality of FUNCTORS in StrictCat's
   hom-setoid, not merely a pointwise agreement -- the same equivalence
   [functor_of_diagram_of_functor] above is stated in. *)
Lemma shape_factor_functor {J C : Category} (F : J ⟶ C) (Hc : CommutativeShape F) :
  @equiv _ (@Functor_StrictEq_Setoid J C) (ShapeFactor F Hc ◯ Reflect J) F.
Proof.
  exists (fun _ => eq_refl); intros; reflexivity.
Qed.

Theorem commutes_iff_factors {J C : Category} (F : J ⟶ C) :
  CommutativeShape F ↔ FactorsThroughReflection F.
Proof.
  split.
  - intro Hc.
    exists (ShapeFactor F Hc), (fun _ => eq_refl).
    (* [hom_cast eq_refl eq_refl] disappears definitionally, and the
       factorization holds on the nose by [QuotientLift_proj]. *)
    intros x y f; reflexivity.
  - intros [K [Hobj Hfac]].
    exact (factors_commutative_shape' F K Hobj Hfac).
Qed.
