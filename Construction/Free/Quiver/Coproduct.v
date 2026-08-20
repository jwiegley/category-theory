Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Coproduct.
Require Import Category.Construction.Free.Quiver.

Generalizable All Variables.

(** * Coproducts of quivers *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed., §III.3
   Exercise 4, printed p. 68 (PDF p. 77); catalog item [maclane:III.3:ex4],
   whose recorded statement summary is

     "Describe coproducts, showing that they exist, in the category of small
      categories Cat, the category of monoids Mon, and the category of
      graphs Grph."

   (doc/plan/books/maclane/inventory/III.json).  The exercise has three
   independent thirds and this file delivers exactly one of them, the Grph
   third: the coproduct of two quivers, its two injections, the copairing
   universal property, and — since the price turned out to be small — the
   [Cocartesian QuiverCategory] instance, which is what "showing that they
   exist" asks for.  The Cat third was already in tree as
   [Cat_Cocartesian] (Instance/Cat/Cocartesian.v) over
   Construction/Coproduct.v, and is cross-linked below rather than redone;
   the Mon third is not touched here.

   nLab: https://ncatlab.org/nlab/show/quiver
   nLab: https://ncatlab.org/nlab/show/coproduct

   Mac Lane's "graph" is what is now called a quiver or directed multigraph.
   Construction/Free/Quiver.v indexes edges directly by their endpoints
   ([edges X Y] is the set of arrows from X to Y), and that encoding is again
   what makes the construction cheap, exactly as it was for the opposite and
   the product in the sibling file Construction/Free/Quiver/Constructions.v:
   nodes are the tagged disjoint union, and the edge family is defined by
   cases on the two tags, with the two CROSS cases empty.  That last clause
   is the whole mathematical content of "disjoint" and is where an error
   would hide, so it is stated several ways: five artifacts in three
   kinds.  They all rest on the SAME definitional fact and so would
   break together rather than giving independent checks below — as two [eq_refl]
   equations naming [False], as two eliminators, and as a concrete
   uninhabitedness witness at the end of the file.

   THE RELATIONSHIP TO THE SIBLING FILE.  Constructions.v builds [QuiverOp]
   and [QuiverProd] for §II.7 Exercise 1; this file builds [QuiverCoprod] for
   §III.3 Exercise 4.  They are different exercises with different content —
   §II.7's asks that the constructions AGREE with the corresponding ones on
   categories along the forgetful functor, §III.3's asks for existence and a
   description — but they invite the same measurements, and where the two can
   be compared the coproduct comes out STRONGER in two places and WEAKER in
   one.  All three differences are recorded here because each is a fact about
   [sum] versus [prod] rather than about the two authors:

   (a) STRONGER: the [≈]-hypothesis form of uniqueness IS proved here.
       Constructions.v discloses that [QuiverPair_unique] takes LEIBNIZ
       equalities of the two composites as hypotheses, and that upgrading
       them would need respectfulness of [QuiverPair] in its arguments, which
       it does not prove.  [QuiverCopair_unique] below takes [≈] hypotheses,
       and [QuiverCopair_respects] IS the corresponding respectfulness.  The
       reason is structural.  A pairing's node action is [fun x => (F x,
       F' x)], so relating two pairings needs an equality of PAIRS built from
       two equalities, and then the transported edge is a pair transported
       along it; a copairing's node action is [fun x => match x with inl a =>
       F a | inr b => F' b end], so at each constructor the required equality
       IS the given one, with no assembly and no transport bookkeeping.

   (b) STRONGER: consequently the universal property is packaged as a class
       instance, [QuiverCategory_Cocartesian], where Constructions.v states
       in terms that "no claim is made that [QuiverProd] is the categorical
       product in [QuiverCategory]".  [Cocartesian C] is notation for
       [@Cartesian (C^op)] (Structure/Cocartesian.v), so the instance
       literally says that [QuiverCategory^op] is cartesian, with
       [product_obj := QuiverCoprod], [exl := QuiverInl], [exr := QuiverInr]
       and [fork := QuiverCopair]; its [ump_products] field, read in the
       opposite, is the copairing property in both directions.  The derived
       vocabulary of Structure/Cocartesian.v is pinned to the named constants
       by [eq_refl] ([Coprod_is_QuiverCoprod] and its three siblings) so that
       no reader has to take on trust which orientation was chosen.

   (c) WEAKER, and this is the one that matters: the analogue of §II.7's
       headline does NOT hold at [eq_refl].  Constructions.v gets
       [QuiverOfCat (C ∏ D) = QuiverProd …] at Leibniz equality of the whole
       [Quiver] record.  The coproduct statement is measured and REFUTED at
       that strength, and the two obstructions are located rather than
       guessed; see the next paragraph.

   PRESERVATION BY THE FORGETFUL FUNCTOR: WHAT IS AND IS NOT TRUE.  The
   question "does U : Cat -> Grph preserve coproducts" is not part of
   Exercise 4, but it is the obvious companion to §II.7 and it is answered
   here.  Measured, strict first:

     [QuiverOfCat_Coproduct_nodes] — the NODE TYPES agree by [eq_refl].

     [QuiverOfCat_Coproduct_edges_ll] and its three siblings — the EDGE SETS
     agree by [eq_refl] AT EVERY PAIR OF CONSTRUCTOR ARGUMENTS, in all four
     cases including the two cross cases where both sides are [False].

     The [edges] FIELDS, as functions of two variable nodes, are NOT
     convertible, and neither are the whole records.  Both failures were
     checked by machine and each is a genuine conversion failure ("cannot
     unify"), not an elaboration or scope error.  There are exactly two
     causes and they are independent:

       - Construction/Coproduct.v is a [Program Definition], and Program's
         pattern-matching compilation gives its [hom] field the
         equation-passing shape [match y as y' return (y' = y0 -> Type) with
         … end eq_refl] rather than a plain nested match.  Under binders that
         term is not convertible with the plain match used here, though at
         constructor arguments both iota-reduce to the same thing — which is
         precisely why the four pointwise statements above DO close.

       - its [homset] field is [{| equiv := …; setoid_equiv := … |}] whose
         second component is a [Qed]-opaque Program obligation (the tree runs
         [Unset Transparent Obligations], Lib/Tactics.v:36).  [Setoid] has
         primitive projections with eta, so conversion compares that field,
         and an opaque constant defeats it.  This is the same obstruction
         Constructions.v records in its edgeset/prod_setoid non-reuse
         note -- NOT, as an earlier draft said, the one it records for
         [Forgetful_preserves_fst]/[_snd], which that file blames on
         [fmap_respects] instead -- met
         here one level earlier: there it blocked an arrow-level statement,
         here it blocks the object-level one.

     Neither obstruction is a fact about coproducts of graphs; both are facts
     about how Construction/Coproduct.v happens to be elaborated.  No attempt
     is made to route around them by re-spelling [QuiverCoprod] to match
     Program's output, and no claim is made that [eq_refl] is unreachable in
     principle.  These two negatives are MEASURED but not GUARDED in this
     file: nothing here re-checks them on a later build, and pinning them
     would take a probe file, which THIS file does not create -- but the
     same commit does.  Test/ProbeCoproduct328.v pins both.  An earlier
     draft stopped at "does not create", leaving a reader with the
     wrong conclusion about the commit.

   What IS delivered instead is [QuiverOfCat_Coproduct_iso], an ISOMORPHISM
   in [QuiverCategory] between the underlying quiver of C ∐ D and the
   coproduct of the underlying quivers, whose two legs are the IDENTITY on
   nodes and the IDENTITY on edges in every case — they carry no data
   whatsoever, which is the precise sense in which the failure above is
   presentational.  Read the word "isomorphism" here at full strength: this
   is an isomorphism in [QuiverCategory], not an equivalence of anything.
   And it is compatible with the injections: [Forgetful_preserves_coprod_inl]
   and [_inr] show that it carries the underlying map of the inclusion
   functor C ⟶ C ∐ D to [QuiverInl], so what is preserved is the coproduct
   DIAGRAM and not merely an abstract object.  The two inclusion functors are
   built here as [CoproductInl] and [CoproductInr] because the tree has no
   named ones — Instance/Cat/Cocartesian.v supplies them only as anonymous
   inline records in the [exl]/[exr] fields of [Cat_Cocartesian], and naming
   them that way would cost a dependency on Instance/Cat, which this file
   does not take.

   THE UNIQUENESS CLAUSE IS WITNESSED, NOT ONLY STATED.  Constructions.v
   discloses that its uniqueness clause has no exhibited competitor: "no
   homomorphism into a product is exhibited that FAILS the two triangles, so
   the clause's discriminating power is disclosed rather than witnessed",
   and observes that doing so needs a concrete quiver with two distinct
   nodes.  The closing section here supplies exactly that on the coproduct
   side: [copair_swap_fails_left] exhibits a homomorphism out of a concrete
   coproduct which satisfies neither triangle, and refutes the first of them
   outright.  The witnesses are two small quivers — [LoopQ], one node with
   one loop, and [TwoQ], two nodes with two parallel edges between every
   ordered pair — and the concrete facts proved of them are that the two
   injections into [QuiverCoprod LoopQ LoopQ] are NOT equivalent (so the
   construction does not collapse the two summands -- SCOPE THAT TO THE
   INSTANCE: this file proves NO general non-degeneracy for the
   injections, containing no [Monic], [Section] or injectivity statement
   at all, an asymmetry with the Mon half of the same commit where the
   corresponding results hold for ARBITRARY factors), that the cross edge
   set
   is empty, and that the copairing of two homomorphisms that differ COMPUTES
   to the left one on the left summand and to the right one on the right, by
   [eq_refl] on both nodes and edges.  Nothing in that section is asserted:
   every negative EXCEPT [coprod_no_cross_edge] is obtained by
     projecting the node component -- that one is the identity on
     [False], since the cross edge set IS [False], so like its general
     siblings above it makes the fact quotable rather than proving
     anything of a
   hypothetical equivalence and discriminating on [Datatypes.inl] versus
   [Datatypes.inr], or on [false] versus [true].  Transports do of course
   occur in the TYPES of the edge-coherence obligations, that being the
   shape of [QuiverHomomorphismEquivalence]; what is claimed is that no
   PROOF in this file manipulates one — each such obligation is either the
   hypothesis read at the corresponding constructor, or eliminated from
   [False], or closed by [reflexivity] once the node equalities have become
   [eq_refl].  No UIP hypothesis and no decidability assumption appears
   anywhere.

   OTHER STRENGTH MEASUREMENTS, all taken rather than estimated.

     BOTH TRIANGLES hold at LEIBNIZ EQUALITY of the whole homomorphism
     record, [QuiverCopair_Inl] and [QuiverCopair_Inr] by [eq_refl] — the
     same outcome Constructions.v reports for its two projections, and for
     the same reason: [QuiverComp]'s respectfulness field is synthesised as
     the composite of the two given ones, and composing with the identity
     that [QuiverInl] carries leaves the copairing's own field, which then
     iota-reduces at each constructor.

     AN EARLIER DRAFT OF THIS HEADER CLAIMED A CONSTANT THAT DOES NOT
     EXIST, and it is recorded here as bad evidence rather than deleted.
     It read: "[QuiverCoswap_is_copair] is [eq_refl] ... recorded rather
     than asserted".  There is no such constant anywhere in the tree,
     and the body below says the opposite in terms: [QuiverCoswap] is
     TAKEN AS A DEFINITION ([QuiverCopair QuiverInr QuiverInl]), so
     there is nothing to record and no second candidate whose agreement
     would be worth measuring.  The phrase "recorded rather than
     asserted" is this file's own honesty vocabulary, which made the
     invented measurement read as a checked one.

     [QuiverCoswap_invol] is only [≈] — the [eq_refl] form was tried and
     rejected with a genuine conversion failure — and the cause is the same
     one the sibling reports, met from the other side.  There
     [QuiverSwap_invol] fails because surjective pairing is not definitional
     for the standard library's [prod]; here the node action of the
     twice-exchanged quiver is a match on a match, which does not reduce
     while the scrutinee is a variable, [sum] having no eta rule either.  In
     both cases it is the absence of a definitional eta rule for the
     standard library's own datatype, not anything about the construction.

   UNIVERSES, measured per constant and reported with causes.
   [coprod_edges@{o1 h1 p1 o2 h2 p2 o h p}] carries only [h1 <= h] and
   [h2 <= h] — every other level stays free, since [Type] is cumulative.
   [coprod_edgeset] and hence [QuiverCoprod] carry in addition

     h1 = h2 = h    and    p1 = p2 = p,

   identifying the two summands' edge and proof levels with the coproduct's.
   The cause is measured, not guessed: this construction REUSES the
   summand's edge setoid verbatim ([edgeset G a b] is handed back
   unchanged), and [Setoid] is not cumulative here — the bare term
   [fun (A : Type@{a}) (S : Setoid@{a a} A) => (S : Setoid@{b b} A)] with
   [a < b] is rejected, which was checked directly rather than taken from
   elsewhere.  This is a real difference from [QuiverProd], which BUILDS a
   fresh componentwise setoid ([edgeset_prod]) and can therefore keep the
   levels apart.  The three OBJECT levels remain free on both sides
   ([o1 <= o], [o2 <= o]), and [False_Setoid@{h p}] carries an EMPTY
   constraint clause.

   The HOMOMORPHISMS are less general than the quiver, exactly as
   Constructions.v reports for its own: [QuiverInl@{o h p}] and
   [QuiverInr@{o h p}] take BOTH summands at one instance and add [h <= p],
   while [QuiverCopair] does better, keeping the three object levels apart
   and inheriting only [h1 = h2] and [p1 = p2] from [QuiverCoprod].
   Everything stated through [@homset QuiverCategory] — [QuiverCopair_eta],
   [QuiverCopair_unique], [QuiverCopair_respects], [QuiverCoswap_invol], the
   [Cocartesian] instance and the whole preservation section — collapses all
   the quivers involved to a SINGLE [Quiver@{u u0 u0}] instance, hom and
   proof levels identified.  That is [QuiverCategory]'s own doing: it is one
   universe instance of [Category], so any statement quantified over its
   hom-setoid is a statement at that instance.  Finally
   [QuiverOfCat_Coproduct_iso] takes [C : Category@{u u0 u0}] and
   [D : Category@{u1 u2 u2}], keeping the two object levels apart but
   identifying each factor's hom and proof levels; the cause is the donor,
   Construction/Coproduct.v being declared
   [Category@{u u0 u0} -> Category@{u1 u2 u2} -> Category@{u3 u4 u4}], the
   same phenomenon Constructions.v attributes to [Opposite] and [Product].
   No attempt was made to recover more generality anywhere, and nothing in
   this file needs it.

   WHAT IS NOT BUILT.  [QuiverCoprod] is not packaged as a bifunctor and no
   action on pairs of homomorphisms is defined (the sibling likewise builds
   no bifunctor for [QuiverProd]); the nullary case — the empty quiver as an
   initial object of [QuiverCategory] — is not supplied, so [Cocartesian] is
   binary here and no [Initial QuiverCategory] instance is claimed;
   [Forgetful] is not shown to preserve coproducts as a general statement
   about a functor (the comparison is exhibited pointwise in C and D, and
   its naturality in C and D is not proved); the correspondence is not
   packaged as a bijection of hom-setoids in [Sets], though its content is
   present — the [ump_products] field of the instance together with
   [QuiverCopair_respects] is exactly what such a bijection would need, and
   only the packaging (and a dependency on Instance/Sets) is missing; the
   free-category functor's behaviour on coproducts is not addressed; and no
   relation is drawn to
   Theory/OGraph.v, whose ×_O multiplies over a FIXED node set and defines
   no coproduct at all, so nothing here bears on it and nothing there bears
   on this. *)

(* SHADOWING GUARD.  Structure/Cocartesian.v defines [inl] and [inr] as the
   coproduct injections of an arbitrary cocartesian category, which shadow
   [Datatypes.inl] and [Datatypes.inr].  Every constructor of [sum] below is
   therefore written qualified, following Instance/Cat/Cocartesian.v and
   Construction/Free/Quiver/Constructions.v.

   [Open Scope category_scope] is DEFENSIVE here, not required, and that was
   measured rather than assumed: the file compiles unchanged with the line
   deleted.  The hazard it guards against is real in general — three scopes
   declare [_ ^op], and [QuiverCategory^op] occurs below in an argument
   position — but the competing notation is declared in Functor/Opposite.v
   (:41), which also opens functor_scope (:44) and which this file does not
   import.  Theory/Functor.v opens functor_scope too (:118) but declares no
   [^op] in it, so nothing here shadows Construction/Opposite.v's. *)
Local Open Scope category_scope.

Local Notation "Q ⇨ Q'" := (QuiverHomomorphism Q Q') (at level 40).
Local Existing Instance edgeset.

(** ** The empty edge setoid *)

(* The cross-summand edge sets are empty, and an empty type carries exactly
   one setoid.  All three [Equivalence] fields are written as explicit terms
   rather than discharged by a tactic or by [Program]: the tree runs
   [Unset Transparent Obligations] (Lib/Tactics.v:36) and [Setoid] has
   primitive projections with eta, so an obligation-built proof would be an
   opaque constant sitting inside [QuiverCoprod] and would defeat the
   [eq_refl] measurements below.  The spelling follows [edgeset_prod] of
   Construction/Free/Quiver/Constructions.v. *)
Definition False_Setoid@{h p} : Setoid@{h p} False := {|
  equiv := fun f (_ : False) => match f return Type@{p} with end;
  setoid_equiv :=
    {| Equivalence_Reflexive := fun x : False => match x with end
     ; Equivalence_Symmetric := fun x : False => match x with end
     ; Equivalence_Transitive := fun x : False => match x with end |}
|}.

(** ** The coproduct quiver *)

Section CoproductQuiver.

(* The edge family: an edge between two left nodes is a left edge, between
   two right nodes a right edge, and there are NO edges between a left node
   and a right node in either direction.  [False] is used for the two cross
   cases exactly as Construction/Coproduct.v uses it for the cross hom-sets
   of C ∐ D. *)
Definition coprod_edges@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2})
  (x y : (@nodes G + @nodes H)%type) : Type@{h} :=
  match x with
  | Datatypes.inl a =>
      match y with
      | Datatypes.inl b => @edges G a b
      | Datatypes.inr _ => False
      end
  | Datatypes.inr a =>
      match y with
      | Datatypes.inl _ => False
      | Datatypes.inr b => @edges H a b
      end
  end.

(* The edge setoid, by the same case analysis.  Note that the summand's own
   setoid is handed back unchanged; see the header for the universe
   identification this forces and why it does not arise for the product. *)
Definition coprod_edgeset@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2})
  (x y : (@nodes G + @nodes H)%type)
  : Setoid@{h p} (coprod_edges@{o1 h1 p1 o2 h2 p2 o h p} G H x y) :=
  match x with
  | Datatypes.inl a =>
      match y with
      | Datatypes.inl b => @edgeset G a b
      | Datatypes.inr _ => False_Setoid
      end
  | Datatypes.inr a =>
      match y with
      | Datatypes.inl _ => False_Setoid
      | Datatypes.inr b => @edgeset H a b
      end
  end.

Definition QuiverCoprod@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2}) : Quiver@{o h p} := {|
  nodes   := (@nodes G + @nodes H)%type;
  edges   := coprod_edges@{o1 h1 p1 o2 h2 p2 o h p} G H;
  edgeset := coprod_edgeset@{o1 h1 p1 o2 h2 p2 o h p} G H
|}.

(* What the fields unfold to, recorded rather than described. *)

Definition QuiverCoprod_nodes@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2}) :
  @nodes (QuiverCoprod@{o1 h1 p1 o2 h2 p2 o h p} G H)
    = (@nodes G + @nodes H)%type := eq_refl.

Context {G H : Quiver}.

Definition QuiverCoprod_edges_ll (a b : @nodes G) :
  @edges (QuiverCoprod G H) (Datatypes.inl a) (Datatypes.inl b)
    = @edges G a b := eq_refl.

Definition QuiverCoprod_edges_rr (a b : @nodes H) :
  @edges (QuiverCoprod G H) (Datatypes.inr a) (Datatypes.inr b)
    = @edges H a b := eq_refl.

(* The two clauses that make the union DISJOINT, stated as equations. *)

Definition QuiverCoprod_edges_lr (a : @nodes G) (b : @nodes H) :
  @edges (QuiverCoprod G H) (Datatypes.inl a) (Datatypes.inr b)
    = False := eq_refl.

Definition QuiverCoprod_edges_rl (a : @nodes H) (b : @nodes G) :
  @edges (QuiverCoprod G H) (Datatypes.inr a) (Datatypes.inl b)
    = False := eq_refl.

(* …and again as eliminators, which is the form a consumer wants.  Both are
   the identity function: the edge set IS [False], so nothing is proved by
   these beyond making the fact quotable. *)

Definition quiver_coprod_no_edge_lr (a : @nodes G) (b : @nodes H)
  (e : @edges (QuiverCoprod G H) (Datatypes.inl a) (Datatypes.inr b))
  : False := e.

Definition quiver_coprod_no_edge_rl (a : @nodes H) (b : @nodes G)
  (e : @edges (QuiverCoprod G H) (Datatypes.inr a) (Datatypes.inl b))
  : False := e.

(* Distinctness of the two families of nodes.  This one is not definitional
   and is not vacuous: it is what says the union is tagged. *)
Definition quiver_coprod_nodes_disjoint (a : @nodes G) (b : @nodes H)
  (p : @eq (@nodes (QuiverCoprod G H))
         (Datatypes.inl a) (Datatypes.inr b)) : False.
Proof. discriminate p. Defined.

End CoproductQuiver.

(** ** The two injections *)

Section Injections.

(* Both injections are the identity on edges: [edges (QuiverCoprod G H)
   (inl x) (inl y)] iota-reduces to [edges G x y], so no map is needed and
   respectfulness is the identity too. *)

Definition QuiverInl@{o h p} {G H : Quiver@{o h p}} : G ⇨ QuiverCoprod G H :=
  Build_QuiverHomomorphism G (QuiverCoprod G H)
    Datatypes.inl
    (fun x y (e : @edges G x y) => e)
    (fun x y f g (e : f ≈ g) => e).

Definition QuiverInr@{o h p} {G H : Quiver@{o h p}} : H ⇨ QuiverCoprod G H :=
  Build_QuiverHomomorphism H (QuiverCoprod G H)
    Datatypes.inr
    (fun x y (e : @edges H x y) => e)
    (fun x y f g (e : f ≈ g) => e).

End Injections.

(** ** The copairing *)

Section Copair.

Context {G H R : Quiver}.
Context (F : G ⇨ R) (F' : H ⇨ R).

Definition copair_nodes (x : @nodes (QuiverCoprod G H)) : @nodes R :=
  match x with
  | Datatypes.inl a => F a
  | Datatypes.inr b => F' b
  end.

Definition copair_edges (x y : @nodes (QuiverCoprod G H))
  : @edges (QuiverCoprod G H) x y
      -> @edges R (copair_nodes x) (copair_nodes y).
Proof.
  destruct x as [a|a], y as [b|b]; cbn.
  - exact (@fedgemap _ _ F a b).
  - exact (fun e => match e with end).
  - exact (fun e => match e with end).
  - exact (@fedgemap _ _ F' a b).
Defined.

Definition copair_edges_respects (x y : @nodes (QuiverCoprod G H))
  : Proper (equiv ==> equiv) (copair_edges x y).
Proof.
  destruct x as [a|a], y as [b|b]; cbn.
  - exact (@fedgemap_respects _ _ F a b).
  - intros e; exact (match e with end).
  - intros e; exact (match e with end).
  - exact (@fedgemap_respects _ _ F' a b).
Defined.

Definition QuiverCopair : QuiverCoprod G H ⇨ R :=
  Build_QuiverHomomorphism (QuiverCoprod G H) R
    copair_nodes copair_edges copair_edges_respects.

End Copair.

Arguments QuiverCopair {G H R} F F'.

(** ** The universal property of the coproduct quiver *)

Section CoproductUniversal.

Context {G H R : Quiver}.

(* BOTH TRIANGLES hold at LEIBNIZ EQUALITY of the whole homomorphism record,
   not merely up to [≈].  [QuiverComp] synthesises the composite's
   respectfulness field as the composite of the two given ones, and
   [QuiverInl] contributes the identity there, so what remains is the
   copairing's own field read at [inl], which iota-reduces to [F]'s. *)

Definition QuiverCopair_Inl (F : G ⇨ R) (F' : H ⇨ R) :
  @compose QuiverCategory G (QuiverCoprod G H) R (QuiverCopair F F')
    QuiverInl = F := eq_refl.

Definition QuiverCopair_Inr (F : G ⇨ R) (F' : H ⇨ R) :
  @compose QuiverCategory H (QuiverCoprod G H) R (QuiverCopair F F')
    QuiverInr = F' := eq_refl.

(* The eta law.  Unlike the product's, this one needs no surjectivity
   principle: at each constructor the node action of the rebuilt copairing
   is the original one on the nose, so every node equality is [eq_refl] and
   the transports in the edge coherence vanish. *)
Definition QuiverCopair_eta (M : QuiverCoprod G H ⇨ R) :
  @equiv _ (@homset QuiverCategory (QuiverCoprod G H) R)
    M (QuiverCopair
         (@compose QuiverCategory G (QuiverCoprod G H) R M QuiverInl)
         (@compose QuiverCategory H (QuiverCoprod G H) R M QuiverInr)).
Proof.
  unshelve eexists.
  - intros [a|a]; reflexivity.
  - intros [a|a] [b|b] e; try (exact (match e with end)); cbn; reflexivity.
Defined.

(* Uniqueness, with hypotheses at [≈].  READ THE CONTRAST with
   [QuiverPair_unique] (Construction/Free/Quiver/Constructions.v), whose
   hypotheses are Leibniz equalities of the two composites: here the
   [≈]-form is available, because the node family of the hypothesis is
   consumed constructor by constructor rather than assembled into an
   equality of pairs.  The two edge-coherence obligations ARE the
   hypotheses' own, at the corresponding constructor. *)
Definition QuiverCopair_unique (M : QuiverCoprod G H ⇨ R)
  (F : G ⇨ R) (F' : H ⇨ R)
  (p : @equiv _ (@homset QuiverCategory G R)
         (@compose QuiverCategory G (QuiverCoprod G H) R M QuiverInl) F)
  (q : @equiv _ (@homset QuiverCategory H R)
         (@compose QuiverCategory H (QuiverCoprod G H) R M QuiverInr) F') :
  @equiv _ (@homset QuiverCategory (QuiverCoprod G H) R)
    M (QuiverCopair F F').
Proof.
  destruct p as [pn pc], q as [qn qc].
  unshelve eexists.
  - intros [a|a]; [ exact (pn a) | exact (qn a) ].
  - intros [a|a] [b|b] e; try (exact (match e with end)).
    + exact (pc a b e).
    + exact (qc a b e).
Defined.

(* Respectfulness of the copairing in both arguments — the statement
   Constructions.v leaves open on the product side, and the reason
   uniqueness above can take [≈] hypotheses. *)
Definition QuiverCopair_respects :
  Proper (@equiv _ (@homset QuiverCategory G R) ==>
          @equiv _ (@homset QuiverCategory H R) ==>
          @equiv _ (@homset QuiverCategory (QuiverCoprod G H) R))
         (@QuiverCopair G H R).
Proof.
  intros F1 F2 [pn pc] F1' F2' [qn qc].
  unshelve eexists.
  - intros [a|a]; [ exact (pn a) | exact (qn a) ].
  - intros [a|a] [b|b] e; try (exact (match e with end)).
    + exact (pc a b e).
    + exact (qc a b e).
Defined.

End CoproductUniversal.

(** ** Exchange of the two summands *)

(* The exchange of summands is DEFINED as the copairing of the two
   injections in the other order — the coproduct-side reading of
   [QuiverSwap_is_pair] (Construction/Free/Quiver/Constructions.v), taken as
   the definition rather than recorded afterwards, since there is no second
   candidate here whose agreement would be worth measuring. *)
Definition QuiverCoswap {G H : Quiver} :
  QuiverCoprod G H ⇨ QuiverCoprod H G := QuiverCopair QuiverInr QuiverInl.

(* Only [≈], and for the dual of the sibling's reason.  There
   [QuiverSwap_invol] cannot be [eq_refl] because surjective pairing is not
   definitional for [prod]; here the node action of the twice-exchanged
   quiver is a match on a match, which does not reduce while the scrutinee
   is a variable — [sum] has no eta rule at all.  The [eq_refl] form was
   tried first and rejected. *)
Definition QuiverCoswap_invol {G H : Quiver} :
  @equiv _ (@homset QuiverCategory (QuiverCoprod G H) (QuiverCoprod G H))
    (@compose QuiverCategory (QuiverCoprod G H) (QuiverCoprod H G)
       (QuiverCoprod G H) (@QuiverCoswap H G) (@QuiverCoswap G H))
    (@id QuiverCategory (QuiverCoprod G H)).
Proof.
  unshelve eexists.
  - intros [a|a]; reflexivity.
  - intros [a|a] [b|b] e; try (exact (match e with end)); reflexivity.
Defined.

(** ** QuiverCategory has binary coproducts *)

(* [Cocartesian C] is notation for [@Cartesian (C^op)]
   (Structure/Cocartesian.v), so this instance literally exhibits
   [QuiverCategory^op] as cartesian.  Read in the opposite, [exl]/[exr] are
   the two injections, [fork] is the copairing, [fork_respects] is
   [QuiverCopair_respects], and [ump_products] is

     M ≈ [F, F']  ↔  (M ∘ inl ≈ F) * (M ∘ inr ≈ F'),

   whose forward direction is [compose_respects] against the two triangles
   (which, being [eq_refl], need no rewriting step at all) and whose
   backward direction is [QuiverCopair_unique].

   The record is built by [refine] against [@Build_Cartesian
   (QuiverCategory^op)] rather than by the [{| … |}] syntax, deliberately:
   the anonymous record notation infers the class's implicit category from
   [product_obj]'s type, and since [obj[C^op]] is [obj[C]] definitionally it
   picks [QuiverCategory] rather than its opposite, after which [fork]'s
   remaining fields fail to typecheck with a misleading message. *)
#[export] Instance QuiverCategory_Cocartesian : @Cocartesian QuiverCategory.
Proof.
  unshelve refine (@Build_Cartesian (QuiverCategory^op)
                     QuiverCoprod
                     (fun _ _ _ F F' => QuiverCopair F F')
                     (fun _ _ => QuiverInl)
                     (fun _ _ => QuiverInr)
                     _ _).
  - intros x y z; exact QuiverCopair_respects.
  - simpl; intros x y z F F' M; split.
    + intro Heq; split.
      * exact (@compose_respects QuiverCategory _ _ _ _ _ Heq _ _
                 (reflexivity QuiverInl)).
      * exact (@compose_respects QuiverCategory _ _ _ _ _ Heq _ _
                 (reflexivity QuiverInr)).
    + intros [p q]; exact (QuiverCopair_unique M F F' p q).
Defined.

(* The derived vocabulary of Structure/Cocartesian.v, pinned to the named
   constants by [eq_refl] so that the orientation is fixed by computation
   rather than by prose. *)

Definition Coprod_is_QuiverCoprod (G H : Quiver) :
  @Coprod QuiverCategory QuiverCategory_Cocartesian G H
    = QuiverCoprod G H := eq_refl.

Definition cocartesian_inl_is_QuiverInl (G H : Quiver) :
  @Structure.Cocartesian.inl QuiverCategory QuiverCategory_Cocartesian G H
    = @QuiverInl G H := eq_refl.

Definition cocartesian_inr_is_QuiverInr (G H : Quiver) :
  @Structure.Cocartesian.inr QuiverCategory QuiverCategory_Cocartesian G H
    = @QuiverInr G H := eq_refl.

Definition merge_is_QuiverCopair {G H R : Quiver} (F : G ⇨ R) (F' : H ⇨ R) :
  @merge QuiverCategory QuiverCategory_Cocartesian R G H F F'
    = QuiverCopair F F' := eq_refl.

(** ** Preservation by the forgetful functor *)

Section Preservation.

Context (C D : Category).

(* Objects: the node types agree on the nose. *)
Definition QuiverOfCat_Coproduct_nodes :
  @nodes (QuiverOfCat (C ∐ D))
    = @nodes (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D)) := eq_refl.

(* Edges: all four cases agree on the nose AT CONSTRUCTOR ARGUMENTS,
   including the two cross cases where both sides are [False].  As functions
   of two variable nodes the two [edges] fields are NOT convertible, and
   neither are the whole [Quiver] records; see the header for the two
   independent causes. *)

Definition QuiverOfCat_Coproduct_edges_ll (a b : obj[C]) :
  @edges (QuiverOfCat (C ∐ D)) (Datatypes.inl a) (Datatypes.inl b)
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inl a) (Datatypes.inl b) := eq_refl.

Definition QuiverOfCat_Coproduct_edges_rr (a b : obj[D]) :
  @edges (QuiverOfCat (C ∐ D)) (Datatypes.inr a) (Datatypes.inr b)
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inr a) (Datatypes.inr b) := eq_refl.

Definition QuiverOfCat_Coproduct_edges_lr (a : obj[C]) (b : obj[D]) :
  @edges (QuiverOfCat (C ∐ D)) (Datatypes.inl a) (Datatypes.inr b)
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inl a) (Datatypes.inr b) := eq_refl.

Definition QuiverOfCat_Coproduct_edges_rl (a : obj[D]) (b : obj[C]) :
  @edges (QuiverOfCat (C ∐ D)) (Datatypes.inr a) (Datatypes.inl b)
    = @edges (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D))
        (Datatypes.inr a) (Datatypes.inl b) := eq_refl.

(* The comparison, in both directions.  Every branch is the identity: on
   nodes because the two node types are the same type, on edges because the
   four equations above are [eq_refl], and in the two cross cases because
   both sides are [False] (either branch would do; the identity is taken so
   that no case is special). *)

Definition QuiverOfCat_Coproduct_to :
  QuiverOfCat (C ∐ D) ⇨ QuiverCoprod (QuiverOfCat C) (QuiverOfCat D).
Proof.
  unshelve eapply Build_QuiverHomomorphism.
  - exact Datatypes.id.
  - intros x y; destruct x as [a|a], y as [b|b];
      solve [ exact (fun e => e) | exact (fun e : False => match e with end) ].
  - intros x y; destruct x as [a|a], y as [b|b];
      solve [ exact (fun f g e => e)
            | exact (fun f : False => match f with end) ].
Defined.

Definition QuiverOfCat_Coproduct_from :
  QuiverCoprod (QuiverOfCat C) (QuiverOfCat D) ⇨ QuiverOfCat (C ∐ D).
Proof.
  unshelve eapply Build_QuiverHomomorphism.
  - exact Datatypes.id.
  - intros x y; destruct x as [a|a], y as [b|b];
      solve [ exact (fun e => e) | exact (fun e : False => match e with end) ].
  - intros x y; destruct x as [a|a], y as [b|b];
      solve [ exact (fun f g e => e)
            | exact (fun f : False => match f with end) ].
Defined.

Definition QuiverOfCat_Coproduct_iso :
  @Isomorphism QuiverCategory (QuiverOfCat (C ∐ D))
    (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D)).
Proof.
  unshelve eapply Build_Isomorphism.
  - exact QuiverOfCat_Coproduct_to.
  - exact QuiverOfCat_Coproduct_from.
  - unshelve eexists.
    + intros [a|a]; reflexivity.
    + intros [a|a] [b|b] e; try (exact (match e with end)); reflexivity.
  - unshelve eexists.
    + intros [a|a]; reflexivity.
    + intros [a|a] [b|b] e; try (exact (match e with end)); reflexivity.
Defined.

(* The two inclusion functors.  The tree has none by name:
   Instance/Cat/Cocartesian.v supplies them only as anonymous inline records
   in the [exl]/[exr] fields of [Cat_Cocartesian], and naming them from
   there would cost a dependency on Instance/Cat. *)

Definition CoproductInl : C ⟶ C ∐ D.
Proof.
  unshelve eapply Build_Functor.
  - exact Datatypes.inl.
  - intros x y f; exact f.
  - intros x y f g Hfg; exact Hfg.
  - intro x; reflexivity.
  - intros x y z f g; reflexivity.
Defined.

Definition CoproductInr : D ⟶ C ∐ D.
Proof.
  unshelve eapply Build_Functor.
  - exact Datatypes.inr.
  - intros x y f; exact f.
  - intros x y f g Hfg; exact Hfg.
  - intro x; reflexivity.
  - intros x y z f g; reflexivity.
Defined.

(* Compatibility with the injections: the comparison carries the underlying
   quiver map of each inclusion functor to the corresponding injection, so
   what is preserved is the coproduct DIAGRAM and not merely an object. *)

Definition Forgetful_preserves_coprod_inl :
  @equiv _ (@homset QuiverCategory (QuiverOfCat C)
              (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D)))
    (@compose QuiverCategory _ _ _ QuiverOfCat_Coproduct_to
       (QuiverHomomorphismOfFunctor _ _ CoproductInl))
    QuiverInl.
Proof.
  unshelve eexists.
  - intro a; reflexivity.
  - intros a b e; reflexivity.
Defined.

Definition Forgetful_preserves_coprod_inr :
  @equiv _ (@homset QuiverCategory (QuiverOfCat D)
              (QuiverCoprod (QuiverOfCat C) (QuiverOfCat D)))
    (@compose QuiverCategory _ _ _ QuiverOfCat_Coproduct_to
       (QuiverHomomorphismOfFunctor _ _ CoproductInr))
    QuiverInr.
Proof.
  unshelve eexists.
  - intro a; reflexivity.
  - intros a b e; reflexivity.
Defined.

End Preservation.

(** ** Non-degeneracy *)

(* Two small quivers, and concrete facts about their coproduct.  [LoopQ] has
   one node carrying one loop; [TwoQ] has two nodes with two PARALLEL edges
   between every ordered pair, so a homomorphism into it has room to move
   both a node and an edge.  Both are built with
   [Build_Quiver_Standard_Eq], whose edge setoids are Leibniz equality.
   Measured rather than assumed: neither witness is pinned to [Set] — both
   are universe-polymorphic, [LoopQ@{u u0 u1} : Quiver@{u0 u1 u}] and
   [TwoQ@{u u0 u1} : Quiver@{u u0 u1}], each carrying only a bound on the
   proof level coming from the Leibniz setoid, since [poly_unit] is
   polymorphic and [bool : Set] is absorbed by cumulativity.  The usual
   concrete-witness price is therefore not paid here; what does confine the
   STATEMENTS below is [@homset QuiverCategory], as the header records. *)

Definition LoopQ : Quiver :=
  Build_Quiver_Standard_Eq poly_unit (fun _ _ => poly_unit).

Definition TwoQ : Quiver :=
  Build_Quiver_Standard_Eq bool (fun _ _ => bool).

(* The loop is a genuine edge, and the cross edge sets of the coproduct are
   genuinely empty. *)

Definition loop_edge : @edges LoopQ ttt ttt := ttt.

Definition coprod_loop_edge_left :
  @edges (QuiverCoprod LoopQ LoopQ)
    (Datatypes.inl ttt) (Datatypes.inl ttt) := ttt.

Definition coprod_loop_edge_right :
  @edges (QuiverCoprod LoopQ LoopQ)
    (Datatypes.inr ttt) (Datatypes.inr ttt) := ttt.

Definition coprod_no_cross_edge
  (e : @edges (QuiverCoprod LoopQ LoopQ)
         (Datatypes.inl ttt) (Datatypes.inr ttt)) : False := e.

(* The two summands are not identified: the injections of [LoopQ] into
   [QuiverCoprod LoopQ LoopQ] are parallel homomorphisms, and they are not
   equivalent.  The proof consumes only the node component of a hypothetical
   equivalence, so no transport and no UIP hypothesis is involved. *)
Definition injections_not_equivalent
  (p : @equiv _ (@homset QuiverCategory LoopQ (QuiverCoprod LoopQ LoopQ))
         QuiverInl QuiverInr) : False.
Proof. destruct p as [pn _]; discriminate (pn ttt). Defined.

Section Witness.

(* Two homomorphisms out of [LoopQ] into [TwoQ] that differ on BOTH the node
   and the edge: one lands on [false] and sends the loop to [false], the
   other lands on [true] and sends the loop to [true]. *)

Definition Ffalse : LoopQ ⇨ TwoQ :=
  Build_QuiverHomomorphism LoopQ TwoQ
    (fun _ => false) (fun _ _ _ => false) (fun _ _ _ _ _ => eq_refl).

Definition Ftrue : LoopQ ⇨ TwoQ :=
  Build_QuiverHomomorphism LoopQ TwoQ
    (fun _ => true) (fun _ _ _ => true) (fun _ _ _ _ _ => eq_refl).

(* The copairing COMPUTES, on nodes and on edges, and differently on the two
   summands: the same loop is carried to [false] from the left and to [true]
   from the right. *)

Definition copair_node_left :
  @fnodes _ _ (QuiverCopair Ffalse Ftrue) (Datatypes.inl ttt)
    = false := eq_refl.

Definition copair_node_right :
  @fnodes _ _ (QuiverCopair Ffalse Ftrue) (Datatypes.inr ttt)
    = true := eq_refl.

Definition copair_edge_left :
  @fedgemap _ _ (QuiverCopair Ffalse Ftrue)
    (Datatypes.inl ttt) (Datatypes.inl ttt) ttt = false := eq_refl.

Definition copair_edge_right :
  @fedgemap _ _ (QuiverCopair Ffalse Ftrue)
    (Datatypes.inr ttt) (Datatypes.inr ttt) ttt = true := eq_refl.

(* The two given homomorphisms really are different. *)
Definition Ffalse_neq_Ftrue
  (p : @equiv _ (@homset QuiverCategory LoopQ TwoQ) Ffalse Ftrue) : False.
Proof. destruct p as [pn _]; discriminate (pn ttt). Defined.

(* The copairing depends on the ORDER of its two arguments. *)
Definition copair_order_matters
  (p : @equiv _ (@homset QuiverCategory (QuiverCoprod LoopQ LoopQ) TwoQ)
         (QuiverCopair Ffalse Ftrue) (QuiverCopair Ftrue Ffalse)) : False.
Proof. destruct p as [pn _]; discriminate (pn (Datatypes.inl ttt)). Defined.

(* A COMPETITOR for the uniqueness clause: a homomorphism out of the
   coproduct which fails the first triangle.  Constructions.v discloses that
   its product-side uniqueness clause has no such witness; this is the
   coproduct-side supply.  The composite with [QuiverInl] is [Ftrue] by
   [QuiverCopair_Inl] — a Leibniz equation — so the goal reduces to
   [Ftrue ≈ Ffalse], which [Ffalse_neq_Ftrue] refutes. *)
Definition copair_swap_fails_left
  (p : @equiv _ (@homset QuiverCategory LoopQ TwoQ)
         (@compose QuiverCategory LoopQ (QuiverCoprod LoopQ LoopQ) TwoQ
            (QuiverCopair Ftrue Ffalse) QuiverInl)
         Ffalse) : False.
Proof. destruct p as [pn _]; discriminate (pn ttt). Defined.

Definition copair_swap_fails_right
  (p : @equiv _ (@homset QuiverCategory LoopQ TwoQ)
         (@compose QuiverCategory LoopQ (QuiverCoprod LoopQ LoopQ) TwoQ
            (QuiverCopair Ftrue Ffalse) QuiverInr)
         Ftrue) : False.
Proof. destruct p as [pn _]; discriminate (pn ttt). Defined.

End Witness.
