Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.

Generalizable All Variables.

(** * [Sets] is complete *)

(* nLab:      https://ncatlab.org/nlab/show/complete+category
   Wikipedia: https://en.wikipedia.org/wiki/Complete_category

   [Complete C] is [∀ (D : Category) (F : D ⟶ C), Limit F]
   (Structure/Complete.v:115): an oracle assigning a chosen limit to every
   diagram.  This file inhabits it at [Sets].

   THE CONSTRUCTION

   The limit of [F : D ⟶ Sets] is the setoid of COMPATIBLE FAMILIES: elements
   of the indexed product of the [F d] whose components agree along every
   arrow of [D],

     [{ x : ∀ d : D, F d & ∀ d d' (f : d ~> d'), fmap[F] f (x d) ≈ x d' }],

   with two such identified when the underlying families agree pointwise.
   The legs are evaluation at [d]; the cone coherence IS the compatibility
   constraint; the mediator out of a competing cone [N] bundles [N]'s legs at
   a point, its compatibility being [N]'s own cone coherence read at that
   point; commuting is [reflexivity] and uniqueness is the symmetry of the
   competing map's commuting equations.

   The first component is literally an element of
   [Sets_iprod_obj (fun d : D => F d)], the dependent-function setoid of
   Instance/Sets/Products.v, so the classical recipe -- a limit is the part of
   the product of all [F d] that is compatible along every arrow -- is
   realised with the product supplied by this issue's other deliverable and
   the compatibility cut performed inline.

   HOW THIS IS *NOT* PROVED, STATED PLAINLY

   It is NOT routed through the standard reduction "a category with all small
   products and equalizers has all small limits".  That theorem does not exist
   in this development: [Complete_HasEqualizers] (Adjunction/GAFT.v:193) runs
   the other way, deriving equalizers FROM completeness -- it is applied to
   this very constant, as [Sets_HasEqualizers] in Adjunction/GAFT/Sets.v --
   and no constant here builds a limit out of two products and an equalizer.
   What is written above is a direct construction; the resemblance to the
   reduction is real but informal, and the equalizer step is done by carrying
   a proof alongside the family rather than by invoking [HasEqualizers].  The
   description at
   Structure/Limit.v:103-106, "a limit is the part of the product of all F x
   whose components are compatible along every arrow of J, exactly the shape
   of the funext-free end of Instance/Sets/End.v", is the shape this file
   follows; Instance/Sets/End.v is its closest in-tree relative.

   SMALLNESS

   [Complete@{u u0 u1 u2}] abbreviates
   [λ C : Category@{u2 u1 u1}, ∀ (D : Category@{u0 u1 u1}) (F : D ⟶ C),
    Limit F], so the diagram category's HOM universe is already forced to
   coincide with [C]'s -- the fact recorded at Adjunction/SAFT.v:138 -- and
   its OBJECT universe [u0] is a separate parameter.  [About Sets_Complete]
   prints

     Sets_Complete@{u u0} : Complete@{u u u u0}      (* with u < u0 *)

   so, writing [Sets@{o so}] as Instance/Sets.v:188 does, [u] is [o] -- the
   universe of the CARRIERS of [Sets]' objects, and of its homs -- and [u0] is
   [so], where [obj[Sets]] itself lives.  The diagram category is
   [Category@{u u u}], i.e. BOTH its objects and its homs live at [o],
   strictly below [obj[Sets]].  That is the smallness side condition, and it
   is exactly what the construction needs: the compatible-family carrier
   quantifies over the objects and arrows of [D], so it fits as a [Sets]
   carrier when both sit at [o].  This is the universe-polymorphic stand-in
   for "D small relative to C" that Structure/Complete.v:32-36 describes.

   WHAT THIS UNLOCKS, AND WHAT IT DOES NOT

   [Complete] is the standing hypothesis of the adjoint functor theorems
   (Adjunction/GAFT.v, Adjunction/SAFT.v) and of [Comma_Complete]
   (Construction/Comma/Limit.v).  Before this file no [Complete] or
   [Cocomplete] instance existed anywhere in the tree, and that absence was
   the last one standing between [GAFT] and an actual application: its other
   two premises were already reachable, [PreservesImageLimit] through
   [right_adjoint_PreservesImageLimit] (Construction/Comma/Limit.v:264, which
   covers every right adjoint) and [SolutionSet] by direct construction.
   Adjunction/GAFT/Sets.v now assembles all three and runs [GAFT] at
   [Id : Sets ⟶ Sets], and docs/INHABITATION.md lists the result among the
   witnessed ones on that basis.  Nothing in this file changes any statement
   of GAFT or SAFT; it supplies an inhabitant of one of their hypotheses.

   Two things that inhabitant does NOT do.  [GAFT]'s frozen universe context
   pins the applying instance to [Sets@{Set _}] (disclosed in the header of
   Adjunction/GAFT/Sets.v), and the functor applied to is [Id], so the
   adjoint produced is [Id] again.  The application demonstrates that the
   premises are simultaneously satisfiable in-tree; it does not produce a new
   adjunction.  [SAFT] remains unapplied: it wants a [Cogenerator], a
   [SubobjectIndex] and a [SubobjectCover] besides, and none of the three has
   an in-tree inhabitant.

   [Cocomplete Sets] is NOT provided.  Colimits of setoids need a quotient of
   the disjoint union by the relation the diagram generates; the technique is
   in the tree (Instance/Sets/Coend.v builds the coend as an inductive setoid
   quotient) but the general construction is not attempted here.

   STATUS: axiom-free.  [Print Assumptions Sets_Complete] reports "Closed
   under the global context"; the Makefile's [print-assumptions] target
   audits it. *)

#[local] Obligation Tactic := idtac.

Section SetsLimit.

Context {D : Category}.
Context (F : D ⟶ Sets).

(* The compatibility constraint cutting the limit out of the indexed product
   of the [F d]: a family is compatible when its components agree along every
   arrow of [D]. *)
Definition Sets_limit_compatible (x : Sets_iprod_obj (fun d : D => F d)) :
  Type :=
  ∀ (d d' : D) (f : d ~{D}~> d'), fmap[F] f (x d) ≈ x d'.

(* The limit carrier: the compatible families, a sub-setoid of the carrier of
   [indexed_product (fun d => F d)] as constructed in Instance/Sets/Products.v.
   The constraint is carried alongside the family rather than quotiented away,
   so no quotient type and no [funext] is involved. *)
Definition Sets_limit_carrier : Type :=
  { x : Sets_iprod_obj (fun d : D => F d) & Sets_limit_compatible x }.

(* Two compatible families are identified when the underlying families are:
   the constraint witness plays no part, exactly as in Instance/Sets/End.v. *)
Definition Sets_limit_equiv : crelation Sets_limit_carrier :=
  fun p q => `1 p ≈ `1 q.

Program Definition Sets_limit_obj : SetoidObject := {|
  carrier   := Sets_limit_carrier;
  is_setoid := {| equiv := Sets_limit_equiv |}
|}.
Next Obligation.
  constructor.
  - intros p d; reflexivity.
  - intros p q Hpq d; symmetry; exact (Hpq d).
  - intros p q r Hpq Hqr d; transitivity (`1 q d);
    [exact (Hpq d)|exact (Hqr d)].
Qed.

(* The leg at [d]: evaluate a compatible family at [d]. *)
Program Definition Sets_limit_leg (d : D) : Sets_limit_obj ~{Sets}~> F d := {|
  morphism := fun p => `1 p d
|}.
Next Obligation. intros d p q Hpq; exact (Hpq d). Qed.

(* The limit cone.  Its coherence condition is precisely the compatibility
   constraint carried by each family. *)
Program Definition Sets_limit_cone : Cone F := {|
  vertex_obj := Sets_limit_obj;
  coneFrom   := {| vertex_map := Sets_limit_leg |}
|}.
Next Obligation. intros d d' f p; exact (`2 p d d' f). Qed.

(* The mediator out of a competing cone [N]: bundle the legs of [N] at a
   point [e] into a family, whose compatibility is [N]'s own cone coherence
   read at [e]. *)
Program Definition Sets_limit_med (N : Cone F) :
  vertex_obj[N] ~{Sets}~> Sets_limit_obj := {|
  morphism := fun e =>
    (fun d => @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d e;
     fun d d' f => @cone_coherence _ _ _ _ (@coneFrom _ _ _ N) d d' f e)
|}.
Next Obligation.
  intros N e e' Hee' d.
  exact (proper_morphism (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) d) e e' Hee').
Qed.

Program Definition Sets_Limit : Limit F := {|
  limit_cone := Sets_limit_cone;
  ump_limits := fun N => {| unique_obj := Sets_limit_med N |}
|}.
Next Obligation. intros N d e; reflexivity. Qed.
Next Obligation. intros N v Hv e d; symmetry; exact (Hv d e). Qed.

End SetsLimit.

(* [Sets] is complete: every diagram of every shape has a limit.  See the
   header for the smallness discipline recorded on the universe context of
   this constant. *)
Definition Sets_Complete : @Complete Sets := fun D F => Sets_Limit F.
