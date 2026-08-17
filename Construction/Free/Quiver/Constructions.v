Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Instance.StrictCat.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Free.Quiver.

Generalizable All Variables.

(** * Opposite and product quivers *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed., §II.7
   Exercise 1, printed p. 51 (PDF p. 61); catalog item [maclane:II.7:ex1].  The
   exercise as the catalog records it — this is the CATALOG'S PARAPHRASE, not
   Mac Lane's own wording — asks one to

     "Define 'opposite graph' and 'product of two graphs' so as to agree with
      the corresponding definitions for categories, i.e. so that the forgetful
      functor U : Cat -> Grph preserves opposites and products."

   (doc/plan/books/maclane/inventory/II.json).  So the mathematical content is
   not the two constructions on their own — either is a two-line reindexing —
   but the AGREEMENT: the definitions are constrained by the requirement that
   the underlying-graph functor carry one to the other.  Everything below is
   therefore organised around the two comparison statements, and each is
   reported at the exact strength it achieves.

   nLab: https://ncatlab.org/nlab/show/quiver

   Mac Lane's "graph" here is what the literature now calls a quiver or a
   directed multigraph: a set of nodes together with, for each ordered pair, a
   set of edges.  [Construction/Free/Quiver.v] indexes the edges directly by
   their endpoints ([edges X Y]) rather than carrying source and target maps
   out of a single edge set, and that encoding is what makes this exercise
   cheap: reversing every edge is the reindexing [fun x y => edges y x], which
   moves no data and needs no equality on nodes, so no transport and no UIP
   hypothesis appears anywhere in this file.  A presentation with an edge set
   and two maps s, t : E -> V would instead have to exhibit the opposite graph
   as the same E with s and t exchanged, and the comparison with [C^op] would
   then be an isomorphism rather than an identity.

   WHAT IS PROVED, AND AT WHAT STRENGTH.  All measurements below were taken,
   not estimated; the file states each one as a Coq term so that the claim and
   its evidence are the same object.

   (1) Both preservation statements hold at LEIBNIZ EQUALITY OF THE WHOLE
       [Quiver] RECORD, by [eq_refl]:

         QuiverOfCat (C^op)   = QuiverOp   (QuiverOfCat C)
         QuiverOfCat (C ∏ D)  = QuiverProd (QuiverOfCat C) (QuiverOfCat D)

       and likewise when phrased through the functor itself, as
       [Forgetful_preserves_op] and [Forgetful_preserves_prod], since
       [fobj[Forgetful]] is [QuiverOfCat] on the nose ([Forgetful_fobj]).  This
       is the strongest of the three outcomes the issue asks to distinguish —
       whole-record equality, not field-by-field, and not merely an isomorphism
       in [QuiverCategory].  Three separate facts conspire to allow it:
       [QuiverOfCat] carries no [Program] obligation (it elaborates with the
       setoid field inlined as [fun X Y => homset X Y]); [Opposite] and
       [Product] are plain [Definition]s whose fields are explicit terms; and
       [Quiver] has primitive projections with eta conversion, so convertible
       fields suffice.

   (2) Preservation also holds ON ARROWS for the opposite, again by [eq_refl]
       ([Forgetful_preserves_op_fmap]): [Forgetful]'s action on a functor is
       [QuiverHomomorphismOfFunctor], and [Functor/Opposite.v]'s
       [Opposite_Functor] is a plain [Definition] with explicit fields.  On the
       product side the corresponding arrow-level statements are the images of
       the projections, and those are only [≈] — see (5).

   (3) The opposite is a DEFINITIONAL INVOLUTION, [QuiverOp_invol] by [eq_refl],
       both on quivers and on homomorphisms ([QuiverOp_map_invol]).  Contrast
       [Construction/Opposite.v:126]'s [op_invol], which is [Qed]-opaque; here
       record eta makes the doubly-reversed quiver convertible to the original,
       so no isomorphism is needed.

   (4) The product projections, the pairing, and BOTH TRIANGLES hold at Leibniz
       equality ([QuiverPair_Fst], [QuiverPair_Snd], by [eq_refl]), and the
       pairing satisfies the eta law [QuiverPair_eta] at [≈].  Together these
       give a genuine universal property, [QuiverPair_unique] — but read its
       hypotheses precisely: they are stated at LEIBNIZ EQUALITY of the two
       composites, not at [≈].  Upgrading them would require respectfulness of
       [QuiverPair] in its two arguments with respect to
       [QuiverHomomorphismEquivalence], which is NOT proved here (it is the
       usual transport bookkeeping over a node-equality family; nothing below
       needs it).  So: a universal property is proved, with hypotheses stronger
       than the [≈]-form a reader might assume.  No claim is made that
       [QuiverProd] is the categorical product in [QuiverCategory].

       The clause is not vacuous — [QuiverPair_Fst]/[_Snd] satisfy its
       hypotheses — and it is not trivial either: eta is NOT definitional, so
       the hypotheses do not simply reduce away (Test/ProbeQuiverConstructions.v
       pins that).  What is NOT supplied is a competitor: no homomorphism into a
       product is exhibited that FAILS the two triangles, so the clause's
       discriminating power is disclosed rather than witnessed.  Doing so needs a
       concrete quiver with two distinct nodes, which nothing here otherwise
       requires.

   (5) Two statements are measured and found NOT to reach [eq_refl], and are
       delivered at [≈] in [QuiverCategory]'s hom-setoid instead.  Both
       measurements are pinned in the build by Test/ProbeQuiverConstructions.v,
       which states each strengthening as a [Fail] command paired with a
       positive control, so the boundary this file's headline rests on is
       guarded rather than merely recorded here:

         [Forgetful_preserves_fst]/[_snd] — [Fst] and [Snd] of
         [Construction/Product.v] are [Program Instance]s, so their
         [fmap_respects] field is an opaque obligation (the tree runs
         [Unset Transparent Obligations], Lib/Tactics.v:36) and cannot be
         convertible to this file's explicit term.

         [QuiverSwap_invol] — the node action of the twice-swapped quiver is
         [fun x => (fst x, snd x)], and surjective pairing is not definitional
         for the standard library's [prod].

       Both negative results are checked by machine, not assumed, and both are
       re-checked on every build.  Each fails by genuine CONVERSION failure
       ("cannot unify"), not by an unrelated elaboration or scope error — the
       distinction matters, since a [Fail] passes just as happily on an
       ill-formed term, which is why the probe file pairs every negative with a
       control that must succeed.

   WHY A NEW FILE.  The issue offers "extend Quiver.v OR add
   Constructions.v".  Quiver.v is a heavily depended-on donor — it carries the
   free/forgetful adjunction, and eight files require it (Free/Quiver's own
   Concrete.v, Examples.v and Presented.v, plus Construction/Free/TwoFunctors.v,
   Instance/Roster.v, Test/Issue138.v, Theory/Diagram.v and Theory/OGraph.v) —
   so a new file keeps the blast radius at zero: nothing existing is touched
   except the [_CoqProject] line that registers this one.

   NOT THE COMPOSABLE-PAIRS PRODUCT.  Theory/OGraph.v is the other §II.7 file
   that multiplies graphs, and the two products are unrelated.  There the node
   set O is FIXED, and A ×_O B has as its arrows the composable pairs <g, f>;
   that product is not symmetric, its unit is the trivial O-graph, and its
   point is to exhibit a category as a monoid.  Here the nodes VARY and the
   product is the cartesian one, pairs of nodes and pairs of edges.  The two do
   not specialise to one another, and OGraph.v says in terms that it defines no
   varying-node product ("No [Grph]-level (varying-node) product is defined"),
   which is the gap this file fills; conversely nothing here bears on ×_O.

   A SMALL HISTORICAL NOTE the issue points out and this file finally acts on:
   Quiver.v has required [Construction.Opposite] and [Construction.Product]
   since its introduction WITHOUT USING EITHER (Quiver.v:10-11; neither name
   occurs in its body).  Those two imports are exactly what this exercise
   needs, so the requirement is at last discharged rather than removed.

   UNIVERSES.  [QuiverOp] and [QuiverProd] are declared with explicit universe
   binders, and neither collapses anything: [QuiverOp@{o h p}] preserves the
   three levels of [Quiver], and [QuiverOp_invol@{o h p}] carries an EMPTY
   constraint clause.  The two preservation lemmas, however, each carry

     h = p       (and, on the product side, also  h1 = p1  and  h2 = p2)

   identifying a category's hom and proof universes.  This is INHERITED FROM
   THE DONORS and is not introduced here: [Construction/Opposite.v]'s
   [Opposite@{u u0} : Category@{u0 u u} -> Category@{u0 u u}] already
   identifies them, as does [Construction/Product.v]'s [Product], whose two
   arguments elaborate at [Category@{u1 u2 u2}] and [Category@{u3 u4 u4}].
   Measured: the bare term [fun (C : Category@{o h p}) => C^op], mentioning
   nothing from this file, already forces [h = p], whereas
   [fun (C : Category@{o h p}) => QuiverOfCat C] carries only [h <= p].  The
   printed statements show the cause directly — [Opposite.Opposite@{h o}] takes
   two universe arguments and [Product.Product@{o h o1 h1 o2 h2}] six, where
   nine would be needed to keep the three levels of both factors apart.

   The HOMOMORPHISMS below are less universe-general than the two quivers, and
   this too is measured rather than glossed.  [QuiverFst@{o1 h1 p1 o2 h2 p2
   o h p}] carries [h1 = h] and [p1 = p], identifying the product's edge and
   proof levels with the FIRST factor's, and [QuiverPair@{u u0 u1 u2 u3 u4 u5}]
   shares one edge level and one proof level across its three quivers.  These
   are identifications AMONG EDGE LEVELS and are a different phenomenon from
   the hom/proof collapse of the preceding paragraph; nothing in this file
   needs the extra generality, and no attempt was made to recover it.  The
   scope of this whole disclosure is the constants named in it and no others.

   WHAT IS NOT BUILT.  [QuiverOp] is not packaged as an endofunctor of
   [QuiverCategory] (the object and arrow maps are here as [QuiverOp] and
   [QuiverOp_map], with the involution both ways, but no [Functor] record and
   no [Forgetful]-commutes-with-it natural comparison); [QuiverProd] is not
   packaged as a bifunctor, and no [Cartesian QuiverCategory] instance is
   claimed; and the [≈]-hypothesis form of [QuiverPair_unique] is open, per
   (4).  None of these is needed by the exercise. *)

(* NOTATION GUARD.  [C^op] (category_scope, Construction/Opposite.v) and [F^op]
   (functor_scope, Functor/Opposite.v) are the same token, and importing
   Functor/Opposite.v opens functor_scope, so a bare [C^op] in an argument
   position carrying no scope annotation elaborates as the *functor* opposite
   and does not typecheck.  Following the precedent recorded in
   Instance/Rng/Mod.v, category_scope is re-opened here so that [^op] means
   [Opposite] by default, and the functor opposite is named explicitly as
   [Opposite_Functor]. *)
Local Open Scope category_scope.

Local Notation "Q ⇨ Q'" := (QuiverHomomorphism Q Q') (at level 40).
Local Existing Instance edgeset.

(** ** The opposite quiver *)

Section OppositeQuiver.

(* Same nodes, every edge reversed.  The endpoint-indexed encoding makes this a
   pure reindexing: [edges y x] is already a type, so nothing is transported
   and no equality on nodes is consumed. *)
Definition QuiverOp@{o h p} (G : Quiver@{o h p}) : Quiver@{o h p} := {|
  nodes   := @nodes G;
  edges   := fun x y => @edges G y x;
  edgeset := fun x y => @edgeset G y x
|}.

(* What the three fields unfold to, recorded rather than described. *)
Definition QuiverOp_nodes@{o h p} (G : Quiver@{o h p}) :
  @nodes (QuiverOp G) = @nodes G := eq_refl.

Definition QuiverOp_edges@{o h p} (G : Quiver@{o h p}) (x y : @nodes G) :
  @edges (QuiverOp G) x y = @edges G y x := eq_refl.

Definition QuiverOp_edgeset@{o h p} (G : Quiver@{o h p}) (x y : @nodes G) :
  @edgeset (QuiverOp G) x y = @edgeset G y x := eq_refl.

(* Involution, at Leibniz equality of the whole [Quiver] record.  [Quiver] has
   primitive projections with eta conversion, so the doubly-reversed record is
   convertible to [G] itself rather than merely isomorphic to it. *)
Definition QuiverOp_invol@{o h p} (G : Quiver@{o h p}) :
  QuiverOp (QuiverOp G) = G := eq_refl.

(* Reversal on homomorphisms: the node action is unchanged and the edge action
   is the same family read at swapped indices. *)
Definition QuiverOp_map@{o1 h1 p1 o2 h2 p2}
  {G : Quiver@{o1 h1 p1}} {G' : Quiver@{o2 h2 p2}} (F : G ⇨ G') :
  QuiverOp G ⇨ QuiverOp G' :=
  Build_QuiverHomomorphism (QuiverOp G) (QuiverOp G')
    (@fnodes _ _ F)
    (fun x y => @fedgemap _ _ F y x)
    (fun x y => @fedgemap_respects _ _ F y x).

Definition QuiverOp_map_invol@{o1 h1 p1 o2 h2 p2}
  {G : Quiver@{o1 h1 p1}} {G' : Quiver@{o2 h2 p2}} (F : G ⇨ G') :
  QuiverOp_map (QuiverOp_map F) = F := eq_refl.

End OppositeQuiver.

(** ** The product quiver *)

Section ProductQuiver.

(* The componentwise setoid on a product of edge sets.  Two points about the
   spelling, both of them measured rather than stylistic.

   First, the three [Equivalence] fields are written out as explicit terms
   rather than discharged by a tactic or by [Program].  The tree runs
   [Unset Transparent Obligations] (Lib/Tactics.v:36), so an obligation-built
   equivalence proof is an opaque constant, and [Setoid] has primitive
   projections with eta — conversion therefore compares the [setoid_equiv]
   fields, and an opaque one defeats the definitional agreement recorded in
   [QuiverOfCat_Product].  The spelling deliberately mirrors
   Construction/Product.v:98-119.

   Second, this is NOT [Lib/Datatypes.v:139]'s [prod_setoid], which is a global
   [Program Instance] with exactly this [equiv] but an opaque [setoid_equiv];
   substituting it here breaks [QuiverOfCat_Product].  That is a deliberate
   non-reuse, so it is guarded rather than merely stated:
   Test/ProbeQuiverConstructions.v builds the [prod_setoid] variant (which is a
   perfectly good quiver — only the DEFINITIONAL agreement is lost) and pins the
   resulting failure. *)
Definition edgeset_prod@{h1 p1 h2 p2 h p}
  {A : Type@{h1}} {B : Type@{h2}}
  (SA : Setoid@{h1 p1} A) (SB : Setoid@{h2 p2} B) : Setoid@{h p} (A * B) := {|
  equiv := fun f g =>
    (@equiv _ SA (fst f) (fst g) * @equiv _ SB (snd f) (snd g));
  setoid_equiv :=
    {| Equivalence_Reflexive := fun x =>
         (@Equivalence_Reflexive _ _ (@setoid_equiv _ SA) (fst x),
          @Equivalence_Reflexive _ _ (@setoid_equiv _ SB) (snd x))
     ; Equivalence_Symmetric := fun x y f =>
         (@Equivalence_Symmetric _ _ (@setoid_equiv _ SA) (fst x) (fst y) (fst f),
          @Equivalence_Symmetric _ _ (@setoid_equiv _ SB) (snd x) (snd y) (snd f))
     ; Equivalence_Transitive := fun x y z f g =>
         (@Equivalence_Transitive _ _ (@setoid_equiv _ SA)
            (fst x) (fst y) (fst z) (fst f) (fst g),
          @Equivalence_Transitive _ _ (@setoid_equiv _ SB)
            (snd x) (snd y) (snd z) (snd f) (snd g)) |}
|}.

(* Nodes are pairs, edges are pairs of edges with matching endpoints, and the
   edge setoid is componentwise. *)
Definition QuiverProd@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2}) : Quiver@{o h p} := {|
  nodes   := (@nodes G * @nodes H)%type;
  edges   := fun x y =>
    (@edges G (fst x) (fst y) * @edges H (snd x) (snd y))%type;
  edgeset := fun x y =>
    edgeset_prod (@edgeset G (fst x) (fst y)) (@edgeset H (snd x) (snd y))
|}.

Definition QuiverProd_nodes@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2}) :
  @nodes (QuiverProd@{o1 h1 p1 o2 h2 p2 o h p} G H)
    = (@nodes G * @nodes H)%type := eq_refl.

Definition QuiverProd_edges@{o1 h1 p1 o2 h2 p2 o h p}
  (G : Quiver@{o1 h1 p1}) (H : Quiver@{o2 h2 p2})
  (x y : @nodes G * @nodes H) :
  @edges (QuiverProd@{o1 h1 p1 o2 h2 p2 o h p} G H) x y
    = (@edges G (fst x) (fst y) * @edges H (snd x) (snd y))%type := eq_refl.

(* The two projections, as quiver homomorphisms. *)
Definition QuiverFst@{o1 h1 p1 o2 h2 p2 o h p}
  {G : Quiver@{o1 h1 p1}} {H : Quiver@{o2 h2 p2}} :
  QuiverProd@{o1 h1 p1 o2 h2 p2 o h p} G H ⇨ G :=
  Build_QuiverHomomorphism (QuiverProd G H) G
    fst
    (fun x y => fst)
    (fun x y f g e => fst e).

Definition QuiverSnd@{o1 h1 p1 o2 h2 p2 o h p}
  {G : Quiver@{o1 h1 p1}} {H : Quiver@{o2 h2 p2}} :
  QuiverProd@{o1 h1 p1 o2 h2 p2 o h p} G H ⇨ H :=
  Build_QuiverHomomorphism (QuiverProd G H) H
    snd
    (fun x y => snd)
    (fun x y f g e => snd e).

(* The pairing of two homomorphisms with a common source. *)
Definition QuiverPair
  {K G H : Quiver} (F : K ⇨ G) (F' : K ⇨ H) : K ⇨ QuiverProd G H :=
  Build_QuiverHomomorphism K (QuiverProd G H)
    (fun x => (F x, F' x))
    (fun x y e => (@fedgemap _ _ F x y e, @fedgemap _ _ F' x y e))
    (fun x y f g e =>
       (@fedgemap_respects _ _ F x y f g e, @fedgemap_respects _ _ F' x y f g e)).

(* Exchange of the two factors. *)
Definition QuiverSwap {G H : Quiver} : QuiverProd G H ⇨ QuiverProd H G :=
  Build_QuiverHomomorphism (QuiverProd G H) (QuiverProd H G)
    (fun x => (snd x, fst x))
    (fun x y e => (snd e, fst e))
    (fun x y f g e => (snd e, fst e)).

(* Swap is the pairing of the two projections in the other order — recorded by
   [eq_refl] rather than asserted. *)
Definition QuiverSwap_is_pair {G H : Quiver} :
  @QuiverSwap G H = QuiverPair QuiverSnd QuiverFst := eq_refl.

End ProductQuiver.

(** ** The universal property of the product quiver *)

Section ProductUniversal.

Context {K G H : Quiver}.

(* Both triangles hold at LEIBNIZ EQUALITY of the whole homomorphism record,
   not merely up to [≈].  The composite's [fedgemap_respects] field reduces —
   [QuiverFst]'s is [fun _ _ _ _ e => fst e] and [QuiverPair]'s is the explicit
   pair of the two given proofs, so [fst] of the pair is the first one back. *)
Definition QuiverPair_Fst (F : K ⇨ G) (F' : K ⇨ H) :
  @compose QuiverCategory K (QuiverProd G H) G QuiverFst (QuiverPair F F') = F
  := eq_refl.

Definition QuiverPair_Snd (F : K ⇨ G) (F' : K ⇨ H) :
  @compose QuiverCategory K (QuiverProd G H) H QuiverSnd (QuiverPair F F') = F'
  := eq_refl.

(* The eta law.  Here [≈] is genuinely needed: the node action of the rebuilt
   pairing is [fun x => (fst (M x), snd (M x))], and surjective pairing is not
   definitional for the standard library's [prod]. *)
Definition QuiverPair_eta (M : K ⇨ QuiverProd G H) :
  @equiv _ (@homset QuiverCategory K (QuiverProd G H))
    M (QuiverPair (@compose QuiverCategory K (QuiverProd G H) G QuiverFst M)
                  (@compose QuiverCategory K (QuiverProd G H) H QuiverSnd M)).
Proof.
  unshelve eexists.
  - intro x; cbn; destruct (@fnodes _ _ M x); reflexivity.
  - intros x y f; cbn.
    generalize (@fedgemap _ _ M x y f).
    destruct (@fnodes _ _ M x), (@fnodes _ _ M y).
    intro e; cbn; split; reflexivity.
Defined.

(* Uniqueness.  READ THE HYPOTHESES: they are Leibniz equalities of the two
   composites, which is what makes the proof a substitution into the eta law.
   The [≈]-hypothesis form would need respectfulness of [QuiverPair] in its two
   arguments, which is not proved in this file (see the header). *)
Definition QuiverPair_unique (M : K ⇨ QuiverProd G H) (F : K ⇨ G) (F' : K ⇨ H)
  (p : @compose QuiverCategory K (QuiverProd G H) G QuiverFst M = F)
  (q : @compose QuiverCategory K (QuiverProd G H) H QuiverSnd M = F') :
  @equiv _ (@homset QuiverCategory K (QuiverProd G H)) M (QuiverPair F F').
Proof.
  destruct p, q; exact (QuiverPair_eta M).
Defined.

End ProductUniversal.

(* Swapping twice is the identity, up to [≈]; see the header for why this one
   cannot be [eq_refl]. *)
Definition QuiverSwap_invol {G H : Quiver} :
  @equiv _ (@homset QuiverCategory (QuiverProd G H) (QuiverProd G H))
    (@compose QuiverCategory (QuiverProd G H) (QuiverProd H G) (QuiverProd G H)
       QuiverSwap QuiverSwap)
    (@id QuiverCategory (QuiverProd G H)).
Proof.
  unshelve eexists.
  - intro x; destruct x; reflexivity.
  - intros [a b] [c d] e; cbn; split; reflexivity.
Defined.

(** ** Preservation by the forgetful functor *)

Section Preservation.

(* Mac Lane's exercise proper: the underlying graph of C^op is the opposite of
   the underlying graph of C, and likewise for binary products.  Both hold at
   Leibniz equality of the whole [Quiver] record, by [eq_refl]; see the header
   for the three facts that allow it. *)

Definition QuiverOfCat_Opposite@{o h p} (C : Category@{o h p}) :
  QuiverOfCat@{o h p} (C^op) = QuiverOp@{o h p} (QuiverOfCat@{o h p} C) := eq_refl.

Definition QuiverOfCat_Product@{o1 h1 p1 o2 h2 p2 o h p}
  (C : Category@{o1 h1 p1}) (D : Category@{o2 h2 p2}) :
  QuiverOfCat@{o h p} (C ∏ D)
    = QuiverProd@{o1 h1 p1 o2 h2 p2 o h p}
        (QuiverOfCat@{o1 h1 p1} C) (QuiverOfCat@{o2 h2 p2} D) := eq_refl.

(* The same two statements phrased through [Forgetful : StrictCat ⟶ Quiv]
   itself, which is what the exercise asks about.  [fobj[Forgetful]] is
   [QuiverOfCat] on the nose, so these are the lemmas above read at StrictCat's
   universe instance. *)

Definition Forgetful_fobj (C : Category) :
  fobj[Forgetful] C = QuiverOfCat C := eq_refl.

Definition Forgetful_preserves_op (C : Category) :
  fobj[Forgetful] (C^op) = QuiverOp (fobj[Forgetful] C) := eq_refl.

Definition Forgetful_preserves_prod (C D : Category) :
  fobj[Forgetful] (C ∏ D) = QuiverProd (fobj[Forgetful] C) (fobj[Forgetful] D)
  := eq_refl.

(* Preservation on arrows as well as objects, for the opposite.  [Forgetful]'s
   action on a functor is [QuiverHomomorphismOfFunctor], and
   [Functor/Opposite.v]'s [Opposite_Functor] is a plain [Definition] with
   explicit fields, so this too is [eq_refl]. *)
Definition Forgetful_preserves_op_fmap
  {C D : Category} (F : C ⟶ D) :
  QuiverHomomorphismOfFunctor _ _ (Opposite_Functor F)
    = QuiverOp_map (QuiverHomomorphismOfFunctor _ _ F) := eq_refl.

(* On the product side the arrow-level content is that [Forgetful] carries the
   product projections of [Cat] to the product projections of [Quiv].  This is
   only [≈]: [Fst] and [Snd] are [Program Instance]s whose [fmap_respects]
   field is an opaque obligation, so no [eq_refl] is available. *)
Definition Forgetful_preserves_fst (C D : Category) :
  @equiv _ (@homset QuiverCategory (QuiverOfCat (C ∏ D)) (QuiverOfCat C))
    (QuiverHomomorphismOfFunctor _ _ (@Fst C D))
    (@QuiverFst (QuiverOfCat C) (QuiverOfCat D)).
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

Definition Forgetful_preserves_snd (C D : Category) :
  @equiv _ (@homset QuiverCategory (QuiverOfCat (C ∏ D)) (QuiverOfCat D))
    (QuiverHomomorphismOfFunctor _ _ (@Snd C D))
    (@QuiverSnd (QuiverOfCat C) (QuiverOfCat D)).
Proof. exists (fun _ => eq_refl); intros; reflexivity. Defined.

End Preservation.
