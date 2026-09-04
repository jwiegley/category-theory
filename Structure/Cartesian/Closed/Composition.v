Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Natural.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Wedge.
Require Import Category.Structure.Coend.
Require Import Category.Construction.Enriched.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.

Generalizable All Variables.

(** * Internal composition in a cartesian closed category *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed., Springer
   GTM 5, 1998, §IV.6, printed p. 98, Exercise 4 (`maclane:IV.6:ex4`),
   verbatim from the printed page:

     "4. In any cartesian closed category obtain a natural transformation
      c^b × b^a → c^a which agrees in Set with composition of functions.
      Prove it (like composition) associative."

   nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
   nLab: https://ncatlab.org/nlab/show/closed+monoidal+category
   nLab: https://ncatlab.org/nlab/show/dinatural+transformation
   nLab: https://ncatlab.org/nlab/show/enriched+category

   NOTATION.  Mac Lane's c^b is this tree's [exponent_obj b c], and the
   tree's notation [y ^ x] abbreviates [exponent_obj x y]
   (Structure/Cartesian/Closed.v:65).  The two spellings therefore agree on
   the DISPLAY -- [internal_compose : c^b × b^a ~> c^a] reads the same in
   both -- while the [exponent_obj] argument pairs are (b,c), (a,b) and
   (a,c) respectively; [internal_compose_obj] pins that by [eq_refl].

   THE CONSTRUCTION.  [internal_compose] is the transpose of the double
   evaluation

     (c^b × b^a) × a --to prod_assoc--> c^b × (b^a × a)
                     --second eval---->  c^b × b
                     --eval----------->  c.

   The DEFINITION spends exactly two [Closed] fields, [exponent_obj]
   (:44) and [exp_iso] (:51): [curry], [uncurry] and [eval] are all
   derived from [exp_iso] (:53-56).  The beta law [ump_exponents'] (:61)
   is what the PROOFS below spend, through [eval_curry] and
   [ump_exponents].  [internal_id x : 1 ~> x^x] is the transpose of the
   projection [exr : 1 × x ~> x].

   Every equation below is a bounded number of rewrites with three
   [eval]-level rules, then the fork algebra -- [exl_fork]/[exr_fork]
   where the composite is already a fork, [unfork] where a whole fork has
   to be split.  [eval_internal_compose_fork]
   strips one [internal_compose] from inside an evaluation,
   [eval_internal_id_fork] one [internal_id], and [eval_ihom_fork] one
   [ihom]; each is [eval_curry] at the respective transpose.  The unit
   laws take the shorter route through [uncurry_internal_compose], the
   transpose read at a pair of generalized elements.

   WHAT "NATURAL" CAN AND CANNOT MEAN HERE, which is the one place where
   the exercise's own wording has to be read with care.  In [c^b × b^a]
   the object [b] occurs CONTRAVARIANTLY in [c^b] and COVARIANTLY in
   [b^a].  An arrow [f : b1 ~> b2] therefore acts on the two factors in
   OPPOSITE directions and the resulting morphism runs between the MIXED
   objects [c^b2 × b1^a] and [c^b1 × b2^a]; there is no functor of [b]
   alone for a natural transformation in [b] to run BETWEEN, and "natural
   in all three objects" is not a well-typed demand.  Genuine naturality
   is available in [a] and in [c], and both are delivered as squares AND
   as transformations:

     - [internal_compose_natural_c] between the covariant functors
       [ComposeSrcC a b] and [ExpBase a], packaged as
       [compose_Transform_c];
     - [internal_compose_natural_a] between the contravariant functors
       [ComposeSrcA b c] and [ExpExp c], both [C^op ⟶ C], packaged as
       [compose_Transform_a].

   For [b] the honest statement is DINATURALITY, and it is delivered as
   an inhabitant of the tree's own vocabulary rather than as a bare
   equation: [internal_compose_dinatural] is the equation,
   [internal_compose_Cowedge_cond] is that equation read as
   Structure/Coend.v:160's [Cowedge_cond] at the mixed-variance
   bifunctor [ComposeB a c : C^op ∏ C ⟶ C],
   [ComposeB a c (b1, b2) = c^b1 × b2^a], with constant apex [c^a], and
   [internal_compose_Wedge] is the resulting
   [Wedge (Opposite_Functor (ComposeB a c))] -- a cowedge for
   [ComposeB a c].  NOTHING here claims naturality in [b];
   Test/ProbeComposition391.v pins the non-statement as a TYPING negative
   (the mixed-object mismatch above), with the dinaturality equation
   beside it as the passing control.

   ASSOCIATIVITY is Mac Lane's own closing demand, "prove it (like
   composition) associative".  It is stated in exactly the shape
   Construction/Enriched.v:133's [ecompose_assoc] field needs, that is
   through the associator, so that the enrichment below discharges that
   field by [exact] rather than by a restatement:

     internal_compose ∘ split internal_compose id
       ≈ internal_compose ∘ split id internal_compose ∘ to prod_assoc.

   Over [CC_Monoidal] the tensor of morphisms IS [split], the associator
   IS the cartesian one and the two unitors ARE the projections, all at
   [eq_refl]; Structure/Ring.v:258-269 records the same identifications
   and [assoc_bimap_is_split], [assoc_tensor_is_prod],
   [assoc_unit_left_is_exr] and [assoc_unit_right_is_exl] re-check them
   here, so a later change to either side would be caught.

   THE PAYOFF is [CCC_Enriched : @Enriched C CC_Monoidal], a cartesian
   closed category enriched over ITSELF, with [eobj := obj[C]],
   [ehom x y := y^x], [eid := internal_id] and
   [ecompose := internal_compose]; all three law fields are [exact] of
   the unit and associativity theorems above, so the enrichment adds no
   equational content of its own.  [Sets_Enriched] instantiates it.
   Self-enrichment as such is NOT new in tree --
   Construction/Enriched/Ab.v:370's [Enriched_Ab_itself] is an
   [@Enriched Ab Ab_Monoidal] -- so the gap this closes is the narrower
   one: no CARTESIAN CLOSED category was enriched over itself.  Nor is
   [CC_Monoidal] a first, and the reason it looks like one is an ALIAS:
   Construction/Enriched/Two.v:131's [Enriched_of_TwoPreorder] is an
   [@Enriched _2 Two_Monoidal], and [Two_Monoidal] IS
   [@CC_Monoidal _2 Two_Cartesian Two_Terminal] at [eq_refl] through the
   plain Definition at Structure/Monoidal/Cartesian.v:49, so a name grep
   for [CC_Monoidal] -- which returns 18 files -- does not see it.  That
   instance is not self-enrichment: its [eobj] is [tpre_carrier P], an
   arbitrary preorder carrier rather than the objects of [_2].

   THE [Set] CLAUSE, at its measured grade.  Mac Lane asks that the
   transformation "agree in Set with composition of functions".  [Sets]
   is this library's category of setoids, whose exponential [c^b] is the
   setoid of ≈-respecting maps, so the statement is pointwise on setoid
   morphisms, and [sets_internal_compose] holds at [eq_refl]: the value
   of [internal_compose (g, f)] at [t] IS [g (f t)].  So does
   [sets_internal_id].  At the level of whole MORPHISMS of [Sets] the
   grade drops to [≈] ([sets_internal_compose_morphism]), and the cause
   is located rather than guessed: the two underlying FUNCTIONS are the
   same term ([sets_internal_compose_underlying], [eq_refl]), so what
   differs is exactly the [proper_morphism] certificate the two sides
   rebuild.  The strict form is refuted and pinned in the probe.

   AN ENGINEERING HAZARD, met again and measured more narrowly than the
   donor states it.  Structure/Cartesian/Closed/Natural.v:315-321 records
   that elaborating a functor's object action INSIDE its own [Program
   Definition] lets [Program] defer an unresolved instance argument of
   [product_obj] into an obligation, which Lib/Foundation.v's [Unset
   Transparent Obligations] makes opaque, after which [fobj] converts
   with nothing.  The five functors here therefore give their object and
   arrow actions as ordinary definitions first.  The boundary is narrower
   than "any inline object action": an inline [exponent_obj] alone DOES
   reduce, and it is [product_obj] -- the [Cartesian] instance -- that is
   deferred, which is the donor's attribution rather than a fact
   re-derived here.  What the probe machine-checks is the SEPARATION, the
   exponent-only functor as a passing control and the product one as a
   CONVERSION negative.  The four [*_fobj] Examples record that FOUR of
   the five shipped functors reduce; [ComposeB] reduces as well, but that
   is measured rather than pinned by an Example.

   UNIVERSES, off BOTH binder and block.  Every constant is over
   [C : Category@{u u0 u0}] -- hom identified with proof -- in the
   BINDER, while not one constraint BLOCK contains a universe equation:
   reading the blocks alone would report no identification.  It is
   inherited, and [Cartesian] alone already forces it, which the probe
   pins as a FORMABILITY negative against the category, its objects, its
   hom-sets, its identities and its composition all accepted at hom and
   proof declared strictly apart.  No word-bounded [Set] occurs in any
   binder or block.

   AXIOMS.  All 71 constants of this file -- the 53 named declarations
   plus the 18 [Program] obligations of the five functors and the
   enrichment, which no source sweep sees -- report "Closed under the
   global context".  [Sets_Closed] obtains its exponentials with no axiom
   (Instance/Coq.v:80-81 records the contrast), so the [Set] clause costs
   nothing; the axiom-carrying [Coq_Closed] (Instance/Coq.v:84) is
   deliberately NOT instantiated here and Instance/Coq.v is not required.

   PRIOR ART, measured.  [internal_compose], [internal_comp],
   [comp_internal] and [internal_id] have zero occurrences anywhere else
   in the tree, and no declaration elsewhere has an object action of the
   shape [c^b × b^a].  Structure/Closed.v does declare a [hom_compose]
   field, but the whole [Class Closed] block there sits inside the
   comment opened at Structure/Closed.v:154 by a dated deferral marker
   and closed at :195, and its shape is the CURRIED Eilenberg-Kelly one,
   [[y, z] ~> [[x, y], [x, z]]] (:175), which is not the shape this
   exercise asks for; it is not revived here.  What did exist, and is
   CONSUMED rather than rebuilt, is Structure/Cartesian/Closed/Natural.v's
   [ihom f h := curry (h ∘ eval ∘ second f)] (:180) -- the internal hom's
   own two-variable action, which IS [fmap[InternalHomFunctor]] at
   [eq_refl] (:222) -- together with [ihom_id], [ihom_comp] and the
   [opobj]/[oparr] readings of a contravariant slot.

   NOT DELIVERED.  No coend or end of [ComposeB], so nothing says the
   cowedge is universal; no [EnrichedFunctor] and no comparison of
   [CCC_Enriched] with Construction/Enriched.v:169's
   [Category_is_Enriched_over_Set]; no relation between [ExpBase] and
   Structure/Cartesian/Closed/Adjunction.v:188's [Exp_Functor], which
   would need that module -- see the note before the functors for what
   is read off its source and what requiring it would cost; no
   monoidal-closed generalisation, so nothing here is stated over
   Structure/Monoidal/Closed.v; no witness at a cartesian closed category
   other than [Sets]; and nothing is registered as an [Instance]. *)

Section Composition.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.

(** ** The composition and identity morphisms *)

(* Mac Lane's c^b × b^a ~> c^a: transpose the double evaluation. *)
Definition internal_compose {a b c : C} : c^b × b^a ~> c^a :=
  curry (eval ∘ second eval ∘ to prod_assoc).

(* [unfork] and [cat] both call [simpl]; without this they would unfold
   [internal_compose] into its transpose and destroy every rewrite below.
   Same discipline as Structure/Cartesian/Closed/Natural.v:185 for [ihom]. *)
Arguments internal_compose : simpl never.

(* The three exponentials, pinned in their [exponent_obj] spelling, so that
   the argument order of the header's notation note is machine-checked. *)
Example internal_compose_obj (a b c : C) :
  (c^b × b^a ~{C}~> c^a)
    = (exponent_obj b c × exponent_obj a b ~{C}~> exponent_obj a c)
  := eq_refl.

(** ** The beta laws *)

Lemma uncurry_internal_compose_raw {a b c : C} :
  uncurry (@internal_compose a b c)
    ≈ eval ∘ second eval ∘ to prod_assoc.
Proof. apply uncurry_curry. Qed.

Lemma eval_internal_compose {a b c : C} :
  eval ∘ first (@internal_compose a b c)
    ≈ eval ∘ second eval ∘ to prod_assoc.
Proof. rewrite eval_first; apply uncurry_internal_compose_raw. Qed.

(* The workhorse.  For any pair of generalized elements [h] and [k] of the
   two exponentials, the transpose of the composite is "apply [h] to the
   result of applying [k]".  Every law below is an instance. *)
Lemma uncurry_internal_compose {w a b c : C}
      (h : w ~> c^b) (k : w ~> b^a) :
  uncurry (internal_compose ∘ (h △ k))
    ≈ uncurry h ∘ (exl △ uncurry k).
Proof.
  rewrite uncurry_comp.
  rewrite uncurry_internal_compose_raw.
  rewrite <- !eval_first.
  unfork.
Qed.

(* The rewrite rule that strips one [internal_compose] from inside an
   evaluation: this is [eval_curry] at the transpose, followed by the fork
   algebra of [prod_assoc].  Associativity, both naturality squares and
   dinaturality are this rule and its two companions applied a bounded
   number of times and then [exl_fork]/[exr_fork] to [reflexivity]. *)
Lemma eval_internal_compose_fork {w a b c : C}
      (g : w ~> c^b × b^a) (k : w ~> a) :
  eval ∘ ((internal_compose ∘ g) △ k)
    ≈ eval ∘ ((exl ∘ g) △ (eval ∘ ((exr ∘ g) △ k))).
Proof.
  unfold internal_compose.
  rewrite eval_curry.
  rewrite <- !comp_assoc.
  unfork.
Qed.

Context `{@Terminal C}.

(* Mac Lane's identity arrow of the internal category: 1 ~> x^x. *)
Definition internal_id {x : C} : 1 ~> x^x := curry exr.

Arguments internal_id : simpl never.

Lemma uncurry_internal_id {x : C} :
  uncurry (@internal_id x) ≈ exr.
Proof. apply uncurry_curry. Qed.

Lemma eval_internal_id_fork {w x : C} (g : w ~> 1) (k : w ~> x) :
  eval ∘ ((internal_id ∘ g) △ k) ≈ k.
Proof.
  unfold internal_id.
  rewrite eval_curry.
  now rewrite exr_fork.
Qed.

(** ** The unit laws *)

(* [1 × y^x ~> y^x]: composing with the internal identity on the left is
   the projection, which is [to unit_left] over [CC_Monoidal]. *)
Theorem internal_compose_id_left {x y : C} :
  @internal_compose x y y ∘ split internal_id id ≈ exr.
Proof.
  apply uncurry_inj.
  unfold split.
  rewrite uncurry_internal_compose.
  rewrite (uncurry_comp (@internal_id y) exl).
  rewrite uncurry_internal_id.
  rewrite <- !eval_first.
  unfork.
  rewrite !exr_fork.
  now rewrite id_left.
Qed.

(* [y^x × 1 ~> y^x]: composing with the internal identity on the right is
   the other projection, which is [to unit_right] over [CC_Monoidal]. *)
Theorem internal_compose_id_right {x y : C} :
  @internal_compose x x y ∘ split id internal_id ≈ exl.
Proof.
  apply uncurry_inj.
  unfold split.
  rewrite uncurry_internal_compose.
  rewrite (uncurry_comp (@internal_id x) exr).
  rewrite uncurry_internal_id.
  rewrite <- !eval_first.
  unfork.
  rewrite !exr_fork.
  cat.
Qed.

(** ** Associativity *)

(* The two projections of the associator, in the composed shape the fork
   algebra below actually meets. *)
Lemma exl_prod_assoc_r {v a b c : C} (h : v ~> (a × b) × c) :
  exl ∘ (to (@prod_assoc C _ a b c) ∘ h) ≈ exl ∘ (exl ∘ h).
Proof. rewrite !comp_assoc; simpl; now rewrite exl_fork. Qed.

Lemma exr_prod_assoc_r {v a b c : C} (h : v ~> (a × b) × c) :
  exr ∘ (to (@prod_assoc C _ a b c) ∘ h)
    ≈ (exr ∘ (exl ∘ h)) △ (exr ∘ h).
Proof.
  rewrite comp_assoc; simpl; rewrite exr_fork.
  rewrite <- fork_comp.
  now rewrite !comp_assoc.
Qed.

(* Mac Lane's "prove it (like composition) associative", in exactly the
   shape [ecompose_assoc] demands: the associator on the right. *)
Theorem internal_compose_assoc {x y z w : C} :
  @internal_compose x y w ∘ split internal_compose id
    ≈ @internal_compose x z w ∘ split id internal_compose
        ∘ to prod_assoc.
Proof.
  apply uncurry_inj.
  unfold split.
  rewrite <- !eval_first.
  unfold first.
  rewrite <- !comp_assoc.
  rewrite !eval_internal_compose_fork.
  rewrite !comp_assoc.
  rewrite !exl_fork, !exr_fork.
  rewrite <- !comp_assoc.
  rewrite !id_left.
  rewrite !exl_prod_assoc_r, !exr_prod_assoc_r.
  rewrite !eval_internal_compose_fork.
  rewrite !exl_fork, !exr_fork.
  reflexivity.
Qed.

(** ** Naturality in [a] and in [c] *)

(* The companion of [eval_internal_compose_fork] for the internal hom's own
   action: it strips one [ihom] from inside an evaluation. *)
Lemma eval_ihom_fork {v a b c d : C} (f : b ~> a) (h : c ~> d)
      (g : v ~> c^a) (m : v ~> b) :
  eval ∘ ((ihom f h ∘ g) △ m) ≈ h ∘ (eval ∘ (g △ (f ∘ m))).
Proof.
  unfold ihom.
  rewrite eval_curry.
  rewrite <- !comp_assoc.
  unfork.
Qed.

(* Naturality in the base [c], at fixed [a] and [b]: both sides are
   morphisms [c^b × b^a ~> c'^a]. *)
Theorem internal_compose_natural_c {a b c c' : C} (g : c ~> c') :
  ihom id g ∘ @internal_compose a b c
    ≈ @internal_compose a b c' ∘ first (ihom id g).
Proof.
  apply uncurry_inj.
  rewrite <- !eval_first.
  unfold first.
  rewrite <- !comp_assoc.
  rewrite eval_ihom_fork.
  rewrite eval_internal_compose_fork.
  rewrite eval_internal_compose_fork.
  rewrite !comp_assoc.
  rewrite !exl_fork, !exr_fork.
  rewrite <- !comp_assoc.
  rewrite eval_ihom_fork.
  rewrite !id_left.
  reflexivity.
Qed.

(* Naturality in the exponent [a], at fixed [b] and [c]: the variable is
   CONTRAVARIANT, so the square runs against an arrow [f : a' ~> a] and
   both sides are morphisms [c^b × b^a ~> c^a']. *)
Theorem internal_compose_natural_a {a a' b c : C} (f : a' ~> a) :
  ihom f id ∘ @internal_compose a b c
    ≈ @internal_compose a' b c ∘ second (ihom f id).
Proof.
  apply uncurry_inj.
  rewrite <- !eval_first.
  unfold first, second.
  rewrite <- !comp_assoc.
  rewrite eval_ihom_fork.
  rewrite eval_internal_compose_fork.
  rewrite eval_internal_compose_fork.
  rewrite !comp_assoc.
  rewrite !exl_fork, !exr_fork.
  rewrite <- !comp_assoc.
  rewrite eval_ihom_fork.
  rewrite !id_left.
  reflexivity.
Qed.

(** ** The two naturality squares, packaged as transformations

    The four functors below are built here rather than imported, and the
    reason is NOT that nothing else would serve.  Two in-tree candidates
    do: Functor/Bifunctor/Partial.v:121's [Partial_l] and :144's
    [Partial_r], applied to Functor/Hom/Internal.v:40's
    [InternalHomFunctor C], give functors agreeing with [ExpBase] and
    [ExpExp] on BOTH actions at [eq_refl] -- object and arrow alike, with
    no residue, only the whole functor RECORD refused because [Program]
    rebuilds the law fields (all measured out of tree).  The marginal
    closure cost is ONE module, 43 to 44: [InternalHomFunctor] is already
    inside the 43, and only Functor/Bifunctor/Partial.v is new.
    They are not adopted here only because doing so is a refactor rather
    than a correction; nothing below depends on the hand-built forms
    beyond their being these functors.  A THIRD candidate,
    Structure/Cartesian/Closed/Adjunction.v:188's [Exp_Functor S], fits
    worse: read off its source its object action is [ExpBase]'s but its
    arrow action is [curry (f ∘ eval)] where [ihom id f] is
    [curry (f ∘ eval ∘ second id)], and requiring that module takes
    this file's transitive closure from 43 modules to 47 (measured).
    Neither of the two SOURCE functors has an in-tree counterpart: no
    declaration elsewhere has an object action of the shape [c^b × b^a],
    the other products of two exponentials in tree being the isomorphism
    statements [y^x × z^x] and [x^y × x^z], where the two exponentials
    share their exponent or their base rather than meeting base to
    exponent. *)

(* The object and arrow actions are given as ordinary definitions and only
   then assembled into functor records.  Elaborating them inside the
   [Program Definition] would not do: [Program] defers the unresolved
   [Cartesian] instance argument of [product_obj] into an OBLIGATION,
   which Lib/Foundation.v's [Unset Transparent Obligations] makes opaque,
   and the resulting [fobj] then converts with nothing -- in particular
   not with the endpoints of [internal_compose].  This is the hazard
   Structure/Cartesian/Closed/Natural.v:315-321 records; it was met again
   here, and the probe measures its boundary: an inline [exponent_obj]
   alone reduces, an inline [product_obj] does not. *)

Definition expBase_obj (a c : C) : C := c^a.

Definition expBase_map (a : C) {c c' : C} (g : c ~> c') :
  expBase_obj a c ~> expBase_obj a c' := ihom id g.

Program Definition ExpBase (a : C) : C ⟶ C := {|
  fobj := expBase_obj a;
  fmap := fun _ _ g => expBase_map a g
|}.
Next Obligation.
  proper; unfold expBase_map, expBase_obj; now rewrites.
Qed.
Next Obligation. unfold expBase_map, expBase_obj; apply ihom_id. Qed.
Next Obligation.
  unfold expBase_map, expBase_obj.
  rewrite ihom_comp; now rewrite id_left.
Qed.

Definition composeSrcC_obj (a b c : C) : C := c^b × b^a.

Definition composeSrcC_map (a b : C) {c c' : C} (g : c ~> c') :
  composeSrcC_obj a b c ~> composeSrcC_obj a b c' :=
  first (ihom id g).

Program Definition ComposeSrcC (a b : C) : C ⟶ C := {|
  fobj := composeSrcC_obj a b;
  fmap := fun _ _ g => composeSrcC_map a b g
|}.
Next Obligation.
  proper; unfold composeSrcC_map, composeSrcC_obj; now rewrites.
Qed.
Next Obligation.
  unfold composeSrcC_map, composeSrcC_obj.
  rewrite ihom_id; apply first_id.
Qed.
Next Obligation.
  unfold composeSrcC_map, composeSrcC_obj.
  rewrite <- first_comp, ihom_comp; now rewrite id_left.
Qed.

Definition expExp_obj (c : C) (a : C^op) : C := c^(opobj a).

Definition expExp_map (c : C) {a a' : C^op} (f : a ~> a') :
  expExp_obj c a ~> expExp_obj c a' := ihom (oparr f) id.

Program Definition ExpExp (c : C) : C^op ⟶ C := {|
  fobj := expExp_obj c;
  fmap := fun _ _ f => expExp_map c f
|}.
Next Obligation.
  proper; unfold expExp_map, expExp_obj, oparr; now rewrites.
Qed.
Next Obligation.
  unfold expExp_map, expExp_obj, oparr; apply ihom_id.
Qed.
Next Obligation.
  unfold expExp_map, expExp_obj, oparr.
  rewrite ihom_comp; now rewrite id_left.
Qed.

Definition composeSrcA_obj (b c : C) (a : C^op) : C :=
  c^b × b^(opobj a).

Definition composeSrcA_map (b c : C) {a a' : C^op} (f : a ~> a') :
  composeSrcA_obj b c a ~> composeSrcA_obj b c a' :=
  second (ihom (oparr f) id).

Program Definition ComposeSrcA (b c : C) : C^op ⟶ C := {|
  fobj := composeSrcA_obj b c;
  fmap := fun _ _ f => composeSrcA_map b c f
|}.
Next Obligation.
  proper; unfold composeSrcA_map, composeSrcA_obj, oparr; now rewrites.
Qed.
Next Obligation.
  unfold composeSrcA_map, composeSrcA_obj, oparr.
  rewrite ihom_id; apply second_id.
Qed.
Next Obligation.
  unfold composeSrcA_map, composeSrcA_obj, oparr.
  rewrite <- second_comp, ihom_comp; now rewrite id_left.
Qed.

(* The four object actions read back on the nose, which is what makes the
   two transformations typecheck with no transport -- and what the hazard
   above would have destroyed. *)
Example expBase_fobj (a c : C) : fobj[ExpBase a] c = c^a := eq_refl.

Example composeSrcC_fobj (a b c : C) :
  fobj[ComposeSrcC a b] c = c^b × b^a := eq_refl.

Example expExp_fobj (c : C) (a : C^op) :
  fobj[ExpExp c] a = c^(opobj a) := eq_refl.

Example composeSrcA_fobj (b c : C) (a : C^op) :
  fobj[ComposeSrcA b c] a = c^b × b^(opobj a) := eq_refl.

(* Mac Lane's "natural transformation", in [c]. *)
Definition compose_Transform_c (a b : C) :
  ComposeSrcC a b ⟹ ExpBase a :=
  @Build_Transform' C C (ComposeSrcC a b) (ExpBase a)
    (fun c => @internal_compose a b c)
    (fun c c' g => @internal_compose_natural_c a b c c' g).

(* And in [a], where the variable is contravariant. *)
Definition compose_Transform_a (b c : C) :
  ComposeSrcA b c ⟹ ExpExp c :=
  @Build_Transform' (C^op) C (ComposeSrcA b c) (ExpExp c)
    (fun a => @internal_compose a b c)
    (fun a a' f => @internal_compose_natural_a a a' b c f).

(* The components ARE [internal_compose], on the nose. *)
Example compose_Transform_c_component (a b c : C) :
  transform (compose_Transform_c a b) c = @internal_compose a b c
  := eq_refl.

Example compose_Transform_a_component (a b c : C) :
  transform (compose_Transform_a b c) a = @internal_compose a b c
  := eq_refl.

(** ** Dinaturality in [b] *)

(* [b] occurs contravariantly on the left of the product and covariantly on
   the right, so there is no functor of [b] for a natural transformation in
   [b] to run between.  What holds is the COWEDGE condition: for
   [f : b1 ~> b2] the two routes out of [c^b2 × b1^a] into [c^a] agree. *)
Theorem internal_compose_dinatural {a c b1 b2 : C} (f : b1 ~> b2) :
  @internal_compose a b1 c ∘ split (ihom f id) id
    ≈ @internal_compose a b2 c ∘ split id (ihom id f).
Proof.
  apply uncurry_inj.
  rewrite <- !eval_first.
  unfold first, split.
  rewrite <- !comp_assoc.
  rewrite !eval_internal_compose_fork.
  rewrite !comp_assoc.
  rewrite !exl_fork, !exr_fork.
  rewrite <- !comp_assoc.
  rewrite !id_left.
  rewrite !eval_ihom_fork.
  rewrite !id_left.
  reflexivity.
Qed.

(* The mixed-variance bifunctor the dinaturality is dinaturality FOR:
   [ComposeB a c (b1, b2) = c^b1 × b2^a], contravariant in the first slot
   and covariant in the second.  Object and arrow actions first, per the
   hazard recorded above. *)

Definition composeB_obj (a c : C) (p : C^op ∏ C) : C :=
  c^(opobj (fst p)) × (snd p)^a.

Definition composeB_map (a c : C) {x y : C^op ∏ C} (m : x ~> y) :
  composeB_obj a c x ~> composeB_obj a c y :=
  split (ihom (oparr (fst m)) id) (ihom id (snd m)).

Program Definition ComposeB (a c : C) : C^op ∏ C ⟶ C := {|
  fobj := composeB_obj a c;
  fmap := fun _ _ m => composeB_map a c m
|}.
Next Obligation.
  proper; unfold composeB_map, composeB_obj, oparr; now rewrites.
Qed.
Next Obligation.
  unfold composeB_map, composeB_obj, oparr; simpl.
  now rewrite !ihom_id, split_id.
Qed.
Next Obligation.
  unfold composeB_map, composeB_obj, oparr; simpl.
  now rewrite split_comp, !ihom_comp, !id_left.
Qed.

(* The constant family [internal_compose] satisfies the tree's own covariant
   cowedge condition (Structure/Coend.v:160) at that bifunctor, with apex
   [c^a]. *)
Definition internal_compose_Cowedge_cond (a c : C) :
  @Cowedge_cond C C (ComposeB a c) (c^a)
    (fun x => @internal_compose a x c).
Proof.
  intros x y f.
  simpl; unfold composeB_map, composeB_obj, oparr, op; simpl.
  rewrite !ihom_id.
  apply internal_compose_dinatural.
Defined.

(* ... and therefore assembles into an inhabitant of [Wedge]. *)
Definition internal_compose_Wedge (a c : C) :=
  @covariant_cowedge C C (ComposeB a c) (c^a)
    (fun x => @internal_compose a x c)
    (internal_compose_Cowedge_cond a c).

(** ** A cartesian closed category is enriched over itself *)

(* The four identifications the enrichment rests on, re-checked here: over
   [CC_Monoidal] the tensor of morphisms IS [split], the associator IS the
   cartesian one, and the two unitors ARE the projections. *)
Example assoc_bimap_is_split {x y z w : C} (f : x ~> y) (g : z ~> w) :
  @bimap C C C (@tensor C CC_Monoidal) _ _ _ _ f g = split f g := eq_refl.

Example assoc_tensor_is_prod {x y z : C} :
  to (@tensor_assoc C CC_Monoidal x y z) = to (@prod_assoc C _ x y z)
  := eq_refl.

Example assoc_unit_left_is_exr {x : C} :
  to (@unit_left C CC_Monoidal x) = exr := eq_refl.

Example assoc_unit_right_is_exl {x : C} :
  to (@unit_right C CC_Monoidal x) = exl := eq_refl.

(* The payoff: [C] enriched over itself, with hom-objects the
   exponentials. *)
Program Definition CCC_Enriched : @Enriched C CC_Monoidal := {|
  eobj := obj[C];
  ehom := fun x y => y^x;
  eid := fun x => internal_id;
  ecompose := fun x y z => internal_compose
|}.
Next Obligation. exact internal_compose_id_left. Qed.
Next Obligation. exact internal_compose_id_right. Qed.
Next Obligation. exact internal_compose_assoc. Qed.

End Composition.

(** * Agreement with composition of functions in [Set] *)

(* Mac Lane's remaining clause: the transformation "agrees in Set with
   composition of functions".  [Sets] is this library's category of
   setoids, whose exponential [c^b] is the setoid of ≈-respecting maps, so
   the statement is pointwise on setoid morphisms. *)

Example sets_internal_compose (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) (t : a) :
  @internal_compose Sets _ _ a b c (g, f) t = g (f t) := eq_refl.

(* At the level of whole morphisms of [Sets] the identification is [≈] and
   not Leibniz, and the cause is located rather than guessed: the two
   UNDERLYING FUNCTIONS are the same term (next [Example]), so what differs
   is exactly the rebuilt [proper_morphism] certificate.  The strict form is
   refuted and pinned in Test/ProbeComposition391.v. *)
Example sets_internal_compose_underlying (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) :
  (fun t : a => @internal_compose Sets _ _ a b c (g, f) t)
    = (fun t : a => (g ∘[Sets] f) t) := eq_refl.

Example sets_internal_compose_morphism (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) :
  @internal_compose Sets _ _ a b c (g, f) ≈[Sets] g ∘ f.
Proof. intro t; reflexivity. Qed.

(* And the identity: [internal_id] is the identity function of [Sets]. *)
Example sets_internal_id (x : Sets)
        (u : @terminal_obj Sets Sets_Terminal) (t : x) :
  @internal_id Sets _ _ Sets_Terminal x u t = t := eq_refl.

(* [Sets] is therefore enriched over itself, with hom-objects the function
   setoids. *)
Definition Sets_Enriched : @Enriched Sets CC_Monoidal := CCC_Enriched.
