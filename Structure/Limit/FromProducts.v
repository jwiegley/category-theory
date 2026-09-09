Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Open Scope category_scope.

(** * Limits from products and equalizers *)

(* Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.2
   Theorems 1 and 2 and Corollary 2 (book p. 113), §V.4 Exercise 2 (book
   p. 118); Riehl, Category Theory in Context, 2nd ed., §3.2 Theorem 3.2.11,
   Remark 3.2.13, Exercise 3.2.ii and §3.5 Theorem 3.5.11; Awodey, Category
   Theory, §5.4 Proposition 5.23, Corollary 5.24 and Theorem 5.25.

   The central existence theorem for limits.  A category with products
   indexed by the objects of a shape J and by the arrows of J, and with
   equalizers, has a limit for every diagram F : J ⟶ C: the equalizer of
   the two canonical maps

       s, t : ∏_{x ∈ ob J} F x  ⇉  ∏_{f ∈ mor J} F (cod f),

   whose components at f are the projection at cod f and the diagram's
   action fmap[F] f after the projection at dom f (Riehl's Remark 3.2.13,
   the element-free description), with legs the object projections after
   the equalizing map.  Hence products plus equalizers give completeness,
   dually coproducts plus coequalizers give cocompleteness, and a functor
   preserving both primitives preserves every limit.

   WHAT IS BUILT, and at what strength.

   (A) [pe_iprod_ext]: two maps into an indexed product agreeing under
       every projection are equal — the uniqueness clause of [iprod_desc]
       as an extensionality principle.  Structure/Bicartesian/Matrix.v's
       [iprod_ext] states the same fact but drags an [IsIndexedCoproduct]
       in from its section; the four-line restatement is disclosed.

   (B) [ArrowIx J := {p : obj J * obj J & fst p ~> snd p}], Mac Lane's
       index ∏_{f ∈ mor J}, with [aix_dom]/[aix_cod]/[aix_arr] and
       [mk_arrow] (readbacks at [eq_refl]).  [Gen idx_arr f] is the
       inductive closure of an arbitrary family of arrows under identities,
       composition and [≈]; [Generates idx_arr] says the family reaches
       every arrow, and [ArrowIx_Generates] discharges it at the full
       index in one constructor.

   (C) Section [Core], ELEMENTARY: over any two [IsIndexedProduct]s, any
       [s t] satisfying the two component equations at a GENERATING
       family, and any [IsEqualizer s t E e], the cone [pe_cone] (apex E,
       legs [projP x ∘ e]) is limiting: [pe_limiting] is Theorem 1.  Cone
       coherence is ONE induction over [Gen] whose only case with content
       is the indexed arrow, closed by the two component equations and
       [fork_eq]; the mediator is [eq_desc] of the tupling of the
       competing cone, the tupling equalizes by [pe_iprod_ext] at Q
       through cone coherence, and uniqueness is the product's uniqueness
       clause followed by the equalizer's.  The section runs under
       [Set Default Proof Using "All"], so every constant of it takes the
       whole context in the order it is declared.

   (D) Section [FromClasses], over [HasIndexedProducts C] and
       [HasEqualizers C]: [pe_obj_product], [pe_arrow_product], [pe_s],
       [pe_t] (by [iprod_desc], Remark 3.2.13), [pe_equalizer], [pe_apex],
       [pe_incl], [pe_limit_cone], [pe_limit_limiting], and the pinned
       [limit_of_products_equalizer F : Limit F].  Theorem 2's explicit
       description is read back at [eq_refl]: the limit's apex IS
       [pe_apex] and its leg at x IS [pe_obj_proj x ∘ pe_incl].

   (E) Corollary 2: [Complete_from_products_equalizers] (pinned), and its
       dual [Cocomplete_from_coproducts_coequalizers] (pinned by Riehl's
       §3.5 checkbox) as the primal theorem at C^op through
       [HasEqualizers_op_of_HasCoequalizers]
       (Structure/Pullback/Reduction.v) and [Opposite_Functor], a [:=]
       with no tactic — [HasIndexedCoproducts C] IS [HasIndexedProducts
       (C^op)] (Structure/Limit/Coproduct.v, #254, which is why the
       issue's "add HasIndexedCoproducts" checkbox needs no work here) and
       [Colimit F] IS [Limit (F^op)].  The colimit-first ORIENTATION is
       therefore delivered as an instantiation, not as a second
       construction: nothing here builds a coequalizer of two coproducts
       covariantly.

   (F) §V.4 Exercise 2: [PreservesIndexedProducts G] and
       [PreservesEqualizers G] are NEW predicates (the image of a product
       with its projections is a product, the image of an equalizer an
       equalizer; measured absent tree-wide at the base commit), and
       [continuous_from_products_equalizers] (pinned) lands in
       Structure/Limit/Preservation.v's cone-level [ContinuousFunctor] —
       the §V.4 notion, since the apex-only class cannot carry the
       conclusion.  The route: the core in D at [G ◯ K] with the G-images
       ([pe_image_s]/[pe_image_t] by [fmap_comp]), transported along
       [pe_image_ConeIso] to [FCone G (pe_limit_cone …)] — an identity
       apex, the legs differing by ONE [fmap_comp] — and then along
       [FCone_iso] of [limitcone_iso] to an arbitrary limiting cone.

   (G) Riehl's Exercise 3.2.ii, generally: section [Refinement] indexes
       the arrow product by ANY generating family, [pe_gen_limiting] makes
       that equalizer limiting, and [pe_gen_restrict_iso] shows the
       restriction does not change the limit — a [ConeIso] to the full
       construction, by [limitcone_iso].  At the full index the refined
       construction IS the construction in apex and every leg (probe
       controls at [eq_refl]) but NOT as a record, the two cones citing
       different [Qed] component lemmas.  Section [Families]:
       [IsIdArrow], [fam_dom]/[fam_cod]/[fam_arr] (a family cut by a
       predicate on [ArrowIx]), [sub_Generates_of_dec] (a predicate
       containing every non-identity arrow generates, given a DECIDER
       [S (mk_arrow f) + IsIdArrow f]), [NonIdArrow] with
       [nonid_Generates] (the non-identity family generates as soon as
       being an identity is decidable), and [AtomicArrow] (non-identity,
       every factorization through two arrows has an identity factor).
       Section [Refined]: [pe_nonid_limiting] under a decider, and
       [pe_atomic_limiting] under the HYPOTHESIS [Generates (fam_arr
       AtomicArrow)] — which IS Riehl's factorization hypothesis, taken
       as a hypothesis and discharged for NO shape here.  Decidability of
       being an identity is not claimed for any shape in this file
       (Test/ProbeFromProducts416.v discharges it on the walking arrow).

   WHY THE CLASS AND NOT [iprod] — the issue's work item 4, DECLINED ON A
   MEASUREMENT.  It asks that the indexed products be routed through
   Instance/Discrete.v's discrete-diagram encoding "so the result composes
   with Structure/Limit/Product.v's existing API rather than introducing a
   rival one".  The API consumed IS that file's: the class
   [HasIndexedProducts] with [indexed_product]/[indexed_product_proj]/
   [indexed_product_ump], and the elementary [IsIndexedProduct] with
   [iprod_desc]; nothing rival is declared.  What is NOT consumed is that
   file's [iprod]/[iprod_proj]/[iprod_ump], because [iprod@{u u0 u1}]
   binds [C : Category@{u1 Set Set}] — the ambient hom AND proof
   universes pinned to the literal [Set], through [DiscreteCat_Functor]
   and [Limit] (the #331/#339 measurement) — so a theorem routed through
   it would hold only for Set-homed categories, and would have excluded
   the classes [Complete] is quantified over.  Pinned as the probe's N8:
   at a hom level declared strictly above [Set], the class, its product
   and [Complete_from_products_equalizers] are accepted while [iprod] is
   refused with [Cannot enforce Set = ch].

   UNIVERSES, off BOTH binder and block (all 91 constants).
   [limit_of_products_equalizer@{u u0 u1 u2 u3 u4 u5}] is over
   [C : Category@{u1 u2 u2}] and [J : Category@{u3 u4 u4}] — hom
   identified with proof in the BINDER, every constant here — with the
   block equations [u = u3] (the class's index universe IS J's object
   universe: the object product is indexed by [obj J]) and [u2 = u4]
   (shape hom = ambient hom, the limit vocabulary's: [Limit]/[IsLimitCone]
   are refused at a shape whose homs sit strictly below the ambient's
   while [Cone] is accepted, probe N7), C's OBJECT universe free.
   [Complete_from_products_equalizers@{u u0 u1}] over [C : Category@{u u0
   u0}] carries NO block equation — bounds only — and concludes
   [Complete@{u0 u0 u0 u}], the diagram category's objects and homs at
   C's hom level: the same smallness discipline as [Sets_Complete].
   [Cocomplete_from_coproducts_coequalizers] carries the strict [u0 < u]
   of [HasIndexedCoproducts]'s own declaration and no equation.
   [continuous_from_products_equalizers] binds C and D at ONE hom level
   ([Category@{u5 u8 u8}], [Category@{u4 u8 u8}]) with bounds only, as do
   [PreservesIndexedProducts] and [PreservesEqualizers]. [pe_cone] and
   [pe_limiting] bind [J : Category@{u u0 u0}], [C : Category@{u1 u0 u0}]
   with bounds only and the index [I : Type@{u3}] FREE; [Gen]'s block is
   LITERALLY EMPTY; [Generates] and [ArrowIx] carry bounds only;
   [pe_gen_restrict_iso] adds [u = u5] (the family's index universe, the
   class supplying ONE index universe per instance).  The hom = proof
   identification has SIX donors each refused alone at [ch < cp] with
   the hom-set, the identity and an endofunctor accepted (probe N6):
   [HasIndexedProducts], [HasEqualizers], [IsIndexedProduct],
   [IsEqualizer], [Limit], [Complete]; none is introduced here and none
   is claimed unavoidable.  ZERO word-bounded [Set] in any binder or
   block; the only two [Set] tokens in the whole [About] dump are the
   motive sorts of the two auto-generated [_rec] eliminators.

   COUNTS.  91/91 constants closed under the global context with ZERO
   [Axioms:] lines — 86 [Print Module] entries (70 [Definition], 14
   [Parameter], 2 [Inductive]) plus the five constructors it lists only
   after a [:=]; all 91 in the [make print-assumptions] gate FULLY
   QUALIFIED.  Closure 38 modules excluding self: dropping
   Structure/Pullback/Reduction costs 9, Structure/Limit/Coproduct and
   Structure/Complete 1 each, every other [Require] 0.  Three [Defined]
   tokens against 14 [Qed], NONE load-bearing — each flipped alone to
   [Qed] leaves this file and the probe compiling — kept [Defined] by the
   data convention.  Five [:= eq_refl] readbacks.  Zero declaration
   collisions over the 91 names plus the probe's, AFTER seven renames
   before landing: [arrow_dom]/[arrow_cod] are Instance/Square.v's,
   [arrow_of] is Theory/Shapes.v's, [sub_dom] is Theory/Subobject.v's
   field, and [two_fam] is Structure/Pullback/Wide.v's.  [make todo]
   grows by 19, ALL in the probe (16 refutation commands + 3 prose
   lines), this file contributing ZERO — so the issue's "adds no new
   hits" box is NOT met as written and is disclosed here.

   Test/ProbeFromProducts416.v carries 16 refutation commands = 1
   instrument + 15 commands pinning EIGHT negatives of THREE kinds told
   apart by the error TEXT — 3 CONVERSION (N1–N3), 2 TYPING (N4–N5; N5's
   message carries a trailing [cannot unify] on the two hom FAMILIES
   [hom[C]] and [hom[C^op]], not on two inhabitants of one type), 3
   UNIVERSE (N6–N8, ten commands) — each stripped ONE AT A TIME in a copy
   of the whole file and compiled alone with its error read; guard
   coverage measured mechanically (40 identifiers inside a refutation
   command, 35 also outside, the five exceptions exhaustively the keyword,
   the three refuting [Example] names and the instrument's absent name);
   rename-simulated 7/7 over the target constants the negatives name,
   every break on a [Check] line.
   The probe also carries the [Sets] instantiation (a SECOND inhabitant
   of [@Complete Sets], not compared with [Sets_Complete]) and the
   walking-arrow generating family: [_2] has three arrows and the
   one-index family at its non-identity arrow generates.

   PROSE REPOINTED in the same commit: Structure/Complete.v:49-62 (line
   neutral, its :58-60 and :64-72 being cited elsewhere), whose closing
   sentence had called [iprod] "the products half of the reduction";
   Structure/Equalizer.v:89, whose "Both arguments run in this library"
   was FALSE for the reduction until this file; Structure/Limit.v:69-72
   (the E.1 LIBRARY-DEFECT: "uniqueness up to unique isomorphism" is
   Structure/Limit/Unique.v's, landed since the issue was filed, and the
   construction is this file's) and :94-96, both line neutral.
   Structure/Topos.v:23-24, which the issue also names, cites the
   PULLBACK reduction (Structure/Pullback/Reduction.v) and not this one,
   so it is untouched; the issue's line drift is recorded here.

   NOT DELIVERED.  No covariant coequalizer-of-coproducts construction
   (the dual is the primal at C^op); no finite-shape variant (Awodey's
   Proposition 5.23 is about FINITE diagrams, whose finiteness predicate
   is #417's, and Corollary 5.24's cardinality bookkeeping is replaced
   by universe polymorphism); no [Set] instantiation IN THIS FILE and no
   computing witness (the [Sets] limit here is an equalizer inside
   Instance/Sets/Complete.v's compatible-family setoid, whose elements
   are not written down); no comparison of the [Sets] instantiation with
   [Sets_Complete]; no shape shown to satisfy the atomic factorization
   hypothesis and no decision procedure for identities; no converse
   (nothing says a complete category has products, that being
   Adjunction/GAFT.v's [Complete_HasEqualizers] for the equalizer half
   and absent for the product half); no naturality of any identification
   in F; nothing registered as an [Instance] — a chosen limit must not
   become globally resolvable. *)

(** ** Joint monicity of the projections of an indexed product *)

(* Two maps into an indexed product that agree under every projection are
   equal — the uniqueness clause of [iprod_desc] read as an extensionality
   principle.  Structure/Bicartesian/Matrix.v:356's [iprod_ext] states the
   same fact but drags a coproduct hypothesis in from its section, and
   Instance/Fun/Terminal.v's [iprod_jointly_monic] sits far outside this
   closure; the four-line restatement is disclosed. *)

Lemma pe_iprod_ext {C : Category} {A : Type} {f : A → C} {p : C}
  {proj : ∀ a : A, p ~> f a} (H : IsIndexedProduct f p proj)
  {c : C} (u v : c ~> p) :
  (∀ a : A, proj a ∘ u ≈ proj a ∘ v) → u ≈ v.
Proof.
  intro Huv.
  pose (d := iprod_desc H (fun a => proj a ∘ v)).
  transitivity (unique_obj d).
  - symmetry; exact (uniqueness d u Huv).
  - exact (uniqueness d v (fun a => reflexivity _)).
Qed.

(** ** The arrow index of a shape *)

Section ArrowIndex.

Context {J : Category}.

(* The arrows of [J] as one type: a pair of objects and an arrow between
   them.  This is the index of Mac Lane's second product, ∏_{f ∈ mor J}. *)

Definition ArrowIx : Type := { p : obj[J] * obj[J] & fst p ~{J}~> snd p }.

Definition aix_dom (a : ArrowIx) : J := fst (`1 a).
Definition aix_cod (a : ArrowIx) : J := snd (`1 a).
Definition aix_arr (a : ArrowIx) : aix_dom a ~{J}~> aix_cod a := `2 a.

Definition mk_arrow {x y : J} (f : x ~{J}~> y) : ArrowIx := ((x, y); f).

Example mk_arrow_dom {x y : J} (f : x ~> y) : aix_dom (mk_arrow f) = x :=
  eq_refl.
Example mk_arrow_cod {x y : J} (f : x ~> y) : aix_cod (mk_arrow f) = y :=
  eq_refl.
Example mk_arrow_of {x y : J} (f : x ~> y) : aix_arr (mk_arrow f) = f :=
  eq_refl.

End ArrowIndex.

(** ** Arrows generated by an indexed family *)

Section Generated.

Context {J : Category}.
Context {I : Type} (idx_dom idx_cod : I → J)
  (idx_arr : ∀ i : I, idx_dom i ~{J}~> idx_cod i).

(* The arrows of [J] that the family [idx_arr] generates under identities,
   composition and [≈]: exactly the hypothesis under which the family may
   index the second product in place of ALL arrows (Riehl, Exercise
   3.2.ii). *)

Inductive Gen : ∀ (x y : J), (x ~{J}~> y) → Type :=
  | gen_idx (i : I) : Gen (idx_dom i) (idx_cod i) (idx_arr i)
  | gen_id (x : J) : Gen x x id
  | gen_comp {x y z : J} (g : y ~{J}~> z) (f : x ~{J}~> y) :
      Gen y z g → Gen x y f → Gen x z (g ∘ f)
  | gen_equiv {x y : J} (f f' : x ~{J}~> y) :
      f ≈ f' → Gen x y f → Gen x y f'.

(* The family generates the whole of [J]. *)

Definition Generates : Type := ∀ (x y : J) (f : x ~{J}~> y), Gen x y f.

End Generated.

Arguments Gen {J I idx_dom idx_cod} idx_arr {x y} f.
Arguments gen_idx {J I idx_dom idx_cod idx_arr} i.
Arguments gen_id {J I idx_dom idx_cod idx_arr} x.
Arguments gen_comp {J I idx_dom idx_cod idx_arr x y z} g f _ _.
Arguments gen_equiv {J I idx_dom idx_cod idx_arr x y} f f' _ _.
Arguments Generates {J I idx_dom idx_cod} idx_arr.

(* The full arrow index generates: every arrow is itself indexed. *)

Definition ArrowIx_Generates {J : Category} :
  Generates (@aix_arr J) :=
  fun x y f => gen_idx (mk_arrow f).

(** ** The core: an equalizer of two maps between two products is limiting *)

(* Everything here is elementary — stated against [IsIndexedProduct] and
   [IsEqualizer], with no class instance, no chosen product and no chosen
   equalizer — so that it applies verbatim to the IMAGE of the construction
   under a functor (§V.4 Exercise 2 below), and to any sub-family of arrows
   that generates (Riehl's refinement). *)

Section Core.

#[local] Set Default Proof Using "All".

Context {J C : Category} (F : J ⟶ C).

(* The product over the objects of J. *)
Context {P : C} (projP : ∀ x : J, P ~> F x)
  (HP : IsIndexedProduct (fun x : J => F x) P projP).

(* The product over a generating family of arrows of J, at their
   codomains. *)
Context {I : Type} {idx_dom idx_cod : I → J}
  {idx_arr : ∀ i : I, idx_dom i ~{J}~> idx_cod i}
  (Hgen : Generates idx_arr).
Context {Q : C} (projQ : ∀ i : I, Q ~> F (idx_cod i))
  (HQ : IsIndexedProduct (fun i : I => F (idx_cod i)) Q projQ).

(* The two canonical maps, given by their components: projection at the
   codomain, and the diagram's action after projection at the domain. *)
Context (s t : P ~> Q)
  (Hs : ∀ i : I, projQ i ∘ s ≈ projP (idx_cod i))
  (Ht : ∀ i : I, projQ i ∘ t ≈ fmap[F] (idx_arr i) ∘ projP (idx_dom i)).

(* Their equalizer. *)
Context {E : C} (e : E ~> P) (HE : IsEqualizer s t E e).

(* The candidate cone: apex the equalizer, legs the object projections
   composed with the equalizing map. *)

Definition pe_leg (x : J) : E ~> F x := projP x ∘ e.

Lemma pe_leg_coherence_gen {x y : J} (f : x ~{J}~> y)
  (G : Gen idx_arr f) : fmap[F] f ∘ pe_leg x ≈ pe_leg y.
Proof.
  induction G as [i | x | x y z g f Hg IHg Hf IHf | x y f f' Hff' Hf IH].
  - unfold pe_leg.
    rewrite comp_assoc, <- (Ht i), <- comp_assoc, <- (fork_eq HE),
      comp_assoc, (Hs i).
    reflexivity.
  - rewrite fmap_id, id_left; reflexivity.
  - rewrite fmap_comp, <- comp_assoc, IHf, IHg; reflexivity.
  - rewrite <- Hff'; exact IH.
Qed.

Lemma pe_leg_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[F] f ∘ pe_leg x ≈ pe_leg y.
Proof. exact (pe_leg_coherence_gen f (Hgen x y f)). Qed.

Definition pe_cone : Cone F :=
  @Build_Cone J C F E
    (@Build_ACone J C E F pe_leg (fun x y f => pe_leg_coherence f)).

(* A competing cone tuples into the object product ... *)

Definition pe_tuple (M : Cone F) : vertex_obj[M] ~> P :=
  unique_obj (iprod_desc HP (fun x => cone_leg M x)).

Lemma pe_tuple_proj (M : Cone F) (x : J) :
  projP x ∘ pe_tuple M ≈ cone_leg M x.
Proof. exact (unique_property (iprod_desc HP (fun x => cone_leg M x)) x). Qed.

(* ... and its tuple equalizes the two canonical maps, by cone coherence
   at each indexed arrow. *)

Lemma pe_tuple_equalizes (M : Cone F) : s ∘ pe_tuple M ≈ t ∘ pe_tuple M.
Proof.
  apply (pe_iprod_ext HQ); intro i.
  rewrite comp_assoc, (Hs i), pe_tuple_proj.
  rewrite comp_assoc, (Ht i), <- comp_assoc, pe_tuple_proj.
  symmetry; apply cone_leg_coh.
Qed.

(* The mediator is the descent of the tuple through the equalizer. *)

Definition pe_med (M : Cone F) : vertex_obj[M] ~> E :=
  unique_obj (eq_desc HE (pe_tuple M) (pe_tuple_equalizes M)).

Lemma pe_med_incl (M : Cone F) : e ∘ pe_med M ≈ pe_tuple M.
Proof.
  exact (unique_property (eq_desc HE (pe_tuple M) (pe_tuple_equalizes M))).
Qed.

Lemma pe_med_leg (M : Cone F) (x : J) : pe_leg x ∘ pe_med M ≈ cone_leg M x.
Proof.
  unfold pe_leg.
  rewrite <- comp_assoc, pe_med_incl.
  apply pe_tuple_proj.
Qed.

Lemma pe_med_unique (M : Cone F) (v : vertex_obj[M] ~> E)
  (Hv : ∀ x : J, pe_leg x ∘ v ≈ cone_leg M x) : pe_med M ≈ v.
Proof.
  apply (uniqueness (eq_desc HE (pe_tuple M) (pe_tuple_equalizes M))).
  symmetry.
  apply (uniqueness (iprod_desc HP (fun x => cone_leg M x))).
  intro x.
  rewrite comp_assoc.
  exact (Hv x).
Qed.

(* Mac Lane §V.2 Theorem 1: the cone is limiting. *)

Theorem pe_limiting : IsLimitCone pe_cone.
Proof.
  intro M.
  unshelve refine {| unique_obj := pe_med M |}.
  - exact (pe_med_leg M).
  - intros v Hv; exact (pe_med_unique M v Hv).
Defined.

End Core.

(** ** The construction from chosen products and equalizers (Theorem 2) *)

Section FromClasses.

Context {C : Category} (HP : HasIndexedProducts C).
Context {J : Category} (F : J ⟶ C).

Definition pe_obj_product : C := indexed_product (fun x : J => F x).

Definition pe_obj_proj (x : J) : pe_obj_product ~> F x :=
  indexed_product_proj (fun x : J => F x) x.

Definition pe_obj_product_ump :
  IsIndexedProduct (fun x : J => F x) pe_obj_product pe_obj_proj :=
  indexed_product_ump (fun x : J => F x).

Definition pe_arrow_product : C :=
  indexed_product (fun a : @ArrowIx J => F (aix_cod a)).

Definition pe_arrow_proj (a : ArrowIx) : pe_arrow_product ~> F (aix_cod a) :=
  indexed_product_proj (fun a : @ArrowIx J => F (aix_cod a)) a.

Definition pe_arrow_product_ump :
  IsIndexedProduct (fun a : @ArrowIx J => F (aix_cod a))
    pe_arrow_product pe_arrow_proj :=
  indexed_product_ump (fun a : @ArrowIx J => F (aix_cod a)).

(* Mac Lane's two maps, Riehl's Remark 3.2.13: defined by their
   components against the projections of the arrow product. *)

Definition pe_s : pe_obj_product ~> pe_arrow_product :=
  unique_obj (iprod_desc pe_arrow_product_ump
    (fun a : ArrowIx => pe_obj_proj (aix_cod a))).

Definition pe_t : pe_obj_product ~> pe_arrow_product :=
  unique_obj (iprod_desc pe_arrow_product_ump
    (fun a : ArrowIx => fmap[F] (aix_arr a) ∘ pe_obj_proj (aix_dom a))).

Lemma pe_s_proj (a : ArrowIx) :
  pe_arrow_proj a ∘ pe_s ≈ pe_obj_proj (aix_cod a).
Proof.
  exact (unique_property (iprod_desc pe_arrow_product_ump
    (fun a : ArrowIx => pe_obj_proj (aix_cod a))) a).
Qed.

Lemma pe_t_proj (a : ArrowIx) :
  pe_arrow_proj a ∘ pe_t ≈ fmap[F] (aix_arr a) ∘ pe_obj_proj (aix_dom a).
Proof.
  exact (unique_property (iprod_desc pe_arrow_product_ump
    (fun a : ArrowIx => fmap[F] (aix_arr a) ∘ pe_obj_proj (aix_dom a))) a).
Qed.

Context (HE : HasEqualizers C).

Definition pe_equalizer := @equalizer C HE _ _ pe_s pe_t.

Definition pe_apex : C := `1 pe_equalizer.
Definition pe_incl : pe_apex ~> pe_obj_product := `1 (`2 pe_equalizer).
Definition pe_incl_IsEqualizer : IsEqualizer pe_s pe_t pe_apex pe_incl :=
  `2 (`2 pe_equalizer).

Definition pe_limit_cone : Cone F :=
  pe_cone F pe_obj_proj pe_obj_product_ump ArrowIx_Generates
    pe_arrow_proj pe_arrow_product_ump pe_s pe_t pe_s_proj pe_t_proj
    pe_incl pe_incl_IsEqualizer.

Definition pe_limit_limiting : IsLimitCone pe_limit_cone :=
  pe_limiting F pe_obj_proj pe_obj_product_ump ArrowIx_Generates
    pe_arrow_proj pe_arrow_product_ump pe_s pe_t pe_s_proj pe_t_proj
    pe_incl pe_incl_IsEqualizer.

(* The pinned name. *)

Definition limit_of_products_equalizer : Limit F :=
  limitcone_limit pe_limit_cone pe_limit_limiting.

(* Theorem 2's explicit description, read back on the nose. *)

Example limit_of_products_equalizer_apex :
  vertex_obj[@limit_cone _ _ _ limit_of_products_equalizer] = pe_apex :=
  eq_refl.

Example limit_of_products_equalizer_leg (x : J) :
  cone_leg (@limit_cone _ _ _ limit_of_products_equalizer) x
    = pe_obj_proj x ∘ pe_incl :=
  eq_refl.

End FromClasses.

(** ** Corollary 2: completeness, and its dual *)

Definition Complete_from_products_equalizers {C : Category}
  (HP : HasIndexedProducts C) (HE : HasEqualizers C) : @Complete C :=
  fun J F => limit_of_products_equalizer HP F HE.

Definition Cocomplete_from_coproducts_coequalizers {C : Category}
  (HP : HasIndexedCoproducts C) (HE : HasCoequalizers C) : @Cocomplete C :=
  fun J F =>
    @Complete_from_products_equalizers (C^op) HP
      (HasEqualizers_op_of_HasCoequalizers HE) (J^op) (Opposite_Functor F).

(** ** §V.4 Exercise 2: a functor preserving products and equalizers is
       continuous *)

(* Cone-level preservation of indexed products and of equalizers: the
   image of a product with its projections is a product, the image of an
   equalizer is an equalizer.  Neither predicate existed in the tree. *)

Definition PreservesIndexedProducts {C D : Category} (G : C ⟶ D) : Type :=
  ∀ (A : Type) (f : A → C) (p : C) (proj : ∀ a : A, p ~> f a),
    IsIndexedProduct f p proj →
    IsIndexedProduct (fun a => G (f a)) (G p) (fun a => fmap[G] (proj a)).

Definition PreservesEqualizers {C D : Category} (G : C ⟶ D) : Type :=
  ∀ (x y : C) (f g : x ~> y) (q : C) (e : q ~> x),
    IsEqualizer f g q e →
    IsEqualizer (fmap[G] f) (fmap[G] g) (G q) (fmap[G] e).

Section Continuity.

Context {C D : Category} (HP : HasIndexedProducts C) (HE : HasEqualizers C).
Context (G : C ⟶ D) (GP : PreservesIndexedProducts G)
  (GE : PreservesEqualizers G).
Context {J : Category} (K : J ⟶ C).

(* The image of the construction is the construction in D, with the
   image maps satisfying the two component equations. *)

Lemma pe_image_s (a : ArrowIx) :
  fmap[G] (pe_arrow_proj HP K a) ∘ fmap[G] (pe_s HP K)
    ≈ fmap[G] (pe_obj_proj HP K (aix_cod a)).
Proof. rewrite <- fmap_comp, pe_s_proj; reflexivity. Qed.

Lemma pe_image_t (a : ArrowIx) :
  fmap[G] (pe_arrow_proj HP K a) ∘ fmap[G] (pe_t HP K)
    ≈ fmap[G ◯ K] (aix_arr a) ∘ fmap[G] (pe_obj_proj HP K (aix_dom a)).
Proof. rewrite <- fmap_comp, pe_t_proj, fmap_comp; reflexivity. Qed.

Definition pe_image_cone : Cone (G ◯ K) :=
  pe_cone (G ◯ K) (fun x => fmap[G] (pe_obj_proj HP K x))
    (GP _ _ _ _ (pe_obj_product_ump HP K)) ArrowIx_Generates
    (fun a => fmap[G] (pe_arrow_proj HP K a))
    (GP _ _ _ _ (pe_arrow_product_ump HP K))
    (fmap[G] (pe_s HP K)) (fmap[G] (pe_t HP K)) pe_image_s pe_image_t
    (fmap[G] (pe_incl HP K HE))
    (GE _ _ _ _ _ _ (pe_incl_IsEqualizer HP K HE)).

Definition pe_image_limiting : IsLimitCone pe_image_cone :=
  pe_limiting (G ◯ K) (fun x => fmap[G] (pe_obj_proj HP K x))
    (GP _ _ _ _ (pe_obj_product_ump HP K)) ArrowIx_Generates
    (fun a => fmap[G] (pe_arrow_proj HP K a))
    (GP _ _ _ _ (pe_arrow_product_ump HP K))
    (fmap[G] (pe_s HP K)) (fmap[G] (pe_t HP K)) pe_image_s pe_image_t
    (fmap[G] (pe_incl HP K HE))
    (GE _ _ _ _ _ _ (pe_incl_IsEqualizer HP K HE)).

(* The image cone and the image OF the constructed cone differ only by
   [fmap_comp] on the legs: same apex, identity comparison. *)

Definition pe_image_ConeIso :
  ConeIso pe_image_cone (FCone G (pe_limit_cone HP K HE)).
Proof.
  exists iso_id.
  intro x; simpl.
  rewrite id_right.
  change (fmap[G] (pe_obj_proj HP K x ∘ pe_incl HP K HE)
            ≈ fmap[G] (pe_obj_proj HP K x) ∘ fmap[G] (pe_incl HP K HE)).
  apply fmap_comp.
Defined.

Definition pe_image_limit_cone_limiting :
  IsLimitCone (FCone G (pe_limit_cone HP K HE)) :=
  limitcone_transport pe_image_ConeIso pe_image_limiting.

(* Any limiting cone is isomorphic to the constructed one; transport. *)

Definition pe_preserves : PreservesLimitCone K G :=
  fun N HN =>
    limitcone_transport
      (FCone_iso G (limitcone_iso (pe_limit_limiting HP K HE) HN))
      pe_image_limit_cone_limiting.

End Continuity.

Definition continuous_from_products_equalizers {C D : Category}
  (HP : HasIndexedProducts C) (HE : HasEqualizers C)
  (G : C ⟶ D) (GP : PreservesIndexedProducts G) (GE : PreservesEqualizers G) :
  ContinuousFunctor G :=
  fun J K => pe_preserves HP HE G GP GE K.

(** ** Riehl's refinement: any generating family of arrows will do *)

Section Refinement.

Context {C : Category} (HP : HasIndexedProducts C) (HE : HasEqualizers C).
Context {J : Category} (F : J ⟶ C).
Context {I : Type} {idx_dom idx_cod : I → J}
  {idx_arr : ∀ i : I, idx_dom i ~{J}~> idx_cod i}
  (Hgen : Generates idx_arr).

Definition pe_gen_product : C := indexed_product (fun i : I => F (idx_cod i)).

Definition pe_gen_proj (i : I) : pe_gen_product ~> F (idx_cod i) :=
  indexed_product_proj (fun i : I => F (idx_cod i)) i.

Definition pe_gen_product_ump :
  IsIndexedProduct (fun i : I => F (idx_cod i)) pe_gen_product pe_gen_proj :=
  indexed_product_ump (fun i : I => F (idx_cod i)).

Definition pe_gen_s : pe_obj_product HP F ~> pe_gen_product :=
  unique_obj (iprod_desc pe_gen_product_ump
    (fun i : I => pe_obj_proj HP F (idx_cod i))).

Definition pe_gen_t : pe_obj_product HP F ~> pe_gen_product :=
  unique_obj (iprod_desc pe_gen_product_ump
    (fun i : I => fmap[F] (idx_arr i) ∘ pe_obj_proj HP F (idx_dom i))).

Lemma pe_gen_s_proj (i : I) :
  pe_gen_proj i ∘ pe_gen_s ≈ pe_obj_proj HP F (idx_cod i).
Proof.
  exact (unique_property (iprod_desc pe_gen_product_ump
    (fun i : I => pe_obj_proj HP F (idx_cod i))) i).
Qed.

Lemma pe_gen_t_proj (i : I) :
  pe_gen_proj i ∘ pe_gen_t
    ≈ fmap[F] (idx_arr i) ∘ pe_obj_proj HP F (idx_dom i).
Proof.
  exact (unique_property (iprod_desc pe_gen_product_ump
    (fun i : I => fmap[F] (idx_arr i) ∘ pe_obj_proj HP F (idx_dom i))) i).
Qed.

Definition pe_gen_equalizer := @equalizer C HE _ _ pe_gen_s pe_gen_t.

Definition pe_gen_apex : C := `1 pe_gen_equalizer.
Definition pe_gen_incl : pe_gen_apex ~> pe_obj_product HP F :=
  `1 (`2 pe_gen_equalizer).

Definition pe_gen_cone : Cone F :=
  pe_cone F (pe_obj_proj HP F) (pe_obj_product_ump HP F) Hgen
    pe_gen_proj pe_gen_product_ump pe_gen_s pe_gen_t
    pe_gen_s_proj pe_gen_t_proj pe_gen_incl (`2 (`2 pe_gen_equalizer)).

(* The equalizer over the generating family is limiting too ... *)

Definition pe_gen_limiting : IsLimitCone pe_gen_cone :=
  pe_limiting F (pe_obj_proj HP F) (pe_obj_product_ump HP F) Hgen
    pe_gen_proj pe_gen_product_ump pe_gen_s pe_gen_t
    pe_gen_s_proj pe_gen_t_proj pe_gen_incl (`2 (`2 pe_gen_equalizer)).

(* ... hence canonically isomorphic, as a cone, to the full construction:
   restricting the index does not change the limit. *)

Definition pe_gen_restrict_iso : ConeIso pe_gen_cone (pe_limit_cone HP F HE) :=
  limitcone_iso pe_gen_limiting (pe_limit_limiting HP F HE).

End Refinement.

(** ** The non-identity and the atomic families *)

Section Families.

Context {J : Category}.

(* An arrow that is an identity up to [≈]. *)

Inductive IsIdArrow : ∀ (x y : J), (x ~{J}~> y) → Type :=
  | is_id_arrow (x : J) (f : x ~{J}~> x) : f ≈ id → IsIdArrow x x f.

(* A family of arrows given by a predicate on the arrow index. *)

Definition fam_dom (S : @ArrowIx J → Type) (a : { a : ArrowIx & S a }) : J :=
  aix_dom (`1 a).
Definition fam_cod (S : @ArrowIx J → Type) (a : { a : ArrowIx & S a }) : J :=
  aix_cod (`1 a).
Definition fam_arr (S : @ArrowIx J → Type) (a : { a : ArrowIx & S a }) :
  fam_dom S a ~{J}~> fam_cod S a := aix_arr (`1 a).

(* A predicate that contains every arrow that is not an identity generates:
   the decider is the hypothesis, and it is exactly what "non-identity"
   costs constructively. *)

Definition sub_Generates_of_dec (S : @ArrowIx J → Type)
  (dec : ∀ (x y : J) (f : x ~{J}~> y), S (mk_arrow f) + IsIdArrow x y f) :
  Generates (fam_arr S).
Proof.
  intros x y f.
  destruct (dec x y f) as [HS | Hid].
  - exact (gen_idx (idx_arr := fam_arr S) (mk_arrow f; HS)).
  - destruct Hid as [x f Hf].
    exact (gen_equiv id f (symmetry Hf) (gen_id x)).
Defined.

(* The non-identity arrows (Riehl, Exercise 3.2.ii, first clause).  The
   family generates as soon as being an identity is DECIDABLE, and the
   decider is the whole cost: nothing here decides it for any shape. *)

Definition NonIdArrow (a : @ArrowIx J) : Type :=
  IsIdArrow (aix_dom a) (aix_cod a) (aix_arr a) → False.

Definition nonid_Generates
  (dec : ∀ (x y : J) (f : x ~{J}~> y),
     IsIdArrow x y f + (IsIdArrow x y f → False)) :
  Generates (fam_arr NonIdArrow) :=
  sub_Generates_of_dec NonIdArrow
    (fun x y f => match dec x y f with
                  | inl Hid => inr Hid
                  | inr Hn => inl Hn
                  end).

(* The atomic arrows (second clause): non-identities with no factorization
   through two non-identities.  Whether they generate is Riehl's
   factorization hypothesis, and it is taken as a HYPOTHESIS here — a
   [Generates (fam_arr AtomicArrow)] — with no shape shown to satisfy it. *)

Definition AtomicArrow (a : @ArrowIx J) : Type :=
  NonIdArrow a *
  (∀ (z : J) (g : z ~{J}~> aix_cod a) (h : aix_dom a ~{J}~> z),
     aix_arr a ≈ g ∘ h →
     IsIdArrow z (aix_cod a) g + IsIdArrow (aix_dom a) z h).

End Families.

(** ** The refined presentations, read off the general one *)

Section Refined.

Context {C : Category} (HP : HasIndexedProducts C) (HE : HasEqualizers C).
Context {J : Category} (F : J ⟶ C).

(* Over the non-identity arrows, given a decider. *)

Definition pe_nonid_limiting
  (dec : ∀ (x y : J) (f : x ~{J}~> y),
     IsIdArrow x y f + (IsIdArrow x y f → False)) :
  IsLimitCone (pe_gen_cone HP HE F (nonid_Generates dec)) :=
  pe_gen_limiting HP HE F (nonid_Generates dec).

(* Over the atomic arrows, given that they generate. *)

Definition pe_atomic_limiting (Hatom : Generates (fam_arr AtomicArrow)) :
  IsLimitCone (pe_gen_cone HP HE F Hatom) :=
  pe_gen_limiting HP HE F Hatom.

End Refined.
