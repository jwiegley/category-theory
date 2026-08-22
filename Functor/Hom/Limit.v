Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Functor.Hom.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Limit.Cartesian.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * Continuity of the covariant hom-functor *)

(* nLab:      https://ncatlab.org/nlab/show/hom-functor
   nLab:      https://ncatlab.org/nlab/show/continuous+functor
   Wikipedia: https://en.wikipedia.org/wiki/Hom_functor
   Mac Lane:  Categories for the Working Mathematician, 2nd ed. (GTM 5),
              §III.4 "Products and coproducts", the remark at book p. 70
              [maclane:III.4:remark3]: the covariant hom-functor
              C(c, −) carries a product existing in C to a product in
              Set.  That remark states the continuity of representables
              for the special case of products; Mac Lane proves
              preservation of limits in general only later, in §V.4
              "Preservation of limits", and it is the §V.4 statement --
              every limit of every shape, not only products -- that this
              file leads with.

   WHAT IS DELIVERED, AND AT WHICH LEVEL.  The headline is
   [hom_ContinuousFunctor c : ContinuousFunctor [Hom c,─]], for an
   arbitrary category C and an arbitrary object c of it.  The word
   "continuous" is used in the sense Structure/Limit/Preservation.v
   fixes: its header states in terms that [ContinuousFunctor] --
   preservation of limits of all shapes IN THE CONE SENSE -- "is what
   the word means in Mac Lane §V.4", and that the apex-only
   [PreservesAllLimits] is a CONSEQUENCE ([Continuous_PreservesAllLimits])
   and not the definition.  Both readings are exposed here:
   [hom_PreservesLimitCone] and [hom_ContinuousFunctor] at cone level,
   [hom_PreservesLimit] and [hom_PreservesAllLimits] as the weaker
   apex-only corollaries, obtained through the donor's own bridges.

   The apex-only reading says that the setoid [C(c, L)] carries SOME
   limit structure over [[Hom c,─] ◯ K], with legs unconstrained; the
   cone-level reading says that the image cone -- apex [C(c, L)], legs
   post-composition with the legs of the limit cone -- is itself
   universal.  The two notions are separated in general by the
   countermodel of Structure/Limit/Preservation/Separation.v.  NO
   separation is proved here for hom-functors: nothing below shows that
   the apex-only statement is strictly weaker FOR THIS FUNCTOR.

   THE PROOF, AND WHY NO [Sets_Complete] APPEARS.  [PreservesLimitCone]
   quantifies over CONES, not over limits that must first be
   constructed, so no completeness of Sets is needed anywhere -- and
   this is structural, not a matter of the proof text: the transitive
   dependency closure of this file is 52 modules, itself included, and
   contains neither Instance/Sets/Complete.v nor
   Instance/Sets/Products.v (measured with coqdep over the _CoqProject
   build set).  Nothing below constructs a limit in Sets, and the
   theorem asserts none.

   The argument is one observation.  Let N be a limiting cone over
   K : J ⟶ C and let M be a competing cone in Sets over
   [Hom c,─] ◯ K, with apex a setoid S.  Each ELEMENT s of S yields the
   family [fun x => cone_leg M x s], which is a cone over K with apex c
   -- its coherence is literally M's own coherence read at s
   ([hom_fibre_coherence], [hom_fibre_cone]).  The universal property of
   N supplies a unique mediator [hom_med_fun s : c ~> vertex_obj[N]].
   The mediating map of Sets is [s ↦ hom_med_fun s]; its respectfulness
   and the uniqueness clause both come from that same [∃!], since two
   [≈]-equal elements of S give fibre cones with [≈]-equal legs.

   THE ISSUE'S THIRD BULLET IS DISCHARGED, AND AN EARLIER REVISION FAILED
   TO SAY SO.  #331 asks to "derive [PreservesImageLimit] for hom-functors
   where applicable".  Structure/Limit/Preservation.v records that
   [ContinuousFunctor] IS [PreservesImageLimit] definitionally -- the very
   hypothesis Construction/Comma/Limit.v introduced and Adjunction/GAFT.v
   and Adjunction/SAFT.v consume -- so [hom_ContinuousFunctor] already
   inhabits it for every hom-functor, with no further work.  That was
   neither claimed nor listed as undelivered before this paragraph.

   WHAT THE CONE LEVEL BUYS HERE, MEASURED.  The legs of the produced
   limiting cone ARE post-composition with the legs of N, at Leibniz
   equality: [hom_preserved_leg] is [eq_refl], with
   [hom_preserved_leg_value] spelling out the action on an element.  The
   mediator produced is the named one: [hom_preserved_mediator] records
   [unique_obj (hom_PreservesLimitCone K N HN M) = hom_med HN M] by
   [eq_refl], and [hom_med_commutes] / [hom_med_unique] are its
   commutation and uniqueness clauses.  The apex-only corollary names
   neither the legs nor the mediator.  SCOPE the first of these:
   [hom_preserved_leg] is an instance of a fact about cone-level
   preservation for an ARBITRARY functor (the same [eq_refl] holds with
   [HomFrom c] replaced by any [F : C ⟶ D]), so it measures what the cone
   level pins in general rather than anything specific to hom-functors.
   [hom_preserved_mediator] IS specific -- it names this file's own
   [hom_med].

   PRODUCTS -- MAC LANE'S OWN CASE -- ARE PROVED DIRECTLY, AND THE
   REASON IS A MEASUREMENT.  [hom_IsIndexedProduct] and
   [hom_IsCartesianProduct] state the §III.4 remark at the tree's
   elementary product records ([IsIndexedProduct] of
   Structure/Limit/Product.v, [IsCartesianProduct] of
   Structure/Cartesian.v), for an arbitrary index [Type] and an
   arbitrary apex-pinned product.  They are NOT derived from the
   headline, and that is deliberate.  Indexed products ARE presented as
   limits of discrete diagrams in tree ([limit_is_indexed_product]), so
   the derivation is available -- but it costs the general statement:

     [DiscreteCat_Functor@{u u0 u1 u2}] has type
       [∀ {A : Type@{u}} {C : Category@{u0 u2 u2}},
          (A → obj[C]) → DiscreteCat@{u Set Set} A ⟶ C],

   so the discrete shape's hom and proof universes are [Set] (likewise
   [family_cone], which returns [Cone@{u Set Set u1 u2 u2}]), while

     [IsLimitCone@{u u0 u1 u2 u3}] has type
       [∀ {J : Category@{u1 u2 u2}} {C : Category@{u3 u2 u2}} …]

   -- the shape's hom-and-proof universe is IDENTIFIED with the ambient
   category's (and [PreservesLimitCone] identifies all three of J, C, D
   at one such universe).  Routing the product corollaries through the
   discrete presentation therefore pins C's hom and proof universes to
   [Set].  The direct statements carry no [Set] at all (see UNIVERSES).
   No bridge is invented and no such derivation is attempted.  READ THE
   CAUSE PRECISELY: it is [DiscreteCat_Functor]'s UNANNOTATED declaration
   (Instance/Discrete.v:52, [{A : Type} {C : Category}]) whose minimized
   type instantiates [DiscreteCat@{u Set Set}] -- NOT [DiscreteCat]
   itself, which is declared [DiscreteCat@{o h p} (A : Type@{o}) :
   Category@{o h p}] (Instance/Discrete.v:37) with hom and proof FREE and
   which elaborates as [DiscreteCat@{Set uh uh} bool] under
   [Constraint Set < uh].  An earlier revision of this paragraph left the
   question "NOT investigated"; an audit then investigated it, and a
   re-annotated discrete-diagram functor -- same object and arrow actions,
   differing only in the [DiscreteCat] instance it names -- LIFTS the
   blocking step, making both [IsLimitCone] over its cones and
   [hom_PreservesLimitCone] at it elaborate above [Set].  So the pin is a
   donor ANNOTATION defect of the [Build_Quiver_Standard_Eq] family
   (Construction/Free/Quiver/Examples.v, issue #300's erratum), not a
   structural obstruction.  What is still NOT established is that the
   WHOLE derivation closes: the tree has [limit_is_indexed_product] but
   not its converse, and [family_cone] is itself unannotated.  So the
   corollaries stay proved directly, and the reason is now a KNOWN
   liftable defect rather than an unexamined one.  What IS
   exhibited, at that price, is the cone-level witness
   [coq_hom_limit_cone], whose ambient category is measurably
   [Coq@{u1 Set Set}] for exactly this reason -- [Two_Discrete] has
   [TwoDHom : TwoDObj → TwoDObj → Set].

   THE CONTRAVARIANT TWIN.  [HomTo c := [Hom ─,c]] is
   [@HomFrom (C^op) c] by [eq_refl] ([hom_to_is_op_hom_from]), so the
   whole contravariant section is instantiation: every constant in it is
   supplied by [:=] with no tactic and no obligation.  What duality
   delivers is [cohom_ContinuousFunctor c : ContinuousFunctor [Hom ─,c]]
   -- continuity for a functor out of C^op, i.e. limits of C^op are
   carried to limits of Sets -- and, read covariantly in C,
   [cohom_colimit_to_limit], which turns a COLIMIT cocone of C into a
   limit cone of Sets.  That reading needs no repackaging: [Cocone K] is
   [Cone (K^op)] and [IsColimitCocone] is [IsLimitCone] at the opposite
   diagram, both definitionally (Structure/Cone.v,
   Structure/Limit/Preservation.v).  The variance of the product
   corollaries follows: [cohom_IsIndexedProduct] takes an
   [IsIndexedCoproduct] in C and returns an [IsIndexedProduct] in Sets,
   its projections being PREcomposition with the coproduct injections.

   UNIVERSES, measured in the constraint blocks rather than read off the
   binders.  [hom_ContinuousFunctor] and [hom_PreservesLimitCone] are
   over [C : Category@{u u0 u0}]: C's hom and proof universes are
   IDENTIFIED, and identified further with the carrier universe of the
   target Sets.  Both identifications are the donors' -- [Sets]' objects
   are [SetoidObject@{o o}], which identifies a setoid's carrier and
   relation universes, and [ContinuousFunctor] itself is declared over
   [{C : Category@{u7 u5 u5}} {D : Category@{u6 u5 u5}}].  C's OBJECT
   universe is not identified with them.  In [hom_PreservesLimitCone]
   the shape J appears as [Category@{u3 u0 u0}]: its object universe is
   free, its hom and proof universes are the ambient category's, which
   is [PreservesLimitCone]'s own doing as quoted above.  The two product
   corollaries are freer: [hom_IsIndexedProduct] carries an index
   [A : Type@{u1}] -- bounded above, but identified with neither of C's
   universes -- and no occurrence of [Set] in its constraint block, and
   neither does [hom_IsCartesianProduct].  None of these restrictions is
   claimed unavoidable.

   NON-VACUITY.  Two witnesses, both over Instance/Coq.v and both using
   limits already in tree; no new category and no new limit is built.
   (1) [coq_hom_product] instantiates the binary product corollary at
   [Coq_Cartesian], and the three [eq_refl] Examples COMPUTE: the two
   projections of [Coq(unit, bool × nat)] read off the components of a
   map out of [unit], and pairing them back returns the pair.  (2)
   [coq_hom_limit_cone] and its instance [coq_hom_bool_nat_limit] take
   the in-tree [Limit] supplied by [Cartesian_Limit] at [Coq_Cartesian]
   and apply the CONE-LEVEL headline to it, so the headline is exercised
   as such and not only through its product corollary.  Witness (2) does
   not compute -- [Cartesian_Limit] is [Qed] -- and it carries the
   [Set] pin analysed above; witness (1) computes and does not.

   ENGINEERING NOTES.  (a) Lib.v sets [Default Proof Using "Type"], so
   the two tactic proofs whose section witness [H] appears only in the
   proof and not in the statement carry an explicit [Proof using H]
   (the Structure/Equalizer/Wide.v idiom).  (b) Structure/Cartesian.v
   carries both the bundled [Cartesian] class and the apex-pinned
   [IsCartesianProduct], but no passage from the first to the second:
   a shape search for [IsCartesianProduct] finds the class at
   Structure/Cartesian.v:145 with consumers at :519/:526/:533, and the
   only terms of that type CONSTRUCTED anywhere are [product_of_pullback]
   (Structure/Pullback/Reduction.v:599) and [pb_prod_IsCartesianProduct]
   (:634, itself an application of the former), both from a pullback over
   the terminal object.  An earlier revision counted "four other files"
   and then "the other two"; the count was stale and the two figures were
   inconsistent, and Structure/Pullback.v mentions the name only inside a
   comment.  The ABSENCE claim -- no [Cartesian → IsCartesianProduct]
   passage -- is unchanged and holds.
   [cartesian_IsCartesianProduct] below supplies the missing
   repackaging; it is used only to state witness (1), and is a plain
   [Program Definition], not an [Instance].
   (c) Written [FCone (HomFrom unit) (coq_two_limit …)] the elaborator
   rejects the functor, reporting [HomFrom unit : Coq ⟶ Sets] as expected
   to have type [Coq ⟶ Coq].  THE CAUSE IS [HomFrom]'s IMPLICIT
   [{C : Category}], undeterminable from a bare [unit : Type] -- NOT
   [FCone]'s category arguments, which may be left implicit: both
   [FCone (HomFrom (unit : obj[Coq])) (…)] and
   [fun u : Coq => FCone (HomFrom u) (…)] elaborate, and
   [coq_hom_limit_cone] below writes them implicitly.  An earlier revision
   of this note said the three category arguments "must be spelled
   explicitly" and were "not repaired by an ascription"; both were wrong,
   and the second is refuted by the first form above.

   WHAT IS NOT DELIVERED (scoped to this file).  No converse and no
   characterisation: nothing says that hom-functors are the only
   continuous functors, and no separation between the cone-level and
   apex-only readings is proved for them.  Cocontinuity of [Hom c,─] is
   not addressed in either direction.  Nothing is proved about
   REFLECTION or CREATION of limits ([ReflectsLimitCone], [CreatesLimit]
   are untouched).  The canonical comparison map is not instantiated:
   [comparison_iso_of_PreservesLimitCone] would give its invertibility
   from the headline, and that composition is not performed.  The result
   is per-object: [Curried_Hom C : C^op ⟶ [C, Sets]] is NOT shown
   continuous, no limit is computed in a functor category, and the
   family [c ↦ the preserved cone] is not exhibited as natural in c --
   there is no statement in [[C^op, Sets]] anywhere below.  No relation
   is drawn to RAPL (Adjunction/Continuity.v) or to the Yoneda
   development; the two are neither derived from nor used by this file.
   The nullary case (terminal objects) is not stated separately.  On the
   dual side the coproduct corollaries are stated but not instantiated
   at any concrete category, and no indexed-product witness is given
   anywhere -- witness (1) is binary. *)

(** ** The covariant hom-functor preserves limit cones *)

Section HomContinuous.

Context {C : Category}.
Context (c : C).

Definition HomFrom : C ⟶ Sets := [Hom c ,─].

(* An element of the apex of a cone over [Hom c,─] ◯ K is itself a cone
   over K with apex c: its legs are the legs of M read at that element,
   and its coherence is M's coherence read there. *)

Section Fibre.

Context {J : Category}.
Context {K : J ⟶ C}.
Context (M : Cone (HomFrom ◯ K)).

Lemma hom_fibre_coherence (s : vertex_obj[M]) {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ cone_leg M x s ≈ cone_leg M y s.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ M) x y f s).
Qed.

Definition hom_fibre_cone (s : vertex_obj[M]) : Cone K :=
  @Build_Cone J C K c
    (@Build_ACone J C c K (fun x => cone_leg M x s)
       (fun x y f => hom_fibre_coherence s f)).

End Fibre.

(* The mediating map of Sets: it sends an element to the mediator its
   fibre cone determines.  Respectfulness is not an extra hypothesis --
   it follows from uniqueness of the mediator, since [≈]-equal elements
   give fibre cones with [≈]-equal legs. *)

Section Mediator.

Context {J : Category}.
Context {K : J ⟶ C}.
Context {N : Cone K}.
Context (HN : IsLimitCone N).
Context (M : Cone (HomFrom ◯ K)).

Definition hom_med_fun (s : vertex_obj[M]) : c ~{C}~> vertex_obj[N] :=
  unique_obj (HN (hom_fibre_cone M s)).

Lemma hom_med_commutes (s : vertex_obj[M]) (x : J) :
  cone_leg N x ∘ hom_med_fun s ≈ cone_leg M x s.
Proof. exact (unique_property (HN (hom_fibre_cone M s)) x). Qed.

Lemma hom_med_unique (s : vertex_obj[M]) (v : c ~{C}~> vertex_obj[N]) :
  (∀ x : J, cone_leg N x ∘ v ≈ cone_leg M x s) → hom_med_fun s ≈ v.
Proof. intro Hv. exact (uniqueness (HN (hom_fibre_cone M s)) v Hv). Qed.

#[local] Instance hom_med_respects : Proper (equiv ==> equiv) hom_med_fun.
Proof.
  intros s t Hst.
  apply hom_med_unique.
  intro x.
  rewrite hom_med_commutes.
  now rewrite Hst.
Qed.

Definition hom_med : vertex_obj[M] ~{Sets}~> fobj[HomFrom] (vertex_obj[N]) :=
  {| morphism := hom_med_fun ; proper_morphism := hom_med_respects |}.

End Mediator.

(* The headline, per diagram and then over all shapes at once. *)

Definition hom_PreservesLimitCone {J : Category} (K : J ⟶ C) :
  PreservesLimitCone K HomFrom.
Proof.
  intros N HN M.
  unshelve refine {| unique_obj := hom_med HN M |}.
  - simpl; intros x s.
    exact (hom_med_commutes HN M s x).
  - simpl; intros v Hv s.
    apply hom_med_unique.
    intro x.
    exact (Hv x s).
Defined.

Definition hom_ContinuousFunctor : ContinuousFunctor HomFrom :=
  fun J K => hom_PreservesLimitCone K.

(* The apex-only readings, through the donor's own bridges.  These are
   WEAKER: they name no legs and no mediator.  Whether they are strictly
   weaker for this particular functor is not settled here. *)

Definition hom_PreservesLimit {J : Category} (K : J ⟶ C) :
  PreservesLimit K HomFrom :=
  PreservesLimitCone_PreservesLimit (hom_PreservesLimitCone K).

Definition hom_PreservesAllLimits : PreservesAllLimits HomFrom :=
  Continuous_PreservesAllLimits hom_ContinuousFunctor.

(* What the cone level pins down, and the apex-only reading does not. *)

Example hom_preserved_leg {J : Category} {K : J ⟶ C} (N : Cone K) (x : J) :
  cone_leg (FCone HomFrom N) x = fmap[HomFrom] (cone_leg N x) := eq_refl.

Lemma hom_preserved_leg_value {J : Category} {K : J ⟶ C} (N : Cone K)
  (x : J) (h : c ~{C}~> vertex_obj[N]) :
  cone_leg (FCone HomFrom N) x h ≈ cone_leg N x ∘ h.
Proof. reflexivity. Qed.

Example hom_preserved_mediator {J : Category} {K : J ⟶ C} {N : Cone K}
  (HN : IsLimitCone N) (M : Cone (HomFrom ◯ K)) :
  unique_obj (hom_PreservesLimitCone K N HN M) = hom_med HN M := eq_refl.

(** ** Mac Lane's own case: products *)

(* Indexed products, at the elementary record of Structure/Limit/Product.v
   and for an arbitrary index [Type].  Proved directly; the header
   records the measured universe cost of routing this through the
   discrete-diagram presentation instead. *)

Section IndexedProducts.

Context {A : Type}.
Context {f : A → C}.
Context {p : C}.
Context {proj : ∀ a : A, p ~{C}~> f a}.
Context (H : IsIndexedProduct f p proj).

Section Fixed.

Context {S : Sets}.
Context (pi : ∀ a : A, S ~{Sets}~> fobj[HomFrom] (f a)).

Definition hom_iprod_med_fun (s : S) : c ~{C}~> p :=
  unique_obj (iprod_desc H (fun a => pi a s)).

Lemma hom_iprod_med_commutes (s : S) (a : A) :
  proj a ∘ hom_iprod_med_fun s ≈ pi a s.
Proof. exact (unique_property (iprod_desc H (fun a => pi a s)) a). Qed.

Lemma hom_iprod_med_unique (s : S) (v : c ~{C}~> p) :
  (∀ a : A, proj a ∘ v ≈ pi a s) → hom_iprod_med_fun s ≈ v.
Proof. intro Hv. exact (uniqueness (iprod_desc H (fun a => pi a s)) v Hv). Qed.

#[local] Instance hom_iprod_med_respects :
  Proper (equiv ==> equiv) hom_iprod_med_fun.
Proof.
  intros s t Hst.
  apply hom_iprod_med_unique.
  intro a.
  rewrite hom_iprod_med_commutes.
  now rewrite Hst.
Qed.

Definition hom_iprod_med : S ~{Sets}~> fobj[HomFrom] p :=
  {| morphism := hom_iprod_med_fun ;
     proper_morphism := hom_iprod_med_respects |}.

End Fixed.

Definition hom_IsIndexedProduct :
  @IsIndexedProduct Sets A (fun a => fobj[HomFrom] (f a))
    (fobj[HomFrom] p) (fun a => fmap[HomFrom] (proj a)).
Proof using H.
  constructor.
  intros S pi.
  unshelve refine {| unique_obj := hom_iprod_med pi |}.
  - simpl; intros a s.
    exact (hom_iprod_med_commutes pi s a).
  - simpl; intros v Hv s.
    apply hom_iprod_med_unique.
    intro a.
    exact (Hv a s).
Defined.

End IndexedProducts.

(* The binary case, at the apex-pinned [IsCartesianProduct]: the
   conclusion is that [C(c, z)] is a product of [C(c, x)] and [C(c, y)]
   in Sets, with post-composition as the two projections. *)

Section BinaryProducts.

Context {x y z : C}.
Context (H : @IsCartesianProduct C x y z).

Definition hom_fork_fun {S : Sets} (F : S ~{Sets}~> fobj[HomFrom] x)
  (G : S ~{Sets}~> fobj[HomFrom] y) (s : S) : c ~{C}~> z :=
  @fork' C x y z H c (F s) (G s).

#[local] Instance hom_fork_respects {S : Sets}
  (F : S ~{Sets}~> fobj[HomFrom] x) (G : S ~{Sets}~> fobj[HomFrom] y) :
  Proper (equiv ==> equiv) (hom_fork_fun F G).
Proof.
  intros s t Hst; unfold hom_fork_fun.
  apply fork'_respects; now rewrite Hst.
Qed.

Definition hom_fork {S : Sets} (F : S ~{Sets}~> fobj[HomFrom] x)
  (G : S ~{Sets}~> fobj[HomFrom] y) : S ~{Sets}~> fobj[HomFrom] z :=
  {| morphism := hom_fork_fun F G ;
     proper_morphism := hom_fork_respects F G |}.

Definition hom_IsCartesianProduct :
  @IsCartesianProduct Sets (fobj[HomFrom] x) (fobj[HomFrom] y)
    (fobj[HomFrom] z).
Proof using H.
  unshelve refine {| fork' := fun S F G => hom_fork F G ;
                     exl' := fmap[HomFrom] (@exl' C x y z H) ;
                     exr' := fmap[HomFrom] (@exr' C x y z H) |}.
  - intros S F F' HF G G' HG s; simpl.
    unfold hom_fork_fun.
    apply fork'_respects; [ exact (HF s) | exact (HG s) ].
  - simpl; intros S F G h.
    split.
    + intro Hh.
      split; intro s.
      * exact (fst (fst (@ump_product C x y z H c (F s) (G s) (h s)) (Hh s))).
      * exact (snd (fst (@ump_product C x y z H c (F s) (G s) (h s)) (Hh s))).
    + intros [Hl Hr] s.
      exact (snd (@ump_product C x y z H c (F s) (G s) (h s))
               (Hl s, Hr s)).
Defined.

End BinaryProducts.

End HomContinuous.

(** ** The contravariant twin: colimits of C become limits of Sets *)

(* [Hom ─,c] IS the covariant hom-functor of C^op, definitionally, so
   every constant here is instantiation: all are supplied by [:=] with
   no tactic. *)

Section HomContravariant.

Context {C : Category}.
Context (c : C).

Definition HomTo : C^op ⟶ Sets := [Hom ─, c].

Example hom_to_is_op_hom_from : HomTo = @HomFrom (C^op) c := eq_refl.

Definition cohom_ContinuousFunctor : ContinuousFunctor HomTo :=
  @hom_ContinuousFunctor (C^op) c.

Definition cohom_PreservesLimitCone {J : Category} (K : J ⟶ C^op) :
  PreservesLimitCone K HomTo := @hom_PreservesLimitCone (C^op) c J K.

(* The covariant reading in C: a colimiting cocone of C is carried to a
   limiting cone of Sets.  [Cocone K] is [Cone (K^op)] and
   [IsColimitCocone] is [IsLimitCone] at the opposite diagram, so no
   repackaging is needed. *)

Definition cohom_colimit_to_limit {J : Category} {K : J ⟶ C}
  (N : Cocone K) (HN : IsColimitCocone N) : IsLimitCone (FCone HomTo N) :=
  cohom_PreservesLimitCone (Opposite_Functor K) N HN.

(* Coproducts of C become products in Sets; the projections are
   PREcomposition with the injections.  DISPLAY HAZARD: [Check] prints
   the hypothesis of [cohom_IsCartesianProduct] as
   [IsCartesianProduct x y z] with the category argument suppressed, so
   the printed type reads as though the product were taken in C.  It is
   not: the source spells [@IsCartesianProduct (C^op) x y z], i.e. z is
   the COPRODUCT of x and y in C. *)

Definition cohom_IsIndexedProduct {A : Type} {g : A → C} {q : C}
  {inj : ∀ a : A, g a ~{C}~> q} (H : IsIndexedCoproduct g q inj) :
  @IsIndexedProduct Sets A (fun a => fobj[HomTo] (g a)) (fobj[HomTo] q)
    (fun a => fmap[HomTo] (inj a)) :=
  @hom_IsIndexedProduct (C^op) c A g q inj H.

Definition cohom_IsCartesianProduct {x y z : C}
  (H : @IsCartesianProduct (C^op) x y z) :
  @IsCartesianProduct Sets (fobj[HomTo] x) (fobj[HomTo] y) (fobj[HomTo] z) :=
  @hom_IsCartesianProduct (C^op) c x y z H.

End HomContravariant.

(** ** Non-vacuity *)

(* The repackaging Structure/Cartesian.v does not carry: a bundled
   [Cartesian] structure read at one chosen pair as an apex-pinned
   product.  Supplied here only to state the witness below; deliberately
   not registered as an [Instance]. *)

Program Definition cartesian_IsCartesianProduct {C : Category}
  `{@Cartesian C} (x y : C) : IsCartesianProduct x y (x × y) := {|
  fork' := fun _ f g => f △ g ;
  exl'  := exl ;
  exr'  := exr
|}.
Next Obligation. apply ump_products. Qed.

(* Witness (1): the binary product corollary at [Coq_Cartesian].  The
   three Examples below compute by [eq_refl]. *)

Definition coq_hom_product (u x y : Coq) :
  @IsCartesianProduct Sets (fobj[HomFrom u] x) (fobj[HomFrom u] y)
    (fobj[HomFrom u] (x × y)%object) :=
  hom_IsCartesianProduct u (cartesian_IsCartesianProduct x y).

Definition coq_hp := coq_hom_product unit bool nat.

Example coq_hom_exl_computes :
  @exl' Sets _ _ _ coq_hp (fun _ : unit => (true, 3%nat)) tt = true := eq_refl.

Example coq_hom_exr_computes :
  @exr' Sets _ _ _ coq_hp (fun _ : unit => (true, 3%nat)) tt = 3%nat := eq_refl.

Example coq_hom_fork_computes :
  @fork' Sets _ _ _ coq_hp _ (@exl' Sets _ _ _ coq_hp)
    (@exr' Sets _ _ _ coq_hp) (fun _ : unit => (true, 3%nat)) tt
    = (true, 3%nat) := eq_refl.

(* Witness (2): the CONE-LEVEL headline at an in-tree limit -- the one
   [Cartesian_Limit] produces from [Coq_Cartesian].  It does not compute
   ([Cartesian_Limit] is [Qed]) and its ambient category is measurably
   [Coq@{u1 Set Set}], for the reason the header analyses. *)

Definition coq_two_limit (F : Two_Discrete ⟶ Coq) : Limit F :=
  snd (Cartesian_Limit Coq) Coq_Cartesian F.

Definition coq_hom_limit_cone (u : Coq) (F : Two_Discrete ⟶ Coq) :
  IsLimitCone (FCone (HomFrom u) (@limit_cone _ _ _ (coq_two_limit F))) :=
  hom_PreservesLimitCone u F _ (limit_limitcone (coq_two_limit F)).

Definition coq_hom_bool_nat_limit :
  IsLimitCone (@FCone Two_Discrete Coq Sets (HomFrom unit)
                 (Pick_Two bool nat)
                 (coq_two_limit (Pick_Two bool nat))) :=
  coq_hom_limit_cone unit (Pick_Two bool nat).
