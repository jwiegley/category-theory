Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.Product.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Discrete.

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

   so, writing [Sets@{o so}] as Instance/Sets.v:198 does, [u] is [o] -- the
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
   [right_adjoint_PreservesImageLimit] (Construction/Comma/Limit.v:266, which
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

   [Cocomplete Sets] is not provided BY THIS FILE.  It is NOT missing from
   the tree, correcting what this sentence used to say: Instance/Sets/
   Cocomplete.v:484's [Sets_Cocomplete] is exactly the quotient of the
   disjoint union this paragraph once called unattempted.

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

(** * Mac Lane's cone-set construction *)

(* Mac Lane, _Categories for the Working Mathematician_, 2nd ed. (GTM 5),
   SV.1 Theorem 1 and the remark following it, printed p. 110 (PDF p. 119);
   item ids [maclane:V.1:thm1], [maclane:V.1:remark1].  Riehl, _Category
   Theory in Context_, 2nd ed., SS3.2 Definition 3.2.3 and Theorem 3.2.4,
   printed pp. 93-94.  Quoted from the rendered page, not from the OCR
   layer, which renders the cone letter nu as "Ii".  ONE DEPARTURE FROM THE
   PAGE, forced by the lexer and disclosed rather than silent: the book
   writes the one point set as [*], so its "Cone" of that argument is
   spelled with an open paren immediately followed by a star -- which is
   exactly Coq's nested-comment opener.  Every quotation below therefore
   reads [Cone ( *, F)], with a space the book does not have.  Nothing else
   is altered.

     "Theorem 1 (Completeness of Set).  If the category J is small, any
      functor F : J-->Set has a limit which is the set Cone ( *, F) of all
      cones sigma : *-->F from the one point set * to F, while the limiting
      cone v, with

          v_j : Cone ( *, F) --> F_j,     sigma |--> sigma_j,          (2)

      is for each j that function sending each cone sigma to the element
      sigma_j in F_j."

   and, on the same page, the sentence this file's discrete section
   discharges:

     "For example, if J is discrete, the set Cone( *, F) of J-cones is just
      the cartesian product Pi_j F_j."

   WHAT IS DELIVERED HERE, AND WHY IT SITS BESIDE THE EXISTING PROOF

   The construction above this comment builds the limit as the setoid of
   COMPATIBLE FAMILIES.  Mac Lane builds it as the SET OF CONES from the one
   point set.  Both are limits of the same diagram, so they are canonically
   isomorphic, and neither is a re-derivation of the other: they are
   different objects.  This section adds Mac Lane's, and does not replace
   [Sets_Limit] or [Sets_Complete].  Three reasons, each measured.  First,
   [Sets_Complete] has code consumers (Adjunction/GAFT/Sets.v,
   Adjunction/Diagonal/Limit.v, Test/ProbeCocomplete329.v).  Second,
   Instance/Sets/Pullback.v's header asserts that the derived pullback apex
   "IS, on the nose, the setoid of COMPATIBLE FAMILIES" and quotes an
   accepted [eq_refl] fragment about it; redefining [Sets_Limit] would make
   that prose false without breaking any build.  Third, the two apexes are
   NOT convertible -- one is a sigma of a dependent function with a
   compatibility witness, the other an [ACone] record -- so there is
   something to compare, and the comparison is the deliverable.  It is
   [cone_apex_iso] in the sibling Instance/Sets/Cone.v, which also carries
   the remark's natural bijection; see that file's header for why the
   comparison could not live here (it costs one module of closure, and this
   file's is held fixed).

   THE APEX IS THE CONE PRESHEAF AT THE TERMINAL SETOID

   [cone_apex F] is [fobj[ConePresheaf F] 1] -- Structure/Cone.v:79's
   presheaf, applied at [Sets]' terminal object -- and not a re-derived
   copy.  Both of its fields are pinned by [eq_refl] below: its carrier is
   [ACone 1 F] and its setoid is [AConeEquiv 1 F].  Since [AConeEquiv]
   compares two cones by their legs and ignores the coherence proof, the
   apex is the set of Mac Lane's [sigma] with his own identification.

   THE LEGS ARE EVALUATION, AND THE PROOF SPENDS THE SINGLETON EXACTLY ONCE

   [cone_leg_at d] is display (2): it sends a cone [p] to the element
   [vertex_map p d ttt].  Its ONE obligation, and the one [cone_set_acone]
   beside it raises, are read off the argument:
   respectfulness is [AConeEquiv]'s own hypothesis at [d] and [ttt], and the
   cone coherence of [cone_set_acone] is the argument cone's own coherence
   read at [ttt].  Neither is [reflexivity]; the coherence in particular is
   not definitional.

   The mediator [cone_set_med N] is Mac Lane's [h]: it sends [e] to the cone
   [tau e].  Commuting is [reflexivity] -- the leg of [cone_set_med N e] at
   [d] evaluated at the point IS [vertex_map N d e].  UNIQUENESS is the one
   place the singleton's unique-inhabitant property is spent, in a single
   [destruct u]: [poly_unit] (Lib/Setoid.v:56) is an inductive with no eta,
   so a variable [u : poly_unit] is not definitionally [ttt].  That
   [destruct] IS Riehl's "restricting along each element regarded as a map
   out of the singleton".  It is essential and not cosmetic: without it the
   goal is not closed by [symmetry; exact (Hv d e)].

   No choice principle and no extensionality: the cone type carries its
   coherence as data, as the compatible-family type above carries its
   compatibility.

   SMALLNESS, AND THE UNIVERSE COMPARISON

   [About] prints, for the two completeness witnesses side by side,

     ConeSet_Complete@{u u0} : Complete@{u u u u0}     (* u < u0 *)
     Sets_Complete@{u u0}    : Complete@{u u u u0}     (* u < u0 *)

   -- the same number of universes, the same binder, the same instance, and
   the same smallness side condition the header above records for
   [Sets_Complete].  Neither is more general than the other.  The blocks
   differ only in WHICH stdlib constants they cite: this one goes through
   [Sets_Terminal] and cites [eq_ind] and friends, the existing one goes
   through [sigT] and cites [Projections].

   THE DISCRETE SPECIAL CASE

   Mac Lane's own sentence, quoted above.  It is delivered against the
   compatible-family apex, whose relation to the indexed product of
   Instance/Sets/Products.v is the direct one: the three [eq_refl] Examples
   record that the limit apex IS [Sets_limit_obj] of the discrete diagram,
   that the product setoid it is cut out of IS literally [Sets_iprod_obj f],
   and that the limit legs ARE the indexed-product projections.

   THE STRENGTH IS AN ISOMORPHISM AND NOT AN EQUALITY, and the reason is not
   universes.  [Sets_limit_compatible] at a discrete shape unfolds to
   [∀ d d' (e : d = d'), fmap[F] e (x d) ≈ x d'], which is a genuine
   Pi-type, not [unit]: it is INHABITED for every family
   ([discrete_compatible], by [destruct e]) but it is not vacuous AS A TYPE.
   So the limit carrier is a sigma and the product carrier is the bare
   family, and they are different types.  The [eq_refl] form of the leg
   equation is refused at CONVERSION and is pinned in
   Test/ProbeConeSets407.v.

   [Structure/Limit/Product/Finite.v:545]'s [iprod_unique_iso] would give
   the same isomorphism in one term, since both sides are indexed products.
   It is deliberately NOT used: requiring that module costs this file
   twenty-one further modules of closure for twelve lines, against
   thirty-one hand-built at zero.  It is cited here rather than consumed.

   A UNIVERSE PIN, DISCLOSED -- AND IT REACHES FOUR OF THE TEN CONSTANTS,
   NOT THE SECTION.  The discrete section is written with [{A : Set}], and
   an earlier revision of this paragraph said the whole section forced it.
   Measured, by restating the section at [{A : Type}] and compiling: SIX
   constants are ACCEPTED there, the headline [discrete_iprod_iso] among
   them, along with [discrete_limit], [discrete_inner_is_iprod],
   [discrete_compatible], [discrete_forget] and [discrete_pair].  Exactly
   FOUR are refused -- [discrete_apex_is_limit_obj],
   [discrete_leg_is_proj], [discrete_iprod_iso_leg] and
   [discrete_iprod_iso_leg_inv] -- and they are exactly the four whose
   statements name Structure/Limit/Product.v's [iprod] or [iprod_proj],
   THREE of them rejected with "cannot ensure that Type is a subtype of
   Set"; the fourth, [discrete_iprod_iso_leg_inv], instead gives a plain
   unification MISMATCH ("expected to have type ?y ~{?Category}~> ?z")
   carrying NO word-bounded [Set] at all -- a different KIND of refusal
   under this development's own taxonomy, measured by restating the six
   accepted constants at [Type] and adding each refused one alone.  An
   earlier revision of this sentence said all four were alike.  The
   MECHANISM is the one described before: [iprod@{u u0 u1}] is declared
   over [C : Category@{u1 Set Set}], pinning the ambient hom and proof
   universes to the literal [Set], and at [C := Sets@{o so} :
   Category@{so o o}] that collapses [Sets]' CARRIER universe [o] to
   [Set], after which [Sets_iprod_obj]'s [u <= u0] bound carries the index
   down too.  [iprod]'s own pin is visible in its printed type
   ([Limit@{u u Set u1} (DiscreteCat_Functor@{u u1 u0 Set} f)]) and takes
   BOTH donors -- [Cone] alone is accepted at levels declared apart, so it
   is the discriminating control -- with both pinned in the probe.  The
   section is written uniformly at [{A : Set}] so that the four readbacks
   apply to the same [f] as the isomorphism they read back; the pin is the
   donor's, is not repaired here, and is not claimed unavoidable.  The core
   section above carries no [Set] at all.

   These definitions are stated at top level rather than in a [Section]
   because a section [Context] fixes its universes once, before the pin can
   propagate, and the discrete diagram is then refused inside it.

   STATUS: axiom-free.  [Print Assumptions] reports "Closed under the global
   context" for every constant below; the Makefile's [print-assumptions]
   target audits them by fully qualified name. *)

Section ConeSet.

Context {D : Category}.
Context (F : D ⟶ Sets).

(* Mac Lane's [Cone ( *, F)]: the cone presheaf of Structure/Cone.v:79
   evaluated at the terminal setoid.  Not a copy -- the two [eq_refl]
   Examples below pin both fields of the [SetoidObject]. *)
Definition cone_apex : obj[Sets] :=
  fobj[ConePresheaf F] (@terminal_obj Sets Sets_Terminal).

Example cone_apex_is_ConePresheaf :
  cone_apex = fobj[ConePresheaf F] (@terminal_obj Sets Sets_Terminal)
  := eq_refl.

Example cone_apex_carrier :
  carrier cone_apex = @ACone D Sets (@terminal_obj Sets Sets_Terminal) F
  := eq_refl.

Example cone_apex_setoid :
  @is_setoid cone_apex = AConeEquiv (@terminal_obj Sets Sets_Terminal) F
  := eq_refl.

(* Display (2): [v_j : Cone ( *, F) --> F_j], [sigma |--> sigma_j].  The
   function sends a cone to the value of its leg at [d] on the one point. *)
Program Definition cone_leg_at (d : D) : cone_apex ~{Sets}~> F d := {|
  morphism := fun p => @vertex_map _ _ _ _ p d ttt
|}.
Next Obligation. intros d p q Hpq; exact (Hpq d ttt). Qed.

(* The leg IS evaluation, on the nose. *)
Example cone_leg_at_is_evaluation (d : D) (p : cone_apex) :
  cone_leg_at d p = @vertex_map _ _ _ _ p d ttt := eq_refl.

(* "hence v as defined in (2) is a cone to the base F": the coherence of
   the cone of legs is the argument cone's own coherence at the point. *)
Program Definition cone_set_acone : ACone cone_apex F := {|
  vertex_map := cone_leg_at
|}.
Next Obligation.
  intros x y f p; exact (@cone_coherence _ _ _ _ p x y f ttt).
Qed.

Definition cone_set_cone : Cone F :=
  {| vertex_obj := cone_apex; coneFrom := cone_set_acone |}.

(* Mac Lane's [h]: "for each x in X, tau x is a cone to F from one point,
   so there is a unique function h : X --> Cone ( *, F) sending each x to
   tau x". *)
Program Definition cone_set_med (N : Cone F) :
  vertex_obj[N] ~{Sets}~> cone_apex := {|
  morphism := fun e =>
    {| vertex_map := fun d => {| morphism := fun _ =>
         @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d e |} |}
|}.
Next Obligation. intros N e d u v Huv; reflexivity. Qed.
Next Obligation.
  intros N e x y f u.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f e).
Qed.
Next Obligation.
  intros N e e' Hee' d u.
  exact (proper_morphism
           (@vertex_map _ _ _ _ (@coneFrom _ _ _ N) d) e e' Hee').
Qed.

(* Commuting is definitional. *)
Lemma cone_set_med_commutes (N : Cone F) (d : D) :
  cone_leg_at d ∘ cone_set_med N
    ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d.
Proof. intros e; reflexivity. Qed.

(* Uniqueness.  The [destruct u] is the one use of the singleton's
   unique-inhabitant property in the whole construction. *)
Lemma cone_set_med_unique (N : Cone F)
  (v : vertex_obj[N] ~{Sets}~> cone_apex) :
  (∀ d : D, cone_leg_at d ∘ v
              ≈ @vertex_map _ _ _ _ (@coneFrom _ _ _ N) d) →
  cone_set_med N ≈ v.
Proof. intros Hv e d u; destruct u; symmetry; exact (Hv d e). Qed.

(* Theorem 1, at the apex-pinned level. *)
Program Definition cone_set_IsALimit : IsALimit F cone_apex := {|
  limit_acone := cone_set_acone;
  ump_limit := fun N => {| unique_obj := cone_set_med N |}
|}.
Next Obligation. exact cone_set_med_commutes. Qed.
Next Obligation. intros N v Hv; exact (cone_set_med_unique N v Hv). Qed.

(* Theorem 1, bundled. *)
Program Definition cone_set_Limit : Limit F := {|
  limit_cone := cone_set_cone;
  ump_limits := fun N => {| unique_obj := cone_set_med N |}
|}.
Next Obligation. exact cone_set_med_commutes. Qed.
Next Obligation. intros N v Hv; exact (cone_set_med_unique N v Hv). Qed.

End ConeSet.

(* Completeness of [Set], by Mac Lane's own construction.  A second witness
   beside [Sets_Complete]; see the header for why both stand. *)
Definition ConeSet_Complete : @Complete Sets := fun D F => cone_set_Limit F.

(** ** Mac Lane's discrete example *)

(* "if J is discrete, the set Cone( *, F) of J-cones is just the cartesian
   product Pi_j F_j".  What is proved HERE is that sentence about the
   COMPATIBLE-FAMILY apex, whose relation to the indexed product is direct.
   The object Mac Lane's sentence actually names is the cone set, and
   Instance/Sets/Cone.v's [cone_apex_discrete_iprod_iso] carries this
   across to it by one [iso_compose] with [cone_apex_iso]; that file is
   where the quoted sentence becomes a theorem about its own subject.  See
   the header for the [Set] pin four of these carry -- the isomorphism
   below is not among them -- and for why they are not in a [Section]. *)

Definition discrete_limit {A : Set} (f : A → obj[Sets]) :
  Limit (DiscreteCat_Functor f) := Sets_Limit (DiscreteCat_Functor f).

(* The limit's apex IS the compatible-family object of the discrete
   diagram. *)
Example discrete_apex_is_limit_obj {A : Set} (f : A → obj[Sets]) :
  iprod f (discrete_limit f)
  = Sets_limit_obj (DiscreteCat_Functor f) := eq_refl.

(* The product setoid it is cut out of IS literally [Sets_iprod_obj f]. *)
Example discrete_inner_is_iprod {A : Set} (f : A → obj[Sets]) :
  Sets_iprod_obj (fun d : DiscreteCat A => (DiscreteCat_Functor f) d)
  = Sets_iprod_obj f := eq_refl.

(* The limit legs ARE the indexed-product projections. *)
Example discrete_leg_is_proj {A : Set} (f : A → obj[Sets]) (a : A) :
  iprod_proj f (discrete_limit f) a
  = Sets_limit_leg (DiscreteCat_Functor f) a := eq_refl.

(* The compatibility constraint is inhabited for every family at a discrete
   shape -- vacuously satisfied, but not vacuous as a type, which is why
   the agreement below is an isomorphism and not an equality. *)
Lemma discrete_compatible {A : Set} (f : A → obj[Sets])
  (x : Sets_iprod_obj (fun d : DiscreteCat A => (DiscreteCat_Functor f) d)) :
  Sets_limit_compatible (DiscreteCat_Functor f) x.
Proof. intros d d' e; destruct e; simpl; reflexivity. Qed.

Program Definition discrete_forget {A : Set} (f : A → obj[Sets]) :
  Sets_limit_obj (DiscreteCat_Functor f) ~{Sets}~> Sets_iprod_obj f := {|
  morphism := fun p => `1 p
|}.
Next Obligation. intros A f p q Hpq a; exact (Hpq a). Qed.

Program Definition discrete_pair {A : Set} (f : A → obj[Sets]) :
  Sets_iprod_obj f ~{Sets}~> Sets_limit_obj (DiscreteCat_Functor f) := {|
  morphism := fun x => (x; discrete_compatible f x)
|}.
Next Obligation. intros A f x y Hxy a; exact (Hxy a). Qed.

(* The discrete limit IS the cartesian product, up to isomorphism. *)
Program Definition discrete_iprod_iso {A : Set} (f : A → obj[Sets]) :
  @Isomorphism Sets (Sets_limit_obj (DiscreteCat_Functor f))
                    (Sets_iprod_obj f) := {|
  to := discrete_forget f; from := discrete_pair f
|}.
Next Obligation. intros A f x a; reflexivity. Qed.
Next Obligation. intros A f p a; reflexivity. Qed.

(* Both leg families, at the setoid grade.  The [eq_refl] form of the first
   is refused at CONVERSION and is pinned in the probe. *)
Lemma discrete_iprod_iso_leg {A : Set} (f : A → obj[Sets]) (a : A) :
  Sets_iprod_proj f a ∘ to (discrete_iprod_iso f)
    ≈ iprod_proj f (discrete_limit f) a.
Proof. intros p; reflexivity. Qed.

Lemma discrete_iprod_iso_leg_inv {A : Set} (f : A → obj[Sets]) (a : A) :
  iprod_proj f (discrete_limit f) a ∘ from (discrete_iprod_iso f)
    ≈ Sets_iprod_proj f a.
Proof. intros x; reflexivity. Qed.
