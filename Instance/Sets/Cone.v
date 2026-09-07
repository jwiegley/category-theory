Require Import Category.Lib.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Diagram.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Quiver.Presented.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Diagonal.
Require Import Category.Functor.Representable.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Cone.Const.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Unique.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Sets.Karoubi.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.GAFT.Sets.
Require Import Category.Adjunction.Diagonal.Limit.

Generalizable All Variables.
#[local] Obligation Tactic := idtac.

(** * Mac Lane's cone-set limit: the comparison, the remark, the cases *)

(* Mac Lane, _Categories for the Working Mathematician_, 2nd ed. (GTM 5),
   SV.1 Theorem 1 and the remark following it, printed p. 110 (PDF p. 119);
   item ids [maclane:V.1:thm1], [maclane:V.1:remark1].  Awodey, _Category
   Theory_ (1st ed., CMU pre-print, September 2005), SS3.3 Example 3.14,
   printed p. 67; item id [awodey:3.3:example14].  Fong & Spivak, _Seven
   Sketches in Compositionality_ (CUP, 2019), SS3.5.3 Theorem 3.95, printed
   p. 112; item id [7sketches:3.5.3:thm3.95].  Riehl, _Category Theory in
   Context_, 2nd ed., SS3.2 Definition 3.2.3, Theorem 3.2.4 and Example
   3.2.7, printed pp. 93-94; item ids [riehl:3.2:def3], [riehl:3.2:thm4],
   [riehl:3.2:example7].

   The construction itself is Instance/Sets/Complete.v's, alongside the
   compatible-family limit that file already carried.  THIS file is the
   rider: the comparison of the two apexes, the remark's natural bijection,
   its identification with the diagonal-limit adjunction, and the equalizer
   and tuple readings.  It is a LEAF -- nothing in the tree depends on it --
   which is why it may carry the heavy [Require]s that the core cannot.

   WHY THESE ARE NOT IN Instance/Sets/Complete.v.  Two separate reasons, and
   only the second is a hard one.  (i) Instance/Sets/Complete.v's transitive
   closure is held at 33 modules ([coqdep -sort], counting the file itself);
   [Structure/Limit/Unique] -- which supplies [limit_unique_iso], i.e. the
   whole comparison -- costs it one more, and the natural-bijection block
   costs four.  Those go here instead, and the number is the reason.  (ii)
   Adjunction/Diagonal/Limit.v:356 REQUIRES Category.Instance.Sets.Complete,
   so the adjunction identification cannot live in that file at all: it
   would be a dependency cycle.  That is what makes this file necessary
   rather than merely tidy.

   THE COMPARISON

   [cone_apex_iso] is [limit_unique_iso] applied to the two limit witnesses.
   Both apexes are limits of the same diagram, so the isomorphism and BOTH
   leg-commutation families come for free -- there is no new proof content
   in this section at all, and the file says so rather than dressing it up.
   What IS worth pinning, and is pinned by [eq_refl], is that the comparison
   is not opaque: its forward leg IS the cone-set mediator
   ([cone_apex_iso_to_is_med]), and the two leg families ARE the named ones
   ([cone_apex_iso_leg_cone], [cone_apex_iso_leg_family]).

   THE APEXES THEMSELVES ARE NOT EQUAL, and the two strict attempts are
   refused: at the object level with "cannot unify" (a CONVERSION refusal),
   because one is a sigma of a dependent function with a compatibility
   witness and the other an [ACone] record.  There is no [≈] grade to fall
   back to either -- objects of [Sets] carry no setoid, so the attempt is a
   RESOLUTION refusal ("Cannot infer the implicit parameter Setoid").  Both
   are pinned in Test/ProbeConeSets407.v; note that a bare [Check] of the
   second is ACCEPTED, printing an open evar, so the refutation command must
   be a [Definition].

   THE REMARK, DISPLAY (3)

     "The crux of this proof is the (natural) bijection

          Cone (X, F) ~= Set (X, Cone ( *, F))                       (3)

      given by tau |--> h, as above."

   The parenthesis around "natural" is the book's, and the book does NOT
   prove it -- that is this issue's work item 4, first half, and it is
   proved here.  [ConeSet_Natural_Iso] is a genuine isomorphism in the
   functor category [[Sets^op, Sets]] between [ConePresheaf F] -- the left
   side of (3) AS A FUNCTOR OF X, which is exactly what Structure/Cone.v:79
   already is -- and [Curried_CoHom Sets (cone_apex F)], the right side.
   Every naturality clause closes by [reflexivity].  [ConeSet_Representable]
   reads the same isomorphism as representability of the cone presheaf,
   which is the content Structure/UniversalProperty/Limit.v:141 states
   abstractly and which is here inhabited.

   THE ADJUNCTION, AND WHICH ORACLE YOU FEED IT

   Mac Lane rewrites (3) as [Nat (Delta X, F) ~= Set (X, Cone ( *, F))] and
   says "By the very definition of limit, this proves that Lim F ~= Cone
   ( *, F)".  In tree the adjunction is #353's [Diagonal_Limit_Adjunction],
   which takes a [HasLimitsOfShape] as a parameter -- a CHOICE of limits --
   and the identification depends on WHICH choice.

   Fed [ConeSet_HasLimitsOfShape], built from the cone-set construction, the
   book's bijection IS the adjunction's transposition, and four [eq_refl]
   readbacks say so: the adjunction's right-hand object is [cone_apex], its
   leg is [cone_leg_at], its backward transpose has [cone_untranspose]'s
   legs, and its counit component is [cone_leg_at ∘ id].  READ THE THIRD AT
   ITS MEASURED GRADE: it is stated LEG BY LEG and not on whole records,
   because the whole-record form is refused -- for the same donor reason the
   forward transposition is, recorded two paragraphs below -- and that
   refusal is pinned in the probe.

   Fed the PRE-EXISTING [Sets_HasLimitsOfShape] -- which is built on
   [Sets_Complete], the compatible-family oracle -- it is not, and not even
   at the same TYPE: ascribing that adjunction's transposition at the
   cone-set codomain is a plain has-type mismatch (a TYPING refusal, no
   "cannot unify" and no universe clause).  That refusal is pinned in the
   probe with the cone-set form beside it as the discriminating control.
   The bridge between the two readings is [cone_apex_iso].

   SO THE HONEST STATEMENT IS THE CONDITIONAL ONE, and it is the interesting
   content of work item 4: the book's bijection is the transposition of the
   diagonal-limit adjunction AT THE CONE-SET ORACLE.  Nothing here claims it
   is the transposition of the pre-existing [Sets_Diagonal_Limit_Adjunction].

   ONE GRADE IS NOT [eq_refl], AND THE LOCALIZATION IS WEAKER THAN THE
   OBVIOUS ONE.  The FORWARD transposition applied to a cone, compared as a
   whole morphism with [cone_transpose], is refused at CONVERSION.  One
   donor fact is measured and true: [Cone_Natural_Transform]'s [ACone] round
   trip (Structure/Cone/Const.v:53) returns the LEG FAMILY on the nose --
   [vertex_map] of the round trip is [vertex_map] of the original at
   [eq_refl] -- while the WHOLE record is refused, its [cone_coherence]
   proof being [abstract]ed at Const.v:58.  But that does NOT localize the
   refusal here, and an earlier revision of this paragraph said it did: the
   two sides of the negative differ ALREADY at the value, refused at a
   point [x : X] and again at the produced cone's leg at [d], both measured.
   So the difference is NOT confined to one law field, no cause is
   isolated, and what holds is the setoid-level identification
   ([coneset_adj_to_is_transpose]).

   EQUALIZERS

   Awodey SS3.3 Example 3.14: in Set the equalizer of [f, g : A → B] is the
   inclusion of [{x ∈ A | f x = g x}].  Riehl SS3.2 Example 3.2.7 says the
   same and adds that it is obtained as the set of cones with summit the
   singleton.

   [HasEqualizers Sets] ALREADY EXISTS THREE TIMES OVER in library files --
   [Sets_HasEqualizers] (Adjunction/GAFT/Sets.v:175), [SetsEqualizers]
   (Adjunction/CokernelPair.v:1119) and [DiagSets_HasEqualizers]
   (Adjunction/Diagonal/Finite.v:1129) -- so no fourth is added here, and
   the issue's checkbox asking for the class "delivered by name" is already
   met by the first of those.  What is delivered instead is what was
   missing: the CONCRETE presentation and the measured relation to it.

   [sets_eq_obj f g] is Awodey's subset as a sub-setoid, [sets_IsEqualizer]
   its universal property (three one-line obligations: the fork condition IS
   the sigma's witness, commuting is [reflexivity] because the inclusion of
   the mediator IS [h] on the nose, uniqueness is pointwise from the
   competing map's own equation).  No choice, no funext, no decidability.
   [existing_apex_is_limit_obj] pins by [eq_refl] that the EXISTING
   instance's apex is [Sets_limit_obj (APair f g)] and its leg is evaluation
   at [ParX] -- so the existing equalizer is the compatible-family setoid
   over the walking parallel pair, and is neither Awodey's subset nor a cone
   set.  The gap to Awodey's is exactly one application of an existing
   donor, [equalizer_unique] (Structure/Equalizer/Fork.v:106), delivered as
   [concrete_vs_existing]; the strict form is refused at CONVERSION and is
   pinned.

   RIEHL'S KAROUBI CHECKBOX.  Instance/Sets/Karoubi.v:41's [sets_split_obj e]
   has carrier [{ a : X & e a ≈ a }].  The issue names the [(id, e)] order,
   and that is what [karoubi_IsEqualizer] delivers.  NOTE THE ASYMMETRY, and
   it is the carrier's: written [e a ≈ a], the [(e, id)] order costs ONE
   [symmetry] against the issue's THREE, so two of the three are the
   order's.  The surviving one is the uniqueness obligation of
   [IsEqualizer]'s [eq_desc], whose goal is [h z ≈ projT1 (v z)]: that
   orientation is the record's field shape and needs [symmetry] at EITHER
   order, measured by compiling the [(e, id)] version with that step and
   without it.  An earlier revision of this paragraph said [(e, id)] needs
   none.  Both compile; only the issue's is shipped, and the other is
   recorded here in prose rather than as a second constant.  No
   idempotency hypothesis is taken: [sets_split_obj] needs none and neither
   does the equalizer.

   A UNIVERSE CONTRAST WORTH KNOWING.  [Parallel]'s constraint block is
   LITERALLY EMPTY, so the equalizer reading carries no [Set] pin at all --
   unlike the discrete reading in Instance/Sets/Complete.v, whose pin is
   [DiscreteCat_Functor]'s.  The asymmetry is the shape functor's, not the
   limit machinery's.

   SEVEN SKETCHES: THE TUPLE FORM

   Theorem 3.95 writes the limit in coordinates: for a shape presented by a
   graph, the limit is the set of vertex-indexed tuples compatible along
   every GENERATING EDGE, with the coordinate projections as legs.  The
   in-tree limit's compatibility quantifies over every ARROW of the shape,
   which over a free category means every PATH.  The bridge is
   [tuple_compat_paths]: a family compatible on generators is compatible
   along every path, by induction on the path.  That is the only new
   MATHEMATICAL content in the section; [tuple_obj]'s setoid obligation and
   the [dpath_fmap] step inside [tuple_bwd] are the rest, and the second is
   flagged at its site as needing a workaround, so neither is an evident
   map.  An earlier revision called this the only new proof content.

   STRONGER THAN THE BOOK, AND THE FILE SAYS SO: the book says "finite
   graph"; [G] here is an ARBITRARY [Quiver], with no finiteness, no
   decidable equality on nodes or edges, and no node-UIP anywhere.  Read the
   [About] of [tuple_iso] for the absence of any such hypothesis.

   The strength is an isomorphism, not an equality, and the [eq_refl] form
   is refused at CONVERSION for the expected reason: the two compatibility
   predicates quantify over paths and over edges respectively.  What DOES
   hold on the nose is recorded by two [eq_refl] Examples: the induced
   functor agrees with the diagram on objects, and the product setoid the
   limit is cut out of IS [Sets_iprod_obj] of the diagram's own vertex
   family.

   SEVEN SKETCHES: PRESENTATION-INDEPENDENCE

   The clause stated alongside the theorem: the limit depends only on the
   generating quiver, so imposed path equations do not affect it.  This is
   CHEAP, and the reason is structural: [Quotient] leaves objects and
   morphisms untouched and coarsens only the hom-setoid, while the limit
   carrier does not read the hom-setoid.  So the carrier is Leibniz-equal
   ([pres_carrier_strict]), the compatibility predicate is Leibniz-equal
   ([pres_compat_strict]), and BOTH legs of [pres_iso] are [fun p => p].

   The OBJECT-level [eq_refl] is nevertheless refused, and that boundary is
   real rather than an artifact of how the statement is written: the carrier
   agrees but the [is_setoid] field does not, its [setoid_equiv] being
   [Sets_limit_obj_obligation_1] applied to two functors that [Compose]
   rebuilds.  It is pinned in the probe, which carries one control of its
   own; the three accepted Examples that locate the refusal in that one
   field -- [pres_fobj_strict], [pres_compat_strict], [pres_carrier_strict]
   -- are in THIS file, at the end of the section, not in the probe.

   WHAT THIS SECTION DOES *NOT* SAY: it is "the limit of a diagram over the
   quotient is the limit of its restriction", which is the checkbox's own
   phrasing.  It does not by itself say the limit is computed from the
   generating edges -- that is the tuple form above.  The two are not
   composed here; composing them would need
   [presented_restrict] (Construction/Free/Quiver/Presented.v:289), which is
   not exercised.

   CLOSURE.  86 modules by [coqdep -sort] counting this file; the drop-one
   marginals are [Adjunction/Diagonal/Limit] 14, [Instance/Sets/Karoubi] 5,
   [Theory/Diagram] 2, [Construction/Free/Quiver/Presented] 2,
   [Adjunction/GAFT/Sets] 2, [Structure/Limit/Unique] 1, every other
   [Require] 0.  Nothing depends on this file, so that cost lands on no one.

   STATUS: axiom-free.  [Print Assumptions] reports "Closed under the global
   context" for every constant below; the Makefile's [print-assumptions]
   target audits them by fully qualified name. *)

(** ** The comparison with the compatible-family limit *)

Section Compare.

Context {D : Category}.
Context (F : D ⟶ Sets).

(* Both apexes are limits of [F], so [limit_unique_iso] supplies the
   comparison and both leg families with no new proof content. *)
Definition cone_apex_iso : Sets_limit_obj F ≅[Sets] cone_apex F :=
  limit_unique_iso (limit_is_alimit (Sets_Limit F)) (cone_set_IsALimit F).

Definition cone_apex_iso_legs :
  (∀ x : D, limit_leg (cone_set_IsALimit F) x ∘ to cone_apex_iso
              ≈ limit_leg (limit_is_alimit (Sets_Limit F)) x) *
  (∀ x : D, limit_leg (limit_is_alimit (Sets_Limit F)) x
              ∘ from cone_apex_iso ≈ limit_leg (cone_set_IsALimit F) x) :=
  limit_unique_iso_legs (limit_is_alimit (Sets_Limit F))
                        (cone_set_IsALimit F).

(* The two leg families are the named ones, on the nose. *)
Example cone_apex_iso_leg_cone :
  limit_leg (cone_set_IsALimit F) = cone_leg_at F := eq_refl.

Example cone_apex_iso_leg_family :
  limit_leg (limit_is_alimit (Sets_Limit F)) = Sets_limit_leg F := eq_refl.

(* And the comparison is not opaque: its forward leg IS the cone-set
   mediator of Mac Lane's proof.  Read its strength exactly: this is
   [limit_unique_iso]'s forward leg being [limit_med] at ANY two limits of
   ANY diagram, instantiated here -- the generic form is accepted -- so
   what it pins is that this comparison reduces, not anything specific to
   the cone set. *)
Example cone_apex_iso_to_is_med :
  to cone_apex_iso
  = cone_set_med F (alimit_cone (limit_is_alimit (Sets_Limit F)))
  := eq_refl.

End Compare.

(* MAC LANE'S DISCRETE SENTENCE, AT THE CONE SET ITSELF.  "If J is
   discrete, the set Cone( *, F) of J-cones is just the cartesian product
   Pi_j F_j" -- the object the sentence NAMES is the cone set, and
   Instance/Sets/Complete.v's [discrete_iprod_iso] states it of the
   compatible-family apex.  One [iso_compose] carries it across, which is
   what makes the quoted sentence a theorem about its own subject rather
   than about the other oracle.  [{A : Set}] is inherited from
   [discrete_iprod_iso]; see that file's universe note. *)
Definition cone_apex_discrete_iprod_iso {A : Set} (f : A -> obj[Sets]) :
  cone_apex (DiscreteCat_Functor f) ≅[Sets] Sets_iprod_obj f :=
  iso_compose (discrete_iprod_iso f)
              (iso_sym (cone_apex_iso (DiscreteCat_Functor f))).

(** ** The remark: display (3), natural in the apex *)

Section Remark.

Context {D : Category}.
Context (F : D ⟶ Sets).

(* Mac Lane's [tau |--> h]: a cone with apex X becomes a map into the cone
   set, sending [e] to the cone [tau e]. *)
Program Definition cone_transpose (X : obj[Sets]) :
  fobj[ConePresheaf F] X
    ~{Sets}~> fobj[Curried_CoHom Sets (cone_apex F)] X := {|
  morphism := fun p =>
    {| morphism := fun e =>
         {| vertex_map := fun d => {| morphism := fun _ =>
              @vertex_map _ _ _ _ p d e |} |} |}
|}.
Next Obligation. intros X p e d u v Huv; reflexivity. Qed.
Next Obligation.
  intros X p e x y f u; exact (@cone_coherence _ _ _ _ p x y f e).
Qed.
Next Obligation.
  intros X p e e' Hee' d u.
  exact (proper_morphism (@vertex_map _ _ _ _ p d) e e' Hee').
Qed.
Next Obligation. intros X p q Hpq e d u; exact (Hpq d e). Qed.

(* The inverse: reindex the tautological cone along h, i.e. compose each
   leg of display (2) with h. *)
Program Definition cone_untranspose (X : obj[Sets]) :
  fobj[Curried_CoHom Sets (cone_apex F)] X
    ~{Sets}~> fobj[ConePresheaf F] X := {|
  morphism := fun h => {| vertex_map := fun d => cone_leg_at F d ∘ h |}
|}.
Next Obligation.
  intros X h x y f e; simpl.
  exact (@cone_coherence _ _ _ _ (h e) x y f ttt).
Qed.
Next Obligation. intros X h h' Hhh' d e; simpl; exact (Hhh' e d ttt). Qed.

(* One round trip is definitional pointwise; the other spends the
   singleton, exactly once, in the same [destruct] the mediator spends. *)
Lemma cone_transpose_round (X : obj[Sets]) (p : fobj[ConePresheaf F] X) :
  cone_untranspose X (cone_transpose X p) ≈ p.
Proof. intros d e; reflexivity. Qed.

Lemma cone_untranspose_round (X : obj[Sets])
  (h : fobj[Curried_CoHom Sets (cone_apex F)] X) :
  cone_transpose X (cone_untranspose X h) ≈ h.
Proof. intros e d u; destruct u; reflexivity. Qed.

(* Display (3) at a fixed apex. *)
Program Definition cone_hom_iso (X : obj[Sets]) :
  @Isomorphism Sets (fobj[ConePresheaf F] X)
                    (fobj[Curried_CoHom Sets (cone_apex F)] X) := {|
  to := cone_transpose X; from := cone_untranspose X
|}.
Next Obligation. intros X; exact (cone_untranspose_round X). Qed.
Next Obligation. intros X; exact (cone_transpose_round X). Qed.

(* The book's parenthetical "(natural)", proved.  Both directions. *)
Lemma cone_transpose_natural (X Y : obj[Sets]) (g : X ~{Sets^op}~> Y) :
  fmap[Curried_CoHom Sets (cone_apex F)] g ∘ cone_transpose X
    ≈ cone_transpose Y ∘ fmap[ConePresheaf F] g.
Proof. intros p e d u; reflexivity. Qed.

Lemma cone_untranspose_natural (X Y : obj[Sets]) (g : X ~{Sets^op}~> Y) :
  fmap[ConePresheaf F] g ∘ cone_untranspose X
    ≈ cone_untranspose Y ∘ fmap[Curried_CoHom Sets (cone_apex F)] g.
Proof. intros h d e; simpl; reflexivity. Qed.

(* Display (3) as an isomorphism of functors of the apex. *)
Program Definition ConeSet_Natural_Iso :
  @Isomorphism ([Sets^op, Sets])
               (ConePresheaf F) (Curried_CoHom Sets (cone_apex F)) := {|
  to   := {| transform := cone_transpose |};
  from := {| transform := cone_untranspose |}
|}.
Next Obligation. intros X Y g; exact (cone_transpose_natural X Y g). Qed.
Next Obligation. intros X Y g p e d u; reflexivity. Qed.
Next Obligation. intros X Y g; exact (cone_untranspose_natural X Y g). Qed.
Next Obligation. intros X Y g h e d; simpl; reflexivity. Qed.
Next Obligation. intros X h e d u; destruct u; reflexivity. Qed.
Next Obligation. intros X p d e; reflexivity. Qed.

(* The components are the two named maps, on the nose. *)
Example coneset_natural_iso_to (X : obj[Sets]) :
  transform[to ConeSet_Natural_Iso] X = cone_transpose X := eq_refl.

Example coneset_natural_iso_from (X : obj[Sets]) :
  transform[from ConeSet_Natural_Iso] X = cone_untranspose X := eq_refl.

(* The cone presheaf is representable, represented by the cone set. *)
Program Definition ConeSet_Representable : Representable (ConePresheaf F) := {|
  repr_obj := (cone_apex F : obj[Sets^op]);
  represented := {| to := _; from := _ |}
|}.
Next Obligation. exact (from ConeSet_Natural_Iso). Defined.
Next Obligation. exact (to ConeSet_Natural_Iso). Defined.
Next Obligation. exact (iso_from_to ConeSet_Natural_Iso). Qed.
Next Obligation. exact (iso_to_from ConeSet_Natural_Iso). Qed.

End Remark.

(** ** The adjunction reading of the remark *)

(* The cone-set construction as a choice of limits of a fixed shape. *)
Definition ConeSet_HasLimitsOfShape (J : Category) :
  HasLimitsOfShape J Sets := fun F => cone_set_Limit F.

(* #353's adjunction, fed the cone-set oracle.  Stated outside the section
   below so that [J] is an explicit argument, as it is for the oracle. *)
Definition ConeSet_Diagonal_Limit_Adjunction (J : Category) :
  @Diagonal Sets J ⊣ LimitFunctor (ConeSet_HasLimitsOfShape J) :=
  Diagonal_Limit_Adjunction (ConeSet_HasLimitsOfShape J).

Section Adjunction.

Context {J : Category}.
Context (F : J ⟶ Sets).

(* Four strict readbacks: the adjoint's value, its leg, its backward
   transposition, and its counit. *)
Example coneset_lim_obj :
  lim_obj (ConeSet_HasLimitsOfShape J) F = cone_apex F := eq_refl.

Example coneset_lim_leg (j : J) :
  lim_leg (ConeSet_HasLimitsOfShape J) F j = cone_leg_at F j := eq_refl.

Example coneset_adj_from_is_untranspose (X : obj[Sets])
  (h : X ~{Sets}~> cone_apex F) (j : J) :
  transform[from (@adj _ _ _ _ (ConeSet_Diagonal_Limit_Adjunction J) X F) h] j
  = @vertex_map _ _ _ _ (cone_untranspose F X h) j := eq_refl.

(* This one discriminates nothing and is kept for the display: it IS
   Adjunction/Diagonal/Limit.v's [lim_counit_component_strict] at this
   oracle, and the same statement is accepted at an arbitrary
   [HasLimitsOfShape] and at the pre-existing [Sets] oracle.  What carries
   content is [coneset_lim_leg] above, which names [cone_leg_at]. *)
Example coneset_counit (j : J) :
  transform[lim_counit (ConeSet_HasLimitsOfShape J) F] j
  = cone_leg_at F j ∘ id := eq_refl.

(* The forward transposition, at the setoid grade.  Its [eq_refl] form is
   refused at CONVERSION and is pinned in the probe.  The header says what
   is and is not localized: the [ACone] round trip's leg family does return
   on the nose, but these two sides differ already at a point, so the
   refusal is not attributed to the coherence field. *)
Lemma coneset_adj_to_is_transpose (X : obj[Sets]) (p : ACone X F) :
  to (@adj _ _ _ _ (ConeSet_Diagonal_Limit_Adjunction J) X F)
     (snd (Cone_Natural_Transform F X) p)
  ≈ cone_transpose F X p.
Proof. intros e d u; reflexivity. Qed.

End Adjunction.

(** ** Equalizers: Awodey's concrete presentation *)

Section Equalizers.

Context {X Y : SetoidObject}.
Context (f g : X ~{Sets}~> Y).

(* The existing [HasEqualizers Sets]' apex is the compatible-family setoid
   over the walking parallel pair, and its leg is evaluation at [ParX]. *)
Example existing_apex_is_limit_obj :
  projT1 (@equalizer Sets Sets_HasEqualizers X Y f g)
  = Sets_limit_obj (APair f g) := eq_refl.

Example existing_leg_is_limit_leg :
  projT1 (projT2 (@equalizer Sets Sets_HasEqualizers X Y f g))
  = Sets_limit_leg (APair f g) ParX := eq_refl.

(* Awodey's [{x ∈ A | f x = g x}], as a sub-setoid. *)
Program Definition sets_eq_obj : SetoidObject := {|
  carrier   := { a : X & f a ≈ g a };
  is_setoid := {| equiv := fun p q => `1 p ≈ `1 q |}
|}.
Next Obligation. equivalence. Qed.

Program Definition sets_eq_incl : sets_eq_obj ~{Sets}~> X := {|
  morphism := fun p => `1 p
|}.
Next Obligation. intros p q Hpq; exact Hpq. Qed.

Program Definition sets_eq_desc {Z : SetoidObject} (h : Z ~{Sets}~> X)
  (Hh : f ∘ h ≈ g ∘ h) : Z ~{Sets}~> sets_eq_obj := {|
  morphism := fun z => (h z; Hh z)
|}.
Next Obligation. intros Z h Hh z z' Hz; simpl; now rewrite Hz. Qed.

(* "with unique factorization because the inclusion is monic". *)
Program Definition sets_IsEqualizer :
  IsEqualizer f g sets_eq_obj sets_eq_incl := {|
  fork_eq := _;
  eq_desc := fun Z h Hh => {| unique_obj := sets_eq_desc h Hh |}
|}.
Next Obligation. intros p; exact (`2 p). Qed.
Next Obligation. intros Z h Hh z; reflexivity. Qed.
Next Obligation. intros Z h Hh v Hv z; simpl; symmetry; exact (Hv z). Qed.

(* The existing instance, read as an elementary equalizer. *)
Definition existing_IsEqualizer :
  IsEqualizer f g (Sets_limit_obj (APair f g))
              (Sets_limit_leg (APair f g) ParX) :=
  projT2 (projT2 (@equalizer Sets Sets_HasEqualizers X Y f g)).

(* The gap between Awodey's presentation and the existing one is one
   application of [equalizer_unique].  The strict form is refused at
   CONVERSION and is pinned in the probe. *)
Definition concrete_vs_existing :
  @Isomorphism Sets sets_eq_obj (Sets_limit_obj (APair f g)) :=
  equalizer_unique f g sets_IsEqualizer existing_IsEqualizer.

End Equalizers.

(** ** Riehl's Karoubi instance *)

Section Karoubi.

Context {X : SetoidObject}.
Context (e : X ~{Sets}~> X).

(* Instance/Sets/Karoubi.v:41's fixed-point sub-setoid, recorded as the
   [(id, e)] equalizer the issue names.  No idempotency is required.  The
   carrier is spelled [e a ≈ a], so this order costs two [symmetry] steps
   MORE than [(e, id)] does; the third, in the uniqueness obligation, is
   needed at either order.  See the header. *)
Program Definition karoubi_med {Z : SetoidObject} (h : Z ~{Sets}~> X)
  (Hh : @id Sets X ∘ h ≈ e ∘ h) : Z ~{Sets}~> sets_split_obj e := {|
  morphism := fun z => (h z; _)
|}.
Next Obligation. intros Z h Hh z; simpl; symmetry; exact (Hh z). Qed.
Next Obligation. intros Z h Hh z z' Hz; simpl; now rewrite Hz. Qed.

Program Definition karoubi_IsEqualizer :
  IsEqualizer (@id Sets X) e (sets_split_obj e) (sets_split_s e) := {|
  fork_eq := _;
  eq_desc := fun Z h Hh => {| unique_obj := karoubi_med h Hh |}
|}.
Next Obligation. intros p; simpl; symmetry; exact (`2 p). Qed.
Next Obligation. intros Z h Hh z; reflexivity. Qed.
Next Obligation. intros Z h Hh v Hv z; simpl; symmetry; exact (Hv z). Qed.

End Karoubi.

(** ** Seven Sketches: the limit in coordinates *)

Section Tuple.

Context {G : Quiver}.
Context (D : Diagram G Sets).

(* Compatibility along the GENERATING EDGES -- the book's condition. *)
Definition tuple_compat (x : ∀ i : G, D i) : Type :=
  ∀ (i j : G) (e : edges i j), dedge D e (x i) ≈ x j.

(* The bridge, and the section's only new mathematical content: a family
   compatible on generators is compatible along every path.  Two smaller
   proofs sit below it -- [tuple_obj]'s setoid obligation and the
   [dpath_fmap] step inside [tuple_bwd]. *)
Lemma tuple_compat_paths (x : ∀ i : G, D i) (H : tuple_compat x)
  {i j : G} (p : tlist edges i j) : dpath D p (x i) ≈ x j.
Proof.
  induction p as [ | a b e p IH ]; simpl.
  - reflexivity.
  - rewrite <- IH; now rewrite (H _ _ e).
Qed.

(* What agrees on the nose. *)
Example tuple_fobj_strict (i : G) : fobj[FunctorOfDiagram D] i = D i
  := eq_refl.

Example tuple_inner_strict :
  Sets_iprod_obj (fun d : FreeOnQuiver G => fobj[FunctorOfDiagram D] d)
  = Sets_iprod_obj (fun i : G => D i) := eq_refl.

(* The book's set of tuples. *)
Program Definition tuple_obj : SetoidObject := {|
  carrier   := { x : Sets_iprod_obj (fun i : G => D i) & tuple_compat x };
  is_setoid := {| equiv := fun p q => `1 p ≈ `1 q |}
|}.
Next Obligation.
  constructor.
  - intros p i; reflexivity.
  - intros p q Hpq i; symmetry; exact (Hpq i).
  - intros p q r Hpq Hqr i; transitivity (`1 q i);
    [exact (Hpq i)|exact (Hqr i)].
Qed.

(* Forward: restrict the path condition to single edges. *)
Program Definition tuple_fwd :
  Sets_limit_obj (FunctorOfDiagram D) ~{Sets}~> tuple_obj := {|
  morphism := fun p => (`1 p ; fun i j e => _)
|}.
Next Obligation. intros p i j e; exact (`2 p i j (tlist_singleton e)). Defined.
Next Obligation. intros p q Hpq i; exact (Hpq i). Qed.

(* Backward: extend along paths.  The natural [rewrite <- (dpath_fmap D f)]
   is stuck on an unresolved [ProperProxy]; the explicit [transitivity]
   through [dpath] is what goes through. *)
Program Definition tuple_bwd :
  tuple_obj ~{Sets}~> Sets_limit_obj (FunctorOfDiagram D) := {|
  morphism := fun p => (`1 p ; fun i j f => _)
|}.
Next Obligation.
  intros p i j f; simpl in f.
  transitivity (dpath D f (`1 p i)).
  - symmetry; exact (dpath_fmap D f (`1 p i)).
  - exact (tuple_compat_paths (`1 p) (`2 p) f).
Defined.
Next Obligation. intros p q Hpq i; exact (Hpq i). Qed.

(* Theorem 3.95: the limit IS the set of compatible tuples. *)
Program Definition tuple_iso :
  @Isomorphism Sets (Sets_limit_obj (FunctorOfDiagram D)) tuple_obj := {|
  to := tuple_fwd; from := tuple_bwd
|}.
Next Obligation. intros p i; reflexivity. Qed.
Next Obligation. intros p i; reflexivity. Qed.

(* "with the coordinate projections as the legs". *)
Program Definition tuple_proj (i : G) : tuple_obj ~{Sets}~> D i := {|
  morphism := fun p => `1 p i
|}.
Next Obligation. intros i p q Hpq; exact (Hpq i). Qed.

Lemma tuple_proj_is_leg (i : G) :
  tuple_proj i ∘ to tuple_iso ≈ Sets_limit_leg (FunctorOfDiagram D) i.
Proof. intros p; reflexivity. Qed.

Lemma tuple_proj_is_leg_inv (i : G) :
  Sets_limit_leg (FunctorOfDiagram D) i ∘ from tuple_iso ≈ tuple_proj i.
Proof. intros p; reflexivity. Qed.

End Tuple.

(** ** Seven Sketches: presentation-independence *)

Section Presentation.

Context (G : Quiver).
Context (R : PathRel G).
Context (S : PresentedQuiver G R ⟶ Sets).

(* The restriction of S along the quotient projection. *)
Definition Srestr : FreeOnQuiver G ⟶ Sets := S ◯ PresentedQuiverProj G R.

(* The imposed equations touch neither the objects nor the compatibility
   predicate nor the carrier -- only the hom-setoid, which the limit
   carrier does not read. *)
Example pres_fobj_strict (i : G) : fobj[S] i = fobj[Srestr] i := eq_refl.

Example pres_compat_strict
  (x : Sets_iprod_obj (fun d : PresentedQuiver G R => fobj[S] d)) :
  Sets_limit_compatible S x = Sets_limit_compatible Srestr x := eq_refl.

Example pres_carrier_strict :
  Sets_limit_carrier S = Sets_limit_carrier Srestr := eq_refl.

Program Definition pres_fwd :
  Sets_limit_obj S ~{Sets}~> Sets_limit_obj Srestr := {|
  morphism := fun p => p
|}.
Next Obligation. intros p q Hpq i; exact (Hpq i). Qed.

Program Definition pres_bwd :
  Sets_limit_obj Srestr ~{Sets}~> Sets_limit_obj S := {|
  morphism := fun p => p
|}.
Next Obligation. intros p q Hpq i; exact (Hpq i). Qed.

(* Both legs are the identity on elements.  The OBJECT-level [eq_refl] is
   nevertheless refused; see the header, and the probe. *)
Program Definition pres_iso :
  @Isomorphism Sets (Sets_limit_obj S) (Sets_limit_obj Srestr) := {|
  to := pres_fwd; from := pres_bwd
|}.
Next Obligation. intros p i; reflexivity. Qed.
Next Obligation. intros p i; reflexivity. Qed.

Lemma pres_iso_legs (i : G) :
  Sets_limit_leg Srestr i ∘ to pres_iso ≈ Sets_limit_leg S i.
Proof. intros p; reflexivity. Qed.

Lemma pres_iso_legs_inv (i : G) :
  Sets_limit_leg S i ∘ from pres_iso ≈ Sets_limit_leg Srestr i.
Proof. intros p; reflexivity. Qed.

End Presentation.
