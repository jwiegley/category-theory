Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.Continuity.
Require Import Category.Theory.Equivalence.Limit.

Generalizable All Variables.

(** * Limits in a full reflective subcategory *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
   Springer GTM 5, §IV.3, Exercise 7, printed p. 92, read from the page
   image:

     "7. If A is a full and reflective subcategory of B, prove that every
      functor S : J -> A with a limit in B has a limit in A."

   Book: Riehl, "Category Theory in Context", Dover 2016, §4.6,
   Proposition 4.6.14, printed p. 171, read from the page image:

     "If D <-> C is a reflective subcategory, then:
      (i) The inclusion D <-> C creates all limits."

   That proposition has a second clause, on colimits in D formed by
   applying the reflector to the colimit in C.  Its exact wording is not
   transcribed here: one of its words matches the case-insensitive pattern
   this repository's [make todo] target scans for, so quoting it in a
   source comment would add a spurious hit.  The clause itself is scoped
   out below; see the paragraph on issue #434.

   Book: Riehl, ibid., §5.6, Corollary 5.6.6, printed p. 211, read from
   the page image:

     "The inclusion of a reflective subcategory creates all limits.  In
      particular, a reflective subcategory of a complete category is
      complete."

   Its proof there reads, in full: "Proposition 5.3.3 proves that the
   inclusion of a reflective subcategory is monadic.  By Theorem 5.6.5(i),
   it follows that this inclusion creates all limits that exist in the
   codomain."

   So Mac Lane asks for INHERITANCE (a limit downstairs yields a limit
   upstairs) and Riehl sharpens the same fact to CREATION, which is
   strictly more: creation also pins the lift, identifies its image with
   the given cone, and reflects limit-ness.  Both readings are delivered,
   the second as the record and the first as a one-line consequence of it.

   DELIVERED, by exact name:

     [reflective_CreatesLimit K : CreatesLimit K (Incl C S)]
       -- Riehl 4.6.14(i)/5.6.6 at one shape and one diagram.

     [reflective_CreatesLimitsOfShape J], [reflective_CreatesAllLimits]
       -- the shape-quantified and fully quantified forms.

     [reflective_inherits_limits (L : Limit (Incl C S ◯ K)) : Limit K]
       -- Mac Lane §IV.3 Exercise 7 verbatim: a limit of the diagram read
          in the ambient category yields a limit of the diagram itself.

     [reflective_Complete : @Complete C -> @Complete (Sub C S)]
       -- Riehl's "in particular".

     [reflective_Incl_PreservesLimitCone K : PreservesLimitCone K (Incl C S)]
       -- the inclusion preserves the limits the subcategory already has,
          with NO completeness hypothesis, because it is a right adjoint.

   Everything is stated in the CONE-LEVEL vocabulary of
   Structure/Limit/Preservation.v ([IsLimitCone], [ConeIso],
   [PreservesLimitCone]); the apex-only [PreservesLimit] is known in this
   library to be insufficient for these purposes (the argument is at
   Construction/Comma/Limit.v:47-66, and Preservation.v:347-350 records
   that only one direction of the bridge holds).

   ** The route, and what is reused rather than re-derived

   Write I := Incl C S and let R be the reflection, so that
   [reflective_adj R : reflector R ⊣ I].

   (1) THE LIFT is [rapl_transposed_cone] (Adjunction/Continuity.v:126)
       instantiated at this adjunction.  That constant sits inside a
       section whose [Context (L : Limit G)] it never consumes, so -- as
       [About] reports at commit 35511442 -- its discharged type takes NO
       limit argument:

         rapl_transposed_cone : ∀ {C D} {F U}, F ⊣ U →
           ∀ {J} (G : J ⟶ C), Cone (U ◯ G) → Cone G

       Its apex is [F (vertex_obj[N])], here [reflector R vertex_obj[N]],
       and its legs are the inverse transposes of the given legs.  Both
       readbacks hold at [eq_refl] ([reflective_lift_apex],
       [reflective_lift_leg]), so no cone is rebuilt by hand.

   (2) THE COMPARISON ISOMORPHISM [I (reflector R L) ≅ L], for a LIMITING
       cone N with apex L, is the only place with proof content.  Its
       forward leg is the limit mediator [unique_obj (HN (FCone I (lift)))]
       and its backward leg is the unit of the reflection; the [ConeIso]
       leg condition is that mediator's own [unique_property], on the nose
       ([reflective_compare_leg] closes by [exact]).  The two inverse laws
       cost different things, and it is worth naming which is which:

         [reflective_compare_unit] (to ∘ η ≈ id) spends the UNIQUENESS
         clause of the limit N at the competing cone N itself: both
         [to ∘ η] and [id] mediate N through N, so they agree.  The
         computation that [to ∘ η] mediates is one associativity, the leg
         condition, [to_adj_unit] read backwards, and [from_adj_comp_law].

         [reflective_unit_compare] (η ∘ to ≈ id) spends FULLNESS.  This
         is one of exactly two places this file consumes it; the other is
         the reflection lemma of (3), which needs I full as well as
         faithful.  It is the only place it is spent BY HAND -- (3) hands
         it straight to a donor.  Fullness of I is
         [Full_Implies_Full_Functor C S (reflective_full R)]; its
         [prefmap] lifts η ∘ to to an arrow g of the subcategory, and then
         ⌊g⌋ ≈ fmap[I] g ∘ η ≈ η ∘ (to ∘ η) ≈ η ≈ ⌊id⌋ by the previous
         law, so g ≈ id by injectivity of ⌊-⌋ and η ∘ to ≈ fmap[I] id.

       Injectivity of ⌊-⌋ is [reflective_to_adj_inj], four tactic lines
       from [to_adj_comp_law] and [from_adj_respects].  The tree does carry
       this fact already, as [adj_to_inj] (Adjunction/Additive.v:266), but
       that file is not in this one's dependency closure and requiring it
       would drag the whole Ab-enrichment layer behind every consumer of
       reflective limits; restating it locally costs four tactic lines.

       [reflective_counit_iso] (Construction/Reflective.v:92) does NOT
       shorten this, and the reason is structural rather than one of
       opacity: that lemma is about an object OF THE SUBCATEGORY, whereas
       L here is an arbitrary object of C, so it does not apply.  (It is
       also closed with [Qed] while producing data, so nothing reduces
       through it; that is a second, independent obstruction, pinned in
       Test/ProbeReflectiveLimit373.v.)

   (3) REFLECTION is [ff_reflect_ump] (Theory/Equivalence/Limit.v:355,
       with [ff_reflects_limit] at :365) applied to the fullness and
       faithfulness of I, in exactly the packaging
       Theory/Equivalence/Creation.v:72 uses for an equivalence: the leg
       side condition is [fun x => reflexivity _] because [FCone]'s legs
       ARE the image legs ([FCone_leg], Preservation.v:323).  Faithfulness
       is [Incl_Faithful] (Construction/Subcategory.v:89), which holds for
       every subcategory whatsoever.

   Nothing in (1)-(3) is a re-derivation: the lift, the reflection lemma,
   the creation class and all its consequences are consumed by name.  What
   is NEW here is the comparison isomorphism of (2) and the assembly.

   ** Prior art, and three claims of issue #373 that are stale

   Measured in this file's worktree, whose base is commit 35511442, by
   the searches named:

   - The issue's donor line numbers have drifted.  [ff_reflects_limit] is
     Theory/Equivalence/Limit.v:365 (the issue says :401);
     [right_adjoint_preserves_limits] is Adjunction/Continuity.v:218 (the
     issue says :202); [equivalence_creates_limits] is
     Theory/Equivalence/Limit.v:450 (an appended note says :486).  Every
     line cited in this header was re-grepped at that commit.

   - The issue's first appended note says the tree has no general
     limit-creation predicate and that a reusable class is the real
     deliverable.  That premise is false: Structure/Limit/Creation.v
     declares [Class CreatesLimit] at :154 with the derived
     [creates_limiting] :163, [creates_lift_unique] :174,
     [creates_reflects_limits] :185, [creates_limit_lift] :191,
     [creation_preserves_limit] :205, [CreatesLimitsOfShape] :225,
     [CreatesAllLimits] :228, [creates_limits_Complete] :246,
     [creates_limits_continuous] :252, [CreatesLimit_compose] :366 and the
     strict variant [StrictlyCreatesLimit] :325.  Six files outside the
     declaring one already consume it (rg -l 'CreatesLimit\b' at 35511442
     returns seven: Structure/Limit/Creation itself,
     Structure/Limit/Constant, Structure/Limit/Components,
     Monad/Eilenberg/Moore/Limit, Construction/Comma/Creation,
     Functor/Hom/Limit, Theory/Equivalence/Creation).  This file CONSUMES
     that class and builds no lookalike.  The note's DEMAND -- creation,
     not merely inheritance -- is right, and is what is delivered.

   - The absence claims that do hold: the four reflective and localization
     files (Construction/Reflective.v, 115 lines;
     Construction/Reflective/Idempotent.v, 467;
     Construction/Localization.v, 290;
     Construction/Localization/Universal.v, 203) contain zero occurrences
     of [Limit] or [Complete]; Construction/Subcategory.v contains zero
     occurrences of [Limit], [Cone] or [Complete]; and
     rg -n 'reflective_inherits|inherits_limit|Reflective_Complete|
     reflective_complete' over '*.v' returns nothing.

   ** Riehl's monadic route, measured and not taken

   Riehl reaches 5.6.6 through monadicity, and the tree has most of the
   pieces: Construction/Reflective/Idempotent.v:198 gives
   [Reflective_IdempotentMonad R] for the monad [Incl C S ◯ reflector R],
   Monad/Eilenberg/Moore/Limit.v:399 gives [em_strict_lift] and the strict
   creation for [EM_Forget], Theory/Equivalence/Creation.v transports
   creation across an equivalence, and [CreatesLimit_compose] composes.
   The step that is missing is the join: Idempotent.v:464's
   [Idempotent_EM_Equivalence] is an equivalence for
   [Sub C MLocal_Subcategory] -- the full subcategory of objects at which
   the unit is invertible -- and NOT for the given S, and no equivalence
   [Sub C S ≃ Sub C MLocal_Subcategory] exists in tree, nor any transport
   of [CreatesLimit] along an equivalence of functors (both searched, zero
   hits).  Building that bridge is a separate piece of work; the direct
   route above needs none of it, so it is the route taken and Riehl's is
   cited rather than followed.

   ** The colimit half

   Clause (ii) of Proposition 4.6.14 -- colimits in the subcategory,
   obtained by applying the reflector -- is NOT proved here.  It belongs
   to issue #434 ("MacLane V.5: A full reflective subcategory of a
   cocomplete category is cocomplete"), whose module is
   Construction/Reflective/Colimit.v; that issue is open.  The ingredient
   it will want, [left_adjoint_PreservesColimitCocone]
   (Adjunction/Continuity.v:246), already exists.

   ** Strengths, strict first

   At [eq_refl]: the lift's apex and its legs; the comparison's forward
   leg IS the limit mediator and its backward leg IS the unit; the created
   [Limit]'s cone IS the lift and its apex IS the reflector applied to the
   apex downstairs.  Six [eq_refl] Examples in all.

   At [≈] only: the two routes
   to [PreservesLimitCone K I] -- [creation_preserves_limit] applied to
   this creation record, and [right_adjoint_PreservesLimitCone] applied to
   the reflection adjunction -- are NOT convertible, neither as terms nor
   at their produced mediators (both refuted at [eq_refl] and pinned in
   the probe).  They do agree on the mediator up to [≈]
   ([reflective_two_routes_agree]), and the argument is one uniqueness
   appeal, not a computation: the mediators are unique, so any two of them
   coincide.  Read from the two definitions, they are visibly different
   terms of one type -- [creation_preserves_limit]
   (Structure/Limit/Creation.v:205) transports limit-ness along a
   composite cone isomorphism assembled from [limitcone_iso],
   [FCone_iso] and [ConeIso_sym], while
   [right_adjoint_PreservesLimitCone] (Adjunction/Continuity.v:205) is
   [rapl_ump] at the cone repackaged as a [Limit].  That is a reading of
   the two sources, not an isolating experiment, and no single step is
   named as THE cause.

   ** Universes

   Measured with [About] under [Set Printing Universes] on all 24
   constants of this file.  Every one is over [C : Category@{u u0 u0}] --
   hom identified with proof -- and that identification sits in the
   BINDER, not in any constraint block: reading the blocks alone would
   report none of it.  It is inherited rather than introduced, and
   [Subcategory] alone already forces it -- [Subcategory@{u u0 u1 u2}]
   takes a [Category@{u u0 u0}] and has an EMPTY constraint block -- which
   the probe pins by rejecting [Subcategory Cu] at a category whose proof
   universe is declared strictly above its hom universe, with that
   category's own hom-set, identity and hom-setoid accepted at those very
   levels.

   The shape-indexed constants additionally bind [J : Category@{u7 u8 u8}]
   and carry, in the block, the equations [u0 = u2], [u0 = u8] and
   [u0 = u10]: C's hom-and-proof level, J's hom-and-proof level, the
   subcategory's [shom] universe and the target hom level of K all
   collapse to one.  The two further equations are [u4 = u11] and
   [u5 = u9], and each relates a level of [Reflective] to a level of
   [Sub] (read off the printed type, where [K] lands in
   [Sub@{u u0 u1 u2 u9 u10 u11} C S]): [u4] is [Reflective]'s second
   universe and [u11] is [Sub]'s seventh, the auxiliary level [Sub]
   declares strictly above C's hom level and which [Incl] carries as its
   sixth -- both are fresh levels, with [u0 < u4] and [u0 < u11] in the
   block; [u5] is [Reflective]'s third universe, one of the two levels
   its record sort [Type@{max(u3,u5)}] is at, and [u9] is the object
   universe of [Sub C S], its fifth and [Incl]'s fifth.  The J-with-C
   collapse is a DIFFERENT axis from the first, it is the cone
   vocabulary's, and it too is inherited: with J's hom level declared
   strictly below C's, [Cone F] is accepted while [cone_leg] and
   [IsLimitCone] are each rejected alone ("Cannot enforce vh = jh").
   [Functor] is NOT among them: [Ju ⟶ Cu] elaborates at those levels,
   and neither is [vertex_obj].  Nor are those two the only donors:
   [IsALimit], [Limit], [ConeIso] and [FCone] are each rejected alone at
   the same levels with the same message -- measured out of tree, NOT
   pinned, so the two the probe pins are a sample of the family and not
   an enumeration.  These are the same donor family
   Structure/Limit/Initial.v's header (:127-145) records for a RELATED
   collapse -- there the axis is the shape's own hom against its own
   proof, and [IsALimit] is a third donor there as it is here.  All three
   formability rejections and their controls are in the probe.

   No binder and no constraint block of any of the 24 constants contains
   [Set]: measured as zero occurrences of that token anywhere in the
   [About] output for all 24.  None of these identifications is claimed
   unavoidable.

   ** Not delivered

   - STRICT creation.  [StrictlyCreatesLimit] (Creation.v:325) is built on
     [StrictLift] (:288), whose [slift_eq] field demands
     [F (vertex_obj[slift_cone]) = vertex_obj[N]] at LEIBNIZ equality of
     objects of C.  The lift here has apex [I (reflector R L)], which is
     isomorphic to L but not equal to it -- that isomorphism is the whole
     content of (2) -- so the strict record is not reachable by this
     construction and is not attempted.  The probe pins the well-typed
     ascription that would assert it.
   - The colimit half, as above.
   - Any bridge to Idempotent.v's Eilenberg-Moore equivalence, as above.
   - Naturality of the comparison isomorphism in K, or in the cone.
   - Preservation or creation of limits by the REFLECTOR (it is a left
     adjoint; nothing here says anything about it).
   - Uniqueness of the created limit beyond what [creates_lift_unique]
     already gives generically.
   - A non-degenerate witness.  The probe's is at the empty shape (so no
     leg condition is exercised; [IsLimitCone] at shape [0] is
     terminality) and at an object already in the subcategory (the
     terminal group is torsion-free, so the reflection is inert up to
     isomorphism); it shows the assembly runs end to end and reduces,
     nothing more.
   - Nothing is registered as an [Instance].  [CreatesLimit] IS a [Class]
     (Creation.v:154), so [reflective_CreatesLimit] could be registered;
     it deliberately is not, since it would make instance resolution
     search for a [Reflective] structure on every subcategory it meets.
     [reflective_incl_adj] is likewise a plain [Definition], not an
     instance of [Adjunction]. *)

Section ReflectiveLimits.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).

Notation I := (Incl C S).

(* The reflection adjunction, under a short name.  Deliberately NOT an
   [Instance]: the transpose notations below name it explicitly. *)

Definition reflective_incl_adj : reflector R ⊣ I := reflective_adj R.

Notation "⌊ f ⌋" := (to   (@adj _ _ _ _ reflective_incl_adj _ _) f).
Notation "⌈ f ⌉" := (from (@adj _ _ _ _ reflective_incl_adj _ _) f).

(* Fullness of the inclusion, in the [Functor.Full] form the reflection
   lemma consumes.  [Construction.Subcategory.Full] (a property of the
   subcategory) and [Theory.Functor.Full] (a structure on a functor) are
   different notions sharing a short name, and both modules are imported
   here, so the result type is written [Functor.Full] qualified. *)

Definition reflective_Incl_Full : Functor.Full I :=
  Full_Implies_Full_Functor C S (reflective_full R).

(* Injectivity of the forward transpose.  [adj_to_inj]
   (Adjunction/Additive.v:266) is the same fact, in a module outside this
   file's closure. *)

Lemma reflective_to_adj_inj {x : C} {y : Sub C S}
  (f g : reflector R x ~{Sub C S}~> y) : ⌊f⌋ ≈ ⌊g⌋ → f ≈ g.
Proof.
  intro Hfg.
  rewrite <- (@to_adj_comp_law _ _ _ _ reflective_incl_adj _ _ f).
  rewrite <- (@to_adj_comp_law _ _ _ _ reflective_incl_adj _ _ g).
  now apply (@from_adj_respects _ _ _ _ reflective_incl_adj).
Qed.

Section Shape.

Context {J : Category}.
Context (K : J ⟶ Sub C S).

(** ** The lift *)

(* A cone over the diagram read in C, transposed across the reflection.
   Its apex is the reflector applied to the apex downstairs. *)

Definition reflective_lift (N : Cone (I ◯ K)) : Cone K :=
  rapl_transposed_cone reflective_incl_adj K N.

Example reflective_lift_apex (N : Cone (I ◯ K)) :
  vertex_obj[reflective_lift N] = reflector R vertex_obj[N] := eq_refl.

Example reflective_lift_leg (N : Cone (I ◯ K)) (x : J) :
  cone_leg (reflective_lift N) x = ⌈ cone_leg N x ⌉ := eq_refl.

(** ** The comparison isomorphism *)

Section Compare.

Context (N : Cone (I ◯ K)).
Context (HN : IsLimitCone N).

(* The mediator of the image of the lift through the limiting cone N. *)

Definition reflective_compare :
  I (reflector R vertex_obj[N]) ~{C}~> vertex_obj[N] :=
  unique_obj (HN (FCone I (reflective_lift N))).

Lemma reflective_compare_leg (x : J) :
  cone_leg N x ∘ reflective_compare ≈ fmap[I] ⌈ cone_leg N x ⌉.
Proof.
  exact (unique_property (HN (FCone I (reflective_lift N))) x).
Qed.

(* One inverse law, by the uniqueness clause of the limit N. *)

Lemma reflective_compare_unit :
  reflective_compare
    ∘ @unit _ _ (reflector R) I reflective_incl_adj vertex_obj[N]
    ≈ id[vertex_obj[N]].
Proof.
  pose proof (uniqueness (HN N)) as Hu.
  transitivity (unique_obj (HN N)).
  - symmetry.
    apply Hu.
    intro x.
    rewrite comp_assoc.
    rewrite reflective_compare_leg.
    rewrite <- (@to_adj_unit _ _ _ _ reflective_incl_adj _ _
                  (⌈ cone_leg N x ⌉)).
    apply (@from_adj_comp_law _ _ _ _ reflective_incl_adj).
  - apply Hu.
    intro x.
    apply id_right.
Qed.

(* The other inverse law, by fullness.  This is the one place fullness
   is spent BY HAND; the reflection lemma below spends it too, by handing
   it to [ff_reflect_ump]. *)

Lemma reflective_unit_compare :
  @unit _ _ (reflector R) I reflective_incl_adj vertex_obj[N]
    ∘ reflective_compare
    ≈ id[I (reflector R vertex_obj[N])].
Proof.
  pose (g := @prefmap _ _ I reflective_Incl_Full
               (reflector R vertex_obj[N]) (reflector R vertex_obj[N])
               (@unit _ _ (reflector R) I reflective_incl_adj
                  vertex_obj[N] ∘ reflective_compare)).
  assert (Hg : fmap[I] g
                 ≈ @unit _ _ (reflector R) I reflective_incl_adj
                     vertex_obj[N] ∘ reflective_compare)
    by exact (@fmap_sur _ _ I reflective_Incl_Full _ _ _).
  assert (Hid : g ≈ id).
  { apply reflective_to_adj_inj.
    rewrite (@to_adj_unit _ _ _ _ reflective_incl_adj _ _ g).
    rewrite Hg.
    rewrite <- comp_assoc.
    rewrite reflective_compare_unit.
    rewrite id_right.
    symmetry.
    rewrite (@to_adj_unit _ _ _ _ reflective_incl_adj _ _ id).
    rewrite fmap_id.
    now rewrite id_left. }
  rewrite <- Hg, Hid.
  apply fmap_id.
Qed.

Definition reflective_cone_iso :
  ConeIso (FCone I (reflective_lift N)) N :=
  ({| to          := reflective_compare
    ; from        := @unit _ _ (reflector R) I reflective_incl_adj
                       vertex_obj[N]
    ; iso_to_from := reflective_compare_unit
    ; iso_from_to := reflective_unit_compare |}
   ; reflective_compare_leg).

Example reflective_cone_iso_to :
  to `1 reflective_cone_iso = reflective_compare := eq_refl.

Example reflective_cone_iso_from :
  from `1 reflective_cone_iso
    = @unit _ _ (reflector R) I reflective_incl_adj vertex_obj[N]
  := eq_refl.

End Compare.

(** ** Reflection *)

(* Full and faithful functors reflect limiting cones.  The packaging is
   the one at Theory/Equivalence/Creation.v:72.  (That file's own comment
   at :69 cites [ff_reflect_ump] at Theory/Equivalence/Limit.v:391, which
   is stale -- it is :355; a defect in an untouched file, recorded here
   and not edited.) *)

Definition reflective_ReflectsLimitCone : ReflectsLimitCone K I :=
  fun M H =>
    @ff_reflect_ump (Sub C S) C I reflective_Incl_Full (Incl_Faithful C S)
      J K M (limitcone_isalimit H) (fun x => reflexivity _).

(** ** Riehl 4.6.14(i) / 5.6.6, at one diagram *)

(* Note that the lift ignores the limiting hypothesis: it is defined for
   every cone downstairs. *)

Definition reflective_CreatesLimit : CreatesLimit K I :=
  {| creates_lift      := fun N _ => reflective_lift N
   ; creates_lift_over := fun N HN => reflective_cone_iso N HN
   ; creates_reflect   := reflective_ReflectsLimitCone |}.

(** ** Mac Lane §IV.3 Exercise 7 *)

Definition reflective_inherits_limits (L : Limit (Incl C S ◯ K)) : Limit K :=
  creates_limit_lift reflective_CreatesLimit L.

Example reflective_inherits_limits_cone (L : Limit (Incl C S ◯ K)) :
  @limit_cone _ _ _ (reflective_inherits_limits L)
    = reflective_lift (@limit_cone _ _ _ L) := eq_refl.

Example reflective_inherits_limits_apex (L : Limit (Incl C S ◯ K)) :
  vertex_obj[@limit_cone _ _ _ (reflective_inherits_limits L)]
    = reflector R vertex_obj[@limit_cone _ _ _ L] := eq_refl.

(** ** The inclusion preserves limits, with no completeness hypothesis *)

Definition reflective_Incl_PreservesLimitCone : PreservesLimitCone K I :=
  right_adjoint_PreservesLimitCone reflective_incl_adj K.

(* The creation route and the right-adjoint route to the same statement
   agree on mediators up to [≈], by uniqueness of the mediator, and are
   not convertible (pinned in the probe). *)

Lemma reflective_two_routes_agree (L : Limit (I ◯ K))
  (M : Cone K) (HM : IsLimitCone M) (P : Cone (I ◯ K)) :
  unique_obj (creation_preserves_limit reflective_CreatesLimit L M HM P)
    ≈ unique_obj (reflective_Incl_PreservesLimitCone M HM P).
Proof using All.
  apply (uniqueness
           (creation_preserves_limit reflective_CreatesLimit L M HM P)).
  exact (unique_property (reflective_Incl_PreservesLimitCone M HM P)).
Qed.

End Shape.

(** ** The quantified forms, and Riehl's "in particular" *)

Definition reflective_CreatesLimitsOfShape (J : Category) :
  CreatesLimitsOfShape J I := fun K => reflective_CreatesLimit K.

Definition reflective_CreatesAllLimits : CreatesAllLimits I :=
  fun J K => reflective_CreatesLimit K.

Definition reflective_Complete (HC : @Complete C) : @Complete (Sub C S) :=
  creates_limits_Complete I HC reflective_CreatesAllLimits.

Definition reflective_Incl_continuous (HC : @Complete C) :
  ∀ (J : Category) (K : J ⟶ Sub C S), PreservesLimitCone K I :=
  creates_limits_continuous I HC reflective_CreatesAllLimits.

End ReflectiveLimits.
