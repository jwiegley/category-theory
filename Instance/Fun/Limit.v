Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.

Generalizable All Variables.

(** * Pointwise limits in a functor category *)

(* Mac Lane §V.3 Theorem 1 and Corollary 1 (book pp. 115-116;
   maclane:V.3:thm1, maclane:V.3:cor1); Awodey §8.5 Proposition 8.7 and its
   Corollary (presheaf categories are complete, evaluation preserves
   limits); Riehl §3.4 Proposition 3.4.9 (limits in a functor category are
   pointwise, and evaluation preserves them).
   nLab: https://ncatlab.org/nlab/show/functor+category
         https://ncatlab.org/nlab/show/limit

   BACKGROUND.  A diagram D : J ⟶ [P, X] of functors has, at each object p
   of P, an evaluated diagram Eval p ◯ D : J ⟶ X.  When each of these has a
   limit in X, the limit apexes assemble into a functor P ⟶ X whose arrow
   part is the mediating morphism between adjacent pointwise limits — unique
   with that property — and the pointwise legs assemble into a limiting
   cone over D in [P, X]: limits in a functor category are computed
   pointwise.  Consequently a functor category into a complete category is
   complete, every presheaf category [C^op, Sets] in particular, and
   evaluation at any object preserves all limits.  Colimits are the dual
   statement over the opposite categories; they are #715's and are not
   written here.  Creation of limits along the discrete inclusion
   (Theorem 2) is Instance/Fun/Creation.v's (#426).

   STALE PREMISES, RE-MEASURED.
     - "There is no [Terminal] structure on [C, D]": Instance/Fun/Terminal.v:362
       [Functor_Category_Terminal] (an [#[export] Instance], #339) and :520
       [Fun_HasIndexedProducts] exist; Instance/Fun/Cartesian.v:111
       [Functor_Category_Cartesian] and Instance/Fun/Pullback.v:316
       [Fun_HasPullbacks] too.  What was absent is the GENERAL shape and any
       preservation statement for an evaluation functor (Instance/Fun/
       Terminal.v:307-309 named that gap; corrected in place here).
     - "no [Complete] inhabitant anywhere": a declaration sweep of the
       non-Test/ tree for constants concluding [@Complete] finds at least
       thirteen, unconditional witnesses and premise-carrying transformers
       together — Instance/Sets/Complete.v:196 [Sets_Complete], :464
       [ConeSet_Complete], Instance/Grp/Limit.v:691 [Grp_Complete],
       Construction/Arrow/Limit.v:426 [Arrow_Complete],
       Construction/Comma/Limit.v:247 [Comma_Complete],
       Construction/Product/Limit.v:620 [PiCat_Complete], [EM_Complete],
       [reflective_Complete] and more; #254 is closed, so Work item 3's
       blocker is discharged and [Presheaf_Complete] is built below.
     - "the evaluation functors do not exist": Adjunction/Diagonal/
       Connected.v:700 [EvalAt], and #424's Instance/Fun/Eval.v [Eval], which
       this file consumes — the dependency on #424 is real: routing through
       [EvalAt] would add 103 files to this file's closure against 2 for
       Eval.v (marginals over the shipped [Require] list; an earlier revision
       said 115, measured against a list without Instance/Sets/Complete.v).
     - Prose sites (Work item 4), all edited LINE-NEUTRALLY: Instance/Fun.v:
       101-104 (the issue says :101-105; :105-106 is a different clause, on
       cartesian closure, which Instance/Fun/Closed.v refutes and which is
       untouched), Instance/Fun/Cartesian.v:17-20 (the issue says :17-21)
       and :36 (now citing [Functor_Category_Terminal]), Structure/
       Complete.v:56-58 (the issue says :55-58; the monadic clause's own
       words at :58-60 are untouched — it is [EM_Complete]'s — though :58
       gained "from Sets"), the fourth site the issue misses,
       Structure/Cartesian/Product.v:34, and Instance/Fun/Terminal.v:298-299
       and :307-309 (that file's NOT DELIVERED list denied both the general
       theorem and any preservation statement; both corrected in place) and
       :100-106 (its "stated in PROSE in three places" framing, now that
       those places point here).  Instance/Fun.v's sentence keeps its
       colimit half, attributed to the nLab and #715.
     - Construction/Product/Limit.v:620's [PiCat_Complete] has term for term
       the same shape as [Functor_Category_Complete], with the projection in
       place of [Eval p]; it is an analogy, not an instance — [PiCat] is a
       dependent product of categories, not [[DiscreteCat I, X]], so neither
       derives from the other.  Its header records the same universe traps.

   WHAT IS DELIVERED (29 named constants plus 11 [Program] obligations,
   every one closed under the global context).
     (1) THE POINTWISE DATA.  Over [D : J ⟶ [P, X]] and [L : ∀ p, Limit (Eval
         p ◯ D)]: [plim_obj], [plim_alimit], [plim_leg], [plim_leg_coherence],
         and joint monicity of the legs ([plim_probe_cone],
         [plim_jointly_monic]).
     (2) THE ARROW PART.  [plim_cone_at f] (the limit at p as a cone over the
         diagram at q, legs [fmap[D j] f ∘ plim_leg p j]; coherence is the
         naturality of [fmap[D] g] followed by cone coherence), [plim_map],
         [plim_map_commutes], and Mac Lane's uniqueness [plim_map_unique].
     (3) THE LIMIT FUNCTOR.  [PointwiseLimit : P ⟶ X]: the three functor
         laws are one [plim_jointly_monic] each.
     (4) THE LIMITING CONE.  [plim_nat j : PointwiseLimit ⟹ D j],
         [PointwiseLimitCone : Cone D].
     (5) THEOREM 1.  [plim_comp_cone] (a cone in [P, X] evaluated at p),
         [plim_ump_map], [plim_ump_commutes], [plim_ump_nat] (natural by
         joint monicity), [PointwiseIsLimitCone : IsLimitCone
         PointwiseLimitCone] — uniqueness in [P, X] IS pointwise uniqueness,
         an equation of transformations reducing componentwise — and the
         issue's pinned [Functor_Category_pointwise_limit : Limit D].
         Readbacks at [eq_refl] (probe): the diagram at p, the object
         action, the leg components, the image cone's apex and legs, the
         mediator's components, the packaged limit's cone.
     (6) PRESERVATION (Riehl 3.4.9 (ii), Awodey 8.7's second clause).
         [Eval_pointwise_IsLimitCone p] — the image of the pointwise cone
         under [Eval p] is limiting with NO coercion, its apex and legs
         being the chosen limit cone's on the nose — and
         [Eval_PreservesLimitCone p : PreservesLimitCone D (Eval p)] for an
         ARBITRARY limiting cone, by [limitcone_transport] along [FCone_iso]
         of [limitcone_iso] (the construction alone gives only the
         canonical cone); [Eval_PreservesLimit] descends to the apex-only
         class.
     (7) COROLLARY 1.  [Fun_HasLimitsOfShape] in the unfolded form
         [(∀ F : J ⟶ X, Limit F) → ∀ D : J ⟶ [P, X], Limit D] — it ascribes
         at Adjunction/Diagonal/Limit.v's [HasLimitsOfShape] downstream
         (probe), and this file does not pay that import — and the issue's
         pinned [Functor_Category_Complete : Complete X → Complete [P, X]];
         [Eval_ContinuousFunctor], [Eval_PreservesAllLimits].  All four are
         ANNOTATED AT THE DEFINITION: written bare, each minimizes P's
         object universe onto its hom universe (probe N2 pins the bare form's
         refusal at [Constraint jo < jh] beside the annotated form's
         acceptance; a section-level [Universe] declaration does NOT lift it,
         measured).
     (8) PRESHEAVES (Awodey's Corollary, Work item 3).  [Presheaf_Complete C :
         Complete [C^op, Sets]] and [Presheaf_Eval_PreservesAllLimits C c]
         from Instance/Sets/Complete.v's [Sets_Complete]; the covariant twin
         [Fun_Sets_Complete].

   UNIVERSES (measured by [About] under [Set Printing Universes] on all 29
   constants).
     - The 22 constants of section [Pointwise] carry exactly four equations,
       [u0 = u2], [u0 = u4], [u0 = u6], [u2 = u4] over [J : Category@{u u0
       u0}], [P : Category@{u1 u2 u2}], [X : Category@{u3 u4 u4}]: J's hom
       = P's hom = X's hom = [P, X]'s hom, one level.  P-hom = X-hom is
       Instance/Fun.v's [Fun]; shape-hom = ambient-hom is Structure/Limit.v's
       [Limit] binder [{J : Category@{u0 u1 u1}} {C : Category@{u2 u1 u1}}],
       applied twice (once in [P, X], once in X) — probe N3 pins it: at a
       shape whose homs sit strictly below X's, the diagram and its [Cone]
       are accepted and its [Limit] is refused.  The OBJECT universes stay
       free (J's, P's and X's are three distinct levels in every block).
     - The four annotated corollaries carry exactly one equation, [jh = ch]
       ([Fun]'s), with [P : Category@{jo jh jh}] free in [jo] — e.g.
       [Functor_Category_Complete@{jo jh co ch u u0 u1 u2 u3 u4 u5} : ∀ {P :
       Category@{jo jh jh}} {X : Category@{co ch ch}}, Complete@{u u2 ch co}
       X → Complete@{u u2 jh u3} [P, X]] with [jo <= jh], [jo <= u3], [jh <
       u4], [co <= u3].
     - The three presheaf constants sit at a category with ONE level for
       objects, homs and proofs ([Presheaf_Complete] and [Fun_Sets_Complete]
       at [C : Category@{u0 u0 u0}] concluding [Complete@{u0 u0 u0 u}];
       [Presheaf_Eval_PreservesAllLimits] at [C : Category@{u2 u2 u2}]
       concluding [PreservesAllLimits]), inherited from [Sets_Complete@{u u0}
       : Complete@{u u u u0}] (its INDEX bullet records the same); no
       equation.
     - No word-bounded [Set], no [JMeq]/[EqdepFacts]/[eq_rect_r] bound in any
       block.

   COUNTS AND CONVENTIONS.
     - 29 [.glob] declaration heads (24 [def], 5 [prf]) plus 11 [Program]
       obligations the [.glob] cannot see ([plim_probe_cone] 1,
       [plim_cone_at] 1, [PointwiseLimit] 3, [plim_nat] 2,
       [PointwiseLimitCone] 1, [plim_comp_cone] 1, [plim_ump_nat] 2), all
       "Closed under the global context", zero [Axioms:] lines; the gate
       carries the 29 heads, fully qualified.  One [Defined]
       ([PointwiseIsLimitCone]), LOAD-BEARING: flipped to [Qed] the file
       compiles but the probe's mediator readback [p425_mediator] is
       refused.  Sixteen [Qed] tokens (five lemmas, eleven obligations).
     - Closure 37 files excluding self: Instance/Sets/Complete.v costs 12
       at the margin (the presheaf corollaries), Instance/Fun/Eval.v 2, the
       other eleven [Require]s 0 (an earlier revision also required
       Category.Theory.Isomorphism, unused; dropped).  No collision: each new
       name has 0 declaration hits elsewhere in the tree.
       Adjunction/Diagonal/Limit.v would add 25 files and is deliberately
       NOT required; Instance/Fun/Terminal.v would add 28 and is not
       compared against here (marginals over the shipped [Require] list; an
       earlier revision said 37 and 39, measured without
       Instance/Sets/Complete.v).
     - Test/ProbeFunLimit425.v carries 4 refutation commands (1 instrument +
       N1 CONVERSION + N2 UNIVERSE + N3 UNIVERSE), each stripped one at a
       time in a copy of the whole file; seven readbacks at [eq_refl]; the
       [HasLimitsOfShape] ascription and [LimitFunctor] on [P, X] as
       positive controls; guard coverage 19 identifier tokens inside the
       refutations / 16 also named outside, comments stripped, with three
       exhaustive exceptions (the keyword, the refuted declaration's name,
       the absent name); rename-simulated 6/6 ([FCone],
       [PointwiseLimitCone], [limit_cone], [Limit], [Eval],
       [Functor_Category_pointwise_limit], module paths excluded) with every
       first break on a positive line.  [make todo] grows by those 4 lines
       only (2222 → 2226), so the issue's "adds no new hits" box is not met
       as written; disclosed.
     - [Eval p] is parenthesised or applied inside a larger term throughout:
       bare at a definition-body head it parses as the [Eval … in]
       vernacular (Instance/Fun/Eval.v's header).

   NOT DELIVERED.
     - The colimit dual ([Cocomplete X → Cocomplete [P, X]], evaluation
       preserving colimits): #715's, superseding the issue's Work item 2
       clause; not one colimit line is written.
     - Creation of limits by evaluation or along the discrete inclusion
       (Theorem 2): Instance/Fun/Creation.v's (#426).
     - A [HasLimitsOfShape]-typed statement inside this file (the unfolded
       form is delivered; the class is imported only by the probe).
     - Any comparison of [Functor_Category_pointwise_limit] with
       Instance/Fun/Terminal.v's [Fun_iprod] or Instance/Fun/Cartesian.v's
       products at their shapes.
     - No edit to Instance/Fun/Eval.v, Structure/Limit.v, Structure/Limit/
       Preservation.v or Instance/Sets/Complete.v; the five prose edits are
       line-neutral and named above. *)

Section Pointwise.

Context {J P X : Category}.
Context (D : J ⟶ [P, X]).

(* The hypothesis of Mac Lane's Theorem 1: each evaluation of the diagram
   has a limit in X. *)
Context (L : ∀ p : P, Limit (Eval p ◯ D)).

(** ** The pointwise data *)

Definition plim_obj (p : P) : X := vertex_obj[@limit_cone _ _ _ (L p)].

Definition plim_alimit (p : P) : IsALimit (Eval p ◯ D) (plim_obj p) :=
  limit_is_alimit (L p).

Definition plim_leg (p : P) (j : J) : plim_obj p ~{X}~> fobj[D j] p :=
  limit_leg (plim_alimit p) j.

Lemma plim_leg_coherence (p : P) {i j : J} (g : i ~{J}~> j) :
  transform[fmap[D] g] p ∘ plim_leg p i ≈ plim_leg p j.
Proof. exact (limit_leg_coherence (plim_alimit p) g). Qed.

(* Two arrows into a pointwise limit that agree on every leg are equal:
   the legs are jointly monic. *)
Program Definition plim_probe_cone {q : P} {c : X} (u : c ~{X}~> plim_obj q) :
  Cone (Eval q ◯ D) := {|
  vertex_obj := c;
  coneFrom := {| vertex_map := fun j => plim_leg q j ∘ u |}
|}.
Next Obligation.
  rewrite comp_assoc.
  now rewrite plim_leg_coherence.
Qed.

Lemma plim_jointly_monic {q : P} {c : X} (u v : c ~{X}~> plim_obj q) :
  (∀ j : J, plim_leg q j ∘ u ≈ plim_leg q j ∘ v) → u ≈ v.
Proof.
  intro H.
  apply (limit_med_eq (plim_alimit q) (plim_probe_cone u) u v);
    intro x; [reflexivity | symmetry; apply H].
Qed.

(** ** The arrow part: the mediator between adjacent pointwise limits *)

(* An arrow f : p ~> q of P turns the limit at p into a cone over the
   diagram evaluated at q, with legs fmap[D j] f after the legs at p;
   coherence is the naturality of fmap[D] g followed by cone coherence. *)
Program Definition plim_cone_at {p q : P} (f : p ~{P}~> q) :
  Cone (Eval q ◯ D) := {|
  vertex_obj := plim_obj p;
  coneFrom := {| vertex_map := fun j => fmap[D j] f ∘ plim_leg p j |}
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite <- (naturality[fmap[D] f0] p q f).
  rewrite <- comp_assoc.
  now rewrite plim_leg_coherence.
Qed.

Definition plim_map {p q : P} (f : p ~{P}~> q) : plim_obj p ~{X}~> plim_obj q :=
  limit_med (plim_alimit q) (plim_cone_at f).

Lemma plim_map_commutes {p q : P} (f : p ~{P}~> q) (j : J) :
  plim_leg q j ∘ plim_map f ≈ fmap[D j] f ∘ plim_leg p j.
Proof. exact (limit_med_commutes (plim_alimit q) (plim_cone_at f) j). Qed.

(* Mac Lane's "unique": the arrow part is determined by its legs. *)
Lemma plim_map_unique {p q : P} (f : p ~{P}~> q)
  (u : plim_obj p ~{X}~> plim_obj q) :
  (∀ j : J, plim_leg q j ∘ u ≈ fmap[D j] f ∘ plim_leg p j) → plim_map f ≈ u.
Proof. exact (limit_med_unique (plim_alimit q) (plim_cone_at f) u). Qed.

(** ** The pointwise limit functor *)

Program Definition PointwiseLimit : P ⟶ X := {|
  fobj := plim_obj;
  fmap := fun _ _ f => plim_map f
|}.
Next Obligation.
  proper.
  apply plim_jointly_monic; intro j.
  rewrite !plim_map_commutes.
  now rewrite X0.
Qed.
Next Obligation.
  apply plim_jointly_monic; intro j.
  rewrite plim_map_commutes, id_right, fmap_id, id_left.
  reflexivity.
Qed.
Next Obligation.
  apply plim_jointly_monic; intro j.
  rewrite plim_map_commutes, comp_assoc, plim_map_commutes.
  rewrite <- comp_assoc, plim_map_commutes, comp_assoc.
  now rewrite fmap_comp.
Qed.

(** ** The limiting cone in [P, X] *)

Program Definition plim_nat (j : J) : PointwiseLimit ~{[P, X]}~> D j := {|
  transform := fun p => plim_leg p j
|}.
Next Obligation. symmetry; apply plim_map_commutes. Qed.
Next Obligation. apply plim_map_commutes. Qed.

Program Definition PointwiseLimitCone : Cone D := {|
  vertex_obj := PointwiseLimit;
  coneFrom := {| vertex_map := plim_nat |}
|}.
Next Obligation. apply plim_leg_coherence. Qed.

(** ** Theorem 1: the pointwise cone is limiting *)

Section Universal.

Context (M : Cone D).

(* A cone over D in [P, X], evaluated at p, is a cone over the evaluated
   diagram. *)
Program Definition plim_comp_cone (p : P) : Cone (Eval p ◯ D) := {|
  vertex_obj := fobj[vertex_obj[M]] p;
  coneFrom := {| vertex_map := fun j => transform[cone_leg M j] p |}
|}.
Next Obligation.
  pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ M) x y f) as Hc.
  simpl in Hc. apply Hc.
Qed.

Definition plim_ump_map (p : P) :
  fobj[vertex_obj[M]] p ~{X}~> plim_obj p :=
  limit_med (plim_alimit p) (plim_comp_cone p).

Lemma plim_ump_commutes (p : P) (j : J) :
  plim_leg p j ∘ plim_ump_map p ≈ transform[cone_leg M j] p.
Proof. exact (limit_med_commutes (plim_alimit p) (plim_comp_cone p) j). Qed.

(* The pointwise mediators are natural in p, by joint monicity. *)
Program Definition plim_ump_nat :
  vertex_obj[M] ~{[P, X]}~> PointwiseLimit := {|
  transform := plim_ump_map
|}.
Next Obligation.
  apply plim_jointly_monic; intro j.
  rewrite comp_assoc, plim_map_commutes.
  rewrite <- comp_assoc, plim_ump_commutes.
  rewrite comp_assoc, plim_ump_commutes.
  apply (naturality[cone_leg M j]).
Qed.
Next Obligation.
  symmetry.
  apply plim_jointly_monic; intro j.
  rewrite comp_assoc, plim_map_commutes.
  rewrite <- comp_assoc, plim_ump_commutes.
  rewrite comp_assoc, plim_ump_commutes.
  apply (naturality[cone_leg M j]).
Qed.

End Universal.

(* Uniqueness in [P, X] is pointwise uniqueness: an equation of
   transformations reduces componentwise. *)
Definition PointwiseIsLimitCone : IsLimitCone PointwiseLimitCone.
Proof.
  intro M.
  unshelve refine {| unique_obj := plim_ump_nat M |}.
  - intros j p; simpl.
    apply plim_ump_commutes.
  - intros v Hv p.
    apply (limit_med_unique (plim_alimit p) (plim_comp_cone M p)).
    intro j.
    exact (Hv j p).
Defined.

(* The issue's pinned name: the limit of D in [P, X]. *)
Definition Functor_Category_pointwise_limit : Limit D :=
  limitcone_limit PointwiseLimitCone PointwiseIsLimitCone.

(** ** Evaluation preserves the limit *)

(* The image of the pointwise cone under Eval p IS the chosen limit cone
   at p in apex and legs (readbacks in the probe), so it is limiting with
   no coercion. *)
Definition Eval_pointwise_IsLimitCone (p : P) :
  IsLimitCone (FCone (Eval p) PointwiseLimitCone) :=
  limit_limitcone (L p).

(* Any limiting cone over D, not only the canonical one, is sent to a
   limiting cone: transport along the essential uniqueness of limits. *)
Definition Eval_PreservesLimitCone (p : P) : PreservesLimitCone D (Eval p) :=
  fun N HN =>
    limitcone_transport
      (ConeIso_sym (FCone_iso (Eval p) (limitcone_iso HN PointwiseIsLimitCone)))
      (Eval_pointwise_IsLimitCone p).

Definition Eval_PreservesLimit (p : P) : PreservesLimit D (Eval p) :=
  PreservesLimitCone_PreservesLimit (Eval_PreservesLimitCone p).

End Pointwise.

(** ** Corollary 1: [P, X] has the limits X has, and is complete when X is *)

(* Both corollaries are annotated at the DEFINITION: written bare, they
   minimize P's object universe down onto its hom universe (measured; the
   probe pins the unannotated form's refusal at a strictly smaller object
   level and the annotated form's acceptance).  The [+] takes in the two
   levels [Functor_Category_pointwise_limit] leaks. *)
Definition Fun_HasLimitsOfShape@{jo jh co ch io u u0 u1 u2 u3 +}
  {J : Category@{io ch ch}} {P : Category@{jo jh jh}} {X : Category@{co ch ch}}
  (LX : ∀ F : J ⟶ X, Limit@{u io ch co} F) :
  ∀ D : J ⟶ [P, X], Limit@{u io ch u3} D :=
  fun D => Functor_Category_pointwise_limit D (fun p => LX (Eval p ◯ D)).

(* The issue's pinned name. *)
Definition Functor_Category_Complete@{jo jh co ch u u0 u1 u2 u3 +}
  {P : Category@{jo jh jh}} {X : Category@{co ch ch}}
  (HX : @Complete@{u u2 ch co} X) : @Complete@{u u2 jh u3} ([P, X]) :=
  fun J D => Functor_Category_pointwise_limit D (fun p => HX J (Eval p ◯ D)).

(** ** Evaluation is continuous when X is complete *)

(* Annotated at the definition for the same reason as the corollaries:
   written bare, both minimize P to one universe [Category@{u u u}]
   (measured). *)
Definition Eval_ContinuousFunctor@{jo jh co ch u u0 u1 u2 u3 +}
  {P : Category@{jo jh jh}} {X : Category@{co ch ch}}
  (HX : @Complete@{u u2 ch co} X) (p : P) : ContinuousFunctor (Eval p) :=
  fun J D => Eval_PreservesLimitCone D (fun q => HX J (Eval q ◯ D)) p.

Definition Eval_PreservesAllLimits@{jo jh co ch u u0 u1 u2 u3 +}
  {P : Category@{jo jh jh}} {X : Category@{co ch ch}}
  (HX : @Complete@{u u2 ch co} X) (p : P) : PreservesAllLimits (Eval p) :=
  Continuous_PreservesAllLimits (Eval_ContinuousFunctor HX p).

(** ** Presheaves: the concrete corollary *)

(* Awodey §8.5's Corollary: every presheaf category is complete, from
   Instance/Sets/Complete.v's [Sets_Complete]; and evaluation at any object
   preserves all limits (Proposition 8.7's second clause).  The covariant
   twin [Fun_Sets_Complete] is recorded too. *)
Definition Presheaf_Complete (C : Category) : @Complete ([C^op, Sets]) :=
  Functor_Category_Complete Sets_Complete.

Definition Presheaf_Eval_PreservesAllLimits (C : Category) (c : C) :
  PreservesAllLimits (@Eval (C^op) Sets c) :=
  @Eval_PreservesAllLimits (C^op) Sets Sets_Complete c.

Definition Fun_Sets_Complete (C : Category) : @Complete ([C, Sets]) :=
  Functor_Category_Complete Sets_Complete.
