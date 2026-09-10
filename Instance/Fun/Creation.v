Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Fun.Limit.

Generalizable All Variables.

(** * Pointwise limits as creation along the discrete inclusion *)

(* Mac Lane §V.3 Theorem 2 (book p. 116; maclane:V.3:thm2): precomposition
   with the inclusion of the discrete category |P| on the objects of P,
   [P, X] ⟶ [|P|, X], creates limits.  Riehl §3.4 Proposition 3.4.9 and
   Exercise 3.4.v (riehl:3.4:prop9): the evaluation functors jointly create
   limits — for the "strictly" of her statement see NOT DELIVERED.
   nLab: https://ncatlab.org/nlab/show/created+limit
         https://ncatlab.org/nlab/show/discrete+category

   BACKGROUND.  Theorem 1 (Instance/Fun/Limit.v, #425) computes the limit of
   a diagram D : J ⟶ [P, X] pointwise, from limits of the evaluated diagrams
   Eval p ◯ D.  Theorem 2 restates this as a creation property: restricting
   a functor P ⟶ X to the discrete category |P| on its objects forgets the
   arrow part and keeps the object-indexed family, and a diagram of functors
   has a limit exactly when its diagram of families does — the pointwise
   limits assemble into the unique lift, and a cone upstairs whose image is
   limiting is limiting.  Riehl reads the same content off the family of
   evaluation functors: they jointly create limits.  Both statements are
   TRANSPORTS of Theorem 1, not parallel proofs (Work item 3): the
   reflection clause is [limitcone_transport] of #425's
   [PointwiseIsLimitCone] along an isomorphism of cones with identity
   components, and every lift IS #425's pointwise cone.

   STALE PREMISES, RE-MEASURED.
     - "The creation vocabulary is itself absent": false since #406.
       Structure/Limit/Creation.v has [CreatesLimit] (:154; [creates_lift],
       [creates_lift_over], [creates_reflect], with Mac Lane's limiting
       clause [creates_limiting] :163 and uniqueness [creates_lift_unique]
       :174 derived), [creates_limit_lift] :191, [CreatesAllLimits] :228,
       [creates_limits_Complete] :246, [creates_limits_continuous] :252,
       Riehl's [StrictLift] :288 / [StrictlyCreatesLimit] :325 with
       [self_lift] :314, and [JointlyCreateLimit] :458 (her Exercise 3.4.v).
       Structure/Limit.v's INDEX bullet records them.
     - "No discrete subcategory on the objects of a category and no
       inclusion functor": TRUE as stated ('discrete subcategory' has 0 hits
       in the tree; 'discrete inclusion' 2, both forward references in
       Instance/Fun/Limit.v), but the ingredient is richer than the issue
       says: Structure/Limit/Comparison.v:535 has the ANNOTATED
       discrete-diagram functor [DiscreteCat_Functor'@{o h p uo uh up +}],
       and Instance/Fun/Discrete.v:234 has [Fun_Discrete_PiCat : [DiscreteCat
       A, B] ≅[Cat] PiCat (fun _ => B)], the "C^{ob A} ≅ ∏_{ob A} C" of the
       Riehl note.  That bridge is Set-PINNED in the target (its :202 uses
       Instance/Discrete.v:59's unannotated [DiscreteCat_Functor]; at a
       general X the application is refused with "Cannot enforce Set = …"),
       so Riehl's route through Construction/Product/Limit.v:603's
       [PiCat_JointlyCreateLimit] is NOT usable here and the reflection is
       proved directly.
     - "Theory/Kan/Extension.v:127 ([Induced])": the definition is :131 (:127
       is a comment line); that no limit property of it existed is true
       (Functor/Construction/Postcompose.v:313 says so in terms).
     - The Riehl note's "no evaluation functor out of a functor category at
       all" and "ls Instance/Fun/ contains exactly one file" are false:
       #424's [Eval] (Instance/Fun/Eval.v) and Adjunction/Diagonal/
       Connected.v:700's [EvalAt] exist; fourteen files besides this one.

   WHAT IS DELIVERED (34 named constants plus 9 [Program] obligations, every
   one closed under the global context).
     (1) THE INCLUSION AND THE RESTRICTION.  [ObjCat : Category@{jo jh jh} :=
         DiscreteCat (obj[P])] at P's own object and hom levels; [DiscInc :
         ObjCat ⟶ P] through the annotated [DiscreteCat_Functor']
         (Instance/Discrete.v's unannotated [DiscreteCat_Functor]
         instantiates [DiscreteCat@{u Set Set}] and would pin P's hom and
         proof levels to [Set] — Structure/Limit/Comparison.v's note above
         its :535 — and is left as it is); [Res : [P, X] ⟶ [ObjCat, X] :=
         Induced DiscInc], the theorem's X^i.  Readbacks at [eq_refl]:
         [res_obj], [res_obj_at], [res_map], and [eval_res_obj]/
         [eval_res_map] — evaluating after restricting IS evaluating, in
         both functor fields.
     (2) REFLECTION (the new content; #425 has only the converse,
         [Eval_PreservesLimitCone], which takes [L]).  For [M : Cone D] with
         every [FCone (Eval p) M] limiting: [ptw_of_cone] (the pointwise
         limits M's evaluations provide), [ptw_apex_readback] and
         [ptw_leg_readback] (the assembled pointwise cone has M's apex and
         M's legs objectwise on the nose), [ptw_map_is_fmap] (the mediator
         between adjacent pointwise limits is M's own arrow action, by
         [plim_map_unique]), [ptw_apex_iso] (an isomorphism in [P, X] whose
         components are identities), [ptw_cone_iso : ConeIso M
         (PointwiseLimitCone D _)], and [Fun_pointwise_reflect : IsLimitCone
         M] := [limitcone_transport] of [PointwiseIsLimitCone] along it.
     (3) JOINT CREATION BY THE EVALUATIONS (Riehl Exercise 3.4.v).
         [ev_family p := Eval p], [ev_lift] (#425's pointwise cone assembled
         from the given family of limiting cones), [ev_lift_apex] and
         [ev_lift_leg] at [eq_refl], [ev_lift_over] (a [ConeIso] with
         [iso_id]), and [Fun_Eval_JointlyCreateLimit : JointlyCreateLimit D
         ev_family].  The image of the lift under [Eval p] is the given cone
         in apex and legs on the nose; the cone RECORDS do not convert, the
         coherence field being a rebuilt proof (probe N1).
     (4) CREATION ALONG THE RESTRICTION (Theorem 2), UNDER THE HYPOTHESIS
         [L : ∀ p, Limit (Eval p ◯ D)].  [res_comp_cone] (a cone over
         [Res ◯ D] evaluated at p), [res_ump_nat] (the mediator into a cone
         downstairs, componentwise the pointwise mediator; naturality over
         the discrete shape is discharged by the obligation tactic),
         [Res_preserves : IsLimitCone (FCone Res M)] for M with limiting
         evaluations, [res_coneiso_at] (an isomorphism of cones downstairs
         restricts to one at each object), [Res_CreatesLimit L : CreatesLimit
         D Res] — [creates_lift] the pointwise cone, [creates_lift_over] by
         [limitcone_iso], [creates_reflect] by [Fun_pointwise_reflect] after
         transporting along [res_coneiso_at] — its alias under the issue's
         name [discrete_inclusion_creates_limits] (ANNOTATED; see
         UNIVERSES), [res_limit L : Limit (Res ◯ D)], and [creation_apex]/
         [creation_leg] at [eq_refl]: the limit [creates_limit_lift] derives
         IS #425's [Functor_Category_pointwise_limit] in apex and legs.
         WHY THE HYPOTHESIS STAYS.  [creates_lift] must turn ONE limiting
         cone downstairs into a cone upstairs, i.e. read the components of a
         limiting cone in [|P|, X] as limiting cones in X.  Mac Lane does so
         silently (limits in a product of categories are computed in each
         factor); the constructive proof patches the apex family at one
         index — [fun q => if q = p then c else N q] — and so needs decidable
         equality on [obj P].  The tree made the same call before:
         Construction/Product/Limit.v ships [Fst_PreservesLimitCone]/
         [Snd_PreservesLimitCone] (:293, :306) for the BINARY product (index
         [bool]) and, for [PiCat] at a general index type, only [pi_reflect]
         and [PiCat_JointlyCreateLimit] — no single-projection preservation
         — and #425's [Eval_PreservesLimitCone] takes [L] for the same
         reason.  A hypothesis-free [CreatesLimit D Res] over Construction/
         Quotient.v:163's [ObjDecEq P] is a follow-on, not written here.
     (5) COROLLARIES.  [Res_CreatesAllLimits (HX : Complete X)],
         [Res_Complete : Complete [P, X]] — completeness of [P, X] once more,
         now as an instance of Structure/Limit/Creation.v's general
         [creates_limits_Complete] (creation plus completeness of [|P|, X],
         the latter #425's [Functor_Category_Complete] at the discrete
         shape) — and [Res_continuous : PreservesLimitCone D Res] through
         [creates_limits_continuous] (Mac Lane §V.4 Theorem 2's first half).
     (6) STRICTNESS.  [strict_self : StrictLift D Res (FCone Res M) :=
         self_lift M]: every cone upstairs strictly lifts its own image.
         Riehl's "strictly creates" (Definition 3.4.7; [StrictlyCreatesLimit],
         whose [slift_eq] is an [eq] of apexes) would need the canonical
         lift's image EQUAL to an arbitrary given cone's apex, an [eq]
         between functor records [DiscreteCat (obj P) ⟶ X] (probe N3 pins
         the refusal; N2 pins that a restricted functor is not even the
         discrete functor on its own object map — the arrow fields differ).

   UNIVERSES (measured by [About] under [Set Printing Universes] on all 34
   constants).
     - [Res@{jo jh co ch u u0 u1}] carries exactly one equation, [jh = ch]
       ([Fun]'s), and leaves P's OBJECT level free: at a shape whose objects
       sit strictly ABOVE its homs ([Constraint smallh < bigo] in the probe's
       section Wide) [ObjCat Pw], [Res Pw Xw] and the type [[Pw, Xw] ⟶ [Pw,
       Xw]] are all accepted.  Seven constants share this freedom: [ObjCat],
       [DiscInc], [Res], [res_obj], [res_obj_at], [res_map], [strict_self].
     - The other 27 constants — every one whose statement mentions [Eval] —
       inherit [jo <= jh] (P's objects ≤ P's homs; [u1 <= u2] or [u <= u0]
       in their blocks).  The FIRST CARRIER is the type [[P, X] ⟶ X] itself,
       not anything in this file or in #424's: [Fun]'s hom universe (a
       natural transformation quantifies over P's objects) sits above jo,
       and [Functor] identifies source and target hom universes, so a
       functor [P, X] ⟶ X forces jo ≤ ch = jh.  Probe N5 refuses the bare
       type [[Pw, Xw] ⟶ Xw] with "Cannot enforce smallh = … because smallh <
       bigo"; N6 refuses [@Eval Pw Xw]; N4 refuses #425's
       [Functor_Category_Complete Pw Xw].  [Res] is more universe-general
       than the theorem it serves.
     - The 20 section constants with J in context (PointwiseReflect,
       JointCreation, ResCreation) carry #425's four equations [u0 = u2],
       [u0 = u4], [u0 = u6], [u2 = u4] over [J : Category@{u u0 u0}], [P :
       Category@{u1 u2 u2}], [X : Category@{u3 u4 u4}]: J's hom = P's hom =
       X's hom = [P, X]'s hom.  The nine constants over [{P X}] alone
       ([eval_res_obj], [eval_res_map], [res_obj], [res_obj_at], [res_map],
       [Res_CreatesAllLimits], [Res_Complete], [Res_continuous],
       [strict_self]) carry [u0 = u2] only; [ev_family] [u2 = u4] only;
       [ObjCat] and [DiscInc] none.  The three corollaries and [strict_self],
       bare top-level definitions over [{P X : Category}], keep P's object
       level distinct from its hom level ([u <= u0], never [u = u0]).
     - [discrete_inclusion_creates_limits] is ANNOTATED AT THE DEFINITION
       ([@{io jo co h +}], one hom level for J, P and X, which the four
       equations identify anyway): written bare over [{J P X : Category}],
       the alias minimized P's object universe onto its hom universe AND J's
       hom onto it ([{J : Category@{u2 u3 u3}} {P : Category@{u3 u3 u3}}],
       measured) — Instance/Fun/Limit.v's trap, now on a [:=] alias.
       Annotated it carries [jo <= h] and no equation.
     - STDLIB BOUNDS, absent from Instance/Fun/Limit.v, enter here through
       [DiscreteCat]: the 21 constants whose statements mention [ObjCat] or
       [Res] carry [jo <= eq.u0], [jo <= Logic_lemmas.equality.u0], [jh <=
       eq_ind.u0] and [jh <= eq_ind_r.u0] (first carrier [ObjCat], from
       [DiscreteCat]'s equality homs) and, all but [ObjCat], also [jh <=
       eq_rect_r.u1], [jh <= EqdepFacts.eq_sigT_sig_eq.u2] and [JMeq.u0 <=
       JMeq.u1] (first carrier [DiscInc], from [DiscreteCat_Functor']'s
       [match] on an equality).  The 13 constants of PointwiseReflect and
       JointCreation carry none.  No word-bounded [Set] in any block.

   COUNTS AND CONVENTIONS.
     - 34 [.glob] declaration heads (33 [def], 1 [prf]) plus 9 [Program]
       obligations the [.glob] cannot see ([ptw_apex_iso] 6, [res_comp_cone]
       1, [res_ump_nat] 2), all "Closed under the global context", zero
       [Axioms:] lines; the gate carries the 34 heads, fully qualified.
     - Six [Defined] ([ptw_cone_iso], [ev_lift_over],
       [Fun_Eval_JointlyCreateLimit], [Res_preserves], [res_coneiso_at],
       [Res_CreatesLimit]), each flipped to [Qed] alone in a copy of the
       file: only [Res_CreatesLimit] is LOAD-BEARING (the [creation_apex]
       readback is refused); the other five compile with the probe unchanged
       and stay transparent because their conclusions are data (isomorphisms
       of cones, a lift, a mediator).  Seven [Qed] tokens outside this
       header (one lemma, six obligations; the other three obligations are
       discharged by the obligation tactic).
     - Closure 52 files excluding self: Structure/Limit/Comparison.v costs
       11 at the margin (it is required for [DiscreteCat_Functor'] alone),
       Instance/Fun/Limit.v 9, Structure/Limit/Creation.v 1, Theory/Kan/
       Extension.v 1, the other twelve [Require]s 0.  Moving
       [DiscreteCat_Functor'] into Instance/Discrete.v would remove those 11
       and give its two consumers (Comparison.v and this file) one source;
       surfaced for the maintainer, not done.  Zero name collisions: each of
       the 34 names has 0 declaration hits elsewhere in the tree.
     - Test/ProbeFunCreation426.v mirrors the [Require] list and carries 7
       refutation commands (1 instrument + N1, N2, N3 CONVERSION + N4, N5, N6
       UNIVERSE), each stripped one at a time in a copy of the whole file,
       each beside its accepted controls; guard coverage 32 identifier tokens
       inside the refutations / 26 also named outside, comments stripped,
       with six exhaustive exceptions (the keyword, a binder, the three
       refuted declarations' names, the absent name); rename-simulated 13/13
       ([Res], [ObjCat], [ev_lift], [PointwiseLimit],
       [Functor_Category_Complete], [Res_CreatesLimit], [FCone],
       [DiscreteCat_Functor'], [Eval], [strict_self], [self_lift],
       [plim_obj], [Complete]; module paths excluded), every first break on
       a positive line.  [make todo] grows by those 7 lines only (2226 →
       2233), so the issue's "adds no new hits" box is not met as written;
       disclosed.
     - [(Eval p)] is parenthesised or applied inside a larger term
       throughout (Instance/Fun/Eval.v's header: bare at a definition-body
       head it parses as the [Eval … in] vernacular).
     - Two forward references in Instance/Fun/Limit.v (:38, :182) now name
       this file; line-neutral.

   NOT DELIVERED.
     - The COLIMIT half (Riehl: [ev] creates colimits too — the Riehl box of
       the issue): #715's; not one colimit line is written.
     - Riehl's STRICT creation ([StrictlyCreatesLimit]): see (6) and probes
       N2/N3.
     - A hypothesis-free [CreatesLimit D Res] (decidable object equality on
       P would give it; see (4)).
     - Riehl's route through [Fun_Discrete_PiCat] and
       [PiCat_JointlyCreateLimit] (Set-pinned bridge; see STALE PREMISES).
     - No edit to Instance/Discrete.v, Structure/Limit/Comparison.v,
       Structure/Limit/Creation.v, Theory/Kan/Extension.v or Instance/Fun/
       Discrete.v. *)

(** ** The object-discrete inclusion and the restriction functor *)

Section Restriction.

Universe jo jh co ch.

Context {P : Category@{jo jh jh}} {X : Category@{co ch ch}}.

(* |P|: the discrete category on the objects of P. *)
Definition ObjCat : Category@{jo jh jh} := DiscreteCat@{jo jh jh} (obj[P]).

(* The inclusion |P| ⟶ P, through Structure/Limit/Comparison.v's annotated
   discrete-diagram functor (Instance/Discrete.v's unannotated one pins the
   target's hom and proof levels to [Set]). *)
Definition DiscInc : ObjCat ⟶ P := DiscreteCat_Functor' (fun p : P => p).

(* Restriction along the inclusion: precomposition, Theory/Kan/Extension.v's
   [Induced]. *)
Definition Res : [P, X] ⟶ [ObjCat, X] := @Induced ObjCat P DiscInc X.

End Restriction.

Section Readbacks.

Context {P X : Category}.

Definition res_obj (H : [P, X]) : fobj[@Res P X] H = H ◯ DiscInc := eq_refl.

Definition res_obj_at (H : [P, X]) (p : P) :
  fobj[fobj[@Res P X] H] p = fobj[H] p := eq_refl.

Definition res_map (H K : [P, X]) (s : H ~{[P, X]}~> K) (p : P) :
  transform[fmap[@Res P X] s] p = transform[s] p := eq_refl.

(* Evaluating after restricting IS evaluating, in both data fields. *)
Definition eval_res_obj (p : P) (H : [P, X]) :
  fobj[(@Eval ObjCat X p) ◯ (@Res P X)] H = fobj[@Eval P X p] H := eq_refl.

Definition eval_res_map (p : P) (H K : [P, X]) (s : H ~{[P, X]}~> K) :
  fmap[(@Eval ObjCat X p) ◯ (@Res P X)] s = fmap[@Eval P X p] s := eq_refl.

End Readbacks.

(** ** Reflection: a cone whose every evaluation is limiting is limiting *)

Section PointwiseReflect.

Context {J P X : Category}.
Context (D : J ⟶ [P, X]).

(* From a cone M in [P, X] all of whose evaluations are limiting, the
   pointwise limit data #425's construction consumes. *)
Definition ptw_of_cone (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) (p : P) : Limit (Eval p ◯ D) :=
  limitcone_limit (FCone (Eval p) M) (H p).

(* The assembled pointwise cone has M's apex and M's legs, objectwise on
   the nose. *)
Definition ptw_apex_readback (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) (p : P) :
  fobj[PointwiseLimit D (ptw_of_cone M H)] p = fobj[vertex_obj[M]] p := eq_refl.

Definition ptw_leg_readback (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) (p : P) (j : J) :
  transform[cone_leg (PointwiseLimitCone D (ptw_of_cone M H)) j] p
    = transform[cone_leg M j] p := eq_refl.

(* The mediator between adjacent pointwise limits IS M's own arrow action,
   by the uniqueness of the arrow part. *)
Lemma ptw_map_is_fmap (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) {x y : P} (f : x ~{P}~> y) :
  plim_map D (ptw_of_cone M H) f ≈ fmap[vertex_obj[M]] f.
Proof.
  apply (plim_map_unique D (ptw_of_cone M H) f).
  intro j.
  symmetry; exact (naturality[cone_leg M j] _ _ f).
Qed.

(* ... so the two cones are isomorphic with IDENTITY components. *)
Program Definition ptw_apex_iso (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) :
  @Isomorphism ([P, X]) (vertex_obj[M]) (PointwiseLimit D (ptw_of_cone M H)) := {|
  to   := {| transform := fun p => id |};
  from := {| transform := fun p => id |}
|}.
Next Obligation.
  rewrite id_left, id_right.
  now rewrite ptw_map_is_fmap.
Qed.
Next Obligation.
  rewrite id_left, id_right.
  now rewrite ptw_map_is_fmap.
Qed.
Next Obligation.
  rewrite id_left, id_right.
  now rewrite ptw_map_is_fmap.
Qed.
Next Obligation.
  rewrite id_left, id_right.
  now rewrite ptw_map_is_fmap.
Qed.
Next Obligation. rewrite ptw_map_is_fmap; cat. Qed.

Definition ptw_cone_iso (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) :
  ConeIso M (PointwiseLimitCone D (ptw_of_cone M H)).
Proof.
  exists (ptw_apex_iso M H).
  intros j p; simpl.
  apply id_right.
Defined.

(* THE REFLECTION — Theorem 1 reformulated: a transport of #425's
   [PointwiseIsLimitCone], not a parallel proof. *)
Definition Fun_pointwise_reflect (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) : IsLimitCone M :=
  limitcone_transport (ConeIso_sym (ptw_cone_iso M H))
    (PointwiseIsLimitCone D (ptw_of_cone M H)).

End PointwiseReflect.

(** ** The family of evaluations jointly creates limits (Riehl Ex 3.4.v) *)

Section JointCreation.

Context {J P X : Category}.
Context (D : J ⟶ [P, X]).

Definition ev_family (p : obj[P]) : [P, X] ⟶ X := (Eval p).

(* The lift is #425's pointwise cone, assembled from the given family. *)
Definition ev_lift (N : ∀ p : obj[P], Cone (Eval p ◯ D))
  (HN : ∀ p : obj[P], IsLimitCone (N p)) : Cone D :=
  PointwiseLimitCone D (fun p => limitcone_limit (N p) (HN p)).

(* The image of the lift under [Eval p] is the given cone in APEX and LEGS
   on the nose; the whole records do not convert (probe). *)
Definition ev_lift_apex (N : ∀ p : obj[P], Cone (Eval p ◯ D))
  (HN : ∀ p : obj[P], IsLimitCone (N p)) (p : obj[P]) :
  vertex_obj[FCone (Eval p) (ev_lift N HN)] = vertex_obj[N p] := eq_refl.

Definition ev_lift_leg (N : ∀ p : obj[P], Cone (Eval p ◯ D))
  (HN : ∀ p : obj[P], IsLimitCone (N p)) (p : obj[P]) (x : J) :
  cone_leg (FCone (Eval p) (ev_lift N HN)) x = cone_leg (N p) x := eq_refl.

Definition ev_lift_over (N : ∀ p : obj[P], Cone (Eval p ◯ D))
  (HN : ∀ p : obj[P], IsLimitCone (N p)) (p : obj[P]) :
  ConeIso (FCone (Eval p) (ev_lift N HN)) (N p).
Proof.
  exists iso_id.
  intro x; simpl; apply id_right.
Defined.

Definition Fun_Eval_JointlyCreateLimit : JointlyCreateLimit D ev_family.
Proof.
  unshelve refine {| jcreates_lift := ev_lift |}.
  - exact ev_lift_over.
  - exact (Fun_pointwise_reflect D).
Defined.

End JointCreation.

(** ** Creation along the restriction functor *)

Section ResCreation.

Context {J P X : Category}.
Context (D : J ⟶ [P, X]).

(* A cone over [Res ◯ D] in [|P|, X], evaluated at an object p. *)
Program Definition res_comp_cone (N : Cone (@Res P X ◯ D)) (p : P) :
  Cone (Eval p ◯ D) := {|
  vertex_obj := fobj[vertex_obj[N]] p;
  coneFrom := {| vertex_map := fun j => transform[cone_leg N j] p |}
|}.
Next Obligation.
  pose proof (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) x y f) as Hc.
  simpl in Hc; apply Hc.
Qed.

(* The mediator into the restricted cone: componentwise the pointwise
   mediator; naturality over the discrete shape is free. *)
Program Definition res_ump_nat (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) (N : Cone (@Res P X ◯ D)) :
  vertex_obj[N] ~{[@ObjCat P, X]}~> fobj[@Res P X] (vertex_obj[M]) := {|
  transform := fun p => unique_obj (H p (res_comp_cone N p))
|}.

(* PRESERVATION: a cone all of whose evaluations are limiting has a limiting
   image under [Res]. *)
Definition Res_preserves (M : Cone D)
  (H : ∀ p : P, IsLimitCone (FCone (Eval p) M)) :
  IsLimitCone (FCone (@Res P X) M).
Proof.
  intro N.
  unshelve refine {| unique_obj := res_ump_nat M H N |}.
  - intros j p; simpl.
    exact (unique_property (H p (res_comp_cone N p)) j).
  - intros v Hv p; simpl.
    exact (uniqueness (H p (res_comp_cone N p)) (transform[v] p)
             (fun j => Hv j p)).
Defined.

(* An isomorphism of cones downstairs restricts to one at each object. *)
Definition res_coneiso_at (L : ∀ p : P, Limit (Eval p ◯ D)) (M : Cone D)
  (i : ConeIso (FCone (@Res P X) M) (FCone (@Res P X) (PointwiseLimitCone D L)))
  (p : P) :
  ConeIso (FCone (Eval p) M) (FCone (Eval p) (PointwiseLimitCone D L)).
Proof.
  exists (fobj_iso (@Eval (@ObjCat P) X p) _ _ (`1 i)).
  intro x.
  exact (`2 i x p).
Defined.

(* CREATION — Mac Lane §V.3 Theorem 2 — under the hypothesis that the
   pointwise limits exist (the header explains why the hypothesis stays). *)
Definition Res_CreatesLimit (L : ∀ p : P, Limit (Eval p ◯ D)) :
  CreatesLimit D (@Res P X).
Proof.
  unshelve refine {| creates_lift := fun N HN => PointwiseLimitCone D L |}.
  - intros N HN.
    exact (limitcone_iso
             (Res_preserves (PointwiseLimitCone D L)
                (fun p => Eval_pointwise_IsLimitCone D L p)) HN).
  - intros M HM.
    apply (Fun_pointwise_reflect D M).
    intro p.
    apply (limitcone_transport
             (ConeIso_sym
                (res_coneiso_at L M
                   (limitcone_iso HM
                      (Res_preserves (PointwiseLimitCone D L)
                         (fun q => Eval_pointwise_IsLimitCone D L q))) p))).
    exact (Eval_pointwise_IsLimitCone D L p).
Defined.

(* The limit downstairs that the pointwise limits give. *)
Definition res_limit (L : ∀ p : P, Limit (Eval p ◯ D)) : Limit (@Res P X ◯ D) :=
  limitcone_limit (FCone (@Res P X) (PointwiseLimitCone D L))
    (Res_preserves (PointwiseLimitCone D L)
       (fun p => Eval_pointwise_IsLimitCone D L p)).

(* The creation-derived limit IS #425's pointwise limit, apex and legs on
   the nose. *)
Definition creation_apex (L : ∀ p : P, Limit (Eval p ◯ D)) :
  vertex_obj[@limit_cone _ _ _ (creates_limit_lift (Res_CreatesLimit L) (res_limit L))]
  = vertex_obj[@limit_cone _ _ _ (Functor_Category_pointwise_limit D L)] := eq_refl.

Definition creation_leg (L : ∀ p : P, Limit (Eval p ◯ D)) (j : J) (p : P) :
  transform[cone_leg (@limit_cone _ _ _
    (creates_limit_lift (Res_CreatesLimit L) (res_limit L))) j] p
  = transform[cone_leg (@limit_cone _ _ _
    (Functor_Category_pointwise_limit D L)) j] p := eq_refl.

End ResCreation.

(* The issue's name for the theorem, an alias of [Res_CreatesLimit] with the
   same hypothesis.  ANNOTATED: written bare over [{J P X : Category}] the
   alias minimized P's object universe onto its hom universe and J's hom
   onto it (measured; the header records the block).  One hom level [h]
   serves J, P and X, which [Res_CreatesLimit]'s four equations identify
   anyway. *)
Definition discrete_inclusion_creates_limits@{io jo co h +}
  {J : Category@{io h h}} {P : Category@{jo h h}} {X : Category@{co h h}}
  (D : J ⟶ [P, X]) (L : ∀ p : P, Limit (Eval p ◯ D)) :
  CreatesLimit D (@Res P X) := Res_CreatesLimit D L.

(** ** Corollaries *)

Section Corollaries.

Context {P X : Category}.

Definition Res_CreatesAllLimits (HX : @Complete X) : CreatesAllLimits (@Res P X) :=
  fun J D => Res_CreatesLimit D (fun p => HX J (Eval p ◯ D)).

(* Completeness of [P, X] once more, now through Structure/Limit/Creation.v's
   general theorem (creation + a complete target). *)
Definition Res_Complete (HX : @Complete X) : @Complete ([P, X]) :=
  creates_limits_Complete (@Res P X) (Functor_Category_Complete HX)
    (Res_CreatesAllLimits HX).

Definition Res_continuous (HX : @Complete X) (J : Category) (D : J ⟶ [P, X]) :
  PreservesLimitCone D (@Res P X) :=
  creates_limits_continuous (@Res P X) (Functor_Category_Complete HX)
    (Res_CreatesAllLimits HX) J D.

End Corollaries.

(** ** Strictness: what converts and what does not *)

Section Strictness.

Context {P X : Category}.

(* The object action of the restriction is the identity ([res_obj_at]
   above). Every cone upstairs strictly lifts its own image (Structure/Limit/
   Creation.v's [self_lift]); Riehl's "strictly creates" would need every
   cone DOWNSTAIRS to be such an image on the nose, an [eq] between functor
   records that does not hold (probe). *)
Definition strict_self {J : Category} (D : J ⟶ [P, X]) (M : Cone D) :
  StrictLift D (@Res P X) (FCone (@Res P X) M) := self_lift M.

End Strictness.
