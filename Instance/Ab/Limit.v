Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.

Generalizable All Variables.

(** * Limits of abelian groups are computed on underlying sets *)

(* nLab: https://ncatlab.org/nlab/show/created+limit
   nLab: https://ncatlab.org/nlab/show/limit#limits_in_categories_of_algebras
   nLab: https://ncatlab.org/nlab/show/Ab
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_abelian_groups
   Mac Lane: Categories for the Working Mathematician, 2nd ed. (GTM 5),
             §V.1 Theorems 2 and 3, book pp. 111-112 (PDF pp. 120-121)
   Awodey:   Category Theory, 1st ed. (CMU pre-print, September 2005),
             §5.6 Proposition 5.32, printed p. 119 (PDF p. 128)

   [Ab_Forget] (Instance/Ab.v:217) STRICTLY CREATES every limit.  Given a
   limiting cone over the underlying diagram of sets, there is exactly one
   abelian-group structure on its apex making every projection a
   homomorphism ([alim_structure_unique], Mac Lane's Theorem 2), the
   resulting cone lies over the given one ON THE NOSE ([alim_over_obj] and
   [alim_over_legs] are both [eq_refl], because [Ab_Forget]'s object map is
   the [cmon_setoid ∘ ab_cmon] projection), it is limiting
   ([alim_created]), and a cone of abelian groups whose image is limiting is
   itself limiting ([ab_reflects]).  Packaged as
   Structure/Limit/Creation.v's own classes --
   [Ab_Forget_StrictlyCreatesLimit], [Ab_Forget_CreatesLimit] and
   [Ab_Forget_creates_limits] -- from which the standard corollaries follow
   by application: [Ab_Complete] (Mac Lane's Theorem 3) and
   [Ab_Forget_creates_continuous : ContinuousFunctor Ab_Forget], the
   cone-level reading, with the apex-only [Ab_Forget_PreservesAllLimits]
   derived from it and [Ab_Forget_reflects_limits] alongside.

   ** WHY A SECOND [ContinuousFunctor Ab_Forget] -- THE MAIN REASON THIS
      FILE EXISTS

   Instance/Ab/FreeNotContinuous.v:475 ALREADY declares
   [Ab_Forget_Continuous : ContinuousFunctor Ab_Forget], and its proof term
   is [right_adjoint_Continuous free_ab_adjunction] (:476) -- RAPL applied
   to Instance/Ab/Free.v:564's [free_ab_adjunction : FreeAb ⊣ Ab_Forget].
   That constant is not touched here, not reused here, and not restated:
   the one declared below is [Ab_Forget_creates_continuous]
   (a DIFFERENT name for a DIFFERENT term), and the difference is the
   point.

   [Ab_Forget_Continuous] PRESUPPOSES the free/forgetful adjunction.
   [Ab_Forget_creates_continuous] presupposes NOTHING beyond
   [Sets_Complete] and the creation result below; no adjunction, no free
   object, no [FreeAb].  That matters for exactly one consumer shape.
   Freyd's General Adjoint Functor Theorem (Adjunction/GAFT.v:241) takes
   [comp : @Complete C] and [cont : @PreservesImageLimit C D U] and RETURNS
   a left adjoint to [U].  Feeding it [Ab_Forget_Continuous] would feed it
   a term built out of the very adjunction it is being asked to produce, so
   the application would be circular and would establish nothing; feeding
   it [Ab_Forget_creates_continuous] does not, and that is what makes an
   [Ab] analogue of Instance/Grp/FreeAFT.v possible.

   ONE CORRECTION TO AN EARLIER REVISION OF THIS PARAGRAPH, since it would
   mislead the reader who tries the application.  [ContinuousFunctor] does
   NOT ascribe where GAFT asks for [PreservesImageLimit]: measured,
   [GAFT Ab_Forget Ab_Complete Ab_Forget_creates_continuous sols] is
   refused with "The term \"Ab_Forget_creates_continuous\" has type
   \"ContinuousFunctor Ab_Forget\" while it is expected to have type
   \"Limit.PreservesImageLimit\" (cannot unify \"Limit.Limit K\" and
   \"Cone.Cone K\")".  The bridge
   [Continuous_PreservesImageLimit] (Construction/Comma/Creation.v:232) is
   load-bearing and must stand in the term, exactly as it does at [Grp]
   (Instance/Grp/FreeAFT.v's [free_group_via_GAFT]), whose probe pins the
   same refusal as its N6.  So the [Ab] triple would be [Ab_Complete],
   [Continuous_PreservesImageLimit Ab_Forget_creates_continuous], and a
   solution set.  NO such [Ab] application is built here -- see NOT
   DELIVERED -- so what is claimed is availability, not use.

   Two further differences, stated so the two constants are not confused.
   [ContinuousFunctor] is not a class and nothing here is registered as an
   [Instance], so the two never compete in resolution; and continuity is
   only one of three things the creation result yields, the other two being
   [Ab_Complete] and the reflection clause [Ab_Forget_reflects_limits],
   which RAPL does not give at all.  No claim is made here that creation is
   formally stronger than continuity -- nothing in this file compares the
   two as propositions.

   ** THE HEADLINE SENTENCE IS MACHINE-CHECKED AT [eq_refl], NOT ARGUED

   At the limits [Sets_Complete] chooses -- the compatible families of
   Instance/Sets/Complete.v -- the created abelian group is the
   COORDINATEWISE one on the nose: [ab_complete_carrier],
   [ab_complete_plus], [ab_complete_zero], [ab_complete_neg] and
   [ab_complete_leg] are five [eq_refl] Examples, at an ARBITRARY shape and
   an ARBITRARY diagram of abelian groups.  Nothing in them is specific to a
   witness category, and no isomorphism is interposed; this file therefore
   needs no concrete witness to be non-vacuous, and builds none.

   ** WHAT IS LIFTED, AND WHY IT IS ONE OPERATION MORE THAN [CMon]

   Instance/Ab.v:115-122's [AbObject] EXTENDS Instance/CMon.v:32-44's
   [CMonObject] by [ab_neg] with [ab_neg_respects] and [ab_neg_left]; the
   coercion [ab_cmon :> CMonObject] supplies [carrier], [cmon_zero],
   [cmon_plus] and the four commutative-monoid laws.  So three operations
   are lifted -- [cmon_plus], [cmon_zero], [ab_neg] -- against six laws:
   associativity, COMMUTATIVITY, the left unit law, the left inverse law,
   and the two [Proper] clauses.  Commutativity is the one law with no
   counterpart in the group template Instance/Grp/Limit.v, and it costs
   exactly the same three lines as the others, because joint monicity of
   the legs does not care what the law says.

   THE MORPHISM SIDE COSTS EXACTLY WHAT THE GROUP CASE COSTS -- an earlier
   draft of this header said it was cheaper, and the measurement refutes
   that.  [AbHom A B] is DEFINED as [CMonHom A B] (Instance/Ab.v:184), so a
   homomorphism owes [cmon_map_zero] and [cmon_map_plus] and nothing else,
   preservation of negation being the theorem [ab_map_neg] (:186) rather
   than a field -- but [GrpHom] is the same shape, with [grp_map_inv]
   (Instance/Grp.v:360) playing [ab_map_neg]'s part.  Measured on the two
   [.vo] files, both carry TEN [Program] obligations with matching names:
   two each for the legs, the mediator and the reflected mediator, one each
   for the three leg families and the constant map.

   THE OBJECT SIDE COSTS TWO CONSTANTS MORE, AND EXACTLY TWO.  Counting
   [def]+[prf] heads in the [.glob] files, this file declares 75 against
   Instance/Grp/Limit.v's 73; the two extra are [alim_comm], which has no
   counterpart because [GrpObject] states no commutativity, and
   [alim_neg_respects], which has none because [GrpObject] does not make
   respectfulness of inversion a FIELD (Instance/Grp.v:184-197 lists only
   [grp_mul_respects]; [grp_inv_Proper] is derived afterwards at :276)
   whereas [AbObject] does (Instance/Ab.v:119).

   ** THE ENGINE IS ONE REUSABLE LEMMA WITH NOTHING ALGEBRAIC IN IT

   [absets_limit_ext] says the legs of a limiting cone in [Sets] are jointly
   monic ELEMENTWISE: two points of the apex agreeing at every leg are
   equal.  It is proved from the mediator's uniqueness alone, with the two
   constant maps out of the apex itself as probes -- so it needs no terminal
   object and pulls in no further module.  Every abelian-group law below is
   then three lines: apply it, rewrite the defining triangle, apply the law
   in [K j].

   ON THE DUPLICATION, DISCLOSED RATHER THAN GLOSSED, AND THE COUNT IS
   FOUR.  [absets_pre], [absets_med_eq], [absets_const] and
   [absets_limit_ext] are Instance/Grp/Limit.v:238-263's [sets_pre],
   [sets_med_eq], [sets_const] and [sets_limit_ext] reproved here under
   different names -- character-for-character identical after
   [s/absets_/sets_/g], which is how the audit measured it.  An earlier
   revision of this paragraph said "this lemma and its two helpers" and
   listed only three donors, dropping [sets_pre]; that undercount is
   corrected here rather than silently.  Neither file is the other's
   dependency and the names do not collide, so a consumer may import both.
   The reason for the copy is not mathematical: the block belongs beside its
   donors in Instance/Sets/Complete.v, and putting it there would edit an
   upstream file, which this change does not do.  Importing
   Instance/Grp/Limit.v to borrow it would drag the whole of Instance/Grp.v
   into [Ab]'s dependency cone for four generic lemmas about [Sets], which
   is worse.  Factoring all FOUR into Instance/Sets/Complete.v and having
   both files consume them is the right repair and is NOT done here.

   ** UNIQUENESS IS THE WHOLE CONTENT OF THEOREM 2, PROVED TWICE OVER

   Elementwise, [alim_zero_unique], [alim_plus_unique] and
   [alim_neg_unique] show each operation is determined by the leg
   conditions, and [alim_structure_unique] bundles them; note what those
   consume -- ONLY that the legs preserve the candidate structure, NO law of
   it, so the statement is sharper than "any abelian-group structure making
   the projections homomorphisms is this one".  Categorically,
   [Ab_lift_cone_unique] is the generic [screates_lift_unique] at this
   instance, giving the canonical cone isomorphism.  A whole-record
   statement "[A' = LimitAb] for any abelian group [A'] on that carrier" is
   NOT delivered and is not a gap more work here could close: it would need
   [cmon_setoid (ab_cmon A') = vertex_obj[L]] as a Leibniz equality and a
   transport in the type of every operation.

   ** ON THE HOUSE RULE THAT MORPHISMS ARE COMPARED WITH [≈]

   Four statements here write [=] between morphisms -- [alim_over_legs],
   [ab_lift_legs], [ab_fcone_leg] and [ab_complete_leg] -- and each does so
   because both sides are the SAME TERM, the witness being [eq_refl].  They
   record Mac Lane's [F sigma = tau] at full strength, which is strictly
   stronger than the [≈] the [StrictLift] clause asks for; every law, every
   proof and the [slift_legs] clause consumed by [ab_strict_lift] use [≈].
   The same applies to the object-level [=] of [alim_over_obj],
   [ab_lift_apex], [ab_fcone_apex], [ab_complete_carrier] and the three
   [ab_complete_*] element equations, which compare OBJECTS and ELEMENTS
   rather than morphisms and are the discipline's sanctioned exception.

   ** UNIVERSES, measured off BOTH binder and block over all 85 constants

   The 85 are the 75 declaration heads plus the ten [Program] obligations,
   read back with [Set Printing Universes] and [About].  ZERO word-bounded
   [Set] occurrences anywhere, and only TEN carry a block EQUATION at all
   (every block carries the strict inequality [u0 < u1] or a relabelling of
   it, which is not an equation and is not counted).  Five of the ten are
   the generic [Sets] section -- [absets_pre], [absets_med_eq],
   [absets_limit_ext], [absets_const] and its obligation
   [absets_const_obligation_1], which no source-level reading sees -- all
   five carrying [u0 = u3], which identifies the shape's hom-and-proof
   universe with [Sets]' carrier universe, and the first three additionally
   [u1 = u2], which identifies two of the ambient's; that [u0 = u3] is
   [IsALimit]'s doing and not this file's.  The other five are the
   [ab_complete_*] readbacks, which BIND their shape explicitly and so carry
   [u = u0], identifying the shape's object universe with its hom-and-proof
   universe -- that is [Complete]'s own [@{u u u u0}] shape written out,
   inherited from [Sets_Complete] and not narrowed here.  The remaining 75
   constants carry no block equation, [Ab_Complete@{u u0 u1} :
   Complete@{u u u u0}] with [u < u0] and [u0 <= u1] among them, so the
   smallness discipline is exactly [Sets_Complete]'s.  This is the same
   count and the same split as Instance/Grp/Limit.v records for its own 83.

   ** WHAT WAS IN TREE BEFORE, MEASURED

   Measured on the worktree this file was written against, by grepping all
   [.v] files for the tokens: [Ab_Complete], [Ab_Forget_creates],
   [Ab_Forget_Preserves] and [Ab_Forget_reflects] each returned ZERO hits,
   so no completeness, creation, preservation or reflection statement about
   [Ab] or [Ab_Forget] existed.  What DID exist about [Ab_Forget] and limits
   is the single constant discussed above, [Ab_Forget_Continuous]
   (Instance/Ab/FreeNotContinuous.v:475), together with its file's negative
   results about the LEFT adjoint [FreeAb] (:466, :469).  No [CMon_Complete]
   exists either; the argument below is written at [Ab] and the [CMon] case
   is not extracted from it.

   ** STATUS: axiom-free

   [Print Assumptions] reports "Closed under the global context" for all of
   [Ab_Complete], [Ab_Forget_creates_continuous], [Ab_Forget_creates_limits],
   [Ab_Forget_StrictlyCreatesLimit], [Ab_Forget_CreatesLimit],
   [Ab_Forget_StrictlyCreatesLimits], [Ab_Forget_PreservesAllLimits],
   [Ab_Forget_reflects_limits], [Ab_Forget_lifts_limits], [LimitAb],
   [ab_reflects], [alim_created], [alim_structure_unique] and
   [Ab_lift_cone_unique], and for all ten [Program] obligations named in the
   UNIVERSES paragraph.  That is twenty-four readbacks, not a
   directory-wide certification of the remaining sixty-one constants;
   nothing here is registered with [make print-assumptions].

   ** NOT DELIVERED

   No colimits and no cocompleteness for [Ab] (Instance/Ab/Coproduct.v and
   Instance/Ab/DirectedColimit.v cover pieces of that ground and are not
   touched).  No GAFT application at [Ab]: the two hypotheses are made
   available, nothing consumes them, and no [Ab] counterpart of
   Instance/Grp/FreeAFT.v is built.  No comparison of the created binary
   product with any cartesian or biproduct structure on [Ab], which would go
   through a discrete diagram and so through Instance/Discrete.v's
   unannotated [DiscreteCat_Functor].  No [CMon] analogue, though the engine
   transfers unchanged -- drop [ab_neg] and its two laws.  No monadicity
   statement and no comparison functor, so nothing here says [Ab] IS an
   Eilenberg-Moore category.  No signature-generic statement covering [Grp],
   [Ab], [CMon] and [Rng] at once; the duplication noted above is real and
   is left standing.  And NOTHING is registered as an [Instance] -- the file
   declares none, following its template, since a chosen limit must not
   become globally resolvable.  No [Test/Probe] file accompanies this one,
   so the [eq_refl] readbacks below are guarded only by being [Example]s in
   this file. *)

(** * Joint monicity of limit legs in [Sets], elementwise *)

Section AbSetsExt.

Context {J : Category}.
Context {F : J ⟶ Sets}.
Context {c : Sets}.
Context (H : IsALimit F c).

Definition absets_pre {d : Sets} (u : d ~{Sets}~> c) : Cone F :=
  @Build_Cone J Sets F d
    (@Build_ACone J Sets d F (fun j => limit_leg H j ∘ u)
       (fun x y f =>
          transitivity (comp_assoc _ _ _)
            (@compose_respects Sets _ _ _ _ _ (limit_leg_coherence H f) _ _
               (reflexivity u)))).

Lemma absets_med_eq {d : Sets} (u v : d ~{Sets}~> c) :
  (∀ j : J, limit_leg H j ∘ u ≈ limit_leg H j ∘ v) → u ≈ v.
Proof.
  intro Huv.
  apply (limit_med_eq H (absets_pre u)).
  - intro j; reflexivity.
  - intro j; symmetry; apply Huv.
Qed.

Program Definition absets_const (x : carrier c) : c ~{Sets}~> c :=
  {| morphism := fun _ => x |}.

Lemma absets_limit_ext (x y : carrier c) :
  (∀ j : J, limit_leg H j x ≈ limit_leg H j y) → x ≈ y.
Proof.
  intro Hxy.
  exact (absets_med_eq (absets_const x) (absets_const y) (fun j a => Hxy j) x).
Qed.

End AbSetsExt.

(** * The created abelian-group structure on a limit of underlying sets *)

Section AbLift.

Context {J : Category}.
Context (K : J ⟶ Ab).
Context (L : Limit (Ab_Forget ◯ K)).

Definition alim_leg (j : J) :
  vertex_obj[L] ~{Sets}~> cmon_setoid (ab_cmon (K j)) :=
  limit_leg (limit_is_alimit L) j.

Lemma alim_leg_coherence {x y : J} (f : x ~{J}~> y)
  (a : carrier vertex_obj[L]) :
  cmon_map (fmap[K] f) (alim_leg x a) ≈ alim_leg y a.
Proof. exact (limit_leg_coherence (limit_is_alimit L) f a). Qed.

Lemma alim_ext (x y : carrier vertex_obj[L]) :
  (∀ j : J, alim_leg j x ≈ alim_leg j y) → x ≈ y.
Proof. exact (absets_limit_ext (limit_is_alimit L) x y). Qed.

(** ** The addition *)

Definition alim_pair : Sets :=
  {| carrier   := carrier vertex_obj[L] * carrier vertex_obj[L]
   ; is_setoid := prod_setoid |}.

Program Definition alim_plus_leg (j : J) :
  alim_pair ~{Sets}~> cmon_setoid (ab_cmon (K j)) :=
  {| morphism := fun p =>
       cmon_plus (K j) (alim_leg j (fst p)) (alim_leg j (snd p)) |}.
Next Obligation.
  intros p q Hpq.
  destruct Hpq as [H1 H2].
  now rewrite H1, H2.
Qed.

Lemma alim_plus_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Ab_Forget ◯ K] f ∘ alim_plus_leg x ≈ alim_plus_leg y.
Proof.
  intro p; simpl.
  rewrite cmon_map_plus.
  now rewrite !alim_leg_coherence.
Qed.

Definition alim_plus_cone : Cone (Ab_Forget ◯ K) :=
  @Build_Cone J Sets (Ab_Forget ◯ K) alim_pair
    (@Build_ACone J Sets alim_pair (Ab_Forget ◯ K)
       alim_plus_leg (@alim_plus_coherence)).

Definition alim_plus_map : alim_pair ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) alim_plus_cone.

Definition alim_plus (a b : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  alim_plus_map (a, b).

Lemma alim_plus_triangle (j : J) (a b : carrier vertex_obj[L]) :
  alim_leg j (alim_plus a b)
    ≈ cmon_plus (K j) (alim_leg j a) (alim_leg j b).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) alim_plus_cone j (a, b)).
Qed.

Lemma alim_plus_respects :
  Proper (equiv ==> equiv ==> equiv) alim_plus.
Proof.
  intros a a' Ha b b' Hb.
  exact (proper_morphism alim_plus_map (a, b) (a', b') (Ha, Hb)).
Qed.

(** ** The zero *)

Program Definition alim_zero_leg (j : J) :
  unit_setoid_object ~{Sets}~> cmon_setoid (ab_cmon (K j)) :=
  {| morphism := fun _ => cmon_zero (K j) |}.

Lemma alim_zero_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Ab_Forget ◯ K] f ∘ alim_zero_leg x ≈ alim_zero_leg y.
Proof. intro p; simpl; apply cmon_map_zero. Qed.

Definition alim_zero_cone : Cone (Ab_Forget ◯ K) :=
  @Build_Cone J Sets (Ab_Forget ◯ K) unit_setoid_object
    (@Build_ACone J Sets unit_setoid_object (Ab_Forget ◯ K)
       alim_zero_leg (@alim_zero_coherence)).

Definition alim_zero_map : unit_setoid_object ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) alim_zero_cone.

Definition alim_zero : carrier vertex_obj[L] := alim_zero_map ttt.

Lemma alim_zero_triangle (j : J) :
  alim_leg j alim_zero ≈ cmon_zero (K j).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) alim_zero_cone j ttt).
Qed.

(** ** The negation *)

Program Definition alim_neg_leg (j : J) :
  vertex_obj[L] ~{Sets}~> cmon_setoid (ab_cmon (K j)) :=
  {| morphism := fun a => ab_neg (K j) (alim_leg j a) |}.
Next Obligation. intros a b Hab; now rewrite Hab. Qed.

Lemma alim_neg_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[Ab_Forget ◯ K] f ∘ alim_neg_leg x ≈ alim_neg_leg y.
Proof.
  intro a; simpl.
  rewrite ab_map_neg.
  now rewrite alim_leg_coherence.
Qed.

Definition alim_neg_cone : Cone (Ab_Forget ◯ K) :=
  @Build_Cone J Sets (Ab_Forget ◯ K) vertex_obj[L]
    (@Build_ACone J Sets vertex_obj[L] (Ab_Forget ◯ K)
       alim_neg_leg (@alim_neg_coherence)).

Definition alim_neg_map : vertex_obj[L] ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) alim_neg_cone.

Definition alim_neg (a : carrier vertex_obj[L]) : carrier vertex_obj[L] :=
  alim_neg_map a.

Lemma alim_neg_triangle (j : J) (a : carrier vertex_obj[L]) :
  alim_leg j (alim_neg a) ≈ ab_neg (K j) (alim_leg j a).
Proof.
  exact (limit_med_commutes (limit_is_alimit L) alim_neg_cone j a).
Qed.

Lemma alim_neg_respects : Proper (equiv ==> equiv) alim_neg.
Proof.
  intros a a' Ha.
  exact (proper_morphism alim_neg_map a a' Ha).
Qed.

(** ** The abelian-group laws, by joint monicity of the legs *)

Lemma alim_assoc (a b c : carrier vertex_obj[L]) :
  alim_plus (alim_plus a b) c ≈ alim_plus a (alim_plus b c).
Proof.
  apply alim_ext; intro j.
  rewrite !alim_plus_triangle.
  apply cmon_plus_assoc.
Qed.

(* The one law with no counterpart in the group template, and it costs
   exactly what the others cost: joint monicity does not care what the law
   says. *)
Lemma alim_comm (a b : carrier vertex_obj[L]) :
  alim_plus a b ≈ alim_plus b a.
Proof.
  apply alim_ext; intro j.
  rewrite !alim_plus_triangle.
  apply cmon_plus_comm.
Qed.

Lemma alim_zero_l (a : carrier vertex_obj[L]) : alim_plus alim_zero a ≈ a.
Proof.
  apply alim_ext; intro j.
  rewrite alim_plus_triangle, alim_zero_triangle.
  apply cmon_plus_zero_l.
Qed.

Lemma alim_neg_l (a : carrier vertex_obj[L]) :
  alim_plus (alim_neg a) a ≈ alim_zero.
Proof.
  apply alim_ext; intro j.
  rewrite alim_plus_triangle, alim_neg_triangle, alim_zero_triangle.
  apply ab_neg_left.
Qed.

(** ** The vertex's equality is propositional *)

(* Since the PR "algebraic carriers are sets" (2026-09-17) an [AbObject]
   carries [cmon_prop], so the lifted group owes a [Prop]-valued relation on
   [vertex_obj[L]] -- and [L] here is an ARBITRARY limit of the underlying
   sets, not the one [Sets_Complete] chooses, so
   Instance/Sets/Propositional.v's [limit_PropEquiv] does not apply on the
   nose.  The edit list for this phase predicted a hypothesis on [L],
   discharged at [Ab_Complete]; that turned out not to be needed, and taking
   one would have been fatal, since [CreatesLimits] quantifies over every [L]
   and leaves no place to put it.

   The relation below is instead the one the section already has a theorem
   about: two points of the vertex are related when every LEG relates them.
   [alim_ext] (:318) is exactly the implication into `≈`, and it holds at an
   arbitrary limit because a limit's vertex is detected by its projections;
   the converse is each leg being a setoid map.  So a limit of propositional
   carriers is propositional, with no extra hypothesis anywhere. *)
Definition alim_prop : PropEquiv (is_setoid vertex_obj[L]) :=
  @PropEquiv_of_relation _ (is_setoid vertex_obj[L])
    (fun x y => forall j : J,
       @pequiv _ _ (cmon_prop (K j)) (alim_leg j x) (alim_leg j y))
    (fun x y H => alim_ext x y (fun j => pequiv_to _ _ (H j)))
    (fun x y H j => pequiv_from _ _ (proper_morphism (alim_leg j) x y H)).

(** ** The lifted abelian group *)

Definition LimitAb : AbObject :=
  {| ab_cmon :=
       {| cmon_setoid        := vertex_obj[L]
        ; cmon_zero          := alim_zero
        ; cmon_plus          := alim_plus
        ; cmon_plus_respects := alim_plus_respects
        ; cmon_plus_assoc    := alim_assoc
        ; cmon_plus_comm     := alim_comm
        ; cmon_plus_zero_l   := alim_zero_l
        ; cmon_prop          := alim_prop |}
   ; ab_neg          := alim_neg
   ; ab_neg_respects := alim_neg_respects
   ; ab_neg_left     := alim_neg_l |}.

(** ** The legs are homomorphisms *)

(* Only [cmon_map_zero] and [cmon_map_plus] are owed: [AbHom] IS [CMonHom]
   (Instance/Ab.v:184), and preservation of negation is the theorem
   [ab_map_neg] (:186) rather than a field. *)
Program Definition alim_hom (j : J) : AbHom LimitAb (K j) :=
  {| cmon_map := alim_leg j |}.
Next Obligation. apply alim_zero_triangle. Qed.
Next Obligation. apply alim_plus_triangle. Qed.

Lemma alim_hom_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ alim_hom x ≈ alim_hom y.
Proof. intro a; exact (alim_leg_coherence f a). Qed.

Definition alim_cone : Cone K :=
  @Build_Cone J Ab K LimitAb
    (@Build_ACone J Ab LimitAb K alim_hom (@alim_hom_coherence)).

(** ** Strictness: the lifted cone lies over [L] on the nose *)

Definition alim_over_obj : Ab_Forget LimitAb = vertex_obj[L] := eq_refl.

Definition alim_over_legs (j : J) :
  fmap[Ab_Forget] (cone_leg alim_cone j) = alim_leg j := eq_refl.

(** ** The lifted cone is limiting *)

Definition acar_med (N : Cone K) :
  cmon_setoid (ab_cmon vertex_obj[N]) ~{Sets}~> vertex_obj[L] :=
  limit_med (limit_is_alimit L) (FCone Ab_Forget N).

Lemma acar_med_commutes (N : Cone K) (j : J) (a : carrier vertex_obj[N]) :
  alim_leg j (acar_med N a) ≈ cmon_map (cone_leg N j) a.
Proof.
  exact (limit_med_commutes (limit_is_alimit L) (FCone Ab_Forget N) j a).
Qed.

Lemma acar_med_zero (N : Cone K) :
  acar_med N (cmon_zero vertex_obj[N]) ≈ alim_zero.
Proof.
  apply alim_ext; intro j.
  rewrite acar_med_commutes, alim_zero_triangle.
  apply cmon_map_zero.
Qed.

Lemma acar_med_plus (N : Cone K) (a b : carrier vertex_obj[N]) :
  acar_med N (cmon_plus vertex_obj[N] a b)
    ≈ alim_plus (acar_med N a) (acar_med N b).
Proof.
  apply alim_ext; intro j.
  rewrite acar_med_commutes, alim_plus_triangle, !acar_med_commutes.
  apply cmon_map_plus.
Qed.

Program Definition alim_med (N : Cone K) : vertex_obj[N] ~{Ab}~> LimitAb :=
  {| cmon_map := acar_med N |}.
Next Obligation. apply acar_med_zero. Qed.
Next Obligation. apply acar_med_plus. Qed.

Definition alim_created : IsALimit K LimitAb.
Proof.
  unshelve refine {| limit_acone := @coneFrom _ _ _ alim_cone |}.
  intro N.
  unshelve refine {| unique_obj := alim_med N |}.
  - intros j a.
    exact (acar_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limit_is_alimit L) (FCone Ab_Forget N)
             (cmon_map v) Hv a).
Defined.

(** ** Uniqueness of the lifted structure (Mac Lane's Theorem 2) *)

Lemma alim_zero_unique (e : carrier vertex_obj[L])
  (He : ∀ j : J, alim_leg j e ≈ cmon_zero (K j)) : e ≈ alim_zero.
Proof.
  apply alim_ext; intro j.
  now rewrite He, alim_zero_triangle.
Qed.

Lemma alim_plus_unique
  (m : carrier vertex_obj[L] → carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hm : ∀ (j : J) a b,
     alim_leg j (m a b) ≈ cmon_plus (K j) (alim_leg j a) (alim_leg j b))
  (a b : carrier vertex_obj[L]) : m a b ≈ alim_plus a b.
Proof.
  apply alim_ext; intro j.
  now rewrite Hm, alim_plus_triangle.
Qed.

Lemma alim_neg_unique
  (n : carrier vertex_obj[L] → carrier vertex_obj[L])
  (Hn : ∀ (j : J) a, alim_leg j (n a) ≈ ab_neg (K j) (alim_leg j a))
  (a : carrier vertex_obj[L]) : n a ≈ alim_neg a.
Proof.
  apply alim_ext; intro j.
  now rewrite Hn, alim_neg_triangle.
Qed.

(* The three clauses together: Mac Lane's "there is exactly one
   abelian-group structure on the limit making every projection a
   homomorphism".  No law of the candidate structure is consumed -- not
   even commutativity -- only that the legs preserve it. *)
Lemma alim_structure_unique
  (e : carrier vertex_obj[L])
  (m : carrier vertex_obj[L] → carrier vertex_obj[L] → carrier vertex_obj[L])
  (n : carrier vertex_obj[L] → carrier vertex_obj[L])
  (He : ∀ j : J, alim_leg j e ≈ cmon_zero (K j))
  (Hm : ∀ (j : J) a b,
     alim_leg j (m a b) ≈ cmon_plus (K j) (alim_leg j a) (alim_leg j b))
  (Hn : ∀ (j : J) a, alim_leg j (n a) ≈ ab_neg (K j) (alim_leg j a)) :
  (e ≈ alim_zero)
    * (∀ a b, m a b ≈ alim_plus a b)
    * (∀ a, n a ≈ alim_neg a).
Proof.
  split; [ split | ].
  - exact (alim_zero_unique e He).
  - exact (alim_plus_unique m Hm).
  - exact (alim_neg_unique n Hn).
Qed.

End AbLift.

(** * Reflection: a cone of abelian groups whose image is limiting is
      limiting *)

Section AbReflect.

Context {J : Category}.
Context (K : J ⟶ Ab).
Context (M : Cone K).
Context (HM : IsLimitCone (FCone Ab_Forget M)).

Definition arefl_med (N : Cone K) :
  cmon_setoid (ab_cmon vertex_obj[N]) ~{Sets}~>
    cmon_setoid (ab_cmon vertex_obj[M]) :=
  limit_med (limitcone_isalimit HM) (FCone Ab_Forget N).

Lemma arefl_med_commutes (N : Cone K) (j : J) (a : carrier vertex_obj[N]) :
  cmon_map (cone_leg M j) (arefl_med N a) ≈ cmon_map (cone_leg N j) a.
Proof using All.
  exact (limit_med_commutes (limitcone_isalimit HM) (FCone Ab_Forget N) j a).
Qed.

Lemma arefl_ext (x y : carrier vertex_obj[M]) :
  (∀ j : J, cmon_map (cone_leg M j) x ≈ cmon_map (cone_leg M j) y) → x ≈ y.
Proof using All. exact (absets_limit_ext (limitcone_isalimit HM) x y). Qed.

Lemma arefl_med_zero (N : Cone K) :
  arefl_med N (cmon_zero vertex_obj[N]) ≈ cmon_zero vertex_obj[M].
Proof using All.
  apply arefl_ext; intro j.
  rewrite arefl_med_commutes, !cmon_map_zero.
  reflexivity.
Qed.

Lemma arefl_med_plus (N : Cone K) (a b : carrier vertex_obj[N]) :
  arefl_med N (cmon_plus vertex_obj[N] a b)
    ≈ cmon_plus vertex_obj[M] (arefl_med N a) (arefl_med N b).
Proof using All.
  apply arefl_ext; intro j.
  rewrite arefl_med_commutes, !cmon_map_plus, !arefl_med_commutes.
  reflexivity.
Qed.

Program Definition arefl_hom (N : Cone K) :
  vertex_obj[N] ~{Ab}~> vertex_obj[M] := {| cmon_map := arefl_med N |}.
Next Obligation. apply arefl_med_zero. Qed.
Next Obligation. apply arefl_med_plus. Qed.

Definition ab_reflects : IsLimitCone M.
Proof using All.
  intro N.
  unshelve refine {| unique_obj := arefl_hom N |}.
  - intros j a.
    exact (arefl_med_commutes N j a).
  - intros v Hv a.
    exact (limit_med_unique (limitcone_isalimit HM) (FCone Ab_Forget N)
             (cmon_map v) Hv a).
Defined.

End AbReflect.

(** * [Ab_Forget] strictly creates every limit *)

Section AbStrictlyCreates.

Context {J : Category}.
Context (K : J ⟶ Ab).

Definition ab_strict_lift (N : Cone (Ab_Forget ◯ K)) (HN : IsLimitCone N) :
  StrictLift K Ab_Forget N :=
  @Build_StrictLift J Ab Sets K Ab_Forget N
    (alim_cone K (@Build_Limit J Sets (Ab_Forget ◯ K) N HN))
    eq_refl
    (fun x => reflexivity _).

Definition Ab_Forget_StrictlyCreatesLimit : StrictlyCreatesLimit K Ab_Forget.
Proof.
  unshelve refine {| screates := ab_strict_lift |}.
  - intros N HN.
    exact (@ump_limit _ _ _ _
             (alim_created K (@Build_Limit J Sets (Ab_Forget ◯ K) N HN))).
  - intros M HM.
    exact (ab_reflects K M HM).
Defined.

Definition Ab_Forget_CreatesLimit : CreatesLimit K Ab_Forget :=
  StrictlyCreatesLimit_CreatesLimit Ab_Forget_StrictlyCreatesLimit.

End AbStrictlyCreates.

Definition Ab_Forget_StrictlyCreatesLimits :
  StrictlyCreatesLimits Ab_Forget :=
  fun J K => Ab_Forget_StrictlyCreatesLimit K.

Definition Ab_Forget_creates_limits : CreatesAllLimits Ab_Forget :=
  fun J K => Ab_Forget_CreatesLimit K.

Definition Ab_Forget_reflects_limits {J : Category} (K : J ⟶ Ab) :
  ReflectsLimitCone K Ab_Forget :=
  creates_reflects_limits (Ab_Forget_CreatesLimit K).

(* Mac Lane's uniqueness clause at the categorical level: any cone of
   abelian groups lying over [N] is canonically isomorphic to the created
   one.  This is the generic [screates_lift_unique] at this instance, not a
   restatement. *)

Definition Ab_lift_cone_unique {J : Category} (K : J ⟶ Ab)
  (N : Cone (Ab_Forget ◯ K)) (HN : IsLimitCone N)
  (M : Cone K) (i : ConeIso (FCone Ab_Forget M) N) :
  ConeIso M (slift_cone (screates N HN)) :=
  screates_lift_unique (Ab_Forget_StrictlyCreatesLimit K) N HN M i.

(** * The image of a cone of abelian groups is the elementwise cone *)

Example ab_fcone_apex {J : Category} (K : J ⟶ Ab) (N : Cone K) :
  vertex_obj[FCone Ab_Forget N] = cmon_setoid (ab_cmon vertex_obj[N])
  := eq_refl.

Example ab_fcone_leg {J : Category} (K : J ⟶ Ab) (N : Cone K) (j : J) :
  cone_leg (FCone Ab_Forget N) j = cmon_map (cone_leg N j) := eq_refl.

(** * Mac Lane's Theorem 2: the lifting half *)

Definition Ab_Forget_lifts_limits {J : Category} (K : J ⟶ Ab)
  (L : Limit (Ab_Forget ◯ K)) : Limit K :=
  creates_limit_lift (Ab_Forget_CreatesLimit K) L.

Example ab_lift_apex {J : Category} (K : J ⟶ Ab)
  (L : Limit (Ab_Forget ◯ K)) :
  Ab_Forget (vertex_obj[Ab_Forget_lifts_limits K L]) = vertex_obj[L]
  := eq_refl.

Example ab_lift_legs {J : Category} (K : J ⟶ Ab)
  (L : Limit (Ab_Forget ◯ K)) (j : J) :
  fmap[Ab_Forget]
    (cone_leg (@limit_cone _ _ _ (Ab_Forget_lifts_limits K L)) j)
    = limit_leg (limit_is_alimit L) j
  := eq_refl.

(** * Corollaries: [Ab] is complete and [Ab_Forget] is continuous *)

Definition Ab_Complete : @Complete Ab :=
  creates_limits_Complete Ab_Forget Sets_Complete Ab_Forget_creates_limits.

(* [ContinuousFunctor] is [PreservesLimitCone] quantified over every shape
   and diagram, which is what the word means in Mac Lane §V.4 -- the
   apex-only [PreservesAllLimits] below is its CONSEQUENCE, not the
   definition (Structure/Limit/Preservation.v:46-56).

   NAME.  This is NOT Instance/Ab/FreeNotContinuous.v:475's
   [Ab_Forget_Continuous], which is the same TYPE by a different TERM:
   that one is [right_adjoint_Continuous free_ab_adjunction] (:476) and so
   presupposes Instance/Ab/Free.v:564's adjunction, while this one comes
   from limit creation and presupposes only [Sets_Complete].  See the
   header for why the distinction is load-bearing rather than cosmetic. *)

Definition Ab_Forget_creates_continuous : ContinuousFunctor Ab_Forget :=
  creates_limits_continuous Ab_Forget Sets_Complete Ab_Forget_creates_limits.

Definition Ab_Forget_PreservesAllLimits : PreservesAllLimits Ab_Forget :=
  creates_limits_PreservesAllLimits Ab_Forget Sets_Complete
    Ab_Forget_creates_limits.

(** * "Limits of abelian groups are computed on underlying sets", literally *)

(* At the limits [Sets_Complete] chooses -- the compatible families of
   Instance/Sets/Complete.v -- the created abelian group is the
   coordinatewise one ON THE NOSE: carrier, addition, zero, negation and
   every projection are all [eq_refl], at an ARBITRARY shape and an
   ARBITRARY diagram of abelian groups.  Nothing here is specific to a
   witness category; the readbacks below are the section header's sentence
   machine-checked. *)

Section AbComputed.

Context {J : Category}.
Context (K : J ⟶ Ab).

Example ab_complete_carrier :
  cmon_setoid (ab_cmon (vertex_obj[Ab_Complete J K]))
    = Sets_limit_obj (Ab_Forget ◯ K) := eq_refl.

Example ab_complete_plus
  (a b : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (cmon_plus (vertex_obj[Ab_Complete J K]) a b) d
    = cmon_plus (K d) (`1 a d) (`1 b d) := eq_refl.

Example ab_complete_zero (d : J) :
  `1 (cmon_zero (vertex_obj[Ab_Complete J K])) d = cmon_zero (K d) := eq_refl.

Example ab_complete_neg
  (a : carrier (Sets_limit_obj (Ab_Forget ◯ K))) (d : J) :
  `1 (ab_neg (vertex_obj[Ab_Complete J K]) a) d
    = ab_neg (K d) (`1 a d) := eq_refl.

Example ab_complete_leg (d : J) :
  cmon_map (cone_leg (@limit_cone _ _ _ (Ab_Complete J K)) d)
    = Sets_limit_leg (Ab_Forget ◯ K) d := eq_refl.

End AbComputed.
