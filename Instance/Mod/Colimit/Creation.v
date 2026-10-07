(** * U : R-Mod ⟶ Ab creates every colimit: Riehl's Corollary 5.6.10 *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.AbCategory.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Ab.ModFunctor.

Generalizable All Variables.

(* Book: Riehl, "Category Theory in Context", 2nd ed., Corollary
         5.6.10, printed p. 212 (PDF p. 232) — riehl:5.6:cor10; with
         her Theorem 5.6.5, printed pp. 210–211 (PDF pp. 230–231),
         Exercise 5.6.ii, printed p. 217, and Definition 3.4.1, printed
         pp. 103–104
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd
         ed., Springer GTM 5, 1998, §V.1, printed pp. 111–112 (PDF
         pp. 120–121), the Definition of creation on printed p. 112
   nLab: https://ncatlab.org/nlab/show/created+limit
   nLab: https://ncatlab.org/nlab/show/monadic+functor
   nLab: https://ncatlab.org/nlab/show/Mod

   Mac Lane defines creation in §V.1.  Having built the limits of groups
   termwise out of the limits of their underlying sets, he says that "each
   forgetful functor 'creates' limits in the sense of the following
   definition" (printed p. 111, PDF p. 120), and the Definition (printed
   p. 112) reads: V : A → X creates limits for F : J → A if
   "(i) To every limiting cone τ" over VF "there is exactly one pair ⟨a, σ⟩
   consisting of an object a ∈ A with Va = x and a cone σ" over F "with
   Vσ = τ, and if, moreover, (ii) This cone" σ "is a limiting cone in A."  "V
   creates colimits" is "the above with the arrows in all cones reversed", and
   he adds that "V creates limits" means only that V produces limits for
   functors F whose composite VF already has a limit.  Riehl's Definition
   3.4.1 (printed pp. 103–104) keeps the conditional and drops the uniqueness:
   F creates the limits of K "if whenever FK has a limit in D, then K has a
   limit as well, in which case a cone over K is a limit cone if and only if
   its image under F is a limit cone", and the definition "dualizes" to
   colimits.  Structure/Limit/Creation.v implements both: [CreatesLimit] is
   Riehl's (a lift, an isomorphism of its image with the given cone, and
   reflection), [StrictlyCreatesLimit] keeps Mac Lane's lift on the nose and
   his clause (ii) and replaces his uniqueness by reflection, and
   [CreatesColimit], [StrictlyCreatesColimit] and [CreatesAllColimits] are the
   same classes read in the opposite categories.

   The algebraic forgetful functors to Set create limits and, as a rule, no
   colimits: the free product of groups is not the disjoint union of their
   sets, and Riehl records, right after the corollary this file proves, that
   U : Group → Set "does not preserve (and so, in particular, does not create)
   coproducts" (printed p. 212).  One level up the answer changes.  Her
   Corollary 5.6.10 (printed p. 212, PDF p. 232) states, in this header's
   paraphrase, that the forgetful functor U : _R Mod → Ab creates every
   colimit that Ab has.  Her proof is monadic.  U is monadic with monad
   R ⊗_ℤ − (her Example 5.5.7(i)); "By Example 4.4.15, for any pair of abelian
   groups A and B, there is a natural isomorphism" involving "the abelian
   group Hom_ℤ(R, B) of group homomorphisms R → B", so that the monad "has a
   right adjoint Hom_ℤ(R, −)" (the sibling's header records how the display
   reads); "By Theorem 4.6.2, R ⊗_ℤ − preserves all colimits and so Theorem
   5.6.5(ii) applies to all diagrams in Ab".  That theorem (printed p. 210)
   reads "A monadic functor U : A → C creates (i) any limits that C has, and
   (ii) any colimits that C has and the monad and its square preserve".  Her
   proof of clause (ii) is a sketch on printed p. 211 — the structure map on
   the nadir "is induced by the universal property of the colimit cone under T
   U^T D with nadir TL" — and Exercise 5.6.ii (printed p. 217) reads "Prove
   Theorem 5.6.5(ii)".

   TWO ROUTES, AND WHICH ONE THIS FILE TAKES.  The tree has every piece of
   Riehl's route but its last.  The monad and the monadicity are
   Instance/Mod/TensorMonad.v's; the tensor–hom adjunction and the
   cocontinuity of the monad and of its square are the sibling
   Instance/Mod/TensorMonad/Cocontinuous.v; the step they feed, her Theorem
   5.6.5(ii) at an Eilenberg–Moore forgetful functor, is issue #1008, OPEN,
   and no [CreatesColimit] at [EM_Forget] exists.  This file therefore proves
   the corollary DIRECTLY, as the colimit dual of Instance/Mod/Limit.v's
   creation of limits, and never mentions the monad: it imports neither
   TensorMonad file, and its closure is 68 files where the sibling's is 82,
   each counting the file itself.  What the monadic route adds, and what a
   follow-up must do to finish it, is recorded in the sibling's header.

   THE CREATED ACTION IS A MEDIATOR.  Let N be a colimiting cocone in Ab under
   U ◯ K — in the tree, a limiting cone in Ab^op over (RMod_Forget_Ab
   R)^op ◯ K^op, whose legs are the insertions ι_i : U (K i) → N.  For a fixed
   scalar r the family i ↦ ι_i ∘ (r ·) is again a cocone in Ab
   ([mcol_smul_cone]): each r · on K i is a homomorphism of groups
   (Instance/Ab/ModFunctor.v's [module_act], unital by Instance/Mod.v's
   [rm_smul_zero_r], additive by [rm_smul_distr_l]; importing it costs one
   file of closure, that file) and the family is coherent because the arrows
   of K are R-linear ([rm_map_smul]).  Its mediator out of the nadir,
   [mcol_smul_map], IS the created action ([mcol_smul],
   [mcol_smul_is_mediator]), and the defining triangle is
   ρ_r (ι_i m) ≈ ι_i (r · m) ([mcol_smul_triangle]).  Being a morphism of
   Ab, the mediator is additive in the vector for nothing:
   [mcol_smul_distr_l] is [cmon_map_plus], one citation.

   THE ENGINE IS JOINT EPIMORPHICITY, FROM UNIQUENESS ALONE.  [mcol_ext] says
   that two Ab maps u, v out of the nadir that agree after every insertion are
   ≈: both are mediators of the one cocone i ↦ v ∘ ι_i, so the uniqueness
   clause of the colimit identifies them.  No elementwise description of the
   colimit is needed, and none exists in the tree.  Here the dual departs from
   its template: Instance/Mod/Limit.v's [mlim_ext] cannot probe its apex with
   constant maps, which are not homomorphisms, and transports the limit to
   Sets to use [absets_limit_ext]; a colimit is tested by maps OUT of its
   nadir, which are homomorphisms already.  The other four module laws are
   each one application of [mcol_ext]: respectfulness in the scalar
   ([mcol_smul_respects]), distributivity over scalars against
   Structure/AbCategory.v's pointwise sum [ab_hom_add] ([mcol_smul_distr_r]),
   associativity against the composite ([mcol_smul_assoc]) and the unit law
   against the identity ([mcol_smul_one]).  [ColimMod] is the module,
   [mcol_hom] the insertions made R-linear, [mcol_cone] the cocone of modules.

   REFLECTION AND THE LIMITING CLAUSE ARE ONE LEMMA.  [mcol_reflect]: a cocone
   of modules whose underlying cocone is colimiting in Ab is colimiting in
   RMod R.  The mediator into another cocone P is the Ab mediator m of the
   underlying cocones; it is R-linear because, for each r, m ∘ (r ·) and (r
   ·) ∘ m agree after every insertion, which is [mcol_ext] once more; its
   uniqueness is the Ab uniqueness.  The created cocone is colimiting by the
   same lemma, since its image in Ab IS N as far as the colimit predicate can
   see: [IsLimitCone] reads a cone's vertex and legs only, never its coherence
   proof.

   PACKAGING.  [mcol_strict_lift] is Structure/Limit/Creation.v's [StrictLift]
   with [slift_eq] closed by [eq_refl] and the legs by [reflexivity]; then
   [RMod_Forget_Ab_StrictlyCreatesColimit], [RMod_Forget_Ab_CreatesColimit]
   through [StrictlyCreatesLimit_CreatesLimit], and
   [RMod_Forget_Ab_creates_colimits : CreatesAllColimits (RMod_Forget_Ab R)],
   Riehl's corollary: its scope, every colimit that Ab has (this header's
   paraphrase of her words, as above), is the class's quantification over
   every shape and diagram with the colimiting cocone in Ab as the
   hypothesis.  Every record over an opposite category is built by
   its explicit constructor with the category named — [@Build_Cone],
   [@Build_ACone], [@Build_Unique], [@Build_StrictLift],
   [@Build_StrictlyCreatesLimit] — never by the [{| |}] builder, which can
   infer the record's category from the first field typed in C^op and mistype
   the rest.  By `grep -lw` for the three colimit classes over the files of
   _CoqProject, five other files name them and none inhabits one:
   Structure/Limit/Creation.v defines them and consumes them as hypotheses,
   Construction/Reflective/Colimit.v, Monad/Eilenberg/Moore/Limit.v and this
   file's sibling Instance/Mod/TensorMonad/Cocontinuous.v mention them in
   comments, and Test/ProbeReflectiveColimit434.v refuses one.  So
   these are the tree's first inhabitants of [StrictlyCreatesColimit],
   [CreatesColimit] and [CreatesAllColimits].

   UNIQUENESS, AT THE STRENGTH THE SETTING SUPPORTS.  Mac Lane's clause (i)
   asks for exactly one lift.  The lift's group is forced — it IS the nadir —
   and its action is unique up to ≈ ([mcol_smul_unique]: any family of Ab
   endomorphisms making every insertion R-linear is ≈ the created action), the
   form uniqueness of an action takes when elements are compared by a setoid's
   ≈.  At [eq_refl] it is refused: two colimit witnesses of one cocone give
   two module terms, not convertible, whose actions agree up to ≈
   ([mcol_smul_unique]; C3 of Test/ProbeTensorMonad465.v).
   [creates_lift_unique] of Structure/Limit/Creation.v gives the canonical
   isomorphism between any two lifts.

   GENERALITY, MEASURED.  The ring is any [RingObject@{a c p}]: commutativity
   is never asked for, Mac Lane's and Riehl's modules being left modules over
   a ring.  The shape [J : Category@{j c c}] has its object universe j FREE,
   bounded only through the colimit predicate (j <= l0 <= l).  The limit side
   is narrower in the shape: About on Instance/Mod/Limit.v's
   [RMod_Forget_Ab_CreatesLimit] prints the block equations u0 = u2 and
   u0 = u3.  The shape's hom universe is the ring's carrier universe there as
   here, the creation classes pinning it; its object universe is too, which
   that file's header traces to [Ab_Complete] through its transport of the
   limit to Sets.  The sibling's tensor–hom premises hold only at
   [RingObject@{c c c}].

   A WITNESS.  The theorem is unconditional but consumes a colimit in Ab, and
   the tree has no cocompleteness of Ab (Instance/Ab/DirectedColimit.v records
   the absence).  Over any shape with a terminal object, though,
   Structure/Limit/Initial.v's [terminal_Colimit] is a colimit of any diagram
   in any category, and [rmod_terminal_colimit] lifts it: its group IS U (K 1)
   and its action at r and m IS K(!)(r · m), both by [eq_refl]
   ([rmod_terminal_group], [rmod_terminal_smul]), and the action is ≈ K 1's
   own ([rmod_terminal_smul_own]).  The precedent is
   Construction/Reflective/Colimit.v's [reflective_terminal_shape_colimit];
   the price is 10 files of closure, Structure/Limit/Initial.v's, measured by
   dropping its Require (the closure falls from 68 files to 58).

   STRENGTHS.  By [eq_refl]: the lift's group is the nadir ([mcol_over_obj])
   and its insertions are the given legs ([mcol_over_legs]); the created
   action IS the mediator ([mcol_smul_is_mediator]); the colimit read back
   through [creates_colimit_lift] has the given nadir as its group and the
   given legs as its insertions ([mcol_lift_apex], [mcol_lift_legs]), and the
   whole lifted module IS [ColimMod] of that colimit read in the opposite
   category ([mcol_lift_module]); the reflected mediator's group map IS the
   Ab mediator of the underlying cocones ([mcol_reflect_mediator]); the
   witness's group and action ([rmod_terminal_group], [rmod_terminal_smul]).
   At ≈ only: the action on an inserted element ([mcol_smul_triangle]), the
   uniqueness of the action ([mcol_smul_unique]), and the witness's action
   against K 1's ([rmod_terminal_smul_own]).  Refused by conversion, each
   pinned in Test/ProbeTensorMonad465.v beside the positive half that stands:
   the action on an inserted element at [eq_refl] (C1), the module reflected
   from a cocone M of modules as M itself (C2), the modules of two colimit
   witnesses of one cocone as one (C3), and the witness's action as K 1's own
   (C4).

   WHY THEY ARE REFUSED.  Not by opacity.  In a copy of this file, its
   sibling, Instance/Mod/TensorMonad.v and their joint closure of 95 files,
   with every [Qed] made [Defined] (Instance/Sets.v too, which flips once
   [setoid_morphism_compose_respects] and its one use are given explicit
   universes), [Transparent Obligations] set and [abstract] made
   [transparent_abstract] — Structure/Cartesian/Closed.v, where that change
   is itself refused, keeping its [Qed]s, and Structure/Limit/Preservation.v's
   [preserves_colimit] given bullets that tolerate the goals the added
   transparency closes — and with the three files' universe annotations
   dropped, all four stand, each stripped copy stopping with "cannot unify"
   inside its command, and every control holds.  There
   [Print Opaque Dependencies] on [ColimMod], [mcol_reflect],
   [rmod_terminal_colimit], [RMod_Forget_Ab_CreatesColimit] and
   [mcol_smul_triangle], with the sibling's [TensorF_left_adjoint],
   [EM_Comparison], [EM_Forget] and [RMod_Forget_Ab], lists 13 constants, all
   of them Corelib's lemmas of generalized rewriting, where this tree lists
   190; no constant of Structure/Cartesian/Closed.v is among them in either.
   CORRECTION (#1347): this tree lists 187 since #1347, whose properness fields
   as terms take Corelib's [subrelation_id_proper], [proper_proper_proxy] and
   [CMorphisms.compose_proper_obligation_1] out of the census.
   C1 and C3 compare the mediator [unique_obj (HN P)], a projection out of a
   VARIABLE colimit witness, with a leg or with another witness's; C2
   compares it with the action field of a variable module M; C4 compares K(!)
   at a variable functor and terminal object with the identity.

   TRANSPARENCY, MEASURED.  Counted by token (grep -o on each keyword with its
   closing period, which keeps this sentence out of the count), 9 [Qed] and 3
   [Defined].  All three are load-bearing, each shown so by making it [Qed]
   in a copy of the whole file: [mcol_smul_cone] opaque stops
   [mcol_smul_map], whose mediator must see the cocone's vertex as N's;
   [mcol_cone] opaque stops [mcol_strict_lift]'s [eq_refl]; and
   [mcol_reflect] opaque stops the readback [mcol_reflect_mediator], which
   pins that the reflected mediator computes, the reason it is kept
   transparent, as Instance/Mod/Limit.v keeps [rmod_reflects].

   UNIVERSES, read off [About] on all 30 constants.  Every constant binds
   R : RingObject@{a c p} (roles auxiliary, carrier, proof), Ab@{o c} and
   RMod@{o x a p c}.  [mcol_smul_cone] adds the shape's object universe j; the
   constants that take a colimit witness add j and the colimit predicate's l
   and l0 ([IsLimitCone@{l l0 j c o}]); and [RMod_Forget_Ab_creates_colimits]
   binds t (the class's own level) and s (the shape's objects) instead of j.
   The strict bounds are Set < o, c < o and c < x everywhere, with c < t and
   s < t on [RMod_Forget_Ab_creates_colimits]; the rest are a <= o, c <= a,
   p <= a and the chain c, o, j <= l, c, j <= l0 <= l, with o, l <= t and
   s <= l0 on [RMod_Forget_Ab_creates_colimits].  There is no equation and no
   other [Set].  First carriers, by [About] on the donors: Set < o and c < o,
   Instance/Ab.v's [Ab@{u p}] (Set < u, p < u); c < x and a <= o,
   Instance/Mod.v's [RMod] (u3 < u0, u1 <= u); c <= a and p <= a, [RingObject]
   (u0 <= u, u1 <= u); c < t and s < t, Structure/Limit/Creation.v's
   [CreatesAllColimits] (u7 < u, u5 < u); the l chain,
   Structure/Limit/Preservation.v's [IsLimitCone].  Two donors carry levels
   outside their statements, and each such level is pinned:
   [cone_leg_coh@{u u0 u1 u2 u3 u4}]'s u3, which neither its type nor its
   block mentions, and [terminal_Colimit@{u u0 u1 u2 u3 u4}]'s u4, bounded
   only from below.  Made a placeholder in a copy of the whole file, each is
   refused with "Universe ... is unbound"; [cone_leg_coh]'s u4, also bounded
   only from below, compiles as a placeholder and is written c with the rest
   ([cone_leg_coh@{j c o c c c}], [terminal_Colimit@{j c o c l0 l}]).  The
   stdlib caps are inherited, each placed by [About] on every constant of its
   donor's dependency cone, as [Print All Dependencies] lists it, at its
   topmost carrier: compose and ID on Instance/Sets.v's
   [setoid_morphism_compose] and [setoid_morphism_id], through
   Instance/CMon.v's [cmon_hom_compose] and [cmon_hom_id] and so through
   [Ab]; prod_rect on Instance/Ab.v's [ab_cancel_l], a setoid rewrite,
   through Instance/Mod.v's [rm_smul_zero_r] and [module_act]; Projections
   (the sigma projections) on Structure/Limit/Preservation.v's
   cone-isomorphism calculus ([coneiso_from]), through
   [creates_colimit_lift].

   NOT DELIVERED.  Riehl's own proof: this file does not go through the monad,
   and her Theorem 5.6.5(ii) is not in the tree (issue #1008; the sibling's
   header lists what finishing that route takes).  No [Cocomplete (RMod R)]
   follows from this file, the tree having no [Cocomplete Ab];
   [creates_colimits_Cocomplete] would give it from one.  No comparison of the
   created colimits with Instance/Mod/Colimit.v's, obtained from the adjoint
   functor theorem, or with Instance/Mod/Coproduct.v's direct sum.  No
   preservation or reflection corollary is restated
   ([creation_preserves_colimit] and [creates_reflects_limits] apply as they
   stand).  No uniqueness of the lift at [eq_refl] (C3).  No witness at a
   shape without a terminal object: the tree has no [Colimit] in Ab of a
   discrete or parallel diagram (Instance/Ab/Coproduct.v's [Ab_Biproduct] is a
   biproduct, and no bridge to a [Colimit] over a discrete shape is built),
   and its one other [Colimit] in Ab, Instance/Ab/DirectedColimit.v's
   [ab_fg_Colimit], is over the finitely generated subgroups of a group,
   not the image of a diagram of modules.
   No right modules, and nothing registered as an [Instance]. *)

(** ** Joint epimorphicity of a colimiting cocone *)

(* Two maps out of the nadir that agree after every insertion are ≈: both
   mediate the cocone i ↦ v ∘ ι_i. *)

Lemma mcol_ext@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  {W : obj[Ab@{o c}]} (u v : vertex_obj[N] ~{Ab@{o c}}~> W)
  (H : ∀ (i : J) (m : carrier (rm_ab (K i))),
         cmon_map u (cmon_map (cone_leg N i) m)
           ≈ cmon_map v (cmon_map (cone_leg N i) m)) :
  u ≈ v.
Proof.
  unshelve eset (P := @Build_Cone (J^op) (Ab@{o c}^op)
    ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op) W
    (@Build_ACone (J^op) (Ab@{o c}^op) W _
       (fun i => v ∘[Ab@{o c}] cone_leg N i) _)).
  - intros x y f m; simpl.
    exact (proper_morphism (cmon_map v) _ _
             (cone_leg_coh@{j c o c c c} N f m)).
  - transitivity (unique_obj (HN P)).
    + symmetry. apply (uniqueness (HN P)).
      intros i m. exact (H i m).
    + apply (uniqueness (HN P)).
      intros i m. reflexivity.
Qed.

(** ** The created action on the nadir *)

(* For a fixed r, i ↦ ι_i ∘ (r ·) is a cocone in Ab; its mediator is the
   action. *)

Definition mcol_smul_cone@{a c p o x j} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (r : carrier (rig_setoid (ring_rig R))) :
  Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op).
Proof.
  unshelve refine
    (@Build_Cone (J^op) (Ab@{o c}^op)
       ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op) vertex_obj[N]
       (@Build_ACone (J^op) (Ab@{o c}^op) vertex_obj[N]
          ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op)
          (fun i => cone_leg N i ∘[Ab@{o c}] module_act (K i) r) _)).
  intros x y f m; simpl.
  transitivity (cmon_map (cone_leg N x)
                  (cmon_map (rm_hom (fmap[K] f)) (rm_smul (K y) r m))).
  - apply (proper_morphism (cmon_map (cone_leg N x))).
    symmetry. exact (rm_map_smul (fmap[K] f) r m).
  - exact (cone_leg_coh@{j c o c c c} N f (rm_smul (K y) r m)).
Defined.

Definition mcol_smul_map@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r : carrier (rig_setoid (ring_rig R))) :
  vertex_obj[N] ~{Ab@{o c}}~> vertex_obj[N] :=
  unique_obj (HN (mcol_smul_cone N r)).

Lemma mcol_smul_triangle@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r : carrier (rig_setoid (ring_rig R)))
  (i : J) (m : carrier (rm_ab (K i))) :
  cmon_map (mcol_smul_map N HN r) (cmon_map (cone_leg N i) m)
    ≈ cmon_map (cone_leg N i) (rm_smul (K i) r m).
Proof. exact (unique_property (HN (mcol_smul_cone N r)) i m). Qed.

Definition mcol_smul@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r : carrier (rig_setoid (ring_rig R)))
  (b : carrier (@vertex_obj _ _ _ N)) : carrier (@vertex_obj _ _ _ N) :=
  cmon_map (mcol_smul_map N HN r) b.

Lemma mcol_smul_respects@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) :
  Proper (equiv ==> equiv ==> equiv) (mcol_smul N HN).
Proof.
  intros r r' Hr b b' Hb. unfold mcol_smul.
  rewrite (proper_morphism (cmon_map (mcol_smul_map N HN r)) _ _ Hb).
  apply (mcol_ext N HN (mcol_smul_map N HN r) (mcol_smul_map N HN r')).
  intros i m.
  rewrite !mcol_smul_triangle.
  apply (proper_morphism (cmon_map (cone_leg N i))).
  exact (rm_smul_respects (K i) r r' Hr m m (reflexivity _)).
Qed.

Lemma mcol_smul_distr_l@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r : carrier (rig_setoid (ring_rig R)))
  (b b' : carrier (@vertex_obj _ _ _ N)) :
  mcol_smul N HN r (cmon_plus vertex_obj[N] b b')
    ≈ cmon_plus vertex_obj[N] (mcol_smul N HN r b) (mcol_smul N HN r b').
Proof. exact (cmon_map_plus (mcol_smul_map N HN r) b b'). Qed.

Lemma mcol_smul_distr_r@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r s : carrier (rig_setoid (ring_rig R)))
  (b : carrier (@vertex_obj _ _ _ N)) :
  mcol_smul N HN (rig_add (ring_rig R) r s) b
    ≈ cmon_plus vertex_obj[N] (mcol_smul N HN r b) (mcol_smul N HN s b).
Proof.
  unfold mcol_smul.
  refine (mcol_ext N HN (mcol_smul_map N HN (rig_add (ring_rig R) r s))
            (ab_hom_add (mcol_smul_map N HN r) (mcol_smul_map N HN s))
            _ b).
  intros i m.
  etransitivity; [ exact (mcol_smul_triangle N HN _ i m) | ].
  etransitivity;
    [ exact (proper_morphism (cmon_map (cone_leg N i)) _ _
               (rm_smul_distr_r (K i) r s m)) | ].
  etransitivity; [ exact (cmon_map_plus (cone_leg N i) _ _) | ].
  exact (cmon_plus_respects _ _ _
           (Equivalence_Symmetric _ _ (mcol_smul_triangle N HN r i m))
           _ _
           (Equivalence_Symmetric _ _ (mcol_smul_triangle N HN s i m))).
Qed.

Lemma mcol_smul_assoc@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r s : carrier (rig_setoid (ring_rig R)))
  (b : carrier (@vertex_obj _ _ _ N)) :
  mcol_smul N HN (rig_mul (ring_rig R) r s) b
    ≈ mcol_smul N HN r (mcol_smul N HN s b).
Proof.
  unfold mcol_smul.
  refine (mcol_ext N HN (mcol_smul_map N HN (rig_mul (ring_rig R) r s))
            (mcol_smul_map N HN r ∘[Ab@{o c}] mcol_smul_map N HN s) _ b).
  intros i m; simpl.
  rewrite mcol_smul_triangle.
  rewrite (mcol_smul_triangle N HN s i m).
  rewrite mcol_smul_triangle.
  apply (proper_morphism (cmon_map (cone_leg N i))).
  apply rm_smul_assoc.
Qed.

Lemma mcol_smul_one@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (b : carrier (@vertex_obj _ _ _ N)) :
  mcol_smul N HN (rig_one (ring_rig R)) b ≈ b.
Proof.
  unfold mcol_smul.
  refine (mcol_ext N HN (mcol_smul_map N HN (rig_one (ring_rig R)))
            (@id Ab@{o c} vertex_obj[N]) _ b).
  intros i m; simpl.
  rewrite mcol_smul_triangle.
  apply (proper_morphism (cmon_map (cone_leg N i))).
  apply rm_smul_one.
Qed.

(** ** The created module and cocone *)

Definition ColimMod@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) : obj[RMod@{o x a p c} R] :=
  @Build_RModObject R vertex_obj[N] (mcol_smul N HN)
    (mcol_smul_respects N HN) (mcol_smul_distr_l N HN)
    (mcol_smul_distr_r N HN) (mcol_smul_assoc N HN) (mcol_smul_one N HN).

Definition mcol_hom@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) (i : J) :
  K i ~{RMod@{o x a p c} R}~> ColimMod N HN :=
  @Build_RModHom R (K i) (ColimMod N HN) (cone_leg N i)
    (fun r m => Equivalence_Symmetric _ _ (mcol_smul_triangle N HN r i m)).

Definition mcol_cone@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) : Cone (K^op).
Proof.
  unshelve refine
    (@Build_Cone (J^op) ((RMod@{o x a p c} R)^op) (K^op) (ColimMod N HN)
       (@Build_ACone (J^op) ((RMod@{o x a p c} R)^op) (ColimMod N HN)
          (K^op) (mcol_hom N HN) _)).
  intros x y f m. exact (cone_leg_coh@{j c o c c c} N f m).
Defined.

(** ** Reflection, and the created cocone is colimiting *)

(* A cocone of modules whose underlying cocone is colimiting in Ab is
   colimiting; the mediator is the Ab one, R-linear by [mcol_ext]. *)

Definition mcol_reflect@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (M : Cone (K^op))
  (HM : IsLimitCone@{l l0 j c o}
          (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) M)) :
  IsLimitCone@{l l0 j c o} M.
Proof.
  intros P.
  pose (m := unique_obj
               (HM (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) P))).
  assert (Hm : ∀ (i : J) (a : carrier (rm_ab (K i))),
             cmon_map m (cmon_map (rm_hom (cone_leg M i)) a)
               ≈ cmon_map (rm_hom (cone_leg P i)) a).
  { intros i a.
    exact (unique_property
             (HM (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) P)) i a). }
  unshelve refine (@Build_Unique _ _ _ (@Build_RModHom R _ _ m _) _ _).
  - intros r b.
    refine (mcol_ext (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) M) HM
              (m ∘[Ab@{o c}] module_act vertex_obj[M] r)
              (module_act vertex_obj[P] r ∘[Ab@{o c}] m) _ b).
    intros i a; simpl.
    transitivity (cmon_map m (cmon_map (rm_hom (cone_leg M i))
                                (rm_smul (K i) r a))).
    + apply (proper_morphism (cmon_map m)).
      symmetry. exact (rm_map_smul (cone_leg M i) r a).
    + rewrite Hm.
      rewrite (rm_map_smul (cone_leg P i) r a).
      apply rm_smul_respects; [ reflexivity | ].
      symmetry. exact (Hm i a).
  - intros i a. exact (Hm i a).
  - intros v Hv b.
    exact (uniqueness
             (HM (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) P))
             (rm_hom v) Hv b).
Defined.

Definition mcol_strict_lift@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) :
  StrictLift (K^op) ((RMod_Forget_Ab@{x o o a p c} R)^op) N :=
  @Build_StrictLift _ _ _ (K^op) ((RMod_Forget_Ab@{x o o a p c} R)^op) N
    (mcol_cone N HN) eq_refl (fun i m => reflexivity _).

(** ** Riehl's Corollary 5.6.10 *)

Definition RMod_Forget_Ab_StrictlyCreatesColimit@{a c p o x j l l0}
  {R : RingObject@{a c p}} {J : Category@{j c c}}
  (K : J ⟶ RMod@{o x a p c} R) :
  StrictlyCreatesColimit@{l x l l l0 j o c o} K
    (RMod_Forget_Ab@{x o o a p c} R) :=
  @Build_StrictlyCreatesLimit (J^op) ((RMod@{o x a p c} R)^op)
    (Ab@{o c}^op) (K^op) ((RMod_Forget_Ab@{x o o a p c} R)^op)
    (fun N HN => mcol_strict_lift N HN)
    (fun N HN => mcol_reflect (mcol_cone N HN) HN)
    (fun M HM => mcol_reflect M HM).

Definition RMod_Forget_Ab_CreatesColimit@{a c p o x j l l0}
  {R : RingObject@{a c p}} {J : Category@{j c c}}
  (K : J ⟶ RMod@{o x a p c} R) :
  CreatesColimit@{l x l l l0 j o c o} K (RMod_Forget_Ab@{x o o a p c} R) :=
  StrictlyCreatesLimit_CreatesLimit
    (RMod_Forget_Ab_StrictlyCreatesColimit@{a c p o x j l l0} K).

Definition RMod_Forget_Ab_creates_colimits@{a c p o x t l l0 s}
  (R : RingObject@{a c p}) :
  CreatesAllColimits@{t l x l l l0 s o c o}
    (RMod_Forget_Ab@{x o o a p c} R) :=
  fun J K => RMod_Forget_Ab_CreatesColimit@{a c p o x s l l0} K.

(** ** Readbacks: the lift is on the nose *)

Example mcol_over_obj@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) :
  rm_ab (ColimMod N HN) = vertex_obj[N] := eq_refl.

Example mcol_over_legs@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N) (i : J) :
  rm_hom (mcol_hom N HN i) = cone_leg N i := eq_refl.

Example mcol_smul_is_mediator@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (r : carrier (rig_setoid (ring_rig R))) :
  rm_smul (ColimMod N HN) r
  = cmon_map (unique_obj (HN (mcol_smul_cone N r))) := eq_refl.

Example mcol_lift_apex@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (K : J ⟶ RMod@{o x a p c} R)
  (L : Colimit (RMod_Forget_Ab@{x o o a p c} R ◯ K)) :
  rm_ab (vertex_obj[creates_colimit_lift
           (RMod_Forget_Ab_CreatesColimit@{a c p o x j l l0} K) L])
  = vertex_obj[L] := eq_refl.

Example mcol_lift_legs@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (K : J ⟶ RMod@{o x a p c} R)
  (L : Colimit (RMod_Forget_Ab@{x o o a p c} R ◯ K)) (i : J) :
  rm_hom (cone_leg (@limit_cone _ _ _
            (creates_colimit_lift
               (RMod_Forget_Ab_CreatesColimit@{a c p o x j l l0} K) L)) i)
  = cone_leg (@limit_cone _ _ _ L) i := eq_refl.

(* The whole lifted module IS [ColimMod] of the given colimit, read in the
   opposite category. *)
Example mcol_lift_module@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (K : J ⟶ RMod@{o x a p c} R)
  (L : Colimit (RMod_Forget_Ab@{x o o a p c} R ◯ K)) :
  vertex_obj[creates_colimit_lift
     (RMod_Forget_Ab_CreatesColimit@{a c p o x j l l0} K) L]
  = ColimMod (cone_op_comp (@limit_cone _ _ _ L))
      (islimitcone_op_comp (limit_limitcone L)) := eq_refl.

(* The reflected mediator computes: its group map IS the Ab mediator of
   the underlying cocones. *)
Example mcol_reflect_mediator@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (M : Cone (K^op))
  (HM : IsLimitCone@{l l0 j c o}
          (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) M))
  (P : Cone (K^op)) :
  rm_hom (unique_obj (mcol_reflect M HM P))
  = unique_obj (HM (FCone ((RMod_Forget_Ab@{x o o a p c} R)^op) P))
  := eq_refl.

(** ** Uniqueness of the created action *)

(* Any family of Ab endomorphisms making every insertion R-linear is ≈ the
   created action. *)

Lemma mcol_smul_unique@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} {K : J ⟶ RMod@{o x a p c} R}
  (N : Cone ((RMod_Forget_Ab@{x o o a p c} R)^op ◯ K^op))
  (HN : IsLimitCone@{l l0 j c o} N)
  (s : carrier (rig_setoid (ring_rig R)) →
       vertex_obj[N] ~{Ab@{o c}}~> vertex_obj[N])
  (Hs : ∀ (i : J) r (m : carrier (rm_ab (K i))),
     cmon_map (s r) (cmon_map (cone_leg N i) m)
       ≈ cmon_map (cone_leg N i) (rm_smul (K i) r m))
  (r : carrier (rig_setoid (ring_rig R)))
  (b : carrier (@vertex_obj _ _ _ N)) :
  cmon_map (s r) b ≈ mcol_smul N HN r b.
Proof.
  refine (mcol_ext N HN (s r) (mcol_smul_map N HN r) _ b).
  intros i m. rewrite Hs. symmetry. apply mcol_smul_triangle.
Qed.

(** ** A witness: every diagram over a shape with a terminal object *)

(* Structure/Limit/Initial.v's [terminal_Colimit] is a colimit in Ab of
   U ◯ K; the lift has group U (K 1) and action K(!)(r · m). *)

Definition rmod_terminal_colimit@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (T : @Terminal J) (K : J ⟶ RMod@{o x a p c} R) :
  Colimit K :=
  creates_colimit_lift (RMod_Forget_Ab_CreatesColimit@{a c p o x j l l0} K)
    (terminal_Colimit@{j c o c l0 l} T (RMod_Forget_Ab@{x o o a p c} R ◯ K)).

Example rmod_terminal_group@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (T : @Terminal J) (K : J ⟶ RMod@{o x a p c} R) :
  rm_ab (vertex_obj[@limit_cone _ _ _
           (rmod_terminal_colimit@{a c p o x j l l0} T K)])
  = rm_ab (K (@terminal_obj J T)) := eq_refl.

Example rmod_terminal_smul@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (T : @Terminal J) (K : J ⟶ RMod@{o x a p c} R)
  (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (rm_ab (K (@terminal_obj J T)))) :
  rm_smul (vertex_obj[@limit_cone _ _ _
             (rmod_terminal_colimit@{a c p o x j l l0} T K)]) r m
  = cmon_map (rm_hom (fmap[K] (@one J T (@terminal_obj J T))))
      (rm_smul (K (@terminal_obj J T)) r m) := eq_refl.

Lemma rmod_terminal_smul_own@{a c p o x j l l0} {R : RingObject@{a c p}}
  {J : Category@{j c c}} (T : @Terminal J) (K : J ⟶ RMod@{o x a p c} R)
  (r : carrier (rig_setoid (ring_rig R)))
  (m : carrier (rm_ab (K (@terminal_obj J T)))) :
  rm_smul (vertex_obj[@limit_cone _ _ _
             (rmod_terminal_colimit@{a c p o x j l l0} T K)]) r m
  ≈ rm_smul (K (@terminal_obj J T)) r m.
Proof.
  change (cmon_map (rm_hom (fmap[K] (@one J T (@terminal_obj J T))))
            (rm_smul (K (@terminal_obj J T)) r m)
          ≈ rm_smul (K (@terminal_obj J T)) r m).
  etransitivity.
  - exact (@fmap_respects _ _ K _ _ (@one J T (@terminal_obj J T)) id
             (one_unique _ _) (rm_smul (K (@terminal_obj J T)) r m)).
  - exact (@fmap_id _ _ K _ (rm_smul (K (@terminal_obj J T)) r m)).
Qed.
