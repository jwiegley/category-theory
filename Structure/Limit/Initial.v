Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Cones.
Require Import Category.Instance.Cones.Limit.
Require Import Category.Instance.One.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Ordinal.

Generalizable All Variables.

(** * Limits over a shape with an initial object, computed by evaluation *)

(* Mac Lane:    Categories for the Working Mathematician, 2nd ed. (GTM 5),
                §III.4 Exercise 3, book p. 72   [maclane:III.4:ex3]
   Fong-Spivak: An Invitation to Applied Category Theory (Seven Sketches),
                §3.5.3 Exercise 3.98
   Riehl:       Category Theory in Context, 2nd ed., §3.1, Example and
                Exercise 3.1.vii
   nLab:        https://ncatlab.org/nlab/show/final+functor
   nLab:        https://ncatlab.org/nlab/show/limit

   THE STATEMENT.  If the indexing category J has an initial object 0, then
   every diagram F : J ⟶ C has a limit, and no construction in C is needed
   to produce it: the limit is the value F 0, and its leg at x is the image
   fmap[F] ¡ of the unique arrow ¡ : 0 ~> x.  Cone coherence is immediate,
   since fmap[F] f ∘ fmap[F] ¡ ≈ fmap[F] (f ∘ ¡) ≈ fmap[F] ¡ by uniqueness
   of arrows out of 0; and the mediator from a competing cone N is simply
   N's own leg at 0, forced because the limit's leg AT 0 is fmap[F] ¡₀ with
   ¡₀ ≈ id, again by uniqueness.  Dually, a terminal object of J computes
   colimits by evaluation at it.

   WHY THE RESULT IS NOT A CURIOSITY.  It is the nullary case of the theory
   of final (cofinal) functors: a functor K : A ⟶ J is FINAL when colimits
   over J may be computed by restricting along K, and INITIAL when limits
   may be (nLab, "final functor").  The inclusion of an initial object of J
   is an initial functor, and the inclusion of a terminal object is a final
   one; restricting to a single object leaves nothing to glue, so the
   (co)limit is the value there.  No cofinality vocabulary exists in this
   tree, and none is introduced here — see WHAT IS NOT DELIVERED.

   RELATION TO Structure/Limit/Terminal.v.  That file is the OTHER extreme
   degenerate shape: J empty, where a cone has no legs and the limit is the
   terminal object of C.  The empty category has no objects and hence no
   initial object, so [Terminal_Limit] is not an instance of anything here,
   and nothing here is an instance of it.  The two files are siblings, not
   refinements of one another.  Note also which category supplies the
   universal object in each: there, the terminal object of the TARGET C;
   here, the initial object of the SHAPE J.

   WHAT WAS ABSENT, AND EXACTLY WHAT SEARCH ESTABLISHES IT.  The tree had
   no statement constraining the indexing category's own initial object.
   Two searches are the evidence, and the claim is scoped to them; both are
   run with THIS file excluded (`-g '!Structure/Limit/Initial.v'`), since
   it now supplies the very matches at issue.  First,
   `rg 'Initial J\b|@Initial J\b' -g '*.v' .` returns nothing.  Second, the
   word-bounded survey `rg -o -N '\b@?Initial [A-Za-z_0-9]+' -g '*.v' .`
   returns twenty-nine distinct two-word matches tree-wide.  Five are prose
   inside comments ("Initial object", "Initial and", "Initial in", "Initial
   structure", and "Initial Algebra" in the paper title at
   Structure/Initial.v:76).  Of the remaining twenty-four, twenty-one name
   a category outright (`AST`, `Ab`, `Algs`, `CMon`, `Cat`, `Coq`, `Field`,
   `FinSet`, `Grp`, `MonS`, `Nat_Proset`, `Par`, `ParE`, `PointedSets`,
   `Props`, `QuiverCategory`, `Rel`, `Rig`, `Rng`, `Sets`, `Top`) and three
   are variables: `C`, the ambient category of the surrounding
   construction; `D`, the target of an equivalence, at
   Theory/Equivalence/Terminal.v:96; and `K`, which occurs only inside
   comments, at Theory/Universal/Arrow/Dual.v:262 and
   Test/ProbeCouniversal.v:128.  That is a search over the SPELLING of the
   hypothesis, not over its meaning: it establishes that nothing in tree
   writes an initial-object hypothesis on a category occupying the index
   position of a diagram.  It does not rule out an equivalent statement
   phrased in some other way.  The two subsidiary searches quoted below are
   run the same way.

   Two further absences, each checked by its own search and each the reason
   a checkbox below had to be BUILT rather than instantiated.
   `Instance/One.v:58`'s [Cat_Terminal] makes `_1` the terminal object OF
   Cat; that is not `_1` having an initial object WITHIN itself, which is
   what the point-diagram corollary needs, and `rg 'Terminal _1|Initial _1'`
   finds no such instance.  Likewise `rg 'Terminal.*Ordinal|ord_top'`
   returns nothing, so the top stage of a successor ordinal had to be
   named and its terminality proved.

   STRENGTHS, MEASURED.  Every identification below marked `eq_refl` is
   shipped as an [Example] with that proof term, so the claim is machine
   checked rather than asserted.  On the nose: the limit's legs are
   `fmap[F] zero` ([initial_leg_strict]); the apex is `F 0`
   ([initial_apex_strict]); the mediator out of a competing cone IS that
   cone's leg at 0 ([initial_med_strict]); the bundled [Limit]'s cone is
   the evaluation cone ([initial_Limit_strict]); the [Limit] recovered from
   the terminal object of [Cones F] has that same cone
   ([initial_Cones_strict]); and on the dual side the four covariant
   accessors [cocone_inj], [colimit_inj], [colimit_med] and [colimit_apex]
   all reduce to the evaluation data ([terminal_cocone_strict],
   [terminal_inj_strict], [terminal_med_strict],
   [terminal_apex_strict]).  The five witness identifications are `eq_refl`
   too: [point_Cones_strict], [point_Sets_apex], [point_Sets_med],
   [ordinal_omega_apex] and [ordinal_omega_bot].

   Only up to `≈`: [initial_leg_id] (`fmap[F] zero ≈ id` at the initial
   object) — it needs both [zero_unique] and [fmap_id], neither of which is
   a conversion.  That rejection at `eq_refl` was MEASURED, by stripping
   the statement to `Definition … := eq_refl` and reading a genuine
   `cannot unify "initial_leg I F 0" and "id{C}"`, and it is PINNED as
   negative 1 of Test/ProbeLimitInitial334.v.  The same holds of the second
   measured rejection: [Limit_Cones] at [initial_Cones_Terminal] and
   [initial_Limit] agree on their cone components by `eq_refl`
   ([initial_Cones_strict], shipped) yet are not convertible as whole
   [Limit] records; that non-convertibility was measured the same way and
   is pinned as negative 2 of the same probe file.  The
   mediator-commutation and uniqueness
   lemmas are `≈` statements because they are equations between morphisms
   of C, which is the library's setoid discipline and not a weakness.


   UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS.  [initial_IsALimit] and
   [initial_Limit] display as `@{u u0 u1 u2 u3 u4}` over
   `J : Category@{u u0 u0}` and `C : Category@{u1 u2 u2}` with `u0 = u2` in
   the block, so J's hom level is identified with its proof level and with
   C's hom and proof levels; the two OBJECT universes `u` and `u1` stay
   FREE (they carry only the bounds `u <= u3` and `u1 <= u4`).  That
   identification is the DONOR's and is not introduced here — but it is
   NOT [IsALimit]'s alone, and an earlier draft of this header said it
   was.  Measured in a section declaring the levels apart
   (`Constraint jh < jp`): `ACone c F` and `Cone F` both elaborate, while
   `cone_leg N x` (Structure/Limit/Preservation.v:108), `IsLimitCone N`
   (:166) and `IsALimit F c` (Structure/Limit.v:129) are ALL rejected,
   each with the same `Cannot enforce jp = jh because jh < jp`.  So there
   are at least three co-equal donors, TWO OF THEM CONE VOCABULARY, and
   the `ACone`/`Cone` control does not show the cause to be [IsALimit]
   rather than the cones — it rules out those two constants and nothing
   more.  Nor is [IsALimit] the donor this file meets first: [initial_med]
   already displays `u0 = u2` while its type mentions no [IsALimit] at all
   (its body is `cone_leg N initial_obj`), and [initial_IsALimit]
   INHERITS the identification rather than introducing it; [initial_leg],
   by contrast, carries only the bound `u0 <= u2`.  All three rejections
   and both controls are PINNED, as negatives 3-5 of
   Test/ProbeLimitInitial334.v.  None of the three donors carries universe
   annotations, so this remains a repairable annotation defect; it is not
   claimed that the identification is unavoidable.

   SEVEN constants carry `Set` in a constraint block — not one, as an
   earlier draft of this header said: [bool_set], [elt_acone],
   [elt_acone_obligation_1], [elt_cone], [point_Sets_apex],
   [point_Sets_med] and [point_Sets_separates], every one of them
   `Set < u` traceable to [bool_set]'s carrier `bool : Set`.  That draft
   named [bool_set] as the CAUSE while omitting it from the list of one,
   which was self-inconsistent as well as undercounted.  This is the
   ordinary price of a concrete witness and it stays local to the [Sets]
   block.  An eighth constant, [ordinal_omega_apex], mentions `Set` in a
   universe INSTANCE (`colimit_apex@{Set u Set Set}`) while acquiring no
   constraint of its own — an instance is not a constraint, and the two
   are counted separately here.  The corollaries proper do carry no `Set`:
   [point_IsALimit], [ordinal_succ_IsAColimit], [One_Initial],
   [Omega_Initial], [Ordinal_Succ_Terminal] and [Omega_no_Terminal] have
   `Set` in no constraint block.

   THE HONEST BICONDITIONAL.  Structure/Limit/Terminal.v states its result
   as an iff, and the pattern is worth matching where it can be matched.
   Here it cannot be matched in the obvious place: nothing in the converse
   direction holds, since a diagram may have a limit for reasons having
   nothing to do with its shape, and NO biconditional of the form
   `Limit F ↔ Initial J` is stated or proved below.  What IS delivered as
   an iff is [limiting_iff_initial_leg_iso]: a cone N over F is limiting
   exactly when its leg at the initial object is invertible.  Both
   directions are proved, the forward one from the two mediators' round
   trips and the backward one by transporting along the resulting cone
   isomorphism ([limitcone_transport]).  The dual
   [colimiting_iff_terminal_inj_iso] is that statement instantiated at the
   opposite categories and then composed with the field permutation of
   [iso_of_op]/[iso_to_op] — invertibility at C^op and at C are the same
   data in a different field order — so no second argument is given.

   NAMING HAZARD, DISCLOSED AND NOT ACTED ON.  Functor/Structure/Terminal.v
   :59 declares `Notation "'InitialFunctor' F" := (@TerminalFunctor _ _
   (F^op) _ _)`, so in this tree "initial functor" means "preserves the
   initial object".  The standard meaning of "initial functor" is the
   cofinality notion recalled above — the one under which the inclusion of
   an initial object into J is the reason this file's theorem is true.  The
   two senses are unrelated.  NOTHING IS RENAMED HERE; the collision is
   recorded so that whoever lands the cofinality vocabulary can resolve it
   there, which is where the issue asks for the fix.

   NOTHING IS REGISTERED FOR INSTANCE RESOLUTION.  [One_Initial],
   [Omega_Initial], [Ordinal_Succ_Terminal] and [initial_Cones_Terminal]
   are plain [Program Definition]s, not [Instance]s: a globally visible
   `Terminal (Cones F)` or `Initial Omega` would change what resolution
   finds elsewhere, and every use below passes its witness explicitly.

   WHAT IS NOT DELIVERED.
   - No cofinality theory: no notion of final or initial functor in the
     cofinal sense, no restriction theorem, no proof that the inclusion of
     the initial object is an initial functor.  The essay above explains
     the result by that theory; the file does not formalize any of it.
   - No converse, in any form.  It is not shown that a shape all of whose
     diagrams have limits computed by evaluation must have an initial
     object, and no `Limit F ↔ Initial J` is claimed.
   - No shape-indexed completeness statement.  Structure/Complete.v:115's
     [Complete] quantifies over ALL shapes, so it is not inhabited by a
     result about one shape, and no "has all limits of shape J" class
     exists in tree to inhabit; none is introduced.
   - No preservation, reflection or creation results: nothing here says
     that an arbitrary functor carries these limits to limits.
   - No uniqueness-up-to-unique-isomorphism restatement:
     Structure/Limit/Unique.v is neither instantiated nor re-derived, and
     no claim is made here about how it bears on these limits.
   - No weighted or enriched version, and no relation to
     Structure/Limit/Kan/Pointwise.v.
   - Riehl's ω+1 is NOT instantiated, and no ω+1 category exists in tree.
     What is delivered for deliverable 4 is (a) the FINITE successor
     ordinals `Ordinal (S n)`, whose top stage is proved terminal, and
     (b) [Omega_no_Terminal], the half of Riehl's remark that ω itself
     supplies: ω has an initial object ([Omega_Initial], so limits over ω
     ARE evaluation at stage 0) and provably no terminal object, which is
     exactly why a sequential colimit indexed by ω is not its value
     anywhere.  Nothing below claims `Ordinal (S n)` is ω+1.
   - Theory/Shapes.v:213's [point_of F := F ttt] names the same object as
     the apex of the point-diagram corollary below, but that file is NOT
     required here (it drags Equations, StrictCat, Two, Comma and Arrow),
     so this is a cross-reference and not reuse.  The five in-tree
     [bool_setoid_object] definitions (Instance/Sets.v:563,
     Theory/Concrete.v:244, Theory/Algebra/Rig.v:442, Instance/Top.v:784,
     Instance/Met/Extended.v:389) are a different matter — see the note at
     [bool_set] below, which corrects an earlier claim about them.  The
     same holds of [iso_of_op]/[iso_to_op]: Theory/Morphisms/CokernelPair.v
     :658 already carries that field permutation, and that module is not
     required here either. *)

(** ** The limit of a diagram over a shape with an initial object *)

Section LimitFromInitial.

Context {J C : Category}.
Context (I : @Initial J).
Context (F : J ⟶ C).

(* The leg at x is the image of the unique arrow ¡ : 0 ~> x. *)

Definition initial_leg (x : J) : F (@initial_obj J I) ~{C}~> F x :=
  fmap[F] (@zero J I x).

(* Cone coherence is uniqueness of arrows out of 0, pushed through F. *)

Lemma initial_leg_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[F] f ∘ initial_leg x ≈ initial_leg y.
Proof.
  unfold initial_leg.
  rewrite <- fmap_comp.
  apply fmap_respects.
  apply (@zero_unique J I).
Qed.

Definition initial_acone : ACone (F (@initial_obj J I)) F :=
  {| vertex_map     := initial_leg
   ; cone_coherence := @initial_leg_coherence |}.

Definition initial_cone : Cone F :=
  {| vertex_obj := F (@initial_obj J I)
   ; coneFrom   := initial_acone |}.

(* The leg AT the initial object is the identity — only up to `≈`; see the
   header's STRENGTHS paragraph for the measured rejection at `eq_refl`. *)

Lemma initial_leg_id : initial_leg (@initial_obj J I) ≈ id.
Proof.
  unfold initial_leg.
  rewrite (@zero_unique J I _ (@zero J I (@initial_obj J I)) id).
  apply fmap_id.
Qed.

(* The mediator from a competing cone is that cone's own leg at 0. *)

Definition initial_med (N : Cone F) :
  vertex_obj[N] ~{C}~> F (@initial_obj J I) :=
  cone_leg N (@initial_obj J I).

Lemma initial_med_commutes (N : Cone F) (x : J) :
  initial_leg x ∘ initial_med N ≈ cone_leg N x.
Proof.
  exact (@cone_coherence _ _ _ _ (@coneFrom _ _ _ N) _ _ (@zero J I x)).
Qed.

(* Uniqueness: evaluate the factorization condition at 0, where the leg is
   `≈ id`.  This is the whole content of the universal property. *)

Lemma initial_med_unique (N : Cone F)
  (v : vertex_obj[N] ~{C}~> F (@initial_obj J I)) :
  (∀ x : J, initial_leg x ∘ v ≈ cone_leg N x) → initial_med N ≈ v.
Proof.
  intro Hv.
  rewrite <- (Hv (@initial_obj J I)).
  rewrite initial_leg_id.
  now rewrite id_left.
Qed.

(* The three packagings: cone-level, apex-pinned, and bundled. *)

Definition initial_IsLimitCone : IsLimitCone initial_cone :=
  fun N =>
    {| unique_obj      := initial_med N
     ; unique_property := initial_med_commutes N
     ; uniqueness      := initial_med_unique N |}.

Definition initial_IsALimit : IsALimit F (F (@initial_obj J I)) :=
  limitcone_isalimit initial_IsLimitCone.

Definition initial_Limit : Limit F :=
  limitcone_limit initial_cone initial_IsLimitCone.

(* Strictness, measured. *)

Example initial_leg_strict (x : J) :
  limit_leg initial_IsALimit x = fmap[F] (@zero J I x) := eq_refl.

Example initial_apex_strict :
  @vertex_obj _ _ _ initial_cone = F (@initial_obj J I) := eq_refl.

Example initial_med_strict (N : Cone F) :
  limit_med initial_IsALimit N = cone_leg N (@initial_obj J I) := eq_refl.

Example initial_Limit_strict :
  @limit_cone _ _ _ initial_Limit = initial_cone := eq_refl.

(** *** The evaluation cone as a terminal object of [Cones F] *)

(* The terminal-cone reading of the same fact: the evaluation cone is a
   terminal object of Instance/Cones.v's category of cones over F.  This is
   what Instance/Cones/Limit.v's [Limit_Cones] consumes, so the two
   presentations can be compared — see [initial_Cones_strict]. *)

Program Definition initial_Cones_Terminal : @Terminal (Cones F) := {|
  terminal_obj := initial_cone;
  one          := fun N => (initial_med N; initial_med_commutes N)
|}.
Next Obligation.
  rewrite <- (initial_med_unique x f X0).
  now rewrite <- (initial_med_unique x g X).
Qed.

Example initial_Cones_strict :
  @limit_cone _ _ _ (@Limit_Cones J C F initial_Cones_Terminal)
    = initial_cone := eq_refl.

(** *** The honest biconditional *)

(* A cone over F is limiting exactly when its leg at the initial object is
   invertible.  Forward: the two mediators are mutually inverse, each round
   trip being pinned by a uniqueness clause.  Backward: that inverse is a
   cone isomorphism from the evaluation cone, along which limiting-ness
   transports. *)

Theorem limiting_iff_initial_leg_iso (N : Cone F) :
  IsLimitCone N ↔ IsIsomorphism (cone_leg N (@initial_obj J I)).
Proof.
  split.
  - intro HN.
    unshelve refine
      {| two_sided_inverse := unique_obj (HN initial_cone) |}.
    + rewrite (unique_property (HN initial_cone) (@initial_obj J I)).
      exact initial_leg_id.
    + transitivity (unique_obj (HN N)).
      * symmetry.
        apply (uniqueness (HN N)).
        intro x.
        rewrite comp_assoc.
        rewrite (unique_property (HN initial_cone) x).
        exact (initial_med_commutes N x).
      * apply (uniqueness (HN N)).
        intro x; now rewrite id_right.
  - intro Hiso.
    unshelve refine (limitcone_transport _ initial_IsLimitCone).
    unshelve eexists.
    + unshelve refine {| to   := two_sided_inverse
                       ; from := cone_leg N (@initial_obj J I) |}.
      * apply is_left_inverse.
      * apply is_right_inverse.
    + intro x; simpl.
      rewrite <- (initial_med_commutes N x).
      rewrite <- comp_assoc.
      rewrite is_right_inverse.
      now rewrite id_right.
Qed.

End LimitFromInitial.

(** ** Reading invertibility back from the opposite category *)

(* [IsIsomorphism] at C^op and at C carry the same inverse and swap their
   two law fields, so passing between them is a field permutation with no
   proof content.  Theory/Morphisms/CokernelPair.v:658 already carries this
   pair, as [IsIsomorphism_of_op] and [op_IsIsomorphism_of]; that module is
   NOT required here — it pulls Theory/Morphisms.v, Structure/Pullback.v,
   Structure/Pushout.v, Theory/Morphisms/Stability.v and
   Theory/Morphisms/Duality.v onto every consumer — so the idiom is copied
   under names that do not collide with it. *)

Section OpIso.

Context {C : Category}.

Definition iso_of_op {a b : C} (h : b ~> a)
  (H : @IsIsomorphism (C^op) a b h) : @IsIsomorphism C b a h :=
  @Build_IsIsomorphism C b a h
    (@two_sided_inverse (C^op) a b h H)
    (@is_left_inverse (C^op) a b h H)
    (@is_right_inverse (C^op) a b h H).

Definition iso_to_op {a b : C} (h : b ~> a)
  (H : @IsIsomorphism C b a h) : @IsIsomorphism (C^op) a b h :=
  @Build_IsIsomorphism (C^op) a b h
    (@two_sided_inverse C b a h H)
    (@is_left_inverse C b a h H)
    (@is_right_inverse C b a h H).

End OpIso.

(** ** The dual: a terminal shape computes colimits by evaluation *)

(* Everything here is the section above read at J^op and C^op.
   `Initial (J^op)` is notation for `Terminal ((J^op)^op)`, and
   Construction/Opposite.v builds duality so that (J^op)^op is J on the
   nose, so a `Terminal J` IS the hypothesis the primal section wants.  The
   four packagings and the two accessors are supplied by `:=` with no
   tactic.  Of the three lemmas, only [terminal_inj_id] is a single
   [exact] of a PRIMAL lemma (`@initial_leg_id (J^op) (C^op) T (F^op)`);
   an earlier draft of this header said all three were, which is wrong on
   two counts.  [terminal_med_commutes] is a single [exact] of
   [colimit_med_commutes] — a Structure/Limit/Preservation.v ACCESSOR, not
   a primal lemma of this file — and [terminal_med_unique] introduces its
   hypothesis first, so it is TWO tactics and again of an accessor.  The
   biconditional is the primal one composed with the field permutation of
   [iso_of_op]/[iso_to_op].  No second argument is given anywhere.

   The accessors are stated covariantly, in C: no `^op` appears in any type
   below, which is the point of routing through
   Structure/Limit/Preservation.v's [Cocone], [cocone_inj], [IsAColimit],
   [colimit_inj] and [colimit_med]. *)

Section ColimitFromTerminal.

Context {J C : Category}.
Context (T : @Terminal J).
Context (F : J ⟶ C).

(* The injection at x is the image of the unique arrow ! : x ~> 1. *)

Definition terminal_inj (x : J) : F x ~{C}~> F (@terminal_obj J T) :=
  fmap[F] (@one J T x).

Definition terminal_cocone : Cocone F :=
  @initial_cone (J^op) (C^op) T (F^op).

Definition terminal_IsColimitCocone : IsColimitCocone terminal_cocone :=
  @initial_IsLimitCone (J^op) (C^op) T (F^op).

Definition terminal_IsAColimit : IsAColimit F (F (@terminal_obj J T)) :=
  @initial_IsALimit (J^op) (C^op) T (F^op).

Definition terminal_Colimit : Colimit F :=
  @initial_Limit (J^op) (C^op) T (F^op).

(* The mediator out of the colimit into a competing cocone is that
   cocone's own injection at the terminal object. *)

Definition terminal_med (N : Cocone F) :
  F (@terminal_obj J T) ~{C}~> vertex_obj[N] :=
  cocone_inj N (@terminal_obj J T).

Lemma terminal_med_commutes (N : Cocone F) (x : J) :
  terminal_med N ∘ terminal_inj x ≈ cocone_inj N x.
Proof. exact (colimit_med_commutes terminal_IsAColimit N x). Qed.

Lemma terminal_med_unique (N : Cocone F)
  (v : F (@terminal_obj J T) ~{C}~> vertex_obj[N]) :
  (∀ x : J, v ∘ terminal_inj x ≈ cocone_inj N x) → terminal_med N ≈ v.
Proof. intro Hv. exact (colimit_med_unique terminal_IsAColimit N v Hv). Qed.

Lemma terminal_inj_id : terminal_inj (@terminal_obj J T) ≈ id.
Proof. exact (@initial_leg_id (J^op) (C^op) T (F^op)). Qed.

(* Strictness of the covariant accessors, measured. *)

Example terminal_cocone_strict (x : J) :
  cocone_inj terminal_cocone x = terminal_inj x := eq_refl.

Example terminal_inj_strict (x : J) :
  colimit_inj terminal_IsAColimit x = terminal_inj x := eq_refl.

Example terminal_med_strict (N : Cocone F) :
  colimit_med terminal_IsAColimit N = terminal_med N := eq_refl.

Example terminal_apex_strict :
  colimit_apex terminal_Colimit = F (@terminal_obj J T) := eq_refl.

(* The dual biconditional.  The primal theorem supplies both directions
   with no second argument; the only residue is that invertibility at C^op
   and at C are the same data in a different field order, which [iso_of_op]
   and [iso_to_op] permute. *)

Definition colimiting_iff_terminal_inj_iso (N : Cocone F) :
  IsColimitCocone N ↔ IsIsomorphism (cocone_inj N (@terminal_obj J T)) :=
  (fun H => iso_of_op _
     (fst (@limiting_iff_initial_leg_iso (J^op) (C^op) T (F^op) N) H),
   fun H => snd (@limiting_iff_initial_leg_iso (J^op) (C^op) T (F^op) N)
     (iso_to_op _ H)).

End ColimitFromTerminal.

(** ** Deliverable: the point shape (Seven Sketches §3.5.3 Ex 3.98) *)

(* `_1` has an initial object — its unique object — and that instance did
   not exist: Instance/One.v:58's [Cat_Terminal] says `_1` is terminal in
   Cat, a different statement (see the header). *)

Program Definition One_Initial : @Initial _1 := {|
  terminal_obj := ttt;
  one          := fun _ => ttt
|}.
Next Obligation. now destruct f, g. Qed.

(* The limit of a diagram of shape 1 is its value at the point.  This is
   the section-1 theorem instantiated, not a second construction. *)

Definition point_cone {C : Category} (F : _1 ⟶ C) : Cone F :=
  @initial_cone _1 C One_Initial F.

Definition point_IsALimit {C : Category} (F : _1 ⟶ C) :
  IsALimit F (F ttt) := @initial_IsALimit _1 C One_Initial F.

Definition point_Limit {C : Category} (F : _1 ⟶ C) : Limit F :=
  @initial_Limit _1 C One_Initial F.

(* The cross-check the exercise asks for: the same cone is a TERMINAL
   OBJECT of the category of cones, and the [Limit] that
   Instance/Cones/Limit.v reads off it is the very cone built above. *)

Definition point_Cones_Terminal {C : Category} (F : _1 ⟶ C) :
  @Terminal (Cones F) := @initial_Cones_Terminal _1 C One_Initial F.

Example point_Cones_strict {C : Category} (F : _1 ⟶ C) :
  @limit_cone _ _ _ (@Limit_Cones _1 C F (point_Cones_Terminal F))
    = point_cone F := eq_refl.

(** *** A computing witness in Sets *)

(* [bool_set] is a REDUNDANT REDECLARATION, and an earlier draft of this
   note gave a reason for it that is false.  That draft said the tree had
   TWO [bool_setoid_object] definitions, in Theory/Concrete.v and
   Theory/Algebra/Rig.v, "neither of which this file has any other reason
   to require".  There are FIVE, and one of them — Instance/Sets.v:563,
   `bool_setoid_object@{t u}` — is byte-identical in content to [bool_set]
   and lives in a module this file ALREADY requires at line 16.  It is
   convertible on the nose (`bool_setoid_object = bool_set := eq_refl`
   compiles against this file's own import list, no new Require), and both
   [Sets] witnesses below replay verbatim against it.  So the copy was
   never forced.  It is kept rather than removed because deleting it is a
   code change, not a correction of the record.  The cone apex, by
   contrast, IS reused
   — it is Instance/Sets.v:253's terminal singleton, so a cone over a point
   diagram with that apex is literally a global element, and the mediator
   below is the element it names. *)

Program Definition bool_set : obj[Sets] :=
  {| carrier := bool ; is_setoid := {| equiv := eq |} |}.

Program Definition elt_acone (b : bool) :
  ACone (@terminal_obj Sets Sets_Terminal) (=(bool_set)) := {|
  vertex_map := fun _ => {| morphism := fun _ => b |}
|}.

Definition elt_cone (b : bool) : Cone (=(bool_set)) :=
  {| vertex_obj := @terminal_obj Sets Sets_Terminal
   ; coneFrom   := elt_acone b |}.

Example point_Sets_apex :
  @vertex_obj _ _ _ (@limit_cone _ _ _ (point_Limit (=(bool_set))))
    = bool_set := eq_refl.

(* The mediator computes: it is the element the competing cone names. *)

Example point_Sets_med (b : bool) :
  limit_med (point_IsALimit (=(bool_set))) (elt_cone b) ttt = b := eq_refl.

(* Non-degeneracy, and it is worth being exact about what this adds.  The
   identification `limit_med … N = cone_leg N 0` holds at ARBITRARY
   arguments ([initial_med_strict]), so instantiating it proves nothing on
   its own.  What is specific to this diagram is that two cones over it
   have provably different mediators, so the limit apex has at least two
   distinct elements.  Be exact about the MECHANISM too: because the
   mediator is DEFINITIONALLY the cone's leg, the statement reduces to
   `true <> false` and [discriminate] closes it — no commutation or
   uniqueness lemma is consumed, so it is not the universal property that
   separates, as an earlier draft of this note said.  What the example
   establishes is the apex's two distinct elements, which is what makes
   the corollary non-degenerate: over a subsingleton apex any two
   mediators would agree automatically. *)

Example point_Sets_separates :
  limit_med (point_IsALimit (=(bool_set))) (elt_cone true) ttt
    <> limit_med (point_IsALimit (=(bool_set))) (elt_cone false) ttt.
Proof. discriminate. Qed.

(** ** Deliverable: successor ordinals (Riehl §3.1) *)

(* The top stage of `Ordinal (S n)`, and its bottom stage, neither of which
   was named in Instance/Ordinal.v. *)

Definition ord_top (n : nat) : Ord_obj (S n) := ord_at n le_t_n.

Definition ord_bot (n : nat) : Ord_obj (S n) :=
  ord_at 0 (le_t_SS (le_t_zero n)).

Lemma ord_top_neq_bot (n : nat) : ord_top (S n) <> ord_bot (S n).
Proof. intro H; discriminate (f_equal ord_val H). Qed.

(* The top stage is terminal: the arrow from x is the bound of x with one
   successor peeled off both sides, and uniqueness is thinness of `le_t`. *)

Program Definition Ordinal_Succ_Terminal (n : nat) :
  @Terminal (Ordinal (S n)) := {|
  terminal_obj := ord_top n;
  one          := fun x => le_t_SS_inv (ord_bound x)
|}.
Next Obligation. apply le_t_irr. Qed.

(* Hence: the colimit of a diagram indexed by a successor ordinal is its
   value at the top stage. *)

Definition ordinal_succ_IsAColimit {n : nat} {C : Category}
  (G : Ordinal (S n) ⟶ C) : IsAColimit G (G (ord_top n)) :=
  @terminal_IsAColimit (Ordinal (S n)) C (Ordinal_Succ_Terminal n) G.

Definition ordinal_succ_Colimit {n : nat} {C : Category}
  (G : Ordinal (S n) ⟶ C) : Colimit G :=
  @terminal_Colimit (Ordinal (S n)) C (Ordinal_Succ_Terminal n) G.

(* A witness whose diagram genuinely varies from stage to stage:
   Instance/Ordinal.v's embedding of `Ordinal (S n)` into ω sends a stage
   to its own index, so the colimit apex is the numeral n and the bottom
   stage is 0.  The same honesty note applies as in the [Sets] witness:
   `colimit_apex … = G (ord_top n)` holds at ARBITRARY G
   ([terminal_apex_strict]), so the apex computation alone shows nothing.
   What is specific here is [ordinal_omega_nonconstant] — the diagram takes
   different values at the bottom and top stages, so "the colimit is the
   value at the top stage" is not a statement about a constant diagram. *)

Example ordinal_omega_apex (n : nat) :
  colimit_apex (ordinal_succ_Colimit (Ord_Omega (S n))) = n := eq_refl.

Example ordinal_omega_bot (n : nat) :
  Ord_Omega (S n) (ord_bot n) = 0%nat := eq_refl.

Lemma ordinal_omega_nonconstant (n : nat) :
  Ord_Omega (S (S n)) (ord_bot (S n))
    <> Ord_Omega (S (S n)) (ord_top (S n)).
Proof. discriminate. Qed.

(** *** Why ω itself is outside the colimit half of the theorem *)

(* ω has an initial object, so LIMITS over ω are evaluation at stage 0 by
   the first section — and provably no terminal object, so the second
   section says nothing about colimits over ω.  That asymmetry is Riehl's
   reason for indexing sequential colimits by ω rather than by a successor
   ordinal: over a successor ordinal the colimit is the top stage and
   nothing is glued.  Note that `Ordinal (S n)` is a FINITE successor
   ordinal; ω+1 is not a category in this tree and is not claimed to be. *)

Program Definition Omega_Initial : @Initial Omega := {|
  terminal_obj := 0%nat;
  one          := fun x => le_t_zero x
|}.
Next Obligation. apply le_t_irr. Qed.

Theorem Omega_no_Terminal : @Terminal Omega → False.
Proof.
  intro T.
  exact (le_t_no_desc (@one Omega T (S (@terminal_obj Omega T)))).
Qed.
