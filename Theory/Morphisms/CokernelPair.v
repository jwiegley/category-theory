Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Morphisms.Duality.

Generalizable All Variables.

(** * Cokernel pairs, and epimorphisms as pushout squares *)

(* nLab:      https://ncatlab.org/nlab/show/cokernel+pair
              https://ncatlab.org/nlab/show/kernel+pair
   Wikipedia: https://en.wikipedia.org/wiki/Epimorphism

   Mac Lane, CWM 2nd ed., §III.3 p. 66 (`maclane:III.3:def7`) and §III.4
   Exercise 4 p. 72 (`maclane:III.4:ex4`).  Fong and Spivak, *Seven
   Sketches in Compositionality*, §7.2.1 Definition 7.5, printed p. 226
   (`7sketches:7.2.1:def7.5`).

   The COKERNEL PAIR of f : x ~> y is the pushout of f with itself: an
   object together with a PARALLEL PAIR u, v : y ~> P satisfying
   u ∘ f ≈ v ∘ f and universal among such pairs.  It is the exact dual of
   Structure/Regular.v's [kernel_pair f := pullback f f], and the two are
   the standard measure of how far f is from being epic (resp. monic): f
   is an epimorphism exactly when its cokernel pair is TRIVIAL, i.e. when
   its two legs coincide, equivalently when the square

       x ---f---> y
       |          |
      f|          | id
       v          v
       y ---id--> y

   is a pushout.  Fong and Spivak take that square to BE the definition of
   an epimorphism, with no hypotheses on the ambient category; Mac Lane
   phrases the same fact through the cokernel pair.  Both readings are
   delivered below, and proved equivalent to Theory/Morphisms.v's
   right-cancellation [Epic].

   ------------------------------------------------------------------
   ** Disambiguation

   This is NOT Structure/Kernel.v's cokernel.  That is the zero-object
   notion — the coequalizer of f against the zero morphism — and it needs
   a [ZeroObject].  The cokernel pair needs nothing but a pushout, and in
   a category with a zero object the two are genuinely different objects.
   The names are close enough to mislead, so nothing here is stated in
   terms of [IsCokernel] and nothing there is stated in terms of this
   file's [IsCokernelPair].

   ------------------------------------------------------------------
   ** Engineering finding: the tree's two pushout notions are named
      inconsistently, and the issue's suggested spelling was unusable

   The library carries two pullback notions and, until this file, only one
   pushout notion:

     - Structure/Pullback.v:161 [Record Pullback f g] is BUNDLED: it
       carries its apex [Pull] as data, so it cannot say that a GIVEN
       square is a pullback.
     - Theory/Morphisms/Stability.v:53 [Record IsPullback f g P p1 p2] is
       APEX-PINNED: apex and both legs are parameters.  That file's own
       header says in terms why it had to exist.
     - Structure/Pushout.v:47 [IsPushout f g := @Pullback (C^op) y z x f g]
       is BUNDLED — despite the [Is] prefix, which in the pullback half of
       the tree marks the pinned form.

   So the name [IsPushout] was already taken, by the form that CANNOT
   state "this square is a pushout".  Read the consequence precisely, and
   NOT as an expressibility claim: the theorem's STATEMENT was already
   writable with what existed, as [@IsPullback (C^op) y z x f g P i1 i2] —
   which is exactly what [IsPushoutSquare] abbreviates, by [eq_refl] — and
   a file importing only pre-commit modules elaborates it.  What did not
   exist is a NAMED, C-facing apex-pinned pushout predicate with accessors
   and a smart constructor, and the natural name for one was taken.  An
   earlier draft of this header said the statement was "not expressible
   with what existed"; that was false and an audit refuted it by compiling
   the pre-existing spelling.  The predicate is called [IsPushoutSquare]
   here; renaming the existing constant was out of scope.

   The predicate itself costs nothing.  Exactly as [IsPushout] is
   [Pullback] in C^op, [IsPushoutSquare] is [IsPullback] in C^op, and its
   two field readings [is_pushout_square_commutes] and
   [is_pushout_square_ump], its C-facing smart constructor
   [Build_IsPushoutSquare], and BOTH conversions with the bundled
   [IsPushout] are supplied by [:=] with NO tactic: the two record fields
   of [IsPullback] read at C^op ARE the commuting square and the universal
   property of a pushout in C, on the nose.  (The mediator kit
   [pushout_square_med_in1] and its three siblings do use tactics; they are
   re-derived directly from [unique_property], and are NEW content rather
   than Structure/Pushout.v's mediator lemmas read at C^op — the two
   mediators are not even convertible, [pushout_med] routing through the
   [Qed]-opaque [pushout_ump] where [pushout_square_med] routes through the
   transparent [is_pushout_square_ump].  Stability.v has no mediator kit
   for [IsPullback] at all.)  The
   round trip through the bundled form closes at [eq_refl] on the WHOLE
   record, guarded as [ctl_roundtrip] in Test/ProbeCokernelPair.v.

   ------------------------------------------------------------------
   ** Engineering finding: writing INTO the C^op reading

   Reading a [IsPushoutSquare] is free; BUILDING one directly is not, and
   the reason is worth recording.  Under [constructor] the two goals are
   presented at C^op, where the cocone legs precompose on the LEFT, so
   [id_left] and [id_right] exchange roles and — worse — the identity
   written in the STATEMENT elaborates as [@id C y] while the goal's head
   is [@compose (C^op) …], which makes [apply id_left] and
   [exact (id_right _)] both fail with "Unable to unify C with C^op" even
   though the terms are convertible: [apply] fixes the category from the
   [id] argument before it reaches the composite.

   Two things follow, and both are in the code rather than in prose.
   First, [Build_IsPushoutSquare] exists so that no caller ever meets that
   presentation; it takes both hypotheses in C-facing form and every proof
   below is an ordinary C-level argument.  Second, the record-literal
   syntax [{| is_pullback_commutes := …; … |}] does NOT work in its body:
   [IsPushoutSquare] is a transparent [Definition], but the literal is
   elaborated against fresh metavariables rather than against the expected
   type, and unification then reads [i1 ∘ f ≈ i2 ∘ g] as a pullback square
   in C with apex [x] — a silently wrong instantiation that surfaces as a
   confusing "cannot unify" against a goal nobody wrote.  The constructor
   must be applied explicitly, [@Build_IsPullback (C^op) y z x f g P i1 i2
   Hcomm Hump].  The same applies to [IsIsomorphism] at C^op, which is why
   [IsIsomorphism_of_op] spells [@Build_IsIsomorphism] out.

   ------------------------------------------------------------------
   ** Universes, measured in the constraint blocks

   Every principal artifact states its category with hom and proof
   IDENTIFIED and the object universe bounded but NEVER identified with
   them — that is the substantive fact, and it holds throughout.  The
   PARAMETER COUNT is not uniform, and an earlier draft of this header
   claimed as measured that it was three everywhere with the category
   always [Category@{u u0 u0}]; an audit refuted that.  Measured:
   [epic_iff_pushout_square@{u u0 u1}] and [monic_iff_pullback_square@{u
   u0 u1}] are three over [Category@{u u0 u0}], but
   [epic_iff_cokernel_pair_trivial], [epic_iff_cokernel_pair_left_iso] and
   [IsCokernelPair] each carry FOUR, and [IsCokernelPair@{u u0 u1 u2}] and
   [cokernel_pair@{u u0 u1}] state their category as [Category@{u0 u1 u1}]
   rather than [Category@{u u0 u0}], with [IsCokernelPair]'s block reading
   [u0 <= u2, u1 <= u2, u2 <= u].

   That identification is INHERITED, and it is attributed PER DONOR rather
   than guessed: over a [Category@{uo uh up}] declared with the strict
   [Constraint uh < up], each of [Epic] (Theory/Morphisms.v),
   [Pullback] (Structure/Pullback.v), [IsPullback]
   (Theory/Morphisms/Stability.v) and [IsPushout] (Structure/Pushout.v) is
   INDEPENDENTLY rejected, each reporting "universe inconsistency: Cannot
   enforce vp = vh because vh < vp", while the ambient category and its
   hom-sets are perfectly formable at that setting.  So [Epic] alone and
   [IsPullback] alone each suffice to force it and nothing in this file
   adds to it; negatives 5-9 and their control pin this, one per donor.
   The identification is NOT claimed unavoidable — no attempt was made to
   repair the donors.

   ------------------------------------------------------------------
   ** What is proved, and at what strength

   - [IsPushoutSquare] with its C-facing accessor and mediator layer, its
     smart constructor, and both conversions with [IsPushout].  No
     [Program] and no obligation anywhere in the file.

   - [cokernel_pair f : IsPushout f f] under [HasPushouts], mirroring
     [kernel_pair f : Pullback f f] one for one; the one-off apex-pinned
     form [IsCokernelPair f P u v]; and the accessor layer [ckp_obj],
     [ckp_left], [ckp_right], [ckp_commutes], [ckp_ump] with its mediator
     kit, stated for an ARBITRARY [IsPushout f f] so that the chosen and
     one-off forms are both served.  [ckp_ump] is stated on PARALLEL PAIRS
     COEQUALIZING f, which is the shape a consumer wants.

   - [epic_iff_pushout_square] : Epic f ↔ IsPushoutSquare f f y id id.
     This is Seven Sketches Definition 7.5 against the library's [Epic],
     as a biconditional, over an arbitrary category with no hypotheses at
     all — in particular with no [HasPushouts], since the square names its
     own apex.

   - [epic_iff_cokernel_pair_trivial] : for ANY [P : IsPushout f f],
     Epic f ↔ ckp_left P ≈ ckp_right P.  Mac Lane's phrasing.

   - [epic_iff_cokernel_pair_left_iso] : the same at full strength —
     Epic f ↔ IsIsomorphism (ckp_left P) — with the two-sided inverse
     named ([epic_ckp_left_iso] exhibits it as the mediator of the pair
     (id, id)).  The forward direction is the useful one; the converse
     holds too and is proved, so "the cokernel pair is trivial" is a
     characterization and not merely a consequence.

     [epic_iff_chosen_ckp_trivial] and [epic_iff_chosen_ckp_left_iso] are
     the same two statements at the CHOSEN cokernel pair under
     [HasPushouts], supplied by [:=] so a consumer need not spell the
     pushout argument.

   - The [Monic] dual, DERIVED VIA C^op AND NOT REPROVED
     ([monic_iff_pullback_square], [monic_iff_kernel_pair_trivial],
     [monic_iff_kernel_pair_fst_iso]).  The derivation is literal: the
     three statements are the three [Epic] ones instantiated at C^op and
     re-typed through Duality.v's [Monic_of_op_Epic]/[op_Epic_of_Monic],
     with no tactic reasoning of their own beyond a two-line [split].
     FOUR conversions carry the transfer, and all four are MEASURED rather
     than assumed: [op_collapse_pushout_square],
     [op_collapse_cokernel_pair], [op_collapse_ckp_left] and
     [op_collapse_ckp_right] close by [eq_refl] — the first because
     (C^op)^op is C definitionally in this library
     (Construction/Opposite.v), the others because a pushout of f with
     itself at C^op IS a pullback of f with itself at C and the
     cokernel-pair legs there ARE the pullback projections here.

     ONE step of the transfer is NOT definitional, and the file says so
     rather than rounding it off: [IsIsomorphism] at C^op and at C carry
     the same inverse but their two law fields are SWAPPED, so
     [IsIsomorphism_of_op]/[op_IsIsomorphism_of] are a field permutation
     and the [eq_refl] identification is REFUTED (negative 1).  That is
     why [monic_iff_kernel_pair_fst_iso] is stated in C rather than left
     reading in C^op.

   NINE negatives in all are pinned in Test/ProbeCokernelPair.v — three
   CONVERSION and six FORMABILITY, kept lexically apart — against twelve
   positive controls.  The sharpest is negative 4: it is the structural
   claim above, made machine-checkable by showing that
   [IsPushout f f y id id] is an "Illegal application" — a TYPING error,
   not a universe inconsistency — so the bundled form provably cannot
   state the epimorphism square.

   The mono half of Seven Sketches Definition 7.5 is issue #672's
   territory; what is delivered here is the dual of THIS issue's epi
   theorem, obtained by duality, not that issue's development.

   ------------------------------------------------------------------
   ** Correction to a claim about the tree

   Issue #323 states that `rg 'cokernel.?pair|CokernelPair'` returns 0
   hits.  THAT IS FALSE, and it was false when the issue was written.
   Three genuine cokernel-pair constructions exist, each built to prove
   "epi ⟹ surjective" in its own category:

     - Instance/Sets.v:448-505, [Section CokernelPair]: [CKSetoid],
       [ck_left], [ck_right], [ck_agree];
     - Instance/Top.v:579-726, [Section CokernelPair]: [CokernelPair],
       [CP_leftLeg], [CP_rightLeg], [CP_legs_agree];
     - Instance/Sets/Pointed.v:401-523, the pointed cokernel pair.

   What is genuinely absent — the sharper gap, and the one this file
   closes — is that NONE of the three is ever related to a pushout.  Each
   supplies an apex, two legs and the equation [u ∘ f ≈ v ∘ f], and stops
   there: no universal property of any of them is proved, the string
   "pushout" does not occur in Instance/Top.v or Instance/Sets/Pointed.v
   at all, and in Instance/Sets.v it occurs only at :116 in an unrelated
   header line.  So three concrete cokernel pairs existed and none of them
   knew it was a pushout.  Instance/Sets/CokernelPair.v repairs that for
   the [Sets] one.

   ------------------------------------------------------------------
   ** NOT DELIVERED (scoped)

   - No functoriality: the cokernel pair is not exhibited as a functor on
     the arrow category, and no adjunction with an equalizer functor is
     built.  That is issue #364's obligation, which is written to CONSUME
     this file's [cokernel_pair] rather than redefine it.

   - No relation to [RegularEpi] or to [Structure/Regular.v]'s
     [regular_coeq]: it is NOT proved here that the coequalizer of a
     cokernel pair is anything in particular, nor that f is a regular epi
     when it coequalizes its own kernel pair.

   - No [HasPushouts] instance is added; the three that exist (Sets,
     FinSet, Proset) are untouched.

   - The [Top] and [Sets/Pointed] cokernel pairs are NOT identified with
     this API.  Only the [Sets] one is, in Instance/Sets/CokernelPair.v.
     Nothing is claimed about whether the other two are pushouts; the
     universal property is simply not proved for them here.

   - No uniqueness-up-to-unique-iso statement for cokernel pairs in
     general.  [epic_iff_cokernel_pair_left_iso] gives an isomorphism only
     in the epic case, where the comparison object is the codomain itself;
     the general two-cokernel-pairs comparison would be
     [pullback_transport] read at C^op and is not performed. *)

(** ** The apex-pinned pushout square *)

Section PushoutSquare.

Context {C : Category}.

(* The square

        x ---g---> z
        |          |
       f|          | i2
        v          v
        y ---i1--> P

   commutes and enjoys the universal property of a pushout.  This is
   [IsPullback] read in C^op, where composition is reversed: the field
   [is_pullback_commutes] there reads [i1 ∘ f ≈ i2 ∘ g] here, and
   [is_pullback_ump] there reads as the mediation of cocones here. *)
Definition IsPushoutSquare {x y z : C} (f : x ~> y) (g : x ~> z)
           (P : C) (i1 : y ~> P) (i2 : z ~> P) : Type :=
  @IsPullback (C^op) y z x f g P i1 i2.

Section Accessors.

Context {x y z : C} {f : x ~> y} {g : x ~> z}.
Context {P : C} {i1 : y ~> P} {i2 : z ~> P}.

(* The C-facing smart constructor.  Without it a caller must build the
   square with goals displayed in C^op, where the legs precompose on the
   left and [id_left]/[id_right] swap roles — an elaboration nuisance
   recorded in the header.  Like the readers below it is definitional:
   both hypotheses fit the C^op record fields by conversion alone. *)
Definition Build_IsPushoutSquare
           (Hcomm : i1 ∘ f ≈ i2 ∘ g)
           (Hump : ∀ (Q : C) (q1 : y ~> Q) (q2 : z ~> Q),
               q1 ∘ f ≈ q2 ∘ g →
               ∃! u : P ~> Q, u ∘ i1 ≈ q1 ∧ u ∘ i2 ≈ q2)
  : IsPushoutSquare f g P i1 i2 :=
  @Build_IsPullback (C^op) y z x f g P i1 i2 Hcomm Hump.

(* Both field readings are definitional: supplied by [:=], no tactic. *)

Definition is_pushout_square_commutes (H : IsPushoutSquare f g P i1 i2) :
  i1 ∘ f ≈ i2 ∘ g := is_pullback_commutes H.

Definition is_pushout_square_ump (H : IsPushoutSquare f g P i1 i2)
           (Q : C) (q1 : y ~> Q) (q2 : z ~> Q) (Hc : q1 ∘ f ≈ q2 ∘ g) :
  ∃! u : P ~> Q, u ∘ i1 ≈ q1 ∧ u ∘ i2 ≈ q2 :=
  is_pullback_ump H Q q1 q2 Hc.

(** *** The mediator kit *)

Definition pushout_square_med (H : IsPushoutSquare f g P i1 i2)
           {Q : C} {q1 : y ~> Q} {q2 : z ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ g)
  : P ~> Q := unique_obj (is_pushout_square_ump H Q q1 q2 Hc).

Lemma pushout_square_med_in1 (H : IsPushoutSquare f g P i1 i2)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ g) :
  pushout_square_med H Hc ∘ i1 ≈ q1.
Proof.
  exact (fst (unique_property (is_pushout_square_ump H Q q1 q2 Hc))).
Qed.

Lemma pushout_square_med_in2 (H : IsPushoutSquare f g P i1 i2)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ g) :
  pushout_square_med H Hc ∘ i2 ≈ q2.
Proof.
  exact (snd (unique_property (is_pushout_square_ump H Q q1 q2 Hc))).
Qed.

Lemma pushout_square_med_unique (H : IsPushoutSquare f g P i1 i2)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ g)
      (v : P ~> Q) :
  v ∘ i1 ≈ q1 -> v ∘ i2 ≈ q2 -> pushout_square_med H Hc ≈ v.
Proof.
  intros H1 H2.
  apply (uniqueness (is_pushout_square_ump H Q q1 q2 Hc)); split; assumption.
Qed.

(* Two mediators agreeing on both legs are equal. *)
Lemma pushout_square_med_eq (H : IsPushoutSquare f g P i1 i2)
      {Q : C} {q1 : y ~> Q} {q2 : z ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ g)
      (u v : P ~> Q) :
  u ∘ i1 ≈ q1 -> u ∘ i2 ≈ q2 -> v ∘ i1 ≈ q1 -> v ∘ i2 ≈ q2 -> u ≈ v.
Proof.
  intros Hu1 Hu2 Hv1 Hv2.
  transitivity (pushout_square_med H Hc).
  - symmetry; apply pushout_square_med_unique; assumption.
  - apply pushout_square_med_unique; assumption.
Qed.

End Accessors.

(** *** Conversions with the bundled [IsPushout]

    Both are field repackagings, exactly as Stability.v's
    [pullback_is_pullback]/[is_pullback_pullback] are; indeed each is that
    conversion read at C^op, and so is supplied with no tactic. *)

Definition pushout_is_pushout_square {x y z : C}
           (f : x ~> y) (g : x ~> z) (P : IsPushout f g) :
  IsPushoutSquare f g (pushout_apex P) (pushout_in1 P) (pushout_in2 P) :=
  @pullback_is_pullback (C^op) y z x f g P.

Definition is_pushout_square_pushout {x y z : C}
           {f : x ~> y} {g : x ~> z}
           {P : C} {i1 : y ~> P} {i2 : z ~> P}
           (H : IsPushoutSquare f g P i1 i2) : IsPushout f g :=
  @is_pullback_pullback (C^op) y z x f g P i1 i2 H.

End PushoutSquare.

Arguments IsPushoutSquare {C x y z} f g P i1 i2.

(** ** The cokernel pair *)

(* The cokernel pair of f : x ~> y is the pushout of f with itself: a
   parallel pair out of y, universal among parallel pairs coequalizing f.

   This is the exact dual of Structure/Regular.v:46's

       Definition kernel_pair `{HasPullbacks C} (f : x ~> y)
         : Pullback f f := pullback f f

   and is spelled to mirror it one for one. *)
Definition cokernel_pair {C : Category} `{H : @HasPushouts C} {x y : C}
  (f : x ~> y) : IsPushout f f := pushout f f.

(* The one-off apex-pinned form: [u] and [v] ARE a cokernel pair of f.
   Unlike [cokernel_pair] this needs no [HasPushouts], the square naming
   its own apex and legs. *)
Definition IsCokernelPair {C : Category} {x y : C} (f : x ~> y)
           (P : C) (u v : y ~> P) : Type := IsPushoutSquare f f P u v.

Section CokernelPairAccessors.

Context {C : Category}.
Context {x y : C}.
Context {f : x ~> y}.

(* Stated for an ARBITRARY pushout of f with itself, so that the chosen
   form [cokernel_pair f] and any one-off witness are both served. *)
Context (P : IsPushout f f).

Definition ckp_obj : C := pushout_apex P.

(* The parallel pair.  Both legs run y ~> ckp_obj: this is what makes the
   cokernel pair a PARALLEL PAIR rather than a general cocone. *)
Definition ckp_left : y ~> ckp_obj := pushout_in1 P.
Definition ckp_right : y ~> ckp_obj := pushout_in2 P.

(* The defining equation. *)
Lemma ckp_commutes : ckp_left ∘ f ≈ ckp_right ∘ f.
Proof. exact (pushout_commutes P). Qed.

(* The universal property, stated on PARALLEL PAIRS COEQUALIZING f. *)
Lemma ckp_ump (Q : C) (q1 q2 : y ~> Q) (Hc : q1 ∘ f ≈ q2 ∘ f) :
  ∃! u : ckp_obj ~> Q, u ∘ ckp_left ≈ q1 ∧ u ∘ ckp_right ≈ q2.
Proof. exact (pushout_ump P Q q1 q2 Hc). Qed.

Definition ckp_med {Q : C} {q1 q2 : y ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ f)
  : ckp_obj ~> Q := pushout_med P Hc.

Lemma ckp_med_left {Q : C} {q1 q2 : y ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ f) :
  ckp_med Hc ∘ ckp_left ≈ q1.
Proof. exact (pushout_med_in1 P Hc). Qed.

Lemma ckp_med_right {Q : C} {q1 q2 : y ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ f) :
  ckp_med Hc ∘ ckp_right ≈ q2.
Proof. exact (pushout_med_in2 P Hc). Qed.

Lemma ckp_med_unique {Q : C} {q1 q2 : y ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ f)
      (v : ckp_obj ~> Q) :
  v ∘ ckp_left ≈ q1 -> v ∘ ckp_right ≈ q2 -> ckp_med Hc ≈ v.
Proof. exact (pushout_med_unique P Hc v). Qed.

Lemma ckp_med_eq {Q : C} {q1 q2 : y ~> Q} (Hc : q1 ∘ f ≈ q2 ∘ f)
      (u v : ckp_obj ~> Q) :
  u ∘ ckp_left ≈ q1 -> u ∘ ckp_right ≈ q2 ->
  v ∘ ckp_left ≈ q1 -> v ∘ ckp_right ≈ q2 -> u ≈ v.
Proof. exact (pushout_med_eq P Hc u v). Qed.

(* The apex-pinned reading of the chosen/one-off pushout. *)
Definition ckp_IsCokernelPair : IsCokernelPair f ckp_obj ckp_left ckp_right :=
  pushout_is_pushout_square f f P.

End CokernelPairAccessors.

Arguments ckp_obj {C x y f} P.
Arguments ckp_left {C x y f} P.
Arguments ckp_right {C x y f} P.

(** ** Epimorphisms are exactly the identity pushout squares *)

Section EpiCharacterization.

Context {C : Category}.
Context {x y : C}.
Context (f : x ~> y).

(* Seven Sketches Definition 7.5, forward: if f is right-cancellable then
   the square on f with two identity legs is a pushout.  The mediator of a
   cocone (q1, q2) is q1 itself — epicness is exactly what says q2 is the
   same morphism. *)
Definition epic_pushout_square (E : Epic f) : IsPushoutSquare f f y id id.
Proof.
  destruct E as [cancel].
  unshelve eapply Build_IsPushoutSquare.
  - (* the square commutes, trivially *)
    reflexivity.
  - intros Q q1 q2 Hc.
    assert (Hq : q1 ≈ q2) by (apply cancel; exact Hc).
    unshelve refine {| unique_obj := q1 |}.
    + split.
      * apply id_right.
      * rewrite id_right; exact Hq.
    + intros v [Hv1 _].
      rewrite <- Hv1, id_right; reflexivity.
Defined.

(* Seven Sketches Definition 7.5, backward: if that square is a pushout
   then f is right-cancellable.  A pair coequalizing f is mediated by a
   SINGLE morphism which, precomposed with the identity twice over, is
   both members of the pair. *)
Definition pushout_square_epic (H : IsPushoutSquare f f y id id) : Epic f.
Proof.
  constructor.
  intros z g1 g2 Hg.
  pose proof (is_pushout_square_ump H z g1 g2 Hg) as U.
  destruct (unique_property U) as [U1 U2].
  rewrite <- U1, <- U2; reflexivity.
Defined.

Theorem epic_iff_pushout_square : Epic f ↔ IsPushoutSquare f f y id id.
Proof. split; [ exact epic_pushout_square | exact pushout_square_epic ]. Qed.

(** *** Mac Lane's phrasing: the cokernel pair is trivial *)

Context (P : IsPushout f f).

(* Forward: right cancellation applied to [ckp_commutes]. *)
Lemma epic_ckp_trivial (E : Epic f) : ckp_left P ≈ ckp_right P.
Proof.
  destruct E as [cancel].
  apply cancel.
  exact (ckp_commutes P).
Qed.

(* Backward: a pair coequalizing f is mediated, and the two legs being
   equal forces the two members of the pair to agree. *)
Lemma ckp_trivial_epic (Ht : ckp_left P ≈ ckp_right P) : Epic f.
Proof.
  constructor.
  intros z g1 g2 Hg.
  transitivity (ckp_med P Hg ∘ ckp_left P).
  - symmetry; exact (ckp_med_left P Hg).
  - rewrite Ht.
    exact (ckp_med_right P Hg).
Qed.

Theorem epic_iff_cokernel_pair_trivial :
  Epic f ↔ ckp_left P ≈ ckp_right P.
Proof. split; [ exact epic_ckp_trivial | exact ckp_trivial_epic ]. Qed.

(** *** The same at full strength: the left leg is an isomorphism *)

(* When f is epic, the mediator of the pair (id, id) is a two-sided
   inverse of either leg, so the cokernel-pair apex collapses onto the
   codomain.  Naming the inverse is what makes this stronger than a bare
   [≅]. *)
Lemma epic_ckp_left_iso (E : Epic f) : IsIsomorphism (ckp_left P).
Proof.
  assert (Hid : id[y] ∘ f ≈ id[y] ∘ f) by reflexivity.
  unshelve refine {| two_sided_inverse := ckp_med P Hid |}.
  - (* ckp_left ∘ med ≈ id, by agreeing with id on both legs *)
    apply (ckp_med_eq P (ckp_commutes P)).
    + rewrite <- comp_assoc, (ckp_med_left P Hid); apply id_right.
    + rewrite <- comp_assoc, (ckp_med_right P Hid), id_right.
      exact (epic_ckp_trivial E).
    + apply id_left.
    + apply id_left.
  - (* med ∘ ckp_left ≈ id *)
    exact (ckp_med_left P Hid).
Qed.

(* Conversely, an invertible left leg forces the two legs to agree: the
   self-cocone (ckp_left, ckp_left) is mediated by a morphism that the
   invertibility pins to the identity. *)
Lemma ckp_left_iso_epic (I : IsIsomorphism (ckp_left P)) : Epic f.
Proof.
  destruct I as [k Hk1 Hk2].
  apply ckp_trivial_epic.
  assert (Hc : ckp_left P ∘ f ≈ ckp_left P ∘ f) by reflexivity.
  (* The self-mediator of the cocone (ckp_left, ckp_left) is forced to be
     the identity, because it is the identity after the invertible leg. *)
  assert (Hw : ckp_med P Hc ≈ id).
  { transitivity (ckp_med P Hc ∘ (ckp_left P ∘ k)).
    - rewrite Hk1, id_right; reflexivity.
    - rewrite comp_assoc, (ckp_med_left P Hc); exact Hk1. }
  (* The mediator carries the RIGHT leg to the left one, and being the
     identity it carries it to itself. *)
  symmetry.
  transitivity (ckp_med P Hc ∘ ckp_right P).
  - rewrite Hw, id_left; reflexivity.
  - exact (ckp_med_right P Hc).
Qed.

Theorem epic_iff_cokernel_pair_left_iso :
  Epic f ↔ IsIsomorphism (ckp_left P).
Proof. split; [ exact epic_ckp_left_iso | exact ckp_left_iso_epic ]. Qed.

End EpiCharacterization.

Arguments epic_iff_pushout_square {C x y} f.
Arguments epic_iff_cokernel_pair_trivial {C x y} f P.
Arguments epic_iff_cokernel_pair_left_iso {C x y} f P.

(** *** The same at the CHOSEN cokernel pair

    Named aliases so that a consumer working under [HasPushouts] need not
    spell the pushout argument.  Each is the general statement applied to
    [cokernel_pair f], supplied by [:=]. *)

Definition epic_iff_chosen_ckp_trivial {C : Category}
           `{H : @HasPushouts C} {x y : C} (f : x ~> y) :
  Epic f ↔ ckp_left (cokernel_pair f) ≈ ckp_right (cokernel_pair f) :=
  epic_iff_cokernel_pair_trivial f (cokernel_pair f).

Definition epic_iff_chosen_ckp_left_iso {C : Category}
           `{H : @HasPushouts C} {x y : C} (f : x ~> y) :
  Epic f ↔ IsIsomorphism (ckp_left (cokernel_pair f)) :=
  epic_iff_cokernel_pair_left_iso f (cokernel_pair f).

(** ** The [Monic] dual, by duality

    Every statement below is one of the three above instantiated at C^op
    and re-typed through Duality.v's [Monic]/[Epic] bridges.  No proof
    content is repeated: each is supplied by [:=] or by a two-line
    [split] over the C^op instance.

    The two conversions that carry the transfer are MEASURED, not assumed;
    see the [eq_refl] lemmas immediately below. *)

Section OpConversions.

Context {C : Category}.
Context {x y : C}.
Context (f : x ~> y).

(* The identity pushout square at C^op IS the identity pullback square at
   C.  This holds because (C^op)^op reduces to C in this library
   (Construction/Opposite.v), so the two [IsPullback] applications are the
   same term.  Measured: [eq_refl]. *)
Definition op_collapse_pushout_square :
  @IsPushoutSquare (C^op) y x x f f x id id
    = @IsPullback C x x y f f x id id := eq_refl.

(* A pushout of f with itself in C^op IS a pullback of f with itself in C,
   and the cokernel-pair legs there ARE the pullback projections here.
   Measured: [eq_refl] in all three.  This is what makes the [Monic]
   statements below literal instantiations rather than restatements. *)
Definition op_collapse_cokernel_pair :
  @IsPushout (C^op) y x x f f = @Pullback C x x y f f := eq_refl.

Definition op_collapse_ckp_left (P : Pullback f f) :
  @ckp_left (C^op) y x f P = pullback_fst f f P := eq_refl.

Definition op_collapse_ckp_right (P : Pullback f f) :
  @ckp_right (C^op) y x f P = pullback_snd f f P := eq_refl.

(* [IsIsomorphism] at C^op and at C carry the same inverse and swap their
   two law fields, so the conversion is a field permutation with no proof
   content.  It is not [eq_refl]: the records differ in field ORDER, and
   the [Fail] probe of Test/ProbeCokernelPair.v pins that. *)
Definition IsIsomorphism_of_op {a b : C} (h : b ~> a)
           (I : @IsIsomorphism (C^op) a b h) : @IsIsomorphism C b a h :=
  @Build_IsIsomorphism C b a h
    (@two_sided_inverse (C^op) a b h I)
    (@is_left_inverse (C^op) a b h I)
    (@is_right_inverse (C^op) a b h I).

Definition op_IsIsomorphism_of {a b : C} (h : b ~> a)
           (I : @IsIsomorphism C b a h) : @IsIsomorphism (C^op) a b h :=
  @Build_IsIsomorphism (C^op) a b h
    (@two_sided_inverse C b a h I)
    (@is_left_inverse C b a h I)
    (@is_right_inverse C b a h I).

End OpConversions.

Section MonoCharacterization.

Context {C : Category}.
Context {x y : C}.
Context (f : x ~> y).

(* [Monic f] ↔ the square on f with two identity legs is a PULLBACK.  This
   is Seven Sketches Definition 7.5's mono clause; that clause proper is
   issue #672's territory, and what is delivered here is strictly the dual
   of this issue's epi theorem, obtained by instantiating it at C^op. *)
Theorem monic_iff_pullback_square : Monic f ↔ IsPullback f f x id id.
Proof.
  split.
  - intro M.
    exact (epic_pushout_square (C:=C^op) f (op_Epic_of_Monic f M)).
  - intro H.
    exact (Monic_of_op_Epic f (pushout_square_epic (C:=C^op) f H)).
Qed.

(* The kernel-pair phrasing: f is monic exactly when its kernel pair is
   trivial, i.e. its two projections coincide.  Stated for an ARBITRARY
   pullback of f with itself, matching the cokernel-pair side. *)
Theorem monic_iff_kernel_pair_trivial (P : Pullback f f) :
  Monic f ↔ pullback_fst f f P ≈ pullback_snd f f P.
Proof.
  split.
  - intro M.
    exact (epic_ckp_trivial (C:=C^op) f P (op_Epic_of_Monic f M)).
  - intro Ht.
    exact (Monic_of_op_Epic f (ckp_trivial_epic (C:=C^op) f P Ht)).
Qed.

(* Stated in C, not in C^op: the projection is an isomorphism there. *)
Theorem monic_iff_kernel_pair_fst_iso (P : Pullback f f) :
  Monic f ↔ IsIsomorphism (pullback_fst f f P).
Proof.
  split.
  - intro M.
    exact (IsIsomorphism_of_op _
             (epic_ckp_left_iso (C:=C^op) f P (op_Epic_of_Monic f M))).
  - intro I.
    exact (Monic_of_op_Epic f
             (ckp_left_iso_epic (C:=C^op) f P (op_IsIsomorphism_of _ I))).
Qed.

End MonoCharacterization.
