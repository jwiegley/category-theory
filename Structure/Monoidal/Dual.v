(** * Dualization into a fixed object, and self-adjointness on the right *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.StarAutonomous.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Right.

(* The hom-set isomorphisms of the closed structure and of
   [AdjointOnTheRight] both live in [Sets], so [Instance/Sets] is in
   scope; this removal keeps its product-monoidal instance out of the
   hint database so that `⨂` cannot resolve to the tensor of [Sets].
   Structure/Monoidal/Closed.v and Structure/Monoidal/StarAutonomous.v
   perform the same removal.  Here it is DEFENSIVE, and that is measured
   rather than assumed: deleting the line leaves this file compiling
   clean (rc = 0).  The reason it costs nothing is that `C` arrives with
   a [SymMonClosed] instance whose coercion [smc_is_symmetric] already
   determines the monoidal structure, so resolution is never offered a
   choice.  It is kept for consistency with the two donors, where the
   ambient category is not so constrained. *)
Remove Hints Sets_Product_Monoidal : typeclass_instances.

(* NOTATION GUARD, inherited from Adjunction/Right.v:35 and obeyed
   here, but DEFENSIVE in this file — and that is measured on both
   halves, not assumed.  Three scopes declare [_ ^op] (category, functor
   and adjunction), and Category.Functor.Opposite and
   Category.Adjunction.Right's transitive imports open theirs, so a bare
   [C^op] can parse as the wrong one; Right.v records a site where the
   guard is genuinely REQUIRED.  Here it is not: deleting the [Open
   Scope] leaves this file compiling clean (rc = 0), and so does
   replacing every [Opposite_Functor (dual d)] by [(dual d)^op].  Both
   are nevertheless kept — the [Open Scope] because the hazard is real in
   general, the [Opposite_Functor] spelling because it is the discipline
   the donor asks consumers to follow.  Same family as the guards in
   Theory/Universal/Arrow/Dual.v and Instance/Rng/Mod.v. *)
Open Scope category_scope.

Generalizable All Variables.

(* Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          §IV.2 Construction 3, printed p. 88 (maclane:IV.2:construction3)
   Book:  Mac Lane, op. cit., §IV.2 Definition 2, printed p. 89, where
          "adjoint on the right" is defined and attributed to Freyd
   Book:  Riehl, "Category Theory in Context", §4.4
   nLab:  https://ncatlab.org/nlab/show/star-autonomous+category
   nLab:  https://ncatlab.org/nlab/show/dualizing+object
   nLab:  https://ncatlab.org/nlab/show/mutually+left+adjoint+functors

   WHAT THIS FILE IS.  Fix an object `d` of a symmetric monoidal closed
   category `C`.  Mac Lane's §IV.2 Construction 3 observes that
   dualization into `d`,

       (- ⇒ d) : C^op ⟶ C,

   is ADJOINT TO ITSELF ON THE RIGHT: there is a bijection

       C(a, x ⇒ d)  ≅  C(x, a ⇒ d),

   natural in both variables, because both sides are the transposes of
   maps out of the tensor — one of `a ⨂ x`, the other of `x ⨂ a` — and
   the symmetry of `⨂` exchanges the two.  Everything sits on the RIGHT
   of the two hom-sets, which is the sense of Mac Lane's Definition 2 and
   of the class [AdjointOnTheRight] (Adjunction/Right.v:334).  The
   canonical unit of the resulting self-adjunction is the map into the
   double dual,

       η_x : x ~> (x ⇒ d) ⇒ d,

   the transpose of `eval'` through the symmetric braid.  It is what this
   file CONSTRUCTS, and it is exactly the map that
   Structure/Monoidal/StarAutonomous.v:269's field [star_double_dual]
   declines to pin: that class POSITS some isomorphism `x ≅ (x⇒d)⇒d`
   without requiring it to be the canonical one, and that file's own
   header (:69-80) records the gap in those terms.  The relationship is
   made explicit below rather than left implicit.

   THE TYPE-LEVEL FIT.  [AdjointOnTheRight {A X} (S : A^op ⟶ X)
   (T : X^op ⟶ A)] is instantiated at A := C, X := C and
   S := T := [dual d].  Both are `C^op ⟶ C`, so the class typechecks with
   no transport, and its field [aor {a x}] unfolds to precisely
   `C(a, dual d x) ≅ C(x, dual d a)`, which is Mac Lane's bijection.  The
   Adjunction/Right.v's own NOT-DELIVERED list records that it builds
   "No self-adjoint-on-the-right PREDICATE"; none is introduced here
   either — this file supplies an INSTANCE at a coinciding pair, not a
   predicate saying when one exists.

   PRIOR ART, MEASURED — AND THIS IS NOT THE CLASS'S FIRST SELF-ADJOINT
   WITNESS, WHICH AN EARLIER DRAFT OF THIS HEADER CLAIMED.  Before this
   file [AdjointOnTheRight] occurred in exactly two files tree-wide —
   Adjunction/Right.v, which declares it, and Test/ProbeRight358.v, its
   probe — and Right.v already carries THREE inhabitants:
   [Id_AdjointOnTheRight] (:583, labelled DEGENERATE there, both functors
   being identities), [Chain3_AdjointOnTheRight] (:651, a Galois pair on
   a three-element chain, whose partner functors differ) and
   [Powerset_AdjointOnTheRight] (:717).  The last of these is ALREADY at
   a coinciding pair — [Powerset_Prop_op] occupies both slots — so
   nothing here is the first witness with S = T, and no such claim is
   made.  What is new is the first witness arising from a MONOIDAL
   CLOSED structure rather than from a fixed concrete category, and the
   first identification of the resulting unit and counit with a
   canonical map: Right.v handles unit and counit generically
   ([aor_counit_transform], :827, and siblings) but the words
   `double dual` occur nowhere in it, and it identifies no witness's
   unit with anything.  The identifiers [dd_unit], [double_dual_unit],
   [dual_self_adjoint_on_the_right], [dual_transpose] and [dual_uncur]
   each occurred ZERO times, and a sweep of all fifty names this file
   declares returns zero collisions tree-wide.  Two near-collisions were
   found by that sweep and are recorded rather than risked: [dual_ev] is
   TAKEN by Instance/FdVect/DoubleDual.v:329 (a different construction,
   the evaluation map of a finite-dimensional double dual), so the
   helper here is [dual_uncur]; and [double_dual_natural] is taken, 9
   occurrences across Instance/FdVect/DoubleDual.v and
   Instance/FdVect/NonNatural.v, so the naturality lemma here is
   [dd_unit_natural].  Neither of those files is in this one's closure,
   but `make print-assumptions` loads many modules into ONE scope, where
   a shared name would silently audit the wrong constant.

   THE DONOR DEVIATION IS LOAD-BEARING, AND IT DICTATES THE WHOLE FILE.
   StarAutonomous.v's header (:82-89) records that [ump_exponents'] is
   stated in ∃!-form and is NOT wired to `curry' := to exp_iso`, so the
   beta law for the PACKAGED `curry'` is not derivable from the class
   fields.  Every transposition below therefore goes through the UMP
   WITNESS [dcur] (StarAutonomous.v:158), whose beta law [dcur_beta]
   (:161) and uniqueness [dcur_uniq] (:165) come straight from the field.
   `curry'` and `uncurry'` are not used anywhere in this file.  A second
   donor fact costs a re-declaration: [dcur_respects]
   (StarAutonomous.v:169) is `#[local]`, so it does not survive that
   file; [dcur_Proper] below restates it (three lines, from [dcur_uniq]
   and [dcur_beta]) because `rewrite` under [dcur] is otherwise
   unavailable.

   THE FACTORING.  Everything is routed through one helper,

       dual_uncur f := eval' ∘ (f ⨂ id) ,

   which is inverse to [dcur] by the UMP ([dual_uncur_dcur],
   [dcur_dual_uncur]).  The transposition is then literally "uncurry,
   braid, re-curry",

       dual_transpose f := dcur (dual_uncur f ∘ braid) ,

   and each of the round trip and the two naturality laws is one line of
   [dual_uncur]-algebra closed by [dcur_uniq].  Spelling the same map
   directly as `dcur (eval' ∘ braid ∘ (id ⨂ f))` would put the two-sided
   tensor action inside every rewrite instead of behind one abbreviation;
   the factoring is recorded here so a later reader does not undo it.
   No claim is made that the direct spelling fails — it was not built.

   WHAT IS DELIVERED.

     - [dual_self_adjoint_on_the_right] : an inhabitant of
       [AdjointOnTheRight (dual d) (dual d)] for an arbitrary object `d`
       of an arbitrary [SymMonClosed] category.  No field failed and no
       field was weakened; all four naturality laws are instances of the
       two lemmas [dual_transpose_nat_dom] and [dual_transpose_nat_cod],
       and the two isomorphism laws are both [dual_transpose_invol].
     - [dd_unit] : the CANONICAL map `x ~> double_dual d x`, CONSTRUCTED
       (`dual_transpose id`) and NOT assumed invertible, together with
       [dd_unit_natural] and the packaged
       [double_dual_unit : Id[C] ⟹ double_dual d].
     - [dual_adjunction] : the ordinary adjunction `(dual d)^op ⊣ dual d`
       between `C^op` and `C`, read off the class by
       [Adjunction_of_AdjointOnTheRight] (Adjunction/Right.v:383) rather
       than rebuilt.
     - The identification of that adjunction's UNIT and COUNIT with
       [dd_unit], and of both transposes at the identity with it.
     - [StarAutonomous_of_dd_unit] and [dual_AdjointEquivalence] : if the
       canonical map is invertible then the star-autonomous class is
       inhabited with [star_double_dual] LITERALLY [dd_unit], and the
       self-adjunction upgrades to an [AdjointEquivalence].

   STRENGTHS, MEASURED STRICT-FIRST.  These hold at `eq_refl`, and are
   shipped as `Example`s so that a later edit cannot silently weaken
   them:

     - `unit dual_adjunction x = dd_unit x`     ([unit_is_dd_unit])
     - `counit dual_adjunction x = dd_unit x`   ([counit_is_dd_unit])

       The second is Mac Lane's remark that for a self-adjunction on the
       right the counit IS the unit read in the opposite category, and it
       is not a coincidence of packaging: `to aor` and `from aor` are the
       SAME function [dual_transpose] at swapped indices, which
       [aor_to_is_from_swapped] records, again at `eq_refl` and on the
       WHOLE `SetoidMorphism`, not merely pointwise.

     - `to aor id = dd_unit x` and `from aor id = dd_unit x`
       ([dd_unit_is_to_at_id], [dd_unit_is_from_at_id])
     - `fobj[double_dual d] x = (x ⇒ d) ⇒ d` and
       `fmap[double_dual d] f = fmap[dual d] (fmap[dual d] f)`
     - `dualizer (StarAutonomous_of_dd_unit H) = d` and
       `to (star_double_dual …) = dd_unit x`
       ([star_double_dual_is_dd_unit]) — note this is the FORWARD LEG,
       the field being an [Isomorphism] and so not a morphism itself —
       the sharp form of the claim that
       invertibility of the canonical map is EXACTLY the standing
       assumption of StarAutonomous.v's third field.

   EXACTLY ONE identification falls back to `≈`, and the residue is
   exhibited rather than described.  StarAutonomous.v's header calls the
   canonical map "the transpose of `eval'` through the symmetric braid",
   i.e. `dcur (eval' ∘ braid)`; [dd_unit] is `dual_transpose id`, which
   unfolds to `dcur (eval' ∘ (id ⨂ id) ∘ braid)`.  The two differ by the
   insertion of `id ⨂ id`, and `bimap` is `fmap[tensor]` whose
   [fmap_id] is an opaque law field, so conversion does not remove it.
   [dd_unit_is_braid_transpose] states the `≈` form; the `eq_refl` form
   is REFUTED and pinned below as CONVERSION negative 1, against a
   control that closes at `eq_refl` once the residue is written out.  The
   direction of the fallback was a design choice made on a measurement,
   not on taste: spelling [dd_unit] the other way round would move the
   `≈` onto the unit/counit identifications, which are the ones Mac
   Lane's construction is actually about.

   WHAT IS NOT DELIVERED.

     - No concrete witness category.  Nothing here exhibits a
       [SymMonClosed] instance, so every result is a conditional; the
       library's [ClosedMonoidal] is cartesian and is excluded on the
       no-go grounds StarAutonomous.v's header states.  This is inherited
       from the donor, which likewise constructs no instance.
     - No CONVERSE to [StarAutonomous_of_dd_unit].  From an arbitrary
       [StarAutonomous] one cannot recover invertibility of the canonical
       map, because the class does not tie [star_double_dual] to it.
       CONVERSION negative 2 pins the sharpest available fact — that
       conversion alone does not establish
       `to (star_double_dual) = dd_unit dualizer x` for an arbitrary
       instance — against the produced instance as a passing control.
       Read that at its strength: it says conversion does not settle the
       equation, NOT that the equation is false.  No countermodel is
       exhibited, and none is claimed to exist.
     - No [EquivalenceOfCategories] record and no
       [AdjointEquivalence_to_Equivalence] composite; the upgrade stops
       at [AdjointEquivalence] (Theory/Equivalence/Adjoint.v:69), which
       is the class whose two extra fields are exactly invertibility of
       the derived unit and counit.
     - No self-adjointness on the LEFT, and nothing about
       [AdjointOnTheLeft]; Adjunction/Right.v's
       [right_does_not_imply_left] applies but is not instantiated here.
     - No uniqueness: nothing says the dual functor is the only functor
       self-adjoint on the right, and no analogue of [right_adjoint_iso].
     - No functoriality or naturality in `d`: [dual], [dd_unit] and the
       self-adjunction are not exhibited as varying with the dualizing
       object.
     - No triangle identities in the vocabulary of
       Adjunction/Natural/Transformation.v; the unit and counit are
       identified with [dd_unit] but the zig-zags are not restated.
     - Nothing about `⅋`, linear distributivity, or Barr coherence; that
       is StarAutonomous.v's ledger entry 4 and is untouched.
     - [StarAutonomous.v] is NOT modified.

   UNIVERSES, MEASURED off BOTH the binder and the constraint block —
   the block alone would give the wrong answer here, which is the point.
   Every constant in this file has hom IDENTIFIED with proof, expressed
   by REUSING the level variable in the BINDER rather than by any
   equation: 94 of the 100 `Category` binder occurrences print
   `C : Category@{u u0 u0}`, and the other six — the three `_ex`
   exported instances, twice each — print `C : Category@{u u2 u2}`, the
   same SHAPE under different level names.  The constraint blocks
   contain NO equation at all, only bounds; the enumeration that follows
   is NOT exhaustive, being the ones worth naming: `u0 < u1` from
   [SymMonClosed], further strict bounds (`u0 < u3`, `u0 < u4`,
   `u2 < u0`) and `≤`-bounds both against [compose], [projections],
   [prod_rect] and [ID] and between this file's own declared levels.
   A reader who checks only the block concludes "no identification" and
   is wrong.  The identification is INHERITED, and FOUR donors are each
   sufficient ON THEIR OWN: under a section declaring `Constraint
   ch < cp`, each of [Opposite], [Monoidal], [SymmetricMonoidal] and
   [SymMonClosed] is rejected ALONE at `Category@{co ch cp}` with a
   genuine `universe inconsistency: Cannot enforce cp = ch`, while
   naming a hom `a ~{Cu}~> b` and an identity `@id Cu a` at those very
   levels is ACCEPTED — and all four are ACCEPTED once the two levels
   are declared equal, so each negative fires on the constraint and not
   on the application.  READ "four" AS FOUR DONORS AND NOT AS FOUR
   INDEPENDENT CAUSES: [SymMonClosed] contains [SymmetricMonoidal]
   (field [smc_is_symmetric]) contains [BraidedMonoidal] (field
   [symmetric_is_braided]) contains [Monoidal] (field
   [braided_is_monoidal]), so three of the four are ONE cause tested at
   three strengths and at most TWO are independent — [Opposite] and the
   monoidal chain, whose weakest member [Monoidal] already suffices.
   Nothing here adds to the identification, and none of the four is
   claimed unavoidable: no re-annotated variant of any donor was
   attempted.  There is no `Set` in any binder or any block.  The four
   rejections are shipped as FORMABILITY negatives below.

   AXIOMS AND COUNT.  50/50 constants closed under the global context.
   The 50 are the 42 source-declared names plus the EIGHT [Program]
   obligations no source sweep sees — six for
   [dual_self_adjoint_on_the_right] and two for [double_dual_unit].  The
   figure is `Print Module` on the compiled module, whitespace-flattened
   before counting (the printer wraps, and a line-anchored sweep silently
   drops a wrapped entry); every one of the 50 was then queried by
   fully-qualified name.  `Print Module` renders the [Qed] constants as
   `Parameter`, which is a display convention and not an axiom.  The file
   declares no [Record], [Class] or [Inductive], so there is no unlisted
   `Build_*`. *)

Section DualSelfAdjoint.

Context {C : Category}.
Context `{@SymMonClosed C}.
Context (d : C).

(** ** Transposition helpers

    [dcur_respects] in the donor is `#[local]` and does not survive that
    file, so it is restated; [dual_uncur] is the inverse of [dcur] on the
    nose, and everything below is stated in terms of it. *)

#[local] Instance dcur_Proper {x y z : C} :
  Proper (equiv ==> equiv) (@dcur C _ x y z).
Proof.
  intros f g Hfg; apply dcur_uniq; rewrite Hfg; apply dcur_beta.
Qed.

Definition dual_uncur {a x : C} (f : a ~> x ⇒ d) : a ⨂ x ~> d :=
  eval' ∘ (f ⨂ id).

#[local] Instance dual_uncur_Proper {a x : C} :
  Proper (equiv ==> equiv) (@dual_uncur a x).
Proof. intros f g Hfg; unfold dual_uncur; now rewrite Hfg. Qed.

Lemma dual_uncur_dcur {a x : C} (g : a ⨂ x ~> d) :
  dual_uncur (dcur g) ≈ g.
Proof. symmetry; apply dcur_beta. Qed.

Lemma dcur_dual_uncur {a x : C} (f : a ~> x ⇒ d) :
  dcur (dual_uncur f) ≈ f.
Proof. apply dcur_uniq; reflexivity. Qed.

(* The dual functor's arrow action IS the transpose of the one-sided
   evaluation, by CONVERSION: [dual] is a [Program Definition] whose
   `fmap` field is that term.  This is the lemma that lets the rewrites
   below fire; a bare `rewrite <- dcur_beta` will not fire through
   `fmap[dual d]` without it. *)
Lemma dual_fmap_unfold {x x' : C} (k : x ~{C}~> x') :
  @fmap _ _ (dual d) x' x k ≈ dcur (eval' ∘ (id ⨂ k)).
Proof. reflexivity. Qed.

Lemma dual_uncur_comp {a a' x : C} (f : a ~> x ⇒ d) (g : a' ~> a) :
  dual_uncur (f ∘ g) ≈ dual_uncur f ∘ (g ⨂ id[x]).
Proof.
  unfold dual_uncur.
  rewrite bimap_comp_id_right; now rewrite comp_assoc.
Qed.

Lemma dual_uncur_dual {a x x' : C} (f : a ~> x' ⇒ d) (k : x ~{C}~> x') :
  dual_uncur (@fmap _ _ (dual d) x' x k ∘ f)
    ≈ dual_uncur f ∘ (id[a] ⨂ k).
Proof.
  unfold dual_uncur.
  transitivity (eval' ∘ (f ⨂ k)).
  - rewrite dual_fmap_unfold, bimap_comp_id_right, comp_assoc.
    rewrite <- (dcur_beta (eval' ∘ (id[x' ⇒ d] ⨂ k))).
    rewrite <- comp_assoc.
    now rewrite bimap_id_left_right.
  - rewrite <- comp_assoc. now rewrite bimap_id_right_left.
Qed.

(** ** The self-transposition

    Mac Lane's bijection `C(a, x ⇒ d) ≅ C(x, a ⇒ d)`: uncurry, cross the
    two factors with the symmetric braid, re-curry.  The SAME function
    serves as both directions of the bijection, at swapped indices. *)

Definition dual_transpose {a x : C} (f : a ~> x ⇒ d) : x ~> a ⇒ d :=
  dcur (dual_uncur f ∘ braid).

#[local] Instance dual_transpose_Proper {a x : C} :
  Proper (equiv ==> equiv) (@dual_transpose a x).
Proof. intros f g Hfg; unfold dual_transpose; now rewrite Hfg. Qed.

Lemma dual_uncur_transpose {a x : C} (f : a ~> x ⇒ d) :
  dual_uncur (dual_transpose f) ≈ dual_uncur f ∘ braid.
Proof. unfold dual_transpose; apply dual_uncur_dcur. Qed.

(* The round trip.  This is the single place where SYMMETRY of the
   braiding — [braid_invol], Structure/Monoidal/Symmetric.v:108 — is
   spent; the two naturality laws below need only [bimap_braid], which
   holds over a bare [BraidedMonoidal] structure. *)
Theorem dual_transpose_invol {a x : C} (f : a ~> x ⇒ d) :
  dual_transpose (dual_transpose f) ≈ f.
Proof.
  unfold dual_transpose at 1.
  rewrite dual_uncur_transpose, <- comp_assoc, braid_invol, id_right.
  apply dcur_dual_uncur.
Qed.

Theorem dual_transpose_nat_dom {a a' x : C}
  (f : a ~> x ⇒ d) (g : a' ~> a) :
  dual_transpose (f ∘ g)
    ≈ @fmap _ _ (dual d) a a' g ∘ dual_transpose f.
Proof.
  apply dcur_uniq.
  transitivity
    (dual_uncur (@fmap _ _ (dual d) a a' g ∘ dual_transpose f));
    [| unfold dual_uncur; reflexivity ].
  rewrite dual_uncur_dual, dual_uncur_transpose, dual_uncur_comp,
          <- !comp_assoc.
  now rewrite bimap_braid.
Qed.

Theorem dual_transpose_nat_cod {a x x' : C}
  (f : a ~> x' ⇒ d) (k : x ~{C}~> x') :
  dual_transpose (@fmap _ _ (dual d) x' x k ∘ f)
    ≈ dual_transpose f ∘ k.
Proof.
  apply dcur_uniq.
  transitivity (dual_uncur (dual_transpose f ∘ k));
    [| unfold dual_uncur; reflexivity ].
  rewrite dual_uncur_comp, dual_uncur_transpose, dual_uncur_dual,
          <- !comp_assoc.
  now rewrite bimap_braid.
Qed.

(** ** Mac Lane §IV.2 Construction 3

    The dual functor is adjoint to itself on the right.  Both legs of the
    hom-set isomorphism are ONE construction at swapped indices; the two
    isomorphism laws are both [dual_transpose_invol], and the four
    naturality fields are the two lemmas above, each used twice. *)

Definition dual_transpose_morphism (a x : C) :
  SetoidMorphism {| carrier   := @hom C a (dual d x)
                  ; is_setoid := @homset C a (dual d x) |}
                 {| carrier   := @hom C x (dual d a)
                  ; is_setoid := @homset C x (dual d a) |} :=
  {| morphism       := @dual_transpose a x
   ; proper_morphism := @dual_transpose_Proper a x |}.

Program Definition dual_self_adjoint_on_the_right :
  @AdjointOnTheRight C C (dual d) (dual d) := {|
  aor := fun a x => {| to   := dual_transpose_morphism a x
                     ; from := dual_transpose_morphism x a |}
|}.
Next Obligation. simpl; apply dual_transpose_invol. Qed.
Next Obligation. simpl; apply dual_transpose_invol. Qed.
Next Obligation. apply dual_transpose_nat_dom. Qed.
Next Obligation. apply dual_transpose_nat_cod. Qed.
Next Obligation. apply dual_transpose_nat_cod. Qed.
Next Obligation. apply dual_transpose_nat_dom. Qed.

Notation "'DSA'" := dual_self_adjoint_on_the_right (only parsing).

(* The two legs are the same construction at swapped indices, at
   whole-[SetoidMorphism] Leibniz equality — this is the precise content
   of Mac Lane's remark that the pair is symmetric in S and T. *)
Example aor_to_is_from_swapped (a x : C) :
  to (@aor C C (dual d) (dual d) DSA a x)
    = from (@aor C C (dual d) (dual d) DSA x a) := eq_refl.

Example aor_from_is_to_swapped (a x : C) :
  from (@aor C C (dual d) (dual d) DSA a x)
    = to (@aor C C (dual d) (dual d) DSA x a) := eq_refl.

(** ** The canonical map into the double dual

    CONSTRUCTED, not assumed invertible.  It is the value of the
    self-transposition at the identity of `x ⇒ d`; equivalently, and up
    to the `id ⨂ id` residue measured in the header, the transpose of
    `eval'` through the braid. *)

Definition dd_unit (x : C) : x ~> double_dual d x :=
  dual_transpose (@id C (x ⇒ d)).

Example double_dual_obj (x : C) :
  fobj[double_dual d] x = ((x ⇒ d) ⇒ d) := eq_refl.

Example double_dual_fmap {a b : C} (f : a ~{C}~> b) :
  @fmap _ _ (double_dual d) a b f
    = @fmap _ _ (dual d) (a ⇒ d) (b ⇒ d) (@fmap _ _ (dual d) b a f)
  := eq_refl.

Example dd_unit_is_to_at_id (x : C) :
  to (@aor C C (dual d) (dual d) DSA (x ⇒ d) x) (@id C (x ⇒ d))
    = dd_unit x := eq_refl.

Example dd_unit_is_from_at_id (x : C) :
  from (@aor C C (dual d) (dual d) DSA x (x ⇒ d)) (@id C (x ⇒ d))
    = dd_unit x := eq_refl.

(* The header's spelling, at `≈`.  The residue is exactly `id ⨂ id`;
   [bimap] is `fmap[tensor]` and [fmap_id] is an opaque law field, so
   conversion does not remove it.  The `eq_refl` form is refuted and
   pinned as CONVERSION negative 1 below. *)
Lemma dd_unit_is_braid_transpose (x : C) :
  dd_unit x ≈ dcur (eval' ∘ braid).
Proof.
  unfold dd_unit, dual_transpose, dual_uncur.
  apply dcur_Proper.
  rewrite bimap_id_id, id_right.
  reflexivity.
Qed.

Theorem dd_unit_natural {a b : C} (f : a ~{C}~> b) :
  @fmap _ _ (double_dual d) a b f ∘ dd_unit a ≈ dd_unit b ∘ f.
Proof.
  unfold dd_unit.
  transitivity (dual_transpose (@fmap _ _ (dual d) b a f)).
  - rewrite <- (id_left (@fmap _ _ (dual d) b a f)) at 1.
    rewrite dual_transpose_nat_dom. reflexivity.
  - rewrite <- (id_right (@fmap _ _ (dual d) b a f)) at 1.
    rewrite dual_transpose_nat_cod. reflexivity.
Qed.

Program Definition double_dual_unit : Id[C] ⟹ double_dual d := {|
  transform := dd_unit
|}.
Next Obligation. apply dd_unit_natural. Qed.
Next Obligation. symmetry; apply dd_unit_natural. Qed.

Example double_dual_unit_component (x : C) :
  transform[double_dual_unit] x = dd_unit x := eq_refl.

(** ** The ordinary adjunction, and Mac Lane's unit and counit

    Read off the class by Adjunction/Right.v:383 rather than rebuilt.
    `Check` displays the result as `(dual d)^op ⊣ dual d`. *)

Definition dual_adjunction :
  @Adjunction (C^op) C (Opposite_Functor (dual d)) (dual d) :=
  Adjunction_of_AdjointOnTheRight DSA.

(* Both at `eq_refl`.  The second is Mac Lane's observation that the
   counit of a self-adjunction on the right is the unit read in the
   opposite category: the two are the SAME TERM, not merely `≈`-equal
   morphisms, and not merely equal componentwise after a transport. *)
Example unit_is_dd_unit (x : C) :
  @unit (C^op) C (Opposite_Functor (dual d)) (dual d) dual_adjunction x
    = dd_unit x := eq_refl.

Example counit_is_dd_unit (x : C) :
  @counit (C^op) C (Opposite_Functor (dual d)) (dual d) dual_adjunction x
    = dd_unit x := eq_refl.

(** ** Relationship to the star-autonomous class

    StarAutonomous.v:269's [star_double_dual] POSITS an isomorphism
    `x ≅ double_dual d x` without requiring it to be the canonical map.
    The two results below say precisely what invertibility of the
    canonical map buys: the class is inhabited with [star_double_dual]
    LITERALLY [dd_unit], and the self-adjunction upgrades to an adjoint
    equivalence.  The converse is not available and is not claimed — see
    the header's NOT DELIVERED list and CONVERSION negative 2. *)

Definition StarAutonomous_of_dd_unit
  (Hiso : forall x : C, IsIsomorphism (dd_unit x)) : @StarAutonomous C _.
Proof.
  refine (@Build_StarAutonomous C _ d
            (fun x y => @exp_iso C _ x y d)
            (fun x => IsIsoToIso (dd_unit x) (Hiso x)) _).
  intros a b f. simpl. symmetry. apply dd_unit_natural.
Defined.

Example star_autonomous_dualizer
  (Hiso : forall x : C, IsIsomorphism (dd_unit x)) :
  @dualizer C _ (StarAutonomous_of_dd_unit Hiso) = d := eq_refl.

Example star_double_dual_is_dd_unit
  (Hiso : forall x : C, IsIsomorphism (dd_unit x)) (x : C) :
  to (@star_double_dual C _ (StarAutonomous_of_dd_unit Hiso) x)
    = dd_unit x := eq_refl.

(* The upgrade.  [AdjointEquivalence] (Theory/Equivalence/Adjoint.v:69)
   carries an adjunction together with invertibility of its derived unit
   and counit; both are [dd_unit] here, so ONE hypothesis discharges both
   fields.  The counit field is stated in `C^op`, where the two inverse
   laws are the C-level ones with left and right exchanged — hence the
   explicit [@Build_IsIsomorphism (C^op)], a record literal `{| … |}`
   resolving to `C` instead. *)
Definition dual_AdjointEquivalence
  (Hiso : forall x : C, IsIsomorphism (dd_unit x)) :
  @AdjointEquivalence C (C^op) (Opposite_Functor (dual d)) (dual d).
Proof.
  unshelve econstructor.
  - exact dual_adjunction.
  - intro x; exact (Hiso x).
  - intro y.
    exact (@Build_IsIsomorphism (C^op) _ _ _
             (@two_sided_inverse C _ _ (dd_unit y) (Hiso y))
             (@is_left_inverse   C _ _ (dd_unit y) (Hiso y))
             (@is_right_inverse  C _ _ (dd_unit y) (Hiso y))).
Defined.

End DualSelfAdjoint.

(** ** Respectfulness, exported

    The instances above are `#[local]` section hints and die at [End];
    a downstream consumer wanting to `rewrite` under [dcur],
    [dual_uncur] or [dual_transpose] needs them in the global database.
    Same shape as the donor's own `#[local] dcur_respects`, restated. *)

#[export] Instance dcur_Proper_ex {C : Category} `{@SymMonClosed C}
  {x y z : C} : Proper (equiv ==> equiv) (@dcur C _ x y z).
Proof.
  intros f g Hfg; apply dcur_uniq; rewrite Hfg; apply dcur_beta.
Qed.

#[export] Instance dual_uncur_Proper_ex {C : Category}
  `{@SymMonClosed C} {d a x : C} :
  Proper (equiv ==> equiv) (@dual_uncur C _ d a x).
Proof. intros f g Hfg; unfold dual_uncur; now rewrite Hfg. Qed.

#[export] Instance dual_transpose_Proper_ex {C : Category}
  `{@SymMonClosed C} {d a x : C} :
  Proper (equiv ==> equiv) (@dual_transpose C _ d a x).
Proof. intros f g Hfg; unfold dual_transpose; now rewrite Hfg. Qed.

(** ** Probe section

    Every rejection the header reports, pinned.  The KINDS are kept
    lexically apart and labelled: FORMABILITY (universe), CONVERSION,
    TYPING.  Each negative was stripped of its [Fail] and run alone, and
    its failure kind read off the WHOLE error message.  The three kinds
    are genuinely distinguishable here, and reading only the tail would
    NOT distinguish two of them: the four FORMABILITY negatives close
    with `universe inconsistency: Cannot enforce cp = ch`; the two
    CONVERSION negatives close with `cannot unify` between two terms of
    ONE type, naming those terms (`dd_unit d x` against
    `dcur (eval' ∘ braid)`, and `to star_double_dual` against
    `dd_unit dualizer x`); the TYPING negative also closes with
    `cannot unify`, but on the OBJECT VARIABLES `x` and `a`, its body
    reporting two DIFFERENT objects of [Sets] as the expected and actual
    types — the two legs of the bijection do not share a type off the
    diagonal, so no term equation between them is statable at all.
    Every control is APPLIED: an unapplied polymorphic constant never
    meets the declared levels and would guard nothing.

    RENAME SIMULATION, 4/4 here and 3/3 in the probe.  Renaming a
    constant only inside a [Fail] would leave the guard vacuously green,
    so each of this file's own constants that a negative or a control
    actually REFERENCES was renamed AT ITS DEFINITION SITE ALONE and the
    file recompiled.  The denominator is FOUR, not the count of names
    appearing anywhere in the probe section: [dd_unit],
    [dual_self_adjoint_on_the_right] (through the `DSA` notation),
    [dd_unit_is_braid_transpose] and [StarAutonomous_of_dd_unit].  All
    four broke at a line that is NOT a [Fail], none went vacuous.  The
    control [Example]s' own declaration names and the [Fail Example]
    names are NOT in the denominator: nothing ever uses them, so renaming
    one cannot break anything and the test would be vacuous by
    construction.  Test/ProbeDual359.v scores 3/3 on the same method from
    OUTSIDE this file.  The definition-site
    method is what makes this test say anything — a whole-file rename is
    a no-op by construction, since the definition is renamed in lockstep
    with its uses, and reports a FALSE "vacuous guard" verdict for every
    constant.  The four DONOR names the formability negatives mention
    ([Opposite], [Monoidal], [SymmetricMonoidal], [SymMonClosed]) cannot
    be renamed from here; they are guarded instead by the applied control
    section immediately below, which names all four outside any
    [Fail]. *)

(* Instrument check: a [Fail] that succeeds prints NOTHING under this
   repository's [coqc], so a probe file with a broken instrument would
   look green.  This one must fail for a reason having nothing to do
   with the subject matter. *)
Fail Example dual_probe_instrument : (true = false) := eq_refl.

Section DualProbeFormabilityControl.

(* Positive half of the formability measurement: with the hom and proof
   universes declared EQUAL, all four donors elaborate at the very same
   applied arguments the negatives below reject.  So each negative fires
   on the CONSTRAINT and not on the application. *)

Universes cco cch.
Context (Cv : Category@{cco cch cch}).
Context (u v : Cv).

Check (u ~{Cv}~> v).
Check (@id Cv u).
Check (@Opposite Cv).
Check (@Monoidal Cv).
Check (@SymmetricMonoidal Cv).
Check (@SymMonClosed Cv).

End DualProbeFormabilityControl.

Section DualProbeFormability.

(* FORMABILITY.  The hom/proof identification carried by every constant
   in this file is INHERITED.  Each of the four donors below is rejected
   ALONE at levels where naming a hom and an identity is accepted, and
   the control section above shows each ACCEPTED once the two levels are
   declared equal.  These are four DONORS, not four independent causes:
   negatives 2-4 are nested classes ([SymMonClosed] contains
   [SymmetricMonoidal] contains [BraidedMonoidal] contains [Monoidal]),
   so they test one cause at three strengths; only [Opposite] is
   independent of that chain. *)

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (a b : Cu).

(* Controls, applied, at the very levels the negatives are rejected at. *)
Check (a ~{Cu}~> b).
Check (@id Cu a).

(* FORMABILITY negative 1: the opposite category. *)
Fail Check (@Opposite Cu).
(* FORMABILITY negative 2: the monoidal structure. *)
Fail Check (@Monoidal Cu).
(* FORMABILITY negative 3: its symmetric refinement. *)
Fail Check (@SymmetricMonoidal Cu).
(* FORMABILITY negative 4: the closed base this file is stated over. *)
Fail Check (@SymMonClosed Cu).

End DualProbeFormability.

Section DualProbeConversion.

Context {C : Category}.
Context `{@SymMonClosed C}.
Context (d : C).

(* CONVERSION negative 1: [dd_unit] is not the bare braid-transpose on
   the nose; the residue is `id ⨂ id`, and writing it out closes the
   very same statement at [eq_refl]. *)
Fail Example dual_neg_braid_strict (x : C) :
  dd_unit d x = dcur (eval' ∘ braid) := eq_refl.

(* Control for negative 1, at [eq_refl], with the residue exhibited. *)
Example dual_ctrl_braid_residue (x : C) :
  dd_unit d x = dcur (eval' ∘ (id[x ⇒ d] ⨂ id[x]) ∘ braid) := eq_refl.

(* Control for negative 1, the `≈` form that IS delivered. *)
Example dual_ctrl_braid_equiv (x : C) :
  dd_unit d x ≈ dcur (eval' ∘ braid).
Proof. apply dd_unit_is_braid_transpose. Qed.

(* CONVERSION negative 2: for an ARBITRARY [StarAutonomous] instance,
   conversion does not establish that the posited double-dual
   isomorphism is the canonical map.  This is the sharpest available
   form of "the class does not pin its iso"; it does NOT say the
   equation is false. *)
Fail Example dual_neg_arbitrary_star (SA : @StarAutonomous C _) (x : C) :
  to (@star_double_dual C _ SA x) = dd_unit (@dualizer C _ SA) x
  := eq_refl.

(* Control for negative 2: at the instance THIS file produces, the same
   equation closes at [eq_refl]. *)
Example dual_ctrl_produced_star
  (Hiso : forall x : C, IsIsomorphism (dd_unit d x)) (x : C) :
  to (@star_double_dual C _ (StarAutonomous_of_dd_unit d Hiso) x)
    = dd_unit d x := eq_refl.

End DualProbeConversion.

Section DualProbeTyping.

Context {C : Category}.
Context `{@SymMonClosed C}.
Context (d : C).

Notation "'DSA'" :=
  (dual_self_adjoint_on_the_right d) (only parsing).

(* TYPING negative: off the diagonal the two legs of the bijection do
   not even have the same type, so "to = from" is not statable there.
   This is the honest form of Mac Lane's symmetry claim. *)
Fail Example dual_neg_offdiagonal (a x : C) :
  to (@aor C C (dual d) (dual d) DSA a x)
    = from (@aor C C (dual d) (dual d) DSA a x) := eq_refl.

(* Control: ON the diagonal the two legs ARE the same term. *)
Example dual_ctrl_diagonal (a : C) :
  to (@aor C C (dual d) (dual d) DSA a a)
    = from (@aor C C (dual d) (dual d) DSA a a) := eq_refl.

(* Control: off the diagonal what holds is the SWAP, at [eq_refl] on the
   whole [SetoidMorphism]. *)
Example dual_ctrl_swapped (a x : C) :
  to (@aor C C (dual d) (dual d) DSA a x)
    = from (@aor C C (dual d) (dual d) DSA x a) := eq_refl.

End DualProbeTyping.
