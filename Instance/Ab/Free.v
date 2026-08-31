Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(** * The free abelian group on a setoid, and the free-forgetful
      adjunction

    nLab:      https://ncatlab.org/nlab/show/free+abelian+group
    nLab:      https://ncatlab.org/nlab/show/free+object
    nLab:      https://ncatlab.org/nlab/show/universal+morphism
    Wikipedia: https://en.wikipedia.org/wiki/Free_abelian_group
    Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
          GTM 5, §IV.8, Exercise 2 -- maclane:IV.8:ex2
    Book: Mac Lane, ibid., §IV.1, printed p. 79 (a free construction
          presented as a hom-set bijection natural in each variable) --
          maclane:IV.1:construction1

    WHAT THIS IS, AND WHAT IT IS NOT.  [FreeAbObject X] is the free
    abelian group on a setoid X: formal sums of generators modulo
    exactly the abelian-group laws, together with the insertion of
    generators [free_ab_insert], the additive extension
    [free_ab_extend], its uniqueness [free_ab_extend_unique], the
    packaged universal property [free_ab_universal], the functor
    [FreeAb : Sets ⟶ Ab] and the adjunction
    [free_ab_adjunction : FreeAb ⊣ Ab_Forget].  It is ONE INPUT to
    Mac Lane's §IV.8 Exercise 2 -- which asks for the free-ring
    adjunction exhibited as a composite in two ways -- and that exercise
    is NOT formalized here: no ring, no monoid ring and no composite
    adjunction appears below.

    A GAP THE TREE RECORDED AND THIS FILE CLOSES.
    Instance/Ab/Tensor.v:44-45 states, of its own construction, that
    "the tree has no free abelian group to quotient (verified across
    Construction/ and Instance/)".  That is why the tensor product there
    is built by generators and relations bespoke to the pair (G, H).
    This file supplies the missing object.  It does NOT refactor
    Instance/Ab/Tensor.v to ride on it: that file's carrier is a
    quotient of formal sums of PAIRS, so routing it through this one
    would be a different construction rather than a citation, and no
    claim is made here that such a routing would work.

    WHY GENERATORS AND RELATIONS, NOT FINITELY SUPPORTED FUNCTIONS.  The
    classical carrier -- finitely supported ℤ-valued functions on X --
    presupposes generators with decidable equality, and
    Instance/Mod/Free.v's header locates the obstruction exactly: the
    CARRIER is not the problem (a [≈]-respecting function paired with a
    list witnessing that it vanishes outside that list is writable over
    a bare setoid), the BASIS INSERTION is.  The basis element at x is
    the function taking 1 at x and 0 elsewhere, and that function cannot
    be WRITTEN without a decision procedure for x ≈ y.  What makes this
    fatal rather than merely restrictive is that [Ab_Forget] lands in
    [Sets], whose objects are setoids, so a left adjoint must exist for
    EVERY generating setoid, decidable or not; a construction available
    only at decidable setoids yields no adjunction at all.  The
    presentation used here is therefore an inductive of formal
    expressions [FATerm] with an inductive congruence [fa_eq] closing
    under exactly the four abelian-group laws, congruence for each
    former, saturation under X's own [≈], and symmetry/transitivity.
    Reflexivity is derived ([fa_refl]), keeping the relation's induction
    principle one case shorter everywhere it is consumed.  As in
    Instance/Ab/Tensor.v and Instance/Mod/Free.v, [fa_Setoid] is NOT
    registered as a typeclass instance and element-level statements are
    written with [fa_eq]; that this IS the [≈] of the free group as an
    object of [Ab] is machine-checked by [free_ab_equiv_is_fa_eq]
    ([eq_refl]) rather than asserted, so every group-level lemma of
    Instance/Ab.v applies to it unchanged.

    RELATION TO Instance/Mod/Free.v.  Structurally this file is that one
    with the scalar former [fv_smul] and the four module laws deleted:
    five constructors of the congruence go away, leaving nine.  The
    DESIGN is copied and the debt is acknowledged; no code is shared and
    Instance/Mod/Free.v is not Required.  Nor is the construction
    DERIVED from it at R := ℤ, and that is a measurement rather than a
    preference: the free abelian group on X is the free ℤ-module on X,
    but transporting the universal property across needs a passage
    Ab → RMod ℤ giving every abelian group its ℤ-action, and no such
    passage exists ([RMod_Forget_Ab], Instance/Mod.v:300, is the
    forgetful direction; Instance/Mod/BaseChange.v's [ZExt Int_Ring]
    does run Ab → RMod ℤ but sends A to ℤ ⊗ A, not to A carrying its
    own ℤ-action, so it is not the passage wanted here)
    -- Instance/Mod/Tensor.v's header records the
    same absence.  The reduction is therefore unavailable in tree; it is
    NOT claimed to be unavailable in principle.

    STRENGTHS, MEASURED STRICT-FIRST.  The mediator is a [Fixpoint] on
    formal expressions, so a great deal is definitional:

      - [eq_refl]: the carrier of the free group IS [FATerm] and its [≈]
        IS [fa_eq] ([free_ab_carrier_is_FATerm], [free_ab_equiv_is_fa_eq]);
        the insertion IS the generator former ([free_ab_insert_is_gen]);
        the additive extension agrees with the given function on
        generators ([free_ab_extend_generators]) and preserves zero,
        addition AND negation definitionally ([free_ab_extend_zero],
        [free_ab_extend_plus], [free_ab_extend_neg] -- recorded at
        Leibniz [=] on the target's CARRIER, which is the convertibility
        exception the house style sanctions, so the header's claim is
        machine-checked rather than inferred from which branch of the
        obligation tactic fired); the free functor's object part is the
        formal-sum group ([FreeAb_obj]); the universal arrow IS the
        insertion ([free_ab_arrow_is_insert]); the UNIT is the insertion
        and hence the one-generator expression ([free_ab_unit_is_insert],
        [free_ab_unit_is_generator]); and the adjunction's forward
        transpose ⌊−⌋ IS [fa_transpose] ([free_ab_transpose_is_adj]).
      - [≈] only: the COUNIT.  It is the other transpose, i.e.
        [unique_obj (ump_universal_arrows …)], and [ump_universal_arrows]
        (Theory/Universal/Arrow.v) is [Qed]-opaque, so nothing reduces
        through it.  What is proved is that it evaluates a formal sum
        ([free_ab_counit_evaluates]).
      - [≈] only: the action of [FreeAb] on an arrow.
        [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by
        universal factorization rather than by a formula, so that it
        relabels generators is a theorem ([free_ab_fmap_generators]).

    Both [≈]-only readings are GUARDED, not merely measured: the
    "Measured negatives" section at the end of the file carries a [Fail]
    for each, plus a third recording that [FreeAbObject] applied to a
    group's own carrier is not CONVERTIBLE with that group (a statement
    about conversion only -- no non-isomorphism is claimed or proved).
    Each is paired with a positive control that must succeed, and each
    was confirmed (by stripping the [Fail] in a scratch file) to be a
    genuine CONVERSION failure -- "cannot unify" -- rather
    than a missing reference.  Every constant named in a negative is
    also named in a positive command elsewhere in the file, so a rename
    at a definition site breaks the build loudly instead of turning a
    [Fail] vacuously green.  The house convention puts such probes in a
    Test/Probe*.v file; they are in-file here because this commit adds
    exactly one file (other Instance/ files already do the same).

    NATURALITY.  §IV.1 presents a free construction as a bijection
    Ab(FreeAb X, A) ≅ Sets(X, U A) natural in X and in A, "each verified
    separately".  Both clauses are proved in the free group's own
    vocabulary ([free_ab_naturality_in_set], by evaluating at a
    generator; [free_ab_naturality_in_group], pointwise by
    [reflexivity]), and that they ARE the adjunction class's own fields
    [to_adj_nat_l] and [to_adj_nat_r] is then recorded by [eq_refl] on
    the STATEMENTS -- a conversion check, not a second derivation.

    NON-DEGENERACY, AND WHAT EACH SEPARATION COSTS.  No induction over
    [fa_eq] can yield a negative -- every constructor concludes an
    equation -- so each refutation maps OUT into a concrete abelian
    group, the technique of Instance/Grp/Free.v's
    [free_group_two_generators_nonabelian].  The general statements are
    over an ARBITRARY abelian group A with an element a ≉ 0, and they
    split by hypothesis:

      - NO decider needed: a generator is not zero
        ([free_ab_gen_not_zero]) and the group is not idempotent
        ([free_ab_gen_not_idempotent]).  The constant map at a suffices.
        The second is where the GROUP structure is spent:
        Instance/Ab.v's [ab_cancel_l] turns a + a ≈ a into a ≈ 0, and
        that cancellation is the one property separating a group from a
        monoid.
      - Decider needed: distinct generators are distinct
        ([free_ab_gen_injective]) and a sum is not one of its summands
        ([free_ab_sum_not_summand]).  Separating two DIFFERENT generators
        means exhibiting a group in which they go to different places,
        and the only such map a bare setoid supplies is the
        characteristic function of a point, which cannot be written
        without deciding [≈].  That is an ARGUMENT, not a theorem: no
        converse is machine-checked here, and the tree's precedent for
        claims of exactly this shape ([arrow_mul_respects_forces_UIP]
        and its siblings) is deliberately not followed.

    Unlike Instance/Mod/Free.v's [free_module_basis_injective] these need
    only ONE hypothesis rather than two: that file's second hypothesis is
    1 ≉ 0 in the coefficient ring, because it probes with the ring viewed
    as a module over itself and the ring may be the zero ring, whereas
    here the target's nondegeneracy is already carried by a ≉ 0.  All
    four are then instantiated at ℤ ([ring_ab Int_Ring]) and the
    two-element generating setoid, where the additive extension COMPUTES
    (e_true + e_true − e_false ↦ 3 + 3 − 5 = 1, by [eq_refl]).

    UNIVERSES, read off the constraint blocks rather than the binders.

      - [FATerm@{u u0}] and [fa_eq@{u u0}] have EMPTY constraint blocks:
        the term type sits at the generating setoid's carrier universe
        and the relation at max(u, u0), with nothing identified.
      - [FreeAbObject@{u u0 u1}] carries [u <= u1] and [u0 <= u1] -- two
        BOUNDS, no identification.  So the construction itself does not
        identify the generating setoid's carrier and relation universes.
      - That identification appears as soon as anything is stated as a
        morphism of [Sets]: [free_ab_insert] carries [u = u0], and
        [free_ab_extend], [free_ab_universal] and the four general
        non-degeneracy theorems additionally identify all three of an
        [AbObject]'s universes with it.  This is the DONORS' doing, and
        it is attributed rather than guessed: [Sets@{o so}] is declared
        as [Category@{so o o}] (Instance/Sets.v:193), so [obj[Sets]] is
        [SetoidObject@{o o}] with carrier and relation already
        identified, and a probe into an ARBITRARY abelian group carrying
        no free-group content at all was measured to acquire exactly the
        same block.  Nothing here adds to it, and it is not claimed
        unavoidable.
      - EXACTLY FOUR of the 76 names the file's [.glob] records (that
        count excludes the 8 generated eliminators and the 4 [Program]
        obligations, and excludes the 4 phantom names the [Fail]
        commands put there) carry [Set] in a constraint block, and all
        four are the concrete two-generator witness ([ab_int_probe] and its
        three computing [Example]s), where [bool : Set] forces it.
        That took work: writing the general separations with ℤ-valued
        characteristic functions pins the generating setoid's carrier
        AND relation universes to [Set], and
        the cause was LOCATED by three probes rather than guessed -- the
        same probe with ℤ but no decidable case split is [Set]-free, and
        the same case split into an abstract target is [Set]-free, while
        the two together pin.  Abstracting the target lifts it, which is
        why the general theorems are stated over an arbitrary A.

    ZERO AXIOMS.  All 88 constants of this file -- 38 transparent
    definitions, 8 generated eliminators, 23 opaque proofs, 4 [Program]
    obligations (invisible to a [.glob] sweep, and reachable only by
    fully qualified name), 2 inductive types and their 13 constructors --
    report "Closed under the global context".  [∃] in this library is
    [sigT], so witnesses are DATA and no choice principle is consumed
    anywhere.

    WHAT IS NOT DELIVERED.

      - No coefficient uniqueness, and -- unlike Instance/Mod/Free.v,
        which proves [fv_normal_form] -- not even the EXISTENCE of a
        normal form: nothing here says every element is a formal sum of
        generators and their negatives.  Hence no decision procedure for
        equality in the free group, no rank, and no proof that the
        insertion is injective for a general (undecidable) generating
        setoid.
      - No statement that [FreeAb] is faithful, no characterization of
        its image, no freeness of subgroups, no comparison with
        Instance/Ab/Tensor.v (see above) or with
        Instance/Ab/DirectedColimit.v's finitely generated subgroups.
      - Mac Lane §IV.8 Exercise 2 itself: no free ring, no monoid ring,
        no composite adjunction, and no comparison with
        Instance/Mon/Free.v or Instance/Rng/Free.v.
      - No [Preadditive] or [Additive] content, and no relation to
        Instance/Ab/Coproduct.v -- in particular the free group on a
        two-element setoid is NOT identified with ℤ ⊕ ℤ. *)

(* The file-global obligation tactic is [cat_simpl], which would run wide
   proof searches on the obligations below and has already introduced the
   parameters by the time an obligation is opened.  Switched off here --
   the Instance/Mod/Free.v:22 idiom -- so every obligation starts with an
   explicit [intros]. *)
#[local] Obligation Tactic := idtac.

(** ** Formal sums and the group quotient *)

Section FreeAbelian.

Context (X : SetoidObject).

(* Formal expressions over the generating setoid: generators, zero, sum,
   negation.  This is Instance/Mod/Free.v's [FVTerm] with the scalar
   former [fv_smul] deleted.  Negation is a CONSTRUCTOR rather than
   iterated addition: there is no scalar ring here to take (-1) from, and
   the abelian group being built is what a derived negation would need. *)
Inductive FATerm : Type :=
  | fa_gen  : carrier X → FATerm
  | fa_zero : FATerm
  | fa_plus : FATerm → FATerm → FATerm
  | fa_neg  : FATerm → FATerm.

(* The quotienting relation: congruence for each former (saturating under
   the generating setoid's own [≈]), the four abelian-group laws,
   symmetry and transitivity.  Reflexivity is derived below, keeping the
   relation's induction principle one case shorter everywhere it is
   consumed. *)
Inductive fa_eq : FATerm → FATerm → Type :=
  | fae_gen {x y : carrier X} : x ≈ y → fa_eq (fa_gen x) (fa_gen y)
  | fae_plus {s s' t t'} :
      fa_eq s s' → fa_eq t t' → fa_eq (fa_plus s t) (fa_plus s' t')
  | fae_neg {s s'} : fa_eq s s' → fa_eq (fa_neg s) (fa_neg s')

  (* abelian group *)
  | fae_assoc (s t u : FATerm) :
      fa_eq (fa_plus (fa_plus s t) u) (fa_plus s (fa_plus t u))
  | fae_comm (s t : FATerm) : fa_eq (fa_plus s t) (fa_plus t s)
  | fae_zero_l (s : FATerm) : fa_eq (fa_plus fa_zero s) s
  | fae_neg_l (s : FATerm) : fa_eq (fa_plus (fa_neg s) s) fa_zero

  | fae_sym {s t} : fa_eq s t → fa_eq t s
  | fae_trans {s t u} : fa_eq s t → fa_eq t u → fa_eq s u.

Lemma fa_refl (s : FATerm) : fa_eq s s.
Proof.
  induction s.
  - exact (fae_gen (reflexivity _)).
  - exact (fae_trans (fae_sym (fae_zero_l fa_zero)) (fae_zero_l fa_zero)).
  - exact (fae_plus IHs1 IHs2).
  - exact (fae_neg IHs).
Qed.

Lemma fa_eq_Equivalence : Equivalence fa_eq.
Proof.
  constructor.
  - exact fa_refl.
  - exact (fun s t => fae_sym).
  - exact (fun s t u => fae_trans).
Qed.

(* Deliberately NOT registered as a typeclass instance -- the
   Instance/Ab/Tensor.v and Instance/Mod/Free.v convention.  Statements
   about elements of the free group below are written with [fa_eq]; the
   [≈] of [FreeAbObject] as an object of [Ab] IS that relation,
   definitionally, so the group-level lemmas of Instance/Ab.v apply to it
   unchanged. *)
Definition fa_Setoid : Setoid FATerm := {|
  equiv        := fa_eq;
  setoid_equiv := fa_eq_Equivalence
|}.

(** ** The free abelian group

    Every law of the group is a constructor of the relation, so the
    record is a literal with ZERO proof obligations.  It is written out in
    one piece so that the underlying setoid, the unit, the addition and
    the negation are all visible at a glance and all reduce. *)
Definition FreeAbObject : AbObject := {|
  ab_cmon := {|
    cmon_setoid := {| carrier := FATerm; is_setoid := fa_Setoid |};
    cmon_zero := fa_zero;
    cmon_plus := fa_plus;
    cmon_plus_respects := fun _ _ Hs _ _ Ht => fae_plus Hs Ht;
    cmon_plus_assoc := fae_assoc;
    cmon_plus_comm := fae_comm;
    cmon_plus_zero_l := fae_zero_l
  |};
  ab_neg := fa_neg;
  ab_neg_respects := fun _ _ Hs => fae_neg Hs;
  ab_neg_left := fae_neg_l
|}.

(* The two claims the paragraph above [fa_Setoid] makes, machine-checked
   rather than asserted: the carrier of the free group, seen through the
   forgetful functor, IS the type of formal expressions, and its [≈] IS
   the quotienting relation.  These are equations between TYPES, not
   between morphisms -- the convertibility exception the house style
   sanctions. *)
Example free_ab_carrier_is_FATerm :
  carrier (Ab_Forget FreeAbObject) = FATerm := eq_refl.

Example free_ab_equiv_is_fa_eq (s t : FATerm) :
  (@equiv _ (is_setoid (Ab_Forget FreeAbObject)) s t) = fa_eq s t
  := eq_refl.

(** ** The insertion of generators

    A generator becomes the corresponding formal expression.
    Respectfulness is the congruence constructor [fae_gen], supplied by
    [exact] rather than as a record field: the target's [≈] is [fa_eq] by
    conversion but not by unification, and only [exact] will convert. *)
Definition free_ab_insert : X ~{Sets}~> Ab_Forget FreeAbObject.
Proof.
  unshelve refine {| morphism := fa_gen |}.
  intros x y H; exact (fae_gen H).
Defined.

(* The insertion IS the generator former on the nose. *)
Example free_ab_insert_is_gen (x : carrier X) :
  free_ab_insert x = fa_gen x := eq_refl.

(** ** The additive extension of a function on generators *)

Section Extension.

Context (A : AbObject).
Context (h : X ~{Sets}~> Ab_Forget A).

(* Fold a formal expression through the target group's operations.  It
   computes on constructors, which is what makes both homomorphism
   obligations below hold by [reflexivity]. *)
Fixpoint fa_eval (t : FATerm) : carrier (cmon_setoid A) :=
  match t with
  | fa_gen x    => h x
  | fa_zero     => cmon_zero A
  | fa_plus s t => cmon_plus A (fa_eval s) (fa_eval t)
  | fa_neg s    => ab_neg A (fa_eval s)
  end.

(* Respectfulness is one induction over the relation: nine cases, one per
   constructor of [fa_eq].  Four are met by the corresponding law of the
   target group; the other five are not laws -- [fae_gen] is saturation
   under X's own [≈], two are congruence for a former, and two are the
   target setoid's symmetry and transitivity. *)
Lemma fa_eval_respects (s t : FATerm) : fa_eq s t → fa_eval s ≈ fa_eval t.
Proof.
  intro He.
  induction He as
    [ x y Hxy
    | s s' t t' _ IHs _ IHt
    | s s' _ IHs
    | s t u | s t | s | s
    | s t _ IHst
    | s t u _ IHst _ IHtu ]; simpl.
  - exact (proper_morphism h _ _ Hxy).
  - exact (cmon_plus_respects A _ _ IHs _ _ IHt).
  - exact (ab_neg_respects A _ _ IHs).
  - exact (cmon_plus_assoc A _ _ _).
  - exact (cmon_plus_comm A _ _).
  - exact (cmon_plus_zero_l A _).
  - exact (ab_neg_left A _).
  - exact (symmetry IHst).
  - exact (transitivity IHst IHtu).
Qed.

(* The extension, as a morphism of [Ab].  [AbHom] IS [CMonHom]
   (Instance/Ab.v:184, a bare [Definition]), so the obligations are
   respectfulness of the fold and preservation of zero and of addition --
   preservation of NEGATION is not among them, being the derived
   [ab_map_neg] rather than a field.  The last two hold by
   [reflexivity], the fixpoint's clauses BEING those two equations.  One
   uniform body is used so that the proof does not depend on the order
   [Program] emits the obligations in. *)
Program Definition free_ab_extend : FreeAbObject ~{Ab}~> A := {|
  cmon_map := {| morphism := fa_eval |}
|}.
Next Obligation.
  first [ (intros s t He; exact (fa_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fa_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fa_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.

(* It agrees with [h] on the generators -- definitionally, not up to
   [≈]. *)
Example free_ab_extend_generators (x : carrier X) :
  cmon_map free_ab_extend (fa_gen x) = h x := eq_refl.

(* The two homomorphism laws, recorded at Leibniz [=] on the CARRIER so
   that the header's strength claim is machine-checked rather than
   inferred from which branch of the obligation tactic fired.  This is
   the convertibility exception the house style sanctions: these are
   equations between elements of A's carrier, not between morphisms. *)
Example free_ab_extend_zero :
  cmon_map free_ab_extend fa_zero = cmon_zero A := eq_refl.

Example free_ab_extend_plus (s t : FATerm) :
  cmon_map free_ab_extend (fa_plus s t)
    = cmon_plus A (cmon_map free_ab_extend s)
                  (cmon_map free_ab_extend t) := eq_refl.

(* Preservation of negation is a THEOREM in [Ab] rather than a field, but
   for THIS homomorphism it is nevertheless definitional, the fixpoint
   having a clause for [fa_neg].  So the derived [ab_map_neg] is not
   needed on the extension's own side; it is needed on the COMPETITOR's
   side in the uniqueness proof below. *)
Example free_ab_extend_neg (s : FATerm) :
  cmon_map free_ab_extend (fa_neg s)
    = ab_neg A (cmon_map free_ab_extend s) := eq_refl.

(** *** Uniqueness

    Any homomorphism out of the free group agreeing with [h] on the
    generators IS the extension.  The induction has one case per former,
    four in all: the generator case is the agreement hypothesis [Hg]
    itself, and the other three are homomorphism laws of the competitor --
    preservation of zero, of sums, and of negation (Instance/Ab.v's
    [ab_map_neg], a theorem and not a field, which is exactly the place
    that derivation earns its keep). *)
Lemma free_ab_extend_unique (g : FreeAbObject ~{Ab}~> A)
  (Hg : ∀ x : carrier X, cmon_map g (fa_gen x) ≈ h x) (t : FATerm) :
  cmon_map g t ≈ fa_eval t.
Proof.
  induction t as [ x | | t1 IHt1 t2 IHt2 | t IHt ]; simpl.
  - exact (Hg x).
  - exact (cmon_map_zero g).
  - refine (transitivity (cmon_map_plus g t1 t2) _).
    exact (cmon_plus_respects A _ _ IHt1 _ _ IHt2).
  - refine (transitivity (ab_map_neg g t) _).
    exact (ab_neg_respects A _ _ IHt).
Qed.

End Extension.

Arguments fa_eval {A} h t.
Arguments free_ab_extend {A} h.

(** ** The universal property, in the shape [universal_arrow_from_UMP]
       consumes *)
Theorem free_ab_universal :
  ∀ (A : AbObject) (h : X ~{Sets}~> Ab_Forget A),
    ∃! g : FreeAbObject ~{Ab}~> A,
      h ≈ fmap[Ab_Forget] g ∘ free_ab_insert.
Proof.
  intros A h.
  unshelve eexists.
  - exact (free_ab_extend h).
  - intro x; simpl; reflexivity.
  - intros g Hg t; simpl.
    symmetry; apply (free_ab_extend_unique A h g).
    intro x; symmetry; exact (Hg x).
Qed.

End FreeAbelian.

Arguments fa_gen {X} x.
Arguments fa_zero {X}.
Arguments fa_plus {X} s t.
Arguments fa_neg {X} s.
Arguments fa_eq {X} s t.
Arguments fa_refl {X} s.
Arguments fae_gen {X x y} _.
Arguments fae_plus {X s s' t t'} _ _.
Arguments fae_neg {X s s'} _.
Arguments fae_assoc {X} s t u.
Arguments fae_comm {X} s t.
Arguments fae_zero_l {X} s.
Arguments fae_neg_l {X} s.
Arguments fae_sym {X s t} _.
Arguments fae_trans {X s t u} _ _.
Arguments fa_eval {X A} h t.
Arguments free_ab_extend {X A} h.
Arguments fa_eval_respects {X} A h s t _.
Arguments free_ab_extend_unique {X} A h g _ t.

(** ** The universal arrow, the free functor and the adjunction *)

(* The free abelian group packaged as a universal arrow.  By
   Theory/Universal/Arrow.v this IS an initial object of the comma
   category [=(X) ↓ Ab_Forget]. *)
Definition free_ab_universal_arrow (X : Sets)
  : UniversalArrow X Ab_Forget :=
  universal_arrow_from_UMP X Ab_Forget (FreeAbObject X) (free_ab_insert X)
    (free_ab_universal X).

(* The same content in the direct encoding, where the universal object is
   named rather than projected out of a comma category. *)
Program Definition free_ab_AUniversalArrow (X : Sets)
  : AUniversalArrow X Ab_Forget (FreeAbObject X) := {|
  universal_arrow := free_ab_insert X
|}.
Next Obligation.
  intros X A h.
  unshelve eexists.
  - exact (free_ab_extend h).
  - intro x; simpl; reflexivity.
  - intros g Hg t; simpl.
    (* [AUniversalArrow]'s uniqueness field is oriented the other way
       round from the comma-packaged one, hence the [symmetry]. *)
    symmetry; apply (free_ab_extend_unique A h g).
    intro x; exact (Hg x).
Qed.

(* The functor and the adjunction come out of the generic machinery with
   no further proof -- the route Instance/Mod/Free.v, Instance/Grp/Free.v,
   Instance/Coq/Monoid/Free.v and Construction/Free/Quiver.v all take. *)
Definition FreeAb : Sets ⟶ Ab :=
  LeftAdjointFunctorFromUniversalArrows Ab_Forget free_ab_universal_arrow.

Definition free_ab_adjunction : FreeAb ⊣ Ab_Forget :=
  AdjunctionFromUniversalArrows Ab_Forget free_ab_universal_arrow.

(** The free functor's object part is the formal-sum group,
    definitionally. *)
Example FreeAb_obj (X : Sets) : FreeAb X = FreeAbObject X := eq_refl.

(** The universal arrow is the insertion of generators on the nose:
    [universal_arrow_from_UMP] stores the supplied morphism as the second
    projection of the comma object it builds, so no proof is involved. *)
Example free_ab_arrow_is_insert (X : Sets) :
  @arrow _ _ X Ab_Forget (free_ab_universal_arrow X) = free_ab_insert X
  := eq_refl.

(** ** The unit is the insertion of generators

    [unit] is DERIVED in Theory/Adjunction.v (it is the transpose of the
    identity), not a field, so what it computes to has to be checked.  It
    is [fmap[U] id ∘ arrow], and [fmap[Ab_Forget] id] is the identity
    setoid map, so the unit is [free_ab_insert] itself. *)

Definition free_ab_unit (X : Sets)
  : X ~{Sets}~> Ab_Forget (FreeAb X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_ab_adjunction X.

Example free_ab_unit_is_insert (X : Sets) (x : carrier X) :
  free_ab_unit X x = free_ab_insert X x := eq_refl.

Example free_ab_unit_is_generator (X : Sets) (x : carrier X) :
  free_ab_unit X x = @fa_gen X x := eq_refl.

(** ** The counit evaluates a formal sum

    The counit is the OTHER transpose, and it does not compute: it is
    [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows]
    (Theory/Universal/Arrow.v) is [Qed]-opaque, so no [eq_refl] is
    available on this side and none is claimed.  What is available -- and
    is the content -- is that it agrees with evaluation up to [≈]. *)

Definition free_ab_counit (A : Ab)
  : FreeAb (Ab_Forget A) ~{Ab}~> A :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_ab_adjunction A.

Lemma free_ab_counit_generator (A : Ab) (a : carrier (Ab_Forget A)) :
  cmon_map (free_ab_counit A) (fa_gen a) ≈ a.
Proof.
  exact (@to_adj_counit _ _ _ _ free_ab_adjunction A a).
Qed.

Theorem free_ab_counit_evaluates (A : Ab) (t : FATerm (Ab_Forget A)) :
  cmon_map (free_ab_counit A) t ≈ fa_eval (@id Sets (Ab_Forget A)) t.
Proof.
  apply (free_ab_extend_unique A (@id Sets (Ab_Forget A))
           (free_ab_counit A)).
  intro a; exact (free_ab_counit_generator A a).
Qed.

(** ** The free functor relabels generators

    [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by universal
    factorization, not by a formula, so what the functor does to a
    generator has to be proved; it is [≈] and not [eq_refl]. *)
Lemma free_ab_fmap_generators {X Y : Sets} (u : X ~{Sets}~> Y)
  (x : carrier X) :
  cmon_map (fmap[FreeAb] u) (fa_gen x) ≈ fa_gen (u x).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_ab_universal_arrow X)
              (@arrow _ _ Y Ab_Forget (free_ab_universal_arrow Y) ∘ u)) x).
Qed.

(** ** The adjunction bijection, and its two naturality clauses

    The forward transpose is restriction to the generators, and it IS the
    adjunction's own ⌊−⌋ -- [free_ab_transpose_is_adj] records that by
    [eq_refl] -- so the two clauses below, proved in the free group's own
    vocabulary, are the class's fields and not weaker statements about
    some other map. *)

Definition fa_transpose {X : Sets} {A : Ab}
  (g : FreeAb X ~{Ab}~> A) : X ~{Sets}~> Ab_Forget A :=
  fmap[Ab_Forget] g ∘ free_ab_insert X.

Example free_ab_transpose_is_adj {X : Sets} {A : Ab}
  (g : FreeAb X ~{Ab}~> A) :
  to (@adj _ _ _ _ free_ab_adjunction X A) g = fa_transpose g := eq_refl.

(** Restriction to the generators is a bijection: the inverse is additive
    extension.  Both round trips are [≈] statements about morphisms, and
    the first of them is [reflexivity] at every generator. *)

Lemma fa_transpose_extend {X : Sets} {A : Ab}
  (h : X ~{Sets}~> Ab_Forget A) : fa_transpose (free_ab_extend h) ≈ h.
Proof. intro x; simpl; reflexivity. Qed.

Lemma fa_extend_transpose {X : Sets} {A : Ab}
  (g : FreeAb X ~{Ab}~> A) : free_ab_extend (fa_transpose g) ≈ g.
Proof.
  intro t; simpl.
  symmetry; apply (free_ab_extend_unique A (fa_transpose g) g).
  intro x; simpl; reflexivity.
Qed.

(** *** Naturality in the generating set *)
Theorem free_ab_naturality_in_set {X Y : Sets} {A : Ab}
  (g : FreeAb Y ~{Ab}~> A) (u : X ~{Sets}~> Y) :
  fa_transpose (g ∘ fmap[FreeAb] u) ≈ fa_transpose g ∘ u.
Proof.
  intro x; simpl.
  exact (proper_morphism (cmon_map g) _ _ (free_ab_fmap_generators u x)).
Qed.

(** *** Naturality in the target group

    Both sides are the same composite of underlying functions, so this is
    [reflexivity] pointwise. *)
Theorem free_ab_naturality_in_group {X : Sets} {A A' : Ab}
  (k : A ~{Ab}~> A') (g : FreeAb X ~{Ab}~> A) :
  fa_transpose (k ∘ g) ≈ fmap[Ab_Forget] k ∘ fa_transpose g.
Proof. intro x; simpl; reflexivity. Qed.

(** The two theorems just proved ARE the adjunction's naturality fields at
    this adjunction: the statements are convertible, so these are the
    clauses and not restatements about a different map. *)
Example free_ab_naturality_in_set_is_to_adj_nat_l
  {X Y : Sets} {A : Ab} (g : FreeAb Y ~{Ab}~> A) (u : X ~{Sets}~> Y) :
  (to (@adj _ _ _ _ free_ab_adjunction X A) (g ∘ fmap[FreeAb] u)
     ≈ to (@adj _ _ _ _ free_ab_adjunction Y A) g ∘ u)
  = (fa_transpose (g ∘ fmap[FreeAb] u) ≈ fa_transpose g ∘ u) := eq_refl.

Example free_ab_naturality_in_group_is_to_adj_nat_r
  {X : Sets} {A A' : Ab} (k : A ~{Ab}~> A') (g : FreeAb X ~{Ab}~> A) :
  (to (@adj _ _ _ _ free_ab_adjunction X A') (k ∘ g)
     ≈ fmap[Ab_Forget] k ∘ to (@adj _ _ _ _ free_ab_adjunction X A) g)
  = (fa_transpose (k ∘ g) ≈ fmap[Ab_Forget] k ∘ fa_transpose g) := eq_refl.

(** ** The triangle identities *)

Corollary free_ab_triangle_left (X : Sets) :
  free_ab_counit (FreeAb X) ∘ fmap[FreeAb] (free_ab_unit X)
    ≈ @id Ab (FreeAb X).
Proof. exact (@counit_fmap_unit _ _ _ _ free_ab_adjunction X). Qed.

Corollary free_ab_triangle_right (A : Ab) :
  fmap[Ab_Forget] (free_ab_counit A) ∘ free_ab_unit (Ab_Forget A)
    ≈ @id Sets (Ab_Forget A).
Proof. exact (@fmap_counit_unit _ _ _ _ free_ab_adjunction A). Qed.

Arguments fa_transpose {X A} g.
Arguments free_ab_fmap_generators {X Y} u x.


(** ** Non-degeneracy

    A free construction is worthless if it collapses, and no induction
    over [fa_eq] can produce a negative -- every constructor concludes an
    equation.  So each refutation below maps OUT of the free group into a
    concrete abelian group and reads the answer off there, exactly as
    Instance/Grp/Free.v's [free_group_two_generators_nonabelian] does.

    The general statements are made over an ARBITRARY abelian group A
    with a distinguished element a that is not zero.  That is not
    generality for its own sake: it is what keeps them universe-free.
    Instantiating them at the integers instead -- writing the
    characteristic function with values 1 and 0 in ℤ -- pins the
    generating setoid's carrier AND relation universes to [Set], which
    was MEASURED by three probes rather than guessed: the same probe with
    ℤ but no decidable case split is free of [Set], and the same case
    split into an abstract A is free of [Set], while the two together
    pin.  So the concrete group is deferred to the two-generator witness
    at the end of the file, where [bool] forces [Set] anyway. *)

Section NonDegeneracy.

Context (X : SetoidObject).
Context (A : AbObject).
Context (a : carrier (cmon_setoid A)).
Context (Ha : a ≈ cmon_zero A → False).

(** *** Two separations that need no decider at all

    The constant map at [a] is a morphism of [Sets] with no hypothesis on
    X whatever, and it already refutes the two cheapest collapses. *)

Definition fa_probe_const : X ~{Sets}~> Ab_Forget A.
Proof using X A a.
  unshelve refine {| morphism := fun _ => a |}.
  intros z z' _; reflexivity.
Defined.

(** A generator is not zero. *)
Theorem free_ab_gen_not_zero (x : carrier X) :
  fa_eq (@fa_gen X x) fa_zero → False.
Proof using X A a Ha.
  intro He.
  exact (Ha (fa_eval_respects A fa_probe_const _ _ He)).
Qed.

(** The group is not idempotent: doubling a generator moves it.  This is
    where the group structure is spent -- [ab_cancel_l] (Instance/Ab.v)
    is what turns a + a ≈ a into a ≈ 0, and it is the one property that
    separates a group from a monoid. *)
Theorem free_ab_gen_not_idempotent (x : carrier X) :
  fa_eq (fa_plus (@fa_gen X x) (fa_gen x)) (fa_gen x) → False.
Proof using X A a Ha.
  intro He.
  pose proof (fa_eval_respects A fa_probe_const _ _ He) as Hv; simpl in Hv.
  apply Ha.
  apply (ab_cancel_l A a).
  transitivity a; [ exact Hv | ].
  symmetry; apply cmon_plus_zero_r.
Qed.

(** *** Separations that need a decider on the generating setoid

    Distinguishing two DIFFERENT generators means exhibiting a group in
    which they go to different places, and the only such map a bare
    setoid supplies is the characteristic function of a point, which
    cannot be WRITTEN without a decision procedure for that setoid's
    [≈].  That is an ARGUMENT, not a theorem: no converse is proved here,
    and the tree's precedent for claims of exactly this shape
    ([arrow_mul_respects_forces_UIP] and its siblings) is deliberately
    not followed.

    Unlike Instance/Mod/Free.v's [free_module_basis_injective] this needs
    only ONE hypothesis rather than two.  That file's second hypothesis
    is 1 ≉ 0 in the coefficient ring, because it probes with the ring
    viewed as a module over itself and the ring may be the zero ring;
    here the nondegeneracy of the target is already carried by [Ha]. *)

Context (Xdec : ∀ x y : carrier X, (x ≈ y) + ((x ≈ y) → False)).

(* The characteristic function of the generator [x]. *)
Definition fa_probe_at (x : carrier X) : X ~{Sets}~> Ab_Forget A.
Proof using X A a Xdec.
  unshelve refine {|
    morphism := fun z => match Xdec x z with
                         | inl _ => a
                         | inr _ => cmon_zero A
                         end
  |}.
  intros z z' Hz; simpl.
  destruct (Xdec x z) as [Hxz|Hxz], (Xdec x z') as [Hxz'|Hxz'].
  - reflexivity.
  - destruct (Hxz' (transitivity Hxz Hz)).
  - destruct (Hxz (transitivity Hxz' (symmetry Hz))).
  - reflexivity.
Defined.

(** Distinct generators give distinct elements. *)
Theorem free_ab_gen_injective (x y : carrier X) :
  fa_eq (@fa_gen X x) (fa_gen y) → x ≈ y.
Proof using X A a Ha Xdec.
  intro He.
  destruct (Xdec x y) as [Hxy|Hxy]; [ exact Hxy | ].
  destruct Ha.
  pose proof (fa_eval_respects A (fa_probe_at x) _ _ He) as Hv.
  simpl in Hv.
  destruct (Xdec x x) as [_|Hxx]; [ | destruct (Hxx (reflexivity x)) ].
  destruct (Xdec x y) as [Hc|_]; [ destruct (Hxy Hc) | ].
  exact Hv.
Qed.

(** A COMPOUND element is separated from a generator: e_x + e_y is not
    e_x when x ≉ y.  Neither theorem above gives this -- both are about
    generators alone -- so it is the sharpest of the four. *)
Theorem free_ab_sum_not_summand (x y : carrier X)
  (Hxy : (x ≈ y) → False) :
  fa_eq (fa_plus (@fa_gen X x) (fa_gen y)) (fa_gen x) → False.
Proof using X A a Ha Xdec.
  intro He.
  pose proof (fa_eval_respects A (fa_probe_at y) _ _ He) as Hv.
  simpl in Hv.
  destruct (Xdec y x) as [Hc|_]; [ destruct (Hxy (symmetry Hc)) | ].
  destruct (Xdec y y) as [_|Hyy]; [ | destruct (Hyy (reflexivity y)) ].
  apply Ha.
  rewrite <- Hv.
  symmetry; apply cmon_plus_zero_l.
Qed.

End NonDegeneracy.

Arguments fa_probe_const {X} A a.
Arguments fa_probe_at {X} A a Xdec x.
Arguments free_ab_gen_not_zero {X} A a Ha x _.
Arguments free_ab_gen_not_idempotent {X} A a Ha x _.
Arguments free_ab_gen_injective {X} A a Ha Xdec x y _.
Arguments free_ab_sum_not_summand {X} A a Ha Xdec x y Hxy _.

(** ** A computing witness on two generators

    The integers, as [ring_ab Int_Ring]: Instance/Rng.v:103's [ring_ab]
    applied to Theory/Algebra/Rig.v:588's [Int_Ring].  This is the same
    term Instance/Ab/Coproduct.v:264 names [ab_Z]; that file is NOT
    required here (it would drag the biproduct closure in for one
    definition), so no in-file identification with that name is stated.

    The generating setoid has TWO elements, so the free group is not ℤ
    itself and the additive extension has something to do. *)

Definition ab_int : AbObject := ring_ab Int_Ring.

Lemma ab_int_one_not_zero : (1%Z : carrier (cmon_setoid ab_int))
  ≈ cmon_zero ab_int → False.
Proof. intro H; compute in H; discriminate H. Qed.

Definition AbTwoGens : SetoidObject := {|
  carrier   := bool;
  is_setoid := {| equiv := eq; setoid_equiv := eq_equivalence |}
|}.

Definition ab_two_gens_dec :
  ∀ x y : carrier AbTwoGens, (x ≈ y) + ((x ≈ y) → False).
Proof.
  intros x y; simpl.
  destruct x, y.
  - exact (inl eq_refl).
  - right; intro H; discriminate.
  - right; intro H; discriminate.
  - exact (inl eq_refl).
Defined.

(* [FATerm]'s index argument is implicit, and in a statement with no
   expected type -- an [fa_eq] between two constructor applications --
   the elaborator has nothing to propagate it from.  These are
   NOTATIONS, not definitions, so each unfolds to the constructor itself
   and nothing below is stated about a different term. *)
Local Notation zgen  := (@fa_gen AbTwoGens).
Local Notation zplus := (@fa_plus AbTwoGens).
Local Notation zneg  := (@fa_neg AbTwoGens).

(* Two integers, read off the two generators. *)
Definition ab_int_probe : AbTwoGens ~{Sets}~> Ab_Forget ab_int.
Proof.
  unshelve refine {|
    morphism := fun b : carrier AbTwoGens => if b then 3%Z else 5%Z
  |}.
  (* [all:] because the respectfulness field of a map out of a setoid
     whose ≈ is Leibniz [=] may be discharged by instance resolution
     before a goal is ever opened; the carriers here are at [Set] either
     way, so nothing is pinned that was not already. *)
  all: intros x y H; simpl in H; subst y; reflexivity.
Defined.

(* The additive extension computes: e_true + e_true + (−e_false)
   ↦ 3 + 3 − 5 = 1. *)
Example int_free_ab_extend_computes :
  fa_eval ab_int_probe
    (zplus (zplus (zgen true) (zgen true)) (zneg (zgen false)))
    = 1%Z := eq_refl.

Example int_free_ab_extend_generator_true :
  fa_eval ab_int_probe (zgen true) = 3%Z := eq_refl.

Example int_free_ab_extend_zero :
  fa_eval ab_int_probe (@fa_zero AbTwoGens) = 0%Z := eq_refl.

(** The four separations, instantiated at ℤ with the element 1 and at the
    decidable two-element setoid. *)

Theorem int_free_ab_gen_not_zero :
  fa_eq (zgen true) (@fa_zero AbTwoGens) → False.
Proof.
  exact (@free_ab_gen_not_zero AbTwoGens ab_int 1%Z
           ab_int_one_not_zero true).
Qed.

Theorem int_free_ab_gen_not_idempotent :
  fa_eq (zplus (zgen true) (zgen true)) (zgen true) → False.
Proof.
  exact (@free_ab_gen_not_idempotent AbTwoGens ab_int 1%Z
           ab_int_one_not_zero true).
Qed.

Theorem int_free_ab_gens_distinct : fa_eq (zgen true) (zgen false) → False.
Proof.
  intro He.
  pose proof (@free_ab_gen_injective AbTwoGens ab_int 1%Z
                ab_int_one_not_zero ab_two_gens_dec true false He) as Hb.
  compute in Hb; discriminate Hb.
Qed.

Theorem int_free_ab_sum_not_summand :
  fa_eq (zplus (zgen true) (zgen false)) (zgen true) → False.
Proof.
  refine (@free_ab_sum_not_summand AbTwoGens ab_int 1%Z
            ab_int_one_not_zero ab_two_gens_dec true false _).
  intro H; discriminate H.
Qed.

(** ** Measured negatives

    Each [Fail] below records a strengthening that the file does NOT
    have, and each is paired with a positive control that must succeed,
    so a rename or a change of definition breaks the file loudly instead
    of turning the [Fail] vacuously green.  The house convention puts
    such probes in a Test/Probe*.v file; they are in-file here because
    this commit adds exactly one file, and moving them costs nothing. *)

(* CONVERSION.  The counit does not compute.  It is
   [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows]
   (Theory/Universal/Arrow.v) is [Qed]-opaque, so nothing reduces
   through it; only the [≈] statement [free_ab_counit_generator] holds.
   Control: the UNIT at the same generator DOES compute. *)
Fail Example counit_does_not_compute (A : Ab) (b : carrier (Ab_Forget A)) :
  cmon_map (free_ab_counit A) (fa_gen b) = b := eq_refl.

Example ab_control_unit_computes (X : Sets) (x : carrier X) :
  free_ab_unit X x = @fa_gen X x := eq_refl.

(* CONVERSION.  The free functor's action on a generator does not
   compute either, for the same reason -- [fmap] of
   [LeftAdjointFunctorFromUniversalArrows] is defined by universal
   factorization, not by a formula.  Only the [≈] statement
   [free_ab_fmap_generators] holds.  Control: the object action DOES
   compute. *)
Fail Example fmap_generator_does_not_compute
  (X Y : Sets) (u : X ~{Sets}~> Y) (x : carrier X) :
  cmon_map (fmap[FreeAb] u) (fa_gen x) = fa_gen (u x) := eq_refl.

Example control_fobj_computes (X : Sets) : FreeAb X = FreeAbObject X
  := eq_refl.

(* CONVERSION.  Even when the generating setoid is the target's own
   carrier, the free group is not CONVERTIBLE with that group:
   [FreeAbObject] is an inductive of formal expressions, so nothing
   identifies its record with ℤ's.  This says nothing about
   ISOMORPHISM -- no such claim is made anywhere in this file, in either
   direction.  Control: the generators of the two-element witness really
   are inhabitants of the free group's carrier. *)
Fail Example free_on_carrier_is_not_the_group :
  FreeAbObject (Ab_Forget ab_int) = ab_int := eq_refl.

Example control_generators_typecheck :
  carrier (Ab_Forget (FreeAbObject AbTwoGens))
  := (zgen true : FATerm AbTwoGens).

(* Instrument check: [Fail] does fire on a genuine conversion failure of
   the same kind as the three negatives above, so their green is not the
   harness reporting success on nothing. *)
Fail Example instrument_check : (0%Z = 1%Z) := eq_refl.
