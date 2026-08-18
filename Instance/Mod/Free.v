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
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(* The global obligation tactic is [cat_simpl], which would run wide proof
   searches on the module obligations below and has already introduced the
   parameters by the time an obligation is opened.  Switched off here, the
   Instance/Mod.v:104 idiom, so every obligation starts with an explicit
   [intros]. *)
#[local] Obligation Tactic := idtac.

(** * The free module on a set, and the free-forgetful adjunction

    nLab:      https://ncatlab.org/nlab/show/free+module
    nLab:      https://ncatlab.org/nlab/show/free+object
    nLab:      https://ncatlab.org/nlab/show/universal+morphism
    Wikipedia: https://en.wikipedia.org/wiki/Free_module
    Wikipedia: https://en.wikipedia.org/wiki/Basis_(linear_algebra)
    Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
          GTM 5, §III.1, printed p. 56 (the free vector space on a set as
          the paradigm universal arrow) — maclane:III.1:construction1
    Book: Mac Lane, ibid., §IV.1, printed p. 79 (the same content in
          adjunction form, opening the adjunctions chapter) —
          maclane:IV.1:construction1
    Book: Riehl, Category Theory in Context, §4.0, printed p. 131 (k[S],
          its functoriality in S, and its universal property stated as a
          left adjoint to the underlying-set functor) —
          riehl:4.0:construction-free-vector-space

    WHY THIS CONSTRUCTION OPENS TWO CHAPTERS.  A basis is the oldest
    universal property in mathematics that nobody called universal.  The
    nineteenth-century statement — every vector is uniquely a finite
    linear combination of basis vectors — is exactly the assertion that a
    function defined on the basis extends to a linear map in one and only
    one way, which is to say that the pair (k[S], insertion of the basis)
    solves a universal mapping problem.  Mac Lane opens §III.1 with this
    example because it is the one every reader already knows, and returns
    to it at the head of §IV.1 because the two-variable bijection

        Vect_k(k[S], W)  ≅  Set(S, U W)

    natural in S and in W is the shortest honest description of what an
    adjunction is.  Riehl opens her chapter 4 the same way.  The reason
    the example carries so much weight is that it is *not* about vector
    spaces: the argument uses only that a module is an abelian group with
    a scalar action, so it runs verbatim over an arbitrary ring, and the
    field-specific content of linear algebra (every module is free, every
    basis has the same size) plays no part.  That is why this file is
    stated over Instance/Mod.v's [RMod R] for an arbitrary [RingObject],
    with the vector-space reading — which is the literal content of all
    three catalogued items — split off into Instance/Vect/Free.v, where
    [Vct_F F] is [RMod (field_ring F)] by DEFINITION
    (Instance/FdVect.v:223) and the specializations are therefore
    conversions rather than transports.

    HOW THE FREE MODULE IS PRESENTED, AND HOW THAT DIFFERS FROM THE
    ISSUE'S SKETCH.  The classical description — "finitely supported
    K-valued functions on X" — presupposes a set of generators with
    decidable equality, and it is worth being exact about WHERE.  The
    CARRIER is not the obstruction: a [≈]-respecting function paired with
    a list witnessing that it vanishes outside that list is writable over
    a bare setoid, and carries zero, pointwise addition and the scalar
    action with no decider anywhere.  The obstruction is the BASIS
    INSERTION, which is what a universal arrow needs: the basis vector at
    x is the function taking 1 at x and 0 elsewhere, and that function
    cannot be WRITTEN without a decision procedure for x ≈ y.  What makes
    this fatal rather than merely restrictive is that [RMod_Forget] lands
    in [Sets], whose objects are setoids, so the left adjoint must exist
    for EVERY generating setoid, decidable or not — a construction
    available only at decidable setoids yields no adjunction at all.  The
    presentation used here is therefore by generators and relations, in
    the style of
    Instance/Ab/Tensor.v and Instance/Sets/Coend.v: [FVTerm] is a plain
    inductive of formal expressions and the equality [fv_eq] is an
    inductive relation closing under exactly the abelian-group laws, the
    four module laws, congruence for each former, saturation under the
    generating setoid's own [≈] and under the ring's, and
    symmetry/transitivity.  Reflexivity is derived ([fv_refl]), keeping
    the relation's induction principle one case shorter everywhere it is
    consumed.  As in Instance/Ab/Tensor.v, [fv_Setoid] is NOT registered
    as a typeclass instance and statements about elements of the free
    module are written with [fv_eq] rather than [≈]; the [≈] of the free
    module as an object of [RMod R] is that relation, definitionally, so
    the module-level lemmas of Instance/Mod.v apply to it unchanged.

    What is lost by not using functions is coefficient uniqueness; what
    is kept is everything the universal property needs, and the classical
    description is recovered in the direction that does not need
    decidability: [fv_normal_form] proves that EVERY element of the free
    module is [fv_eq] to a finite formal linear combination
    r₁·e_{x₁} + … + rₙ·e_{xₙ} of basis vectors ([fv_lc] of a list), which
    is the "finitely supported" half of the classical statement.  The
    other half — that the list is unique up to rearrangement and
    combination of like terms — is exactly what needs a decider on X, and
    it is NOT proved here.  Three non-degeneracy results measure how far
    that leaves the construction from collapsing, and they cost different
    things: [free_module_scalars_faithful] (distinct scalars give
    distinct multiples of a basis vector) needs NO hypothesis at all;
    [free_module_two_independent] (the basis is linearly independent —
    if r·e_x + s·e_y vanishes and x ≉ y then both coefficients vanish,
    which is the statement a reader of §III.1 wants) needs only a decider
    for X's [≈]; and [free_module_basis_injective] (distinct generators
    give distinct basis vectors) needs that decider together with 1 ≉ 0
    in R.  The section header there ARGUES — it does not prove; no
    converse is machine-checked — why hypotheses are needed at all:
    separating two generators means mapping into a module in which they
    go to different places, and building such a map out of a bare setoid
    is the decision procedure.

    STRENGTHS, MEASURED.  The mediator is a [Fixpoint] on formal
    expressions, so:

      - [eq_refl]: the linear extension preserves zero, addition and the
        scalar action DEFINITIONALLY (all three homomorphism obligations
        close by [reflexivity]); it agrees with the given function on
        generators definitionally ([free_module_extend_generators], an
        [eq_refl] on carriers); the free functor's object part is the
        formal-sum module ([FreeMod_obj]); the universal arrow IS the
        basis insertion ([free_module_arrow_is_insert]); the UNIT is the
        one-generator expression ([free_module_unit_is_insert]); and the
        adjunction's forward transpose ⌊−⌋ IS [fv_transpose]
        ([free_module_transpose_is_adj]) — which is what lets the two
        naturality clauses below be stated in the transpose's own
        vocabulary and still be the class's fields verbatim.
      - [≈] only: the COUNIT.  It is the other transpose, i.e.
        [unique_obj (ump_universal_arrows …)], and [ump_universal_arrows]
        (Theory/Universal/Arrow.v) is [Qed]-opaque, so it does not
        compute and no [eq_refl] is claimed on that side.  What is proved
        is that it evaluates a formal linear combination in the module
        ([free_module_counit_evaluates]).
      - [≈] only, and NOT for want of trying: the action of the free
        functor on an arrow.  [LeftAdjointFunctorFromUniversalArrows]
        defines [fmap] by universal factorization rather than by a
        formula, so that it relabels generators is a theorem
        ([free_module_fmap_generators]), not a computation.

    THE TWO NATURALITY CLAUSES.  §IV.1 asks for naturality of the
    bijection in each variable separately, and both are stated and proved
    here in the free module's own vocabulary rather than by citing the
    class: [free_module_naturality_in_set] (in the generating set, proved
    by evaluating on generators through [free_module_fmap_generators])
    and [free_module_naturality_in_module] (in the target module, proved
    pointwise by [reflexivity], both sides being the same composite of
    underlying functions).  That they are the class's own fields
    [to_adj_nat_l] and [to_adj_nat_r] at this adjunction is then recorded
    by [eq_refl] on the STATEMENTS
    ([free_module_naturality_in_set_is_to_adj_nat_l] and its sibling) —
    a conversion check that the independently proved theorems are the
    fields, not a second derivation of them.

    WHAT IS NOT DELIVERED.

      - No uniqueness of coefficients.  [fv_normal_form] IS proved —
        every element is [fv_eq] to some [fv_lc l] — so what is missing
        is not the existence of a linear-combination form but its
        CANONICITY: the list is not unique up to rearrangement and
        collection of like terms, and nothing here says two lists
        denoting the same element are related.  Hence also no decision
        procedure for equality in the free module, no dimension, and no
        proof that the basis insertion is injective for a GENERAL
        generating setoid (see above for why).
      - No statement that [FreeMod] is faithful, and no characterization
        of its image; no proof that a free module is projective; no
        invariant basis number.
      - No comparison with Instance/FdVect.v's [StdVect] (which carries a
        chosen coordinate isomorphism to Fⁿ), and so no proof that the
        free module on [Fin.t n] is finite-dimensional in that file's
        sense — that comparison needs the coefficient uniqueness just
        disclaimed. *)

(** ** Formal linear combinations and the module quotient *)

Section FreeModule.

Context (R : RingObject).
Context (X : SetoidObject).

(* Formal expressions over the generating setoid: generators, zero, sum,
   negation, scalar multiple.  Negation is a CONSTRUCTOR rather than the
   derived (−1)·(−): deriving it would need 0·t ≈ 0 in the free module,
   whose usual proof cancels [0·t] against itself and so already needs
   the group structure being built. *)
Inductive FVTerm : Type :=
  | fv_gen  : carrier X → FVTerm
  | fv_zero : FVTerm
  | fv_plus : FVTerm → FVTerm → FVTerm
  | fv_neg  : FVTerm → FVTerm
  | fv_smul : carrier (rig_setoid (ring_rig R)) → FVTerm → FVTerm.

(* The quotienting relation: congruence for each former (saturating under
   the generating setoid's [≈] and the ring's), the abelian-group laws,
   the four module laws, symmetry and transitivity.  Reflexivity is
   derived below. *)
Inductive fv_eq : FVTerm → FVTerm → Type :=
  | fe_gen {x y : carrier X} : x ≈ y → fv_eq (fv_gen x) (fv_gen y)
  | fe_plus {s s' t t'} :
      fv_eq s s' → fv_eq t t' → fv_eq (fv_plus s t) (fv_plus s' t')
  | fe_neg {s s'} : fv_eq s s' → fv_eq (fv_neg s) (fv_neg s')
  | fe_smul {r r' : carrier (rig_setoid (ring_rig R))} {s s'} :
      r ≈ r' → fv_eq s s' → fv_eq (fv_smul r s) (fv_smul r' s')

  (* abelian group *)
  | fe_assoc (s t u : FVTerm) :
      fv_eq (fv_plus (fv_plus s t) u) (fv_plus s (fv_plus t u))
  | fe_comm (s t : FVTerm) : fv_eq (fv_plus s t) (fv_plus t s)
  | fe_zero_l (s : FVTerm) : fv_eq (fv_plus fv_zero s) s
  | fe_neg_l (s : FVTerm) : fv_eq (fv_plus (fv_neg s) s) fv_zero

  (* module *)
  | fe_smul_distr_l (r : carrier (rig_setoid (ring_rig R))) (s t : FVTerm) :
      fv_eq (fv_smul r (fv_plus s t))
            (fv_plus (fv_smul r s) (fv_smul r t))
  | fe_smul_distr_r (r r' : carrier (rig_setoid (ring_rig R))) (s : FVTerm) :
      fv_eq (fv_smul (rig_add (ring_rig R) r r') s)
            (fv_plus (fv_smul r s) (fv_smul r' s))
  | fe_smul_assoc (r r' : carrier (rig_setoid (ring_rig R))) (s : FVTerm) :
      fv_eq (fv_smul (rig_mul (ring_rig R) r r') s)
            (fv_smul r (fv_smul r' s))
  | fe_smul_one (s : FVTerm) :
      fv_eq (fv_smul (rig_one (ring_rig R)) s) s

  | fe_sym {s t} : fv_eq s t → fv_eq t s
  | fe_trans {s t u} : fv_eq s t → fv_eq t u → fv_eq s u.

Lemma fv_refl (s : FVTerm) : fv_eq s s.
Proof.
  induction s.
  - exact (fe_gen (reflexivity _)).
  - exact (fe_trans (fe_sym (fe_zero_l fv_zero)) (fe_zero_l fv_zero)).
  - exact (fe_plus IHs1 IHs2).
  - exact (fe_neg IHs).
  - exact (fe_smul (reflexivity _) IHs).
Qed.

Lemma fv_eq_Equivalence : Equivalence fv_eq.
Proof.
  constructor.
  - exact fv_refl.
  - exact (fun s t => fe_sym).
  - exact (fun s t u => fe_trans).
Qed.

Definition fv_Setoid : Setoid FVTerm := {|
  equiv        := fv_eq;
  setoid_equiv := fv_eq_Equivalence
|}.

(** ** The free module

    Every law of the module is a constructor of the relation; nothing is
    proved.  The record is written out in one literal so that the
    underlying setoid, the group operations and the action are all
    visible at a glance and all reduce. *)
Definition FreeModObject : RModObject R := {|
  rm_ab := {|
    ab_cmon := {|
      cmon_setoid := {| carrier := FVTerm; is_setoid := fv_Setoid |};
      cmon_zero := fv_zero;
      cmon_plus := fv_plus;
      cmon_plus_respects := fun _ _ Hs _ _ Ht => fe_plus Hs Ht;
      cmon_plus_assoc := fe_assoc;
      cmon_plus_comm := fe_comm;
      cmon_plus_zero_l := fe_zero_l
    |};
    ab_neg := fv_neg;
    ab_neg_respects := fun _ _ Hs => fe_neg Hs;
    ab_neg_left := fe_neg_l
  |};
  rm_smul := fv_smul;
  rm_smul_respects := fun _ _ Hr _ _ Hs => fe_smul Hr Hs;
  rm_smul_distr_l := fe_smul_distr_l;
  rm_smul_distr_r := fe_smul_distr_r;
  rm_smul_assoc := fe_smul_assoc;
  rm_smul_one := fe_smul_one
|}.

(** ** The insertion of the basis

    A generator becomes the corresponding formal expression.
    Respectfulness is the congruence constructor [fe_gen], supplied by
    [exact] rather than as a record field: the target's [≈] is [fv_eq]
    by conversion but not by unification, and only [exact] will convert. *)
Definition fv_insert : X ~{Sets}~> RMod_Forget R FreeModObject.
Proof.
  unshelve refine {| morphism := fv_gen |}.
  intros x y H; exact (fe_gen H).
Defined.

(** ** The linear extension of a function on generators *)

Section Extension.

Context (W : RModObject R).
Context (h : X ~{Sets}~> RMod_Forget R W).

(* Fold a formal expression through the target module's operations.  It
   computes on constructors, which is what makes all three homomorphism
   obligations below hold by [reflexivity]. *)
Fixpoint fv_eval (t : FVTerm) : carrier (cmon_setoid W) :=
  match t with
  | fv_gen x    => h x
  | fv_zero     => cmon_zero W
  | fv_plus s t => cmon_plus W (fv_eval s) (fv_eval t)
  | fv_neg s    => ab_neg W (fv_eval s)
  | fv_smul r s => rm_smul W r (fv_eval s)
  end.

(* Respectfulness is one induction over the relation: 14 cases, one per
   constructor of [fv_eq].  Eight are met by the corresponding law of the
   target module (four abelian-group, four module); the other six are
   not laws — [fe_gen] is saturation under X's own [≈], three are
   congruence for a former, and two are the target setoid's symmetry and
   transitivity. *)
Lemma fv_eval_respects (s t : FVTerm) : fv_eq s t → fv_eval s ≈ fv_eval t.
Proof.
  intro He.
  induction He as
    [ x y Hxy
    | s s' t t' _ IHs _ IHt
    | s s' _ IHs
    | r r' s s' Hr _ IHs
    | s t u | s t | s | s
    | r s t | r r' s | r r' s | s
    | s t _ IHst
    | s t u _ IHst _ IHtu ]; simpl.
  - exact (proper_morphism h _ _ Hxy).
  - exact (cmon_plus_respects W _ _ IHs _ _ IHt).
  - exact (ab_neg_respects W _ _ IHs).
  - exact (rm_smul_respects W _ _ Hr _ _ IHs).
  - exact (cmon_plus_assoc W _ _ _).
  - exact (cmon_plus_comm W _ _).
  - exact (cmon_plus_zero_l W _).
  - exact (ab_neg_left W _).
  - exact (rm_smul_distr_l W _ _ _).
  - exact (rm_smul_distr_r W _ _ _).
  - exact (rm_smul_assoc W _ _ _).
  - exact (rm_smul_one W _).
  - exact (symmetry IHst).
  - exact (transitivity IHst IHtu).
Qed.

(* The extension, as a morphism of [RMod R].  The four obligations are
   respectfulness of the fold and preservation of zero, of addition and
   of the action; the last three hold by [reflexivity], the fixpoint's
   clauses BEING those three equations.  One uniform body is used so that
   the proof does not depend on the order [Program] emits them in. *)
Program Definition fv_extend : FreeModObject ~{RMod R}~> W := {|
  rm_hom := {| cmon_map := {| morphism := fv_eval |} |}
|}.
Next Obligation.
  first [ (intros s t He; exact (fv_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fv_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fv_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (fv_eval_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.

(* It agrees with [h] on the basis — definitionally, not up to [≈]. *)
Example free_module_extend_generators (x : carrier X) :
  cmon_map (rm_hom fv_extend) (fv_gen x) = h x := eq_refl.

(* The three homomorphism laws, recorded at Leibniz [=] on the CARRIER so
   that the header's strength claim is machine-checked rather than
   inferred from which branch of the obligation tactic fired.  This is
   the convertibility exception: these are equations between elements of
   [W]'s carrier, not between morphisms. *)
Example free_module_extend_zero :
  cmon_map (rm_hom fv_extend) fv_zero = cmon_zero W := eq_refl.

Example free_module_extend_plus (s t : FVTerm) :
  cmon_map (rm_hom fv_extend) (fv_plus s t)
    = cmon_plus W (cmon_map (rm_hom fv_extend) s)
                  (cmon_map (rm_hom fv_extend) t) := eq_refl.

Example free_module_extend_smul
  (r : carrier (rig_setoid (ring_rig R))) (s : FVTerm) :
  cmon_map (rm_hom fv_extend) (fv_smul r s)
    = rm_smul W r (cmon_map (rm_hom fv_extend) s) := eq_refl.

(** *** Uniqueness

    Any module homomorphism out of the free module agreeing with [h] on
    the basis IS the extension.  The induction has one case per former,
    five in all: the generator case is the agreement hypothesis [Hg]
    itself, and the other four are homomorphism laws of the competitor —
    preservation of zero, of sums, of negation (Instance/Mod.v's
    [rmod_map_neg], which is Instance/Ab.v's [ab_map_neg] and not a
    field) and of the action. *)
Lemma fv_extend_unique (g : FreeModObject ~{RMod R}~> W)
  (Hg : ∀ x : carrier X, cmon_map (rm_hom g) (fv_gen x) ≈ h x) (t : FVTerm) :
  cmon_map (rm_hom g) t ≈ fv_eval t.
Proof.
  induction t as [ x | | t1 IHt1 t2 IHt2 | t IHt | r t IHt ]; simpl.
  - exact (Hg x).
  - exact (cmon_map_zero (rm_hom g)).
  - refine (transitivity (cmon_map_plus (rm_hom g) t1 t2) _).
    exact (cmon_plus_respects W _ _ IHt1 _ _ IHt2).
  - refine (transitivity (rmod_map_neg g t) _).
    exact (ab_neg_respects W _ _ IHt).
  - refine (transitivity (rm_map_smul g r t) _).
    exact (rm_smul_respects W _ _ (reflexivity r) _ _ IHt).
Qed.

End Extension.

Arguments fv_eval {W} h t.
Arguments fv_extend {W} h.

(** ** The universal property, in the shape [universal_arrow_from_UMP]
       consumes *)
Theorem free_module_universal :
  ∀ (W : RModObject R) (h : X ~{Sets}~> RMod_Forget R W),
    ∃! g : FreeModObject ~{RMod R}~> W,
      h ≈ fmap[RMod_Forget R] g ∘ fv_insert.
Proof.
  intros W h.
  unshelve eexists.
  - exact (fv_extend h).
  - intro x; simpl; reflexivity.
  - intros g Hg t; simpl.
    symmetry; apply (fv_extend_unique W h g).
    intro x; symmetry; exact (Hg x).
Qed.

End FreeModule.

Arguments FVTerm {R X}.
Arguments fv_gen {R X} x.
Arguments fv_zero {R X}.
Arguments fv_plus {R X} s t.
Arguments fv_neg {R X} s.
Arguments fv_smul {R X} r s.
Arguments fv_eq {R X} s t.
Arguments fv_refl {R X} s.
Arguments fe_gen {R X x y} _.
Arguments fe_plus {R X s s' t t'} _ _.
Arguments fe_neg {R X s s'} _.
Arguments fe_smul {R X r r' s s'} _ _.
Arguments fe_assoc {R X} s t u.
Arguments fe_comm {R X} s t.
Arguments fe_zero_l {R X} s.
Arguments fe_neg_l {R X} s.
Arguments fe_smul_distr_l {R X} r s t.
Arguments fe_smul_distr_r {R X} r r' s.
Arguments fe_smul_assoc {R X} r r' s.
Arguments fe_smul_one {R X} s.
Arguments fe_sym {R X s t} _.
Arguments fe_trans {R X s t u} _ _.
Arguments FreeModObject {R} X.
Arguments fv_insert {R} X.
Arguments fv_eval {R X W} h t.
Arguments fv_extend {R X W} h.
Arguments fv_eval_respects {R X} W h s t _.
Arguments fv_extend_unique {R X} W h g _ t.
Arguments free_module_universal {R} X W h.

(** ** The universal arrow, the free functor and the adjunction *)

Section FreeModuleAdjunction.

Context (R : RingObject).

(* The free module packaged as a universal arrow.  By
   Theory/Universal/Arrow.v this IS an initial object of the comma
   category [=(X) ↓ RMod_Forget R]. *)
Definition free_module_universal_arrow (X : Sets)
  : UniversalArrow X (RMod_Forget R) :=
  universal_arrow_from_UMP X (RMod_Forget R) (FreeModObject X) (fv_insert X)
    (free_module_universal X).

(* The same content in the direct encoding, where the universal object is
   named rather than projected out of a comma category. *)
Program Definition free_module_AUniversalArrow (X : Sets)
  : AUniversalArrow X (RMod_Forget R) (FreeModObject X) := {|
  universal_arrow := fv_insert X
|}.
Next Obligation.
  intros X W h.
  unshelve eexists.
  - exact (fv_extend h).
  - intro x; simpl; reflexivity.
  - intros g Hg t; simpl.
    (* [AUniversalArrow]'s uniqueness field is oriented the other way
       round from the comma-packaged one, hence the [symmetry]. *)
    symmetry; apply (fv_extend_unique W h g).
    intro x; exact (Hg x).
Qed.

(* The functor and the adjunction come out of the generic machinery with
   no further proof — the route Instance/Grp/Free.v,
   Instance/Coq/Monoid/Free.v and Construction/Free/Quiver.v all take. *)
Definition FreeMod : Sets ⟶ RMod R :=
  LeftAdjointFunctorFromUniversalArrows (RMod_Forget R)
    free_module_universal_arrow.

Definition free_module_adjunction : FreeMod ⊣ RMod_Forget R :=
  AdjunctionFromUniversalArrows (RMod_Forget R) free_module_universal_arrow.

(** The free functor's object part is the formal-sum module,
    definitionally. *)
Example FreeMod_obj (X : Sets) : FreeMod X = FreeModObject X := eq_refl.

(** The universal arrow is the basis insertion on the nose:
    [universal_arrow_from_UMP] stores the supplied morphism as the second
    projection of the comma object it builds, so no proof is involved. *)
Example free_module_arrow_is_insert (X : Sets) :
  @arrow _ _ X (RMod_Forget R) (free_module_universal_arrow X) = fv_insert X
  := eq_refl.

(** ** The unit is the basis insertion

    [unit] is DERIVED in Theory/Adjunction.v (it is the transpose of the
    identity), not a field, so what it computes to has to be checked.  It
    is [fmap[U] id ∘ arrow], and [fmap[RMod_Forget R] id] is the identity
    setoid map, so the unit is [fv_insert] itself. *)

Definition free_module_unit (X : Sets)
  : X ~{Sets}~> RMod_Forget R (FreeMod X) :=
  @Category.Theory.Adjunction.unit _ _ _ _ free_module_adjunction X.

Example free_module_unit_is_insert (X : Sets) (x : carrier X) :
  free_module_unit X x = fv_insert X x := eq_refl.

Example free_module_unit_is_generator (X : Sets) (x : carrier X) :
  free_module_unit X x = @fv_gen R X x := eq_refl.

(** ** The counit evaluates a formal linear combination

    The counit is the OTHER transpose, and it does not compute: it is
    [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows] is
    [Qed]-opaque, so no [eq_refl] is available on this side and none is
    claimed.  What is available — and is the content — is that it agrees
    with evaluation up to [≈]. *)

Definition free_module_counit (W : RMod R)
  : FreeMod (RMod_Forget R W) ~{RMod R}~> W :=
  @Category.Theory.Adjunction.counit _ _ _ _ free_module_adjunction W.

Lemma free_module_counit_generator (W : RMod R)
  (m : carrier (RMod_Forget R W)) :
  cmon_map (rm_hom (free_module_counit W)) (fv_gen m) ≈ m.
Proof.
  exact (@to_adj_counit _ _ _ _ free_module_adjunction W m).
Qed.

Theorem free_module_counit_evaluates (W : RMod R)
  (t : @FVTerm R (RMod_Forget R W)) :
  cmon_map (rm_hom (free_module_counit W)) t
    ≈ fv_eval (@id Sets (RMod_Forget R W)) t.
Proof.
  apply (fv_extend_unique W (@id Sets (RMod_Forget R W))
           (free_module_counit W)).
  intro m; exact (free_module_counit_generator W m).
Qed.

(** ** The free functor relabels basis vectors

    Riehl's "functoriality on maps of generating sets".
    [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by universal
    factorization, not by a formula, so what the functor does to a
    generator has to be proved. *)
Lemma free_module_fmap_generators {X Y : Sets} (u : X ~{Sets}~> Y)
  (x : carrier X) :
  cmon_map (rm_hom (fmap[FreeMod] u)) (fv_gen x) ≈ fv_gen (u x).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (free_module_universal_arrow X)
              (@arrow _ _ Y (RMod_Forget R)
                 (free_module_universal_arrow Y) ∘ u)) x).
Qed.

(** ** The adjunction bijection, and its two naturality clauses

    Mac Lane §IV.1 presents the free construction as the bijection

        RMod(FreeMod X, W)  ≅  Sets(X, U W)

    natural in X and in W, "each verified separately".  The forward
    transpose is restriction to the basis, and it IS the adjunction's own
    ⌊−⌋ — [free_module_transpose_is_adj] records that by [eq_refl] — so
    the two clauses below, proved in the free module's own vocabulary,
    are the class's fields and not weaker statements about some other
    map. *)

Definition fv_transpose {X : Sets} {W : RMod R}
  (g : FreeMod X ~{RMod R}~> W) : X ~{Sets}~> RMod_Forget R W :=
  fmap[RMod_Forget R] g ∘ fv_insert X.

Example free_module_transpose_is_adj {X : Sets} {W : RMod R}
  (g : FreeMod X ~{RMod R}~> W) :
  to (@adj _ _ _ _ free_module_adjunction X W) g = fv_transpose g := eq_refl.

(** Restriction to the basis is a bijection: the inverse is linear
    extension.  Both round trips are [≈] statements about morphisms, and
    the first of them is [reflexivity] at every generator. *)

Lemma fv_transpose_extend {X : Sets} {W : RMod R}
  (h : X ~{Sets}~> RMod_Forget R W) : fv_transpose (fv_extend h) ≈ h.
Proof. intro x; simpl; reflexivity. Qed.

Lemma fv_extend_transpose {X : Sets} {W : RMod R}
  (g : FreeMod X ~{RMod R}~> W) : fv_extend (fv_transpose g) ≈ g.
Proof.
  intro t; simpl.
  symmetry; apply (fv_extend_unique W (fv_transpose g) g).
  intro x; simpl; reflexivity.
Qed.

(** *** Naturality in the generating set

    For u : X ~> Y in [Sets], restricting to the basis after
    precomposing with the relabelling [fmap[FreeMod] u] is the same as
    restricting and then precomposing with u.  The proof evaluates both
    sides at a generator and uses [free_module_fmap_generators]; it does
    not cite the adjunction. *)
Theorem free_module_naturality_in_set {X Y : Sets} {W : RMod R}
  (g : FreeMod Y ~{RMod R}~> W) (u : X ~{Sets}~> Y) :
  fv_transpose (g ∘ fmap[FreeMod] u) ≈ fv_transpose g ∘ u.
Proof.
  intro x; simpl.
  exact (proper_morphism (cmon_map (rm_hom g)) _ _
           (free_module_fmap_generators u x)).
Qed.

(** *** Naturality in the target module

    For k : W ~> W' linear, restricting to the basis after postcomposing
    with k is the same as restricting and then postcomposing with the
    underlying function of k.  Both sides are the same composite of
    underlying functions, so this is [reflexivity] pointwise. *)
Theorem free_module_naturality_in_module {X : Sets} {W W' : RMod R}
  (k : W ~{RMod R}~> W') (g : FreeMod X ~{RMod R}~> W) :
  fv_transpose (k ∘ g) ≈ fmap[RMod_Forget R] k ∘ fv_transpose g.
Proof. intro x; simpl; reflexivity. Qed.

(** The two theorems just proved ARE the adjunction's naturality fields
    at this adjunction: the statements are convertible, so these are the
    clauses Mac Lane asks for and not restatements about a different
    map. *)
Example free_module_naturality_in_set_is_to_adj_nat_l
  {X Y : Sets} {W : RMod R} (g : FreeMod Y ~{RMod R}~> W)
  (u : X ~{Sets}~> Y) :
  (to (@adj _ _ _ _ free_module_adjunction X W) (g ∘ fmap[FreeMod] u)
     ≈ to (@adj _ _ _ _ free_module_adjunction Y W) g ∘ u)
  = (fv_transpose (g ∘ fmap[FreeMod] u) ≈ fv_transpose g ∘ u) := eq_refl.

Example free_module_naturality_in_module_is_to_adj_nat_r
  {X : Sets} {W W' : RMod R} (k : W ~{RMod R}~> W')
  (g : FreeMod X ~{RMod R}~> W) :
  (to (@adj _ _ _ _ free_module_adjunction X W') (k ∘ g)
     ≈ fmap[RMod_Forget R] k ∘ to (@adj _ _ _ _ free_module_adjunction X W) g)
  = (fv_transpose (k ∘ g) ≈ fmap[RMod_Forget R] k ∘ fv_transpose g) := eq_refl.

(** ** The triangle identities

    Both are instances of Theory/Adjunction.v's derived corollaries; they
    are named here because they are what makes the unit/counit
    presentation of this adjunction usable. *)

Corollary free_module_triangle_left (X : Sets) :
  free_module_counit (FreeMod X) ∘ fmap[FreeMod] (free_module_unit X)
    ≈ @id (RMod R) (FreeMod X).
Proof. exact (@counit_fmap_unit _ _ _ _ free_module_adjunction X). Qed.

Corollary free_module_triangle_right (W : RMod R) :
  fmap[RMod_Forget R] (free_module_counit W)
    ∘ free_module_unit (RMod_Forget R W)
    ≈ @id Sets (RMod_Forget R W).
Proof. exact (@fmap_counit_unit _ _ _ _ free_module_adjunction W). Qed.

End FreeModuleAdjunction.

Arguments free_module_universal_arrow {R} X.
Arguments fv_transpose {R X W} g.
Arguments free_module_fmap_generators {R X Y} u x.

(** ** Every element is a finite linear combination of basis vectors

    The classical description of the free module — "finitely supported
    K-valued functions on X" — has two halves.  The half that does not
    need a decider on X is proved here: every formal expression is
    [fv_eq] to a sum r₁·e_{x₁} + … + rₙ·e_{xₙ} indexed by a list of
    scalar/generator pairs.  The other half, that the list is unique up
    to rearrangement and combination of like terms, is exactly what a
    decider buys and is NOT proved.

    The three list operations are defined here rather than imported so
    that this file takes no dependency on [Coq.Lists.List]; [list],
    [nil] and [cons] are [Coq.Init.Datatypes]'. *)

Section NormalForm.

Context (R : RingObject).
Context (X : SetoidObject).

Definition fv_pair : Type :=
  (carrier (rig_setoid (ring_rig R)) * carrier X)%type.

Fixpoint fv_lc (l : list fv_pair) : @FVTerm R X :=
  match l with
  | nil       => fv_zero
  | cons p l' => fv_plus (fv_smul (fst p) (fv_gen (snd p))) (fv_lc l')
  end.

Fixpoint fv_app (l l' : list fv_pair) : list fv_pair :=
  match l with
  | nil       => l'
  | cons p l0 => cons p (fv_app l0 l')
  end.

Fixpoint fv_negate (l : list fv_pair) : list fv_pair :=
  match l with
  | nil       => nil
  | cons p l0 => cons (ring_neg R (fst p), snd p) (fv_negate l0)
  end.

Fixpoint fv_scale (r : carrier (rig_setoid (ring_rig R)))
         (l : list fv_pair) : list fv_pair :=
  match l with
  | nil       => nil
  | cons p l0 => cons (rig_mul (ring_rig R) r (fst p), snd p) (fv_scale r l0)
  end.

Lemma fv_lc_app (l l' : list fv_pair) :
  fv_eq (fv_lc (fv_app l l')) (fv_plus (fv_lc l) (fv_lc l')).
Proof.
  induction l as [|p l IHl]; simpl.
  - exact (fe_sym (fe_zero_l _)).
  - exact (fe_trans (fe_plus (fv_refl _) IHl) (fe_sym (fe_assoc _ _ _))).
Qed.

(* Negating a combination negates each coefficient. *)
Lemma fv_lc_negate (l : list fv_pair) :
  fv_eq (fv_lc (fv_negate l)) (fv_neg (fv_lc l)).
Proof.
  induction l as [|p l IHl]; simpl.
  - exact (fe_sym (ab_neg_zero (FreeModObject X))).
  - refine (fe_trans (fe_plus (rm_smul_neg_l (FreeModObject X) _ _) IHl) _).
    exact (fe_sym (ab_neg_plus (FreeModObject X) _ _)).
Qed.

(* Scaling a combination scales each coefficient. *)
Lemma fv_lc_scale (r : carrier (rig_setoid (ring_rig R))) (l : list fv_pair) :
  fv_eq (fv_lc (fv_scale r l)) (fv_smul r (fv_lc l)).
Proof.
  induction l as [|p l IHl]; simpl.
  - exact (fe_sym (rm_smul_zero_r (FreeModObject X) r)).
  - exact (fe_trans (fe_plus (fe_smul_assoc _ _ _) IHl)
             (fe_sym (fe_smul_distr_l _ _ _))).
Qed.

Theorem fv_normal_form (t : @FVTerm R X) :
  ∃ l : list fv_pair, fv_eq t (fv_lc l).
Proof.
  induction t as [ x | | t1 IHt1 t2 IHt2 | t IHt | r t IHt ].
  - exists (cons (rig_one (ring_rig R), x) nil); simpl.
    refine (fe_trans (fe_sym (fe_zero_l _)) _).
    refine (fe_trans (fe_comm _ _) _).
    exact (fe_plus (fe_sym (fe_smul_one _)) (fv_refl _)).
  - exists nil; exact (fv_refl _).
  - destruct IHt1 as [l1 H1], IHt2 as [l2 H2].
    exists (fv_app l1 l2).
    exact (fe_trans (fe_plus H1 H2) (fe_sym (fv_lc_app l1 l2))).
  - destruct IHt as [l Hl].
    exists (fv_negate l).
    exact (fe_trans (fe_neg Hl) (fe_sym (fv_lc_negate l))).
  - destruct IHt as [l Hl].
    exists (fv_scale r l).
    exact (fe_trans (fe_smul (reflexivity r) Hl) (fe_sym (fv_lc_scale r l))).
Qed.

End NormalForm.

Arguments fv_lc {R X} l.
Arguments fv_normal_form {R X} t.

(** ** Non-degeneracy

    A free module on the empty or a one-element generating set would
    demonstrate nothing about the quotient: what has to be ruled out is
    that the generated congruence collapses the construction.  Three
    separations are proved, and they cost different things.  The only
    tool used is that any function on generators extends, so evaluating
    the extension separates formal expressions. *)

Section NonDegeneracy.

Context (R : RingObject).
Context (X : SetoidObject).

(** *** Distinct scalars give distinct multiples of a basis vector

    This needs NO hypothesis on X and none on R beyond what
    [RingObject] already carries.  Map every generator to 1 in R viewed
    as a module over itself (Instance/Mod.v's [Ring_RMod]); then r·e_x
    evaluates to r·1 ≈ r. *)

Definition fv_probe_one : X ~{Sets}~> RMod_Forget R (Ring_RMod R).
Proof.
  unshelve refine {| morphism := fun _ => rig_one (ring_rig R) |}.
  intros a b _; exact (reflexivity (rig_one (ring_rig R))).
Defined.

Theorem free_module_scalars_faithful
  (r s : carrier (rig_setoid (ring_rig R))) (x : carrier X) :
  fv_eq (@fv_smul R X r (fv_gen x)) (fv_smul s (fv_gen x)) → r ≈ s.
Proof.
  intro He.
  pose proof (fv_eval_respects (Ring_RMod R) fv_probe_one _ _ He) as Hv.
  simpl in Hv.
  rewrite (rig_mul_one_r (ring_rig R) r) in Hv.
  rewrite (rig_mul_one_r (ring_rig R) s) in Hv.
  exact Hv.
Qed.

(** *** Distinct generators give distinct basis vectors

    This one is NOT hypothesis-free.  Why the hypotheses are not an
    artifact of the proof is ARGUED here, not proved — neither converse
    is machine-checked below, and the tree's precedent for exactly this
    shape of claim ([arrow_mul_respects_forces_UIP],
    [skeleton0_skeletal_forces_UIP], [faithful_QuiverElements_implies_UIP])
    is deliberately not followed.  The argument: separating two
    generators means exhibiting a module in which they go to different
    places; the only maps into a module that a bare setoid supplies are
    the ones that can be WRITTEN, and the characteristic function of a
    point cannot be written without a decision procedure for that
    setoid's [≈].  For the other hypothesis the argument is shorter and
    firmer — a ring in which 1 ≈ 0 is the zero ring, over which every
    module is trivial, so [fv_gen x] and [fv_gen y] are [fv_eq] for ALL
    x and y and the conclusion does not hold at all — but it too is left
    as an argument rather than a refutation. *)

Context (Xdec : ∀ x y : carrier X, (x ≈ y) + ((x ≈ y) → False)).
Context (Rnz : rig_one (ring_rig R) ≈ rig_zero (ring_rig R) → False).

(* The characteristic function of the generator [x], with values in R
   viewed as a module over itself. *)
Definition fv_probe_at (x : carrier X)
  : X ~{Sets}~> RMod_Forget R (Ring_RMod R).
Proof using R X Xdec.
  unshelve refine {|
    morphism := fun z => match Xdec x z with
                         | inl _ => rig_one (ring_rig R)
                         | inr _ => rig_zero (ring_rig R)
                         end
  |}.
  intros z z' Hz; simpl.
  destruct (Xdec x z) as [Hxz|Hxz], (Xdec x z') as [Hxz'|Hxz'].
  - reflexivity.
  - destruct (Hxz' (transitivity Hxz Hz)).
  - destruct (Hxz (transitivity Hxz' (symmetry Hz))).
  - reflexivity.
Defined.

Theorem free_module_basis_injective (x y : carrier X) :
  fv_eq (@fv_gen R X x) (fv_gen y) → x ≈ y.
Proof using R X Xdec Rnz.
  intro He.
  destruct (Xdec x y) as [Hxy|Hxy]; [ exact Hxy | ].
  destruct Rnz.
  pose proof (fv_eval_respects (Ring_RMod R) (fv_probe_at x) _ _ He) as Hv.
  simpl in Hv.
  destruct (Xdec x x) as [_|Hxx]; [ | destruct (Hxx (reflexivity x)) ].
  destruct (Xdec x y) as [Hc|_]; [ destruct (Hxy Hc) | ].
  exact Hv.
Qed.

(** *** The basis is linearly independent

    The statement a reader of §III.1 actually wants, at two generators:
    if r·e_x + s·e_y vanishes and x ≉ y then both coefficients vanish.
    Only the decider is spent — NOT [Rnz], which is why this is the
    stronger of the two separations: over the zero ring it degenerates to
    a truth rather than to a falsehood.  The proof evaluates through the
    characteristic function of one generator, which sends the other's
    basis vector to 0. *)
Theorem free_module_two_independent (x y : carrier X)
  (Hxy : (x ≈ y) → False) (r s : carrier (rig_setoid (ring_rig R))) :
  fv_eq (fv_plus (@fv_smul R X r (fv_gen x)) (fv_smul s (fv_gen y))) fv_zero →
  (r ≈ rig_zero (ring_rig R)) * (s ≈ rig_zero (ring_rig R)).
(* [Rnz] is deliberately absent: this separation does not need it, and
   naming the section variables keeps that visible in the signature. *)
Proof using R X Xdec.
  intro He.
  split.
  - pose proof (fv_eval_respects (Ring_RMod R) (fv_probe_at x) _ _ He) as Hv.
    simpl in Hv.
    destruct (Xdec x x) as [_|Hxx]; [ | destruct (Hxx (reflexivity x)) ].
    destruct (Xdec x y) as [Hc|_]; [ destruct (Hxy Hc) | ].
    (* r·1 + s·0 ≈ 0 *)
    rewrite (rig_mul_one_r (ring_rig R) r) in Hv.
    rewrite (rig_mul_zero_r (ring_rig R) s) in Hv.
    rewrite (rig_add_zero_r (ring_rig R) r) in Hv.
    exact Hv.
  - pose proof (fv_eval_respects (Ring_RMod R) (fv_probe_at y) _ _ He) as Hv.
    simpl in Hv.
    destruct (Xdec y x) as [Hc|_];
      [ destruct (Hxy (symmetry Hc)) | ].
    destruct (Xdec y y) as [_|Hyy]; [ | destruct (Hyy (reflexivity y)) ].
    (* r·0 + s·1 ≈ 0 *)
    rewrite (rig_mul_zero_r (ring_rig R) r) in Hv.
    rewrite (rig_mul_one_r (ring_rig R) s) in Hv.
    rewrite (rig_add_zero_l (ring_rig R) s) in Hv.
    exact Hv.
Qed.

End NonDegeneracy.

Arguments fv_probe_one {R} X.
Arguments free_module_scalars_faithful {R X} r s x _.
Arguments free_module_basis_injective {R X} Xdec Rnz x y _.
Arguments free_module_two_independent {R X} Xdec x y Hxy r s _.

(** ** A computing witness over the integers

    ℤ is the cheapest ring in tree whose action computes
    (Theory/Algebra/Rig.v's [Int_Ring], Instance/Mod.v's [Int_RMod]).
    The generating setoid has TWO elements, so the free module is not the
    ring itself and the linear extension has something to do. *)

Definition TwoGens : SetoidObject := {|
  carrier   := bool;
  is_setoid := {| equiv := eq; setoid_equiv := eq_equivalence |}
|}.

Definition two_gens_dec :
  ∀ x y : carrier TwoGens, (x ≈ y) + ((x ≈ y) → False).
Proof.
  intros x y; simpl.
  destruct x, y.
  - exact (inl eq_refl).
  - right; intro H; discriminate.
  - right; intro H; discriminate.
  - exact (inl eq_refl).
Defined.

(* The two generators are distinct.  Like [two_gens_dec] this is a fact
   about the generating setoid alone — nothing about any ring enters —
   so it is stated here rather than beside either scalar witness, and
   Instance/Vect/Free.v consumes this one rather than restating it. *)
Lemma two_gens_distinct : @equiv _ (is_setoid TwoGens) true false → False.
Proof. intro H; discriminate H. Qed.

(* [FVTerm]'s two index arguments are implicit, and in a statement with
   no expected type — an [fv_eq] between two constructor applications —
   the elaborator has nothing to propagate them from.  These are
   NOTATIONS, not definitions, so each unfolds to the constructor itself
   and nothing below is stated about a different term. *)
Local Notation zgen  := (@fv_gen Int_Ring TwoGens).
Local Notation zsmul := (@fv_smul Int_Ring TwoGens).
Local Notation zplus := (@fv_plus Int_Ring TwoGens).

(* Two integers, read off the two generators. *)
Definition int_probe : TwoGens ~{Sets}~> RMod_Forget Int_Ring Int_RMod.
Proof.
  unshelve refine {| morphism := fun b : carrier TwoGens => if b then 3%Z else 5%Z |}.
  (* [all:] because the respectfulness field of a map out of a setoid
     whose ≈ is Leibniz [=] may be discharged by instance resolution
     before a goal is ever opened; the carriers here are at [Set]
     either way, so nothing is pinned that was not already. *)
  all: intros x y H; simpl in H; subst y; reflexivity.
Defined.

(* The linear extension computes: 2·e_true + e_false ↦ 2·3 + 5 = 11. *)
Example int_free_extend_computes :
  fv_eval int_probe
    (zplus (zsmul 2%Z (zgen true)) (zgen false)) = 11%Z := eq_refl.

Example int_free_extend_generator_true :
  fv_eval int_probe (zgen true) = 3%Z := eq_refl.

(* ℤ is not the zero ring, so the basis insertion is injective on this
   generating setoid. *)
Lemma int_one_neq_zero :
  rig_one (ring_rig Int_Ring) ≈ rig_zero (ring_rig Int_Ring) → False.
Proof. intro H; compute in H; discriminate H. Qed.

Theorem int_free_basis_distinct :
  fv_eq (zgen true) (zgen false) → False.
Proof.
  intro He.
  pose proof (free_module_basis_injective two_gens_dec int_one_neq_zero
                true false He) as Hb.
  compute in Hb; discriminate Hb.
Qed.

(* The basis is linearly independent over ℤ too.  This one spends the
   decider but NOT [int_one_neq_zero] — the ℚ reading of the same
   theorem is [free_vect_basis_independent]. *)
Theorem int_free_two_independent
  (r s : carrier (rig_setoid (ring_rig Int_Ring))) :
  fv_eq (zplus (zsmul r (zgen true)) (zsmul s (zgen false)))
        (@fv_zero Int_Ring TwoGens) →
  ((@equiv _ (rig_setoid (ring_rig Int_Ring)) r (rig_zero (ring_rig Int_Ring))) *
   (@equiv _ (rig_setoid (ring_rig Int_Ring)) s (rig_zero (ring_rig Int_Ring))))%type.
Proof.
  exact (@free_module_two_independent Int_Ring TwoGens two_gens_dec
           true false two_gens_distinct r s).
Qed.

(* ...and the scalars embed, with no decidability spent. *)
Theorem int_free_scalars_distinct :
  fv_eq (zsmul 2%Z (zgen true)) (zsmul 3%Z (zgen true)) → False.
Proof.
  intro He.
  pose proof (@free_module_scalars_faithful Int_Ring TwoGens 2%Z 3%Z true He)
    as Hz.
  compute in Hz; discriminate Hz.
Qed.
