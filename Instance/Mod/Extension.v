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
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Rng.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

Open Scope category_scope.

#[local] Obligation Tactic := idtac.

(** * Extension of scalars, as the left adjoint of restriction

    nLab:      https://ncatlab.org/nlab/show/extension+of+scalars
    nLab:      https://ncatlab.org/nlab/show/restriction+of+scalars
    Wikipedia: https://en.wikipedia.org/wiki/Extension_of_scalars
    Book: Riehl, Category Theory in Context, Dover 2016, Sec. 4.1,
          Example 4.1.10 (extension of scalars S (x)_R - is left adjoint
          to restriction of scalars along a ring homomorphism
          phi : R -> S) — riehl:4.1:example10

    THE MATHEMATICS.  A ring homomorphism phi : R -> S makes every
    S-module into an R-module by letting r act as phi r does; that is
    Instance/Rng/Mod.v's [Restrict phi : RMod S ⟶ RMod R], Mac Lane's
    construction 8, and it is the RIGHT adjoint here.  Its left adjoint
    carries an R-module M to S (x)_R M, the tensor product of M with S
    regarded as a module over R, with S acting on the left-hand factor.
    The unit is m |-> 1 (x) m, and the universal property is that an
    R-linear map M -> Restrict phi N extends uniquely to an S-linear map
    S (x)_R M -> N.  Riehl's Example 4.1.10 is exactly that adjunction.

    WHAT IS DELIVERED

    * [ExtBase phi] — S as a left R-module along phi, which is literally
      [RestrictObj phi (Ring_RMod S)]: nothing new is constructed, and
      [ExtBase_smul] records by [eq_refl] that r acts as phi r times.

    * [ExtBimodule phi : Bimodule S R] — S as an (S, R)-bimodule, left
      multiplication for S and right multiplication through phi for R.
      NO hypothesis is needed for it; every clause is a rig law with one
      of [rig_map_add], [rig_map_mul], [rig_map_one] spliced in.

    * [ExtendObj phi Hc M : RModObject S] — the extension of scalars.
      Its abelian group IS the one Instance/Mod/Tensor.v's
      [TensorMod (ExtBase phi) M] already carries; only the action is
      new, and it is built as a family of MEDIATORS ([ext_act]), which
      is what makes respectfulness in the module argument free and
      leaves only respectfulness in the SCALAR argument to prove
      ([ext_smul_scalar], one [tensor_hom_ext]).

    * [extend_unit], [extend_med], [extend_med_commutes],
      [extend_med_unique], [extend_universal] (the ∃!),
      [extend_universal_arrow], [ExtendScalars] and
      [extend_restrict_adjunction] — the universal arrow, the functor
      and the adjunction.

    * [extend_ring_iso : S (x)_R R ≅ S] in [RMod S], which pins the
      object rather than merely exhibiting elements of it, and
      [extend_gen_nonzero], the non-degeneracy that follows from it.

    THE HYPOTHESIS, AND EXACTLY WHERE IT IS SPENT.  Riehl states the
    adjunction for arbitrary rings.  What is proved here carries one
    extra hypothesis, [CentralImage phi]: every phi r commutes with
    every element of S.  It is a VISIBLE argument of every constant that
    needs it, and it is discharged by commutativity of S through
    [central_of_commutative].

    The restriction is NOT Riehl's and is NOT inherent to the theorem.
    It is the price of reusing Instance/Mod/Tensor.v, whose tensor
    product is of two LEFT modules over ONE ring, balanced at
    (r . v) (x) w = v (x) (r . w).  The classical S (x)_R M balances at
    (s . phi r) (x) m = s (x) (r . m), with S a RIGHT R-module; the
    donor's balancing instead reads (phi r . s) (x) m = s (x) (r . m).
    Centrality is exactly the statement that those two agree, and
    [ext_actions_agree_iff] says so: the bimodule's right R-action and
    the left R-action the donor balances against are the same map if and
    only if the image of phi is central.  That theorem is CHEAP — the
    two sides are one equation read in its two orders, so both
    directions are [symmetry] — and its value is that it names where the
    restriction lives, not that it is deep.  A genuine (S, R)-bimodule
    tensor product would remove the hypothesis; none is built here, and
    none exists in tree.

    Centrality is used five times, and nowhere else:

    1. [ext_scale]'s [rbl_smul_l] obligation, to see that
       x |-> s . x is R-linear on [ExtBase] — s (phi r x) = phi r (s x).
       This is what makes the S-action well defined on the quotient.
    2. [extend_restrict_action]'s [mt_smul] case, through
       phi (r r') ≈ phi (r' r), which centrality supplies and which is
       false for a general phi.  (This is also the commutator identity
       that the donor's [rbl_commutator] forces on the object; it is
       supplied here, not assumed separately.)
    3. [ext_bil]'s [rbl_smul_r] obligation, to move phi r past x in
       x . g (r . m).  The [rbl_smul_l] clause beside it needs NOTHING.
    4. [ext_lmul]'s linearity obligation, to see that left
       multiplication by s is a map of the restricted R-modules.
    5. [extend_ring_iso]'s second obligation, in the same step.

    WHAT IS REUSED AND WHAT IS REBUILT.  The tensor product itself is
    reused entirely: [TensorMod], [tensor_med], [tensor_med_fun],
    [tensor_med_respects], [tensor_hom_ext], [tensor_balanced],
    [tensor_zero_l], [tensor_zero_r] and the constructors of [mt_eq].  No
    inductive is declared in this file and no induction over [mt_eq] is
    performed; the ONE induction anywhere below is over the TERM, in
    [extend_restrict_action].  What had to be built is the S-module
    structure, which the donor cannot supply — [TensorMod V V'] is an
    object of [RMod R], and an object of [RMod S] on the same carrier is
    a different record.  The action is nevertheless not built by hand:
    each s gives a bilinear map and hence a mediator, so the fold
    [tensor_med_fun] is what computes, and the four module laws are
    four applications of [tensor_hom_ext].

    [ExtendScalars] AND THE FUNCTOR THE PLUMBING PRODUCES.  They are the
    same constant: [ExtendScalars] is DEFINED as
    [LeftAdjointFunctorFromUniversalArrows (Restrict phi) …], the route
    Instance/Mod/Free.v, Instance/Grp/Free.v and
    Construction/Free/Quiver.v all take, so there are not two functors to
    compare.  What that costs is that the ARROW action is defined by
    universal factorization rather than by a formula, which is why
    [extend_fmap_gen] — the statement that it relabels the right-hand
    factor — is a theorem and holds up to ≈ only.

    STRENGTHS, MEASURED STRICT-FIRST.  Strict ([eq_refl]): the object
    part of the functor ([ExtendScalars_obj]); the universal arrow IS
    [extend_unit] ([extend_arrow_is_unit]); the unit of the adjunction
    computes to 1 (x) m ([extend_adj_unit_computes], and
    [extend_unit_computes] before it); the action on an elementary
    tensor ([ext_smul_gen]); the mediator on an elementary tensor
    ([extend_med_gen]); and over Q the factorization COMPUTES —
    (1/2) (x) 3 = 3/2 ([QZ_med_computes]).

    Two boundaries are NOT strict, and both are guarded by a [Fail] that
    names the constants, with an instrument check beside them:

    * the R-action the tensor carries and the R-action obtained by
      restricting the S-action along phi ([ext_probe_action_strict]).
      The cause discriminates: the first is the CONSTRUCTOR
      [mt_smul r], the second the FOLD [tensor_med_fun (ext_scale
      (phi r))].  They agree up to ≈ by [extend_restrict_action], and
      [ext_restrict_id] packages that agreement as a morphism.
    * the counit ([ext_probe_counit_strict]), because it is
      [unique_obj] of the [Qed]-opaque [ump_universal_arrows] — the same
      cause Instance/Mod/Free.v records for its own counit.  Contrast
      the unit, which does compute.

    UNIVERSES.  Read off the constraint blocks (with [Set Printing
    Universes]), [ExtendScalars] and [extend_restrict_adjunction] both
    IDENTIFY all six universes of the two rings: u = u0 = u1 = u2 = u3 =
    u4.  That is the DONOR's doing and not this file's, and it was
    measured rather than guessed: [obj[Rng]] rejects
    [RingObject@{ra ra rc}] under [Constraint ra < rc] with "Cannot
    enforce rc = ra", while [RingObject@{ra rb rc}] with [ra < rb] is
    perfectly formable on its own — so it is the CATEGORY [Rng], not the
    record [RingObject], that collapses them, and any statement about a
    morphism of [Rng] inherits the collapse.  That measurement is NOT
    guarded by a [Fail] in this file: pinning it would require writing a
    universe instance on [RingObject], whose arity is a portability
    hazard across the supported Coq/Rocq versions, and the cost of a
    guard that silently stops discriminating is higher than the cost of
    saying plainly that this one is measured.  Every concrete ring in
    tree satisfies the collapse, so no witness is affected.

    NOT DELIVERED, and none of it is claimed.

    * No (S, R)-bimodule tensor product, hence no version of the theorem
      for a phi whose image is not central.  Nothing here says the
      object built is the classical S (x)_R M when R is not commutative;
      Instance/Mod/Tensor.v's own header records that its object gains
      relations over a non-commutative ring, and that collapse is
      inherited, unmeasured.
    * No coefficient uniqueness, no normal form, hence no decision
      procedure for equality in the extension (inherited from the
      donor's presentation).
    * No base-change composition: nothing relates [ExtendScalars] along
      psi ◯ phi to the composite of the two extensions, and no unit
      [ExtendScalars id ≅ Id] is proved.
    * No right adjoint of [Restrict] (the coextension Hom_R(S, -)), so
      restriction is not exhibited here as both a left and a right
      adjoint.
    * No right-module reading: [RestrictR] exists in the donor, but no
      extension of scalars for right modules is built.
    * No relation to Instance/Rng/Mod.v's [ModIndexed], [ModTotal] or
      [ModFibred]; in particular nothing is said about opfibredness.
    * No naturality of [extend_ring_iso] in R, S or phi, and no
      projection formula, flatness or exactness statement.
    * The Q witness pins the OBJECT ([QZ_iso]) but no statement is made
      about Q (x)_Z M for a general abelian group M.

    All 97 constants of this file — 53 named plus 44 [Program]
    obligations — report "Closed under the global context". *)

(** ** The hypothesis: the image of phi is central in S *)

Definition CentralImage {R S : RingObject} (phi : R ~{Rng}~> S) : Type :=
  ∀ (r : carrier (rig_setoid (ring_rig R)))
    (s : carrier (rig_setoid (ring_rig S))),
    rig_mul (ring_rig S) (rig_map phi r) s
      ≈ rig_mul (ring_rig S) s (rig_map phi r).

Lemma central_of_commutative {R S : RingObject} (phi : R ~{Rng}~> S)
  (Hcomm : ∀ a b : carrier (rig_setoid (ring_rig S)),
      rig_mul (ring_rig S) a b ≈ rig_mul (ring_rig S) b a) :
  CentralImage phi.
Proof. intros r s; apply Hcomm. Qed.

Section ExtensionOfScalars.

Context {R S : RingObject}.
Context (phi : R ~{Rng}~> S).

(** S as a left R-module along phi. *)
Definition ExtBase : RModObject R := RestrictObj phi (Ring_RMod S).

Example ExtBase_smul (r : carrier (rig_setoid (ring_rig R)))
  (x : carrier (rig_setoid (ring_rig S))) :
  rm_smul ExtBase r x = rig_mul (ring_rig S) (rig_map phi r) x := eq_refl.

(** S as an (S, R)-bimodule along phi: left multiplication for S, right
    multiplication through phi for R.  NO hypothesis is needed for this;
    every clause is a rig law with [rig_map_add], [rig_map_mul] or
    [rig_map_one] spliced in. *)
Program Definition ExtBimodule : Bimodule S R := {|
  bm_left  := Ring_RMod S;
  bm_rsmul := fun s r => rig_mul (ring_rig S) s (rig_map phi r)
|}.
Next Obligation.
  intros s s' Hs r r' Hr; simpl.
  now rewrite Hs, Hr.
Qed.
Next Obligation. intros s t r; simpl; apply (rig_distr_r (ring_rig S)). Qed.
Next Obligation.
  intros s r r'; simpl.
  rewrite (rig_map_add phi r r').
  apply (rig_distr_l (ring_rig S)).
Qed.
Next Obligation.
  intros s r r'; simpl.
  rewrite (rig_map_mul phi r r').
  symmetry; apply (rig_mul_assoc (ring_rig S)).
Qed.
Next Obligation.
  intros s; simpl.
  rewrite (rig_map_one phi).
  apply (rig_mul_one_r (ring_rig S)).
Qed.
Next Obligation. intros r s t; simpl; apply (rig_mul_assoc (ring_rig S)). Qed.

(** Where the restriction lives, stated as an equivalence rather than
    asserted: the bimodule's RIGHT R-action and the LEFT R-action that
    the tensor product of Instance/Mod/Tensor.v balances against are the
    same map exactly when the image of phi is central. *)
Theorem ext_actions_agree_iff :
  (∀ (r : carrier (rig_setoid (ring_rig R)))
     (s : carrier (rig_setoid (ring_rig S))),
      bm_rsmul ExtBimodule s r ≈ rm_smul ExtBase r s) ↔ CentralImage phi.
Proof.
  split.
  - intros H r s; symmetry; exact (H r s).
  - intros H r s; symmetry; exact (H r s).
Qed.

Context (Hc : CentralImage phi).

Section OneModule.

Context (M : RMod R).

(** The elementary tensor x (x) m, with the two module arguments named
    so that [mt_gen]'s implicit arguments are determined. *)
Definition ext_gen (x : carrier (rig_setoid (ring_rig S)))
  (m : carrier (cmon_setoid M))
  : carrier (cmon_setoid (TensorMod ExtBase M)) := @mt_gen R ExtBase M x m.

(** The scaling bilinear map. *)
Program Definition ext_scale (s : carrier (rig_setoid (ring_rig S)))
  : RBilinear ExtBase M (TensorMod ExtBase M) := {|
  rbl_map := fun x m => mt_gen (rig_mul (ring_rig S) s x) m
|}.
Next Obligation.
  intros s x x' Hx m m' Hm; simpl.
  apply mte_gen; [ | exact Hm ].
  now rewrite Hx.
Qed.
Next Obligation.
  intros s x y m; simpl.
  refine (mte_trans _ (mte_add_l _ _ _)).
  apply mte_gen; [ | reflexivity ].
  apply (rig_distr_l (ring_rig S)).
Qed.
Next Obligation.
  intros s x m n; simpl.
  exact (mte_add_r _ _ _).
Qed.
Next Obligation.
  intros s r x m; simpl.
  refine (mte_trans _ (mte_sym (mte_act_l r _ m))).
  apply mte_gen; [ | reflexivity ].
  (* s * (phi r * x)  =  phi r * (s * x): the ONLY use of centrality
     in the construction of the S-action. *)
  rewrite <- (rig_mul_assoc (ring_rig S) s (rig_map phi r) x).
  rewrite <- (Hc r s).
  apply (rig_mul_assoc (ring_rig S)).
Qed.
Next Obligation.
  intros s r x m; simpl.
  exact (mte_sym (mte_act_r r _ m)).
Qed.

Definition ext_act (s : carrier (rig_setoid (ring_rig S)))
  : TensorMod ExtBase M ~{RMod R}~> TensorMod ExtBase M :=
  tensor_med (ext_scale s).

Definition ext_smul (s : carrier (rig_setoid (ring_rig S)))
  (t : carrier (cmon_setoid (TensorMod ExtBase M)))
  : carrier (cmon_setoid (TensorMod ExtBase M)) :=
  tensor_med_fun (ext_scale s) t.

Example ext_smul_is_act (s : carrier (rig_setoid (ring_rig S)))
  (t : carrier (cmon_setoid (TensorMod ExtBase M))) :
  ext_smul s t = cmon_map (rm_hom (ext_act s)) t := eq_refl.

Example ext_smul_gen (s x : carrier (rig_setoid (ring_rig S)))
  (m : carrier (cmon_setoid M)) :
  ext_smul s (ext_gen x m) = ext_gen (rig_mul (ring_rig S) s x) m := eq_refl.

(** Respectfulness of the action in the SCALAR argument is the one clause
    that is not free: it is [tensor_hom_ext] between two mediators. *)
Lemma ext_smul_scalar (s s' : carrier (rig_setoid (ring_rig S)))
  (Hs : s ≈ s') (t : carrier (cmon_setoid (TensorMod ExtBase M))) :
  ext_smul s t ≈ ext_smul s' t.
Proof.
  refine (tensor_hom_ext (ext_act s) (ext_act s') _ t).
  intros x m; simpl.
  apply mte_gen; [ now rewrite Hs | reflexivity ].
Qed.

Lemma ext_smul_respects : Proper (equiv ==> equiv ==> equiv) ext_smul.
Proof.
  intros s s' Hs t t' Ht.
  transitivity (ext_smul s t').
  - exact (tensor_med_respects (ext_scale s) t t' Ht).
  - exact (ext_smul_scalar s s' Hs t').
Qed.

(** The extension of scalars: the same abelian group as the tensor
    product over R, with S acting on the left-hand factor. *)
Program Definition ExtendObj : RModObject S := {|
  rm_ab   := rm_ab (TensorMod ExtBase M);
  rm_smul := ext_smul
|}.
Next Obligation. exact ext_smul_respects. Qed.
Next Obligation. intros s t u; reflexivity. Qed.
Next Obligation.
  intros s s' t.
  refine (tensor_hom_ext (ext_act (rig_add (ring_rig S) s s'))
            (rmod_hom_add (ext_act s) (ext_act s')) _ t).
  intros x m; simpl.
  refine (mte_trans _ (mte_add_l _ _ _)).
  apply mte_gen; [ | reflexivity ].
  apply (rig_distr_r (ring_rig S)).
Qed.
Next Obligation.
  intros s s' t.
  refine (tensor_hom_ext (ext_act (rig_mul (ring_rig S) s s'))
            (rmod_hom_compose (ext_act s) (ext_act s')) _ t).
  intros x m; simpl.
  apply mte_gen; [ | reflexivity ].
  apply (rig_mul_assoc (ring_rig S)).
Qed.
Next Obligation.
  intros t.
  refine (tensor_hom_ext (ext_act (rig_one (ring_rig S)))
            (@rmod_hom_id R (TensorMod ExtBase M)) _ t).
  intros x m; simpl.
  apply mte_gen; [ | reflexivity ].
  apply (rig_mul_one_l (ring_rig S)).
Qed.

(** ** The R-action underlying the S-action

    Restricting [ExtendObj] back along phi returns the R-module structure
    the tensor product already carries.  The proof is one induction over
    the term, with the scalar generalized; the last case is the only one
    with content, and it is where centrality is spent for the second
    time — through phi (r r') ≈ phi (r' r), which centrality supplies and
    which is FALSE for a general phi. *)
Lemma extend_restrict_action (r : carrier (rig_setoid (ring_rig R)))
  (t : carrier (cmon_setoid (TensorMod ExtBase M))) :
  rm_smul (TensorMod ExtBase M) r t ≈ ext_smul (rig_map phi r) t.
Proof.
  revert r.
  induction t as [ x m | | t1 IH1 t2 IH2 | t1 IH1 | r' t1 IH1 ]; intro r.
  - exact (mte_act_l r x m).
  - exact (rm_smul_zero_r (TensorMod ExtBase M) r).
  - transitivity (cmon_plus (TensorMod ExtBase M)
                    (rm_smul (TensorMod ExtBase M) r t1)
                    (rm_smul (TensorMod ExtBase M) r t2)).
    + apply rm_smul_distr_l.
    + exact (cmon_plus_respects (TensorMod ExtBase M) _ _ (IH1 r) _ _ (IH2 r)).
  - transitivity (ab_neg (TensorMod ExtBase M)
                    (rm_smul (TensorMod ExtBase M) r t1)).
    + apply rm_smul_neg_r.
    + exact (ab_neg_respects (TensorMod ExtBase M) _ _ (IH1 r)).
  - rewrite (rm_map_smul (ext_act (rig_map phi r)) r' t1).
    rewrite <- (IH1 r).
    rewrite <- !(rm_smul_assoc (TensorMod ExtBase M)).
    transitivity (ext_smul (rig_map phi (rig_mul (ring_rig R) r r')) t1);
      [ apply IH1 | ].
    transitivity (ext_smul (rig_map phi (rig_mul (ring_rig R) r' r)) t1).
    + apply ext_smul_scalar.
      rewrite !(rig_map_mul phi).
      apply Hc.
    + symmetry; apply IH1.
Qed.

(** ** The unit: m goes to 1 (x) m *)

Program Definition extend_unit
  : M ~{RMod R}~> RestrictObj phi ExtendObj := {|
  rm_hom := {| cmon_map :=
                 {| morphism := fun m => ext_gen (rig_one (ring_rig S)) m |} |}
|}.
Next Obligation.
  first [ (intros m m' Hm; exact (mte_gen (reflexivity _) Hm))
        | (intros m n; exact (mte_add_r _ _ _))
        | (intros r m; exact (mte_sym (tensor_balanced r _ m)))
        | (exact (tensor_zero_r _)) ].
Qed.
Next Obligation.
  first [ (intros m m' Hm; exact (mte_gen (reflexivity _) Hm))
        | (intros m n; exact (mte_add_r _ _ _))
        | (intros r m; exact (mte_sym (tensor_balanced r _ m)))
        | (exact (tensor_zero_r _)) ].
Qed.
Next Obligation.
  first [ (intros m m' Hm; exact (mte_gen (reflexivity _) Hm))
        | (intros m n; exact (mte_add_r _ _ _))
        | (intros r m; exact (mte_sym (tensor_balanced r _ m)))
        | (exact (tensor_zero_r _)) ].
Qed.
Next Obligation.
  first [ (intros m m' Hm; exact (mte_gen (reflexivity _) Hm))
        | (intros m n; exact (mte_add_r _ _ _))
        | (intros r m; exact (mte_sym (tensor_balanced r _ m)))
        | (exact (tensor_zero_r _)) ].
Qed.

Example extend_unit_computes (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom extend_unit) m = ext_gen (rig_one (ring_rig S)) m := eq_refl.

(** Every elementary tensor is the unit scaled: x (x) m = x . (1 (x) m).
    This is what makes the unit generate, and it is used three times
    below. *)
Lemma ext_gen_scale (x : carrier (rig_setoid (ring_rig S)))
  (m : carrier (cmon_setoid M)) :
  ext_gen x m ≈ ext_smul x (ext_gen (rig_one (ring_rig S)) m).
Proof.
  apply mte_gen; [ symmetry; apply (rig_mul_one_r (ring_rig S))
                 | reflexivity ].
Qed.

(** The identity on elements, read as a map from the tensor's own
    R-module structure to the restriction of the S-module structure.  Its
    one obligation IS [extend_restrict_action]. *)
Program Definition ext_restrict_id
  : TensorMod ExtBase M ~{RMod R}~> RestrictObj phi ExtendObj := {|
  rm_hom := {| cmon_map := {| morphism := fun t => t |} |}
|}.
Next Obligation.
  first [ (intros t t' Ht; exact Ht)
        | (intros r t; exact (extend_restrict_action r t))
        | reflexivity ].
Qed.
Next Obligation.
  first [ (intros t t' Ht; exact Ht)
        | (intros r t; exact (extend_restrict_action r t))
        | reflexivity ].
Qed.
Next Obligation.
  first [ (intros t t' Ht; exact Ht)
        | (intros r t; exact (extend_restrict_action r t))
        | reflexivity ].
Qed.
Next Obligation.
  first [ (intros t t' Ht; exact Ht)
        | (intros r t; exact (extend_restrict_action r t))
        | reflexivity ].
Qed.

(** ** The universal property *)

Section Mediator.

Context (N : RModObject S).
Context (g : M ~{RMod R}~> RestrictObj phi N).

(** (x, m) |-> x . g m, R-bilinear into the restriction of N.  Only the
    last clause needs centrality; the R-action on the FIRST variable
    passes through phi with nothing spent. *)
Program Definition ext_bil : RBilinear ExtBase M (RestrictObj phi N) := {|
  rbl_map := fun x m => rm_smul N x (cmon_map (rm_hom g) m)
|}.
Next Obligation.
  intros x x' Hx m m' Hm; simpl.
  now rewrite Hx, Hm.
Qed.
Next Obligation.
  intros x y m; simpl.
  apply (rm_smul_distr_r N).
Qed.
Next Obligation.
  intros x m n; simpl.
  rewrite (cmon_map_plus (rm_hom g) m n).
  apply (rm_smul_distr_l N).
Qed.
Next Obligation.
  intros r x m; simpl.
  apply (rm_smul_assoc N).
Qed.
Next Obligation.
  intros r x m; simpl.
  rewrite (rm_map_smul g r m); simpl.
  rewrite <- !(rm_smul_assoc N).
  apply rm_smul_respects; [ symmetry; apply Hc | reflexivity ].
Qed.

Definition ext_med_R : TensorMod ExtBase M ~{RMod R}~> RestrictObj phi N :=
  tensor_med ext_bil.

(** Left multiplication by s, as a map of the restricted R-modules: the
    third place centrality is spent. *)
Program Definition ext_lmul (s : carrier (rig_setoid (ring_rig S)))
  : RestrictObj phi N ~{RMod R}~> RestrictObj phi N := {|
  rm_hom := {| cmon_map := {| morphism := fun y => rm_smul N s y |} |}
|}.
Next Obligation.
  first [ (intros s y y' Hy; simpl; now rewrite Hy)
        | (intros s y z; simpl; apply (rm_smul_distr_l N))
        | (intros s r y; simpl;
           rewrite <- !(rm_smul_assoc N);
           apply rm_smul_respects; [ symmetry; apply Hc | reflexivity ])
        | (intros s; simpl; apply (rm_smul_zero_r N)) ].
Qed.
Next Obligation.
  first [ (intros s y y' Hy; simpl; now rewrite Hy)
        | (intros s y z; simpl; apply (rm_smul_distr_l N))
        | (intros s r y; simpl;
           rewrite <- !(rm_smul_assoc N);
           apply rm_smul_respects; [ symmetry; apply Hc | reflexivity ])
        | (intros s; simpl; apply (rm_smul_zero_r N)) ].
Qed.
Next Obligation.
  first [ (intros s y y' Hy; simpl; now rewrite Hy)
        | (intros s y z; simpl; apply (rm_smul_distr_l N))
        | (intros s r y; simpl;
           rewrite <- !(rm_smul_assoc N);
           apply rm_smul_respects; [ symmetry; apply Hc | reflexivity ])
        | (intros s; simpl; apply (rm_smul_zero_r N)) ].
Qed.
Next Obligation.
  first [ (intros s y y' Hy; simpl; now rewrite Hy)
        | (intros s y z; simpl; apply (rm_smul_distr_l N))
        | (intros s r y; simpl;
           rewrite <- !(rm_smul_assoc N);
           apply rm_smul_respects; [ symmetry; apply Hc | reflexivity ])
        | (intros s; simpl; apply (rm_smul_zero_r N)) ].
Qed.

(** The factorization, as a map of S-modules. *)
Program Definition extend_med : ExtendObj ~{RMod S}~> N := {|
  rm_hom := rm_hom ext_med_R
|}.
Next Obligation.
  intros s t.
  refine (tensor_hom_ext (rmod_hom_compose ext_med_R (ext_act s))
            (rmod_hom_compose (ext_lmul s) ext_med_R) _ t).
  intros x m; simpl.
  apply (rm_smul_assoc N).
Qed.

Lemma extend_med_commutes (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom extend_med) (ext_gen (rig_one (ring_rig S)) m)
    ≈ cmon_map (rm_hom g) m.
Proof. exact (rm_smul_one N (cmon_map (rm_hom g) m)). Qed.

(** An S-linear map out of the extension IS an R-linear map out of the
    tensor product, by [extend_restrict_action]. *)
Program Definition ext_forget (h : ExtendObj ~{RMod S}~> N)
  : TensorMod ExtBase M ~{RMod R}~> RestrictObj phi N := {|
  rm_hom := rm_hom h
|}.
Next Obligation.
  intros h r t.
  rewrite (extend_restrict_action r t).
  exact (rm_map_smul h (rig_map phi r) t).
Qed.

Lemma extend_med_unique (h : ExtendObj ~{RMod S}~> N)
  (Hh : ∀ m, cmon_map (rm_hom h) (ext_gen (rig_one (ring_rig S)) m)
               ≈ cmon_map (rm_hom g) m)
  (t : carrier (cmon_setoid (TensorMod ExtBase M))) :
  cmon_map (rm_hom h) t ≈ cmon_map (rm_hom extend_med) t.
Proof.
  refine (tensor_hom_ext (ext_forget h) ext_med_R _ t).
  intros x m; simpl.
  transitivity (rm_smul N x
                  (cmon_map (rm_hom h) (ext_gen (rig_one (ring_rig S)) m))).
  - rewrite <- (rm_map_smul h x (ext_gen (rig_one (ring_rig S)) m)).
    apply proper_morphism, ext_gen_scale.
  - now rewrite (Hh m).
Qed.

End Mediator.

Theorem extend_universal (N : RModObject S)
  (g : M ~{RMod R}~> Restrict phi N) :
  ∃! h : ExtendObj ~{RMod S}~> N,
    g ≈ fmap[Restrict phi] h ∘ extend_unit.
Proof.
  unshelve eexists.
  - exact (extend_med N g).
  - intro m; simpl; symmetry; exact (extend_med_commutes N g m).
  - intros h Hh t; simpl.
    symmetry.
    apply (extend_med_unique N g h).
    intro m; symmetry; exact (Hh m).
Qed.

Definition extend_universal_arrow : UniversalArrow M (Restrict phi) :=
  universal_arrow_from_UMP M (Restrict phi) ExtendObj extend_unit
    extend_universal.

End OneModule.

(** ** The functor and the adjunction *)

Definition ExtendScalars : RMod R ⟶ RMod S :=
  LeftAdjointFunctorFromUniversalArrows (Restrict phi) extend_universal_arrow.

Definition extend_restrict_adjunction : ExtendScalars ⊣ Restrict phi :=
  AdjunctionFromUniversalArrows (Restrict phi) extend_universal_arrow.

(** ** Strengths, measured strict-first *)

(** The functor produced by the adjunction plumbing IS [ExtendObj] on
    objects, on the nose. *)
Example ExtendScalars_obj (M : RMod R) :
  fobj[ExtendScalars] M = ExtendObj M := eq_refl.

Example extend_arrow_is_unit (M : RMod R) :
  @arrow _ _ M (Restrict phi) (extend_universal_arrow M) = extend_unit M
  := eq_refl.

Definition extend_adj_unit (M : RMod R)
  : M ~{RMod R}~> Restrict phi (ExtendScalars M) :=
  @Category.Theory.Adjunction.unit _ _ _ _ extend_restrict_adjunction M.

Example extend_adj_unit_computes (M : RMod R) (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (extend_adj_unit M)) m
    = ext_gen M (rig_one (ring_rig S)) m := eq_refl.

Example extend_med_gen (M : RMod R) (N : RModObject S)
  (g : M ~{RMod R}~> RestrictObj phi N)
  (x : carrier (rig_setoid (ring_rig S))) (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (extend_med M N g)) (ext_gen M x m)
    = rm_smul N x (cmon_map (rm_hom g) m) := eq_refl.

(** The counit does NOT compute: it is [unique_obj] of the [Qed]-opaque
    [ump_universal_arrows].  What holds is agreement up to [≈]. *)
Definition extend_adj_counit (N : RMod S)
  : ExtendScalars (Restrict phi N) ~{RMod S}~> N :=
  @Category.Theory.Adjunction.counit _ _ _ _ extend_restrict_adjunction N.

Lemma extend_counit_unit (N : RMod S) (m : carrier (cmon_setoid N)) :
  cmon_map (rm_hom (extend_adj_counit N))
    (ext_gen (Restrict phi N) (rig_one (ring_rig S)) m) ≈ m.
Proof.
  exact (@to_adj_counit _ _ _ _ extend_restrict_adjunction N m).
Qed.

Lemma extend_counit_gen (N : RMod S)
  (x : carrier (rig_setoid (ring_rig S))) (m : carrier (cmon_setoid N)) :
  cmon_map (rm_hom (extend_adj_counit N))
    (ext_gen (Restrict phi N) x m) ≈ rm_smul N x m.
Proof.
  rewrite (ext_gen_scale (Restrict phi N) x m).
  rewrite (rm_map_smul (extend_adj_counit N) x
             (ext_gen (Restrict phi N) (rig_one (ring_rig S)) m)).
  now rewrite (extend_counit_unit N m).
Qed.

(** The arrow action relabels the right-hand factor.  It is defined by
    universal factorization, not by a formula, so this is a theorem. *)
Lemma extend_fmap_gen {M M' : RMod R} (u : M ~{RMod R}~> M')
  (x : carrier (rig_setoid (ring_rig S))) (m : carrier (cmon_setoid M)) :
  cmon_map (rm_hom (fmap[ExtendScalars] u)) (ext_gen M x m)
    ≈ ext_gen M' x (cmon_map (rm_hom u) m).
Proof.
  rewrite (ext_gen_scale M x m).
  rewrite (rm_map_smul (fmap[ExtendScalars] u) x
             (ext_gen M (rig_one (ring_rig S)) m)).
  rewrite <- (unique_property
                (ump_universal_arrows (extend_universal_arrow M)
                   (@arrow _ _ M' (Restrict phi)
                      (extend_universal_arrow M') ∘ u)) m).
  symmetry; apply ext_gen_scale.
Qed.

(** ** The extension of the rank-one free module

    S (x)_R R is S again — the cheapest non-degenerate computation, and
    the one that pins the object rather than merely exhibiting elements
    of it.  Both legs are built here; the round trip on the tensor is
    [tensor_hom_ext] plus the balanced law, and centrality is spent once
    more, in exactly the step that moves phi r past x. *)

Program Definition ext_ring_hom
  : Ring_RMod R ~{RMod R}~> RestrictObj phi (Ring_RMod S) := {|
  rm_hom := {| cmon_map := {| morphism := rig_map phi |} |}
|}.
Next Obligation.
  first [ (intros a b Hab; now rewrite Hab)
        | (intros a b; apply (rig_map_add phi))
        | (intros a b; apply (rig_map_mul phi))
        | (apply (rig_map_zero phi)) ].
Qed.
Next Obligation.
  first [ (intros a b Hab; now rewrite Hab)
        | (intros a b; apply (rig_map_add phi))
        | (intros a b; apply (rig_map_mul phi))
        | (apply (rig_map_zero phi)) ].
Qed.
Next Obligation.
  first [ (intros a b Hab; now rewrite Hab)
        | (intros a b; apply (rig_map_add phi))
        | (intros a b; apply (rig_map_mul phi))
        | (apply (rig_map_zero phi)) ].
Qed.

Definition extend_ring_to
  : ExtendObj (Ring_RMod R) ~{RMod S}~> Ring_RMod S :=
  extend_med (Ring_RMod R) (Ring_RMod S) ext_ring_hom.

Program Definition extend_ring_from
  : Ring_RMod S ~{RMod S}~> ExtendObj (Ring_RMod R) := {|
  rm_hom := {| cmon_map := {| morphism :=
    fun s => ext_gen (Ring_RMod R) s (rig_one (ring_rig R)) |} |}
|}.
Next Obligation.
  first
    [ (intros s s' Hs; simpl; apply mte_gen; [ exact Hs | reflexivity ])
    | (exact (@tensor_zero_l R ExtBase (Ring_RMod R) (rig_one (ring_rig R))))
    | (intros s t;
       exact (@mte_add_l R ExtBase (Ring_RMod R) s t (rig_one (ring_rig R))))
    | (intros s t; reflexivity) ].
Qed.
Next Obligation.
  first
    [ (intros s s' Hs; simpl; apply mte_gen; [ exact Hs | reflexivity ])
    | (exact (@tensor_zero_l R ExtBase (Ring_RMod R) (rig_one (ring_rig R))))
    | (intros s t;
       exact (@mte_add_l R ExtBase (Ring_RMod R) s t (rig_one (ring_rig R))))
    | (intros s t; reflexivity) ].
Qed.
Next Obligation.
  first
    [ (intros s s' Hs; simpl; apply mte_gen; [ exact Hs | reflexivity ])
    | (exact (@tensor_zero_l R ExtBase (Ring_RMod R) (rig_one (ring_rig R))))
    | (intros s t;
       exact (@mte_add_l R ExtBase (Ring_RMod R) s t (rig_one (ring_rig R))))
    | (intros s t; reflexivity) ].
Qed.
Next Obligation.
  first
    [ (intros s s' Hs; simpl; apply mte_gen; [ exact Hs | reflexivity ])
    | (exact (@tensor_zero_l R ExtBase (Ring_RMod R) (rig_one (ring_rig R))))
    | (intros s t;
       exact (@mte_add_l R ExtBase (Ring_RMod R) s t (rig_one (ring_rig R))))
    | (intros s t; reflexivity) ].
Qed.

Program Definition extend_ring_iso
  : @Isomorphism (RMod S) (ExtendObj (Ring_RMod R)) (Ring_RMod S) := {|
  to   := extend_ring_to;
  from := extend_ring_from
|}.
Next Obligation.
  intro s; simpl.
  rewrite (rig_map_one phi); apply (rig_mul_one_r (ring_rig S)).
Qed.

Next Obligation.
  intro t.
  refine (tensor_hom_ext
            (ext_forget (Ring_RMod R) (ExtendObj (Ring_RMod R))
               (rmod_hom_compose extend_ring_from extend_ring_to))
            (ext_restrict_id (Ring_RMod R)) _ t).
  intros x r; simpl.
  refine (mte_trans (@mte_gen R ExtBase (Ring_RMod R) _ _ _ _
                       (symmetry (Hc r x)) (reflexivity _)) _).
  refine (mte_trans (@tensor_balanced R ExtBase (Ring_RMod R) r x
                       (rig_one (ring_rig R))) _).
  exact (@mte_gen R ExtBase (Ring_RMod R) _ _ _ _
           (reflexivity x) (rig_mul_one_r (ring_rig R) r)).
Qed.

(** Non-degeneracy, by mapping OUT: no induction over [mt_eq] could give
    a negative.  If S is not the zero ring then 1 (x) 1 is not 0. *)
Lemma extend_gen_nonzero
  (Hnz : rig_one (ring_rig S) ≈ rig_zero (ring_rig S) → False) :
  ext_gen (Ring_RMod R) (rig_one (ring_rig S)) (rig_one (ring_rig R))
    ≈ cmon_zero (ExtendObj (Ring_RMod R)) → False.
Proof.
  intro He.
  apply Hnz.
  pose proof (proper_morphism (cmon_map (rm_hom extend_ring_to)) _ _ He)
    as Hz.
  simpl in Hz.
  rewrite <- Hz.
  rewrite (rig_map_one phi).
  symmetry; apply (rig_mul_one_r (ring_rig S)).
Qed.

End ExtensionOfScalars.

(** ** Guarded negatives

    Two conversion boundaries, each with an instrument check beside them.
    The positive controls are the [eq_refl] Examples above, which name
    the same constants. *)

(* Instrument check: a scope-free false equation, so that a [Fail] that
   passes for the wrong reason would show up here first. *)
Fail Definition ext_probe_instrument : true = false := eq_refl.

(* The R-action the tensor product carries and the R-action obtained by
   restricting the S-action along phi agree only up to [≈]
   ([extend_restrict_action]); the first is [mt_smul r], the second is
   the fold [tensor_med_fun (ext_scale (phi r))]. *)
Fail Example ext_probe_action_strict {R S : RingObject}
  (phi : R ~{Rng}~> S) (Hc : CentralImage phi) (M : RMod R)
  (r : carrier (rig_setoid (ring_rig R)))
  (t : carrier (cmon_setoid (TensorMod (ExtBase phi) M))) :
  rm_smul (TensorMod (ExtBase phi) M) r t
    = rm_smul (RestrictObj phi (ExtendObj phi Hc M)) r t := eq_refl.

(* The counit does not compute: it is [unique_obj] of the [Qed]-opaque
   [ump_universal_arrows], so nothing reduces through it.  Compare the
   UNIT, which does compute — [extend_adj_unit_computes] above. *)
Fail Example ext_probe_counit_strict {R S : RingObject}
  (phi : R ~{Rng}~> S) (Hc : CentralImage phi) (N : RMod S)
  (m : carrier (cmon_setoid N)) :
  cmon_map (rm_hom (extend_adj_counit phi Hc N))
    (ext_gen phi (Restrict phi N) (rig_one (ring_rig S)) m) = m := eq_refl.

(** ** A witness: extension of scalars along the inclusion of Z into Q

    [Coq.QArith.QArith] is required HERE rather than at the head of the
    file: importing it shadows [Setoid]'s [equiv], which every [Proper]
    statement above mentions by name.  Instance/Rng.v takes the same
    precaution, writing [Setoid.equiv] in the one record it builds after
    the import. *)

Require Import Coq.QArith.QArith.

Lemma Q_central : CentralImage ZtoQ.
Proof.
  apply central_of_commutative.
  intros a b; simpl; apply Qmult_comm.
Qed.

Lemma Q_one_neq_zero :
  rig_one (ring_rig Q_Ring) ≈ rig_zero (ring_rig Q_Ring) → False.
Proof. intro H; vm_compute in H; discriminate. Qed.

Definition QZ_extend : RModObject Q_Ring :=
  ExtendObj ZtoQ Q_central (Ring_RMod Int_Ring).

Example QZ_is_ExtendScalars :
  fobj[ExtendScalars ZtoQ Q_central] (Ring_RMod Int_Ring) = QZ_extend
  := eq_refl.

(** Q (x)_Z Z is Q, as an isomorphism of Q-modules. *)
Definition QZ_iso
  : @Isomorphism (RMod Q_Ring) QZ_extend (Ring_RMod Q_Ring) :=
  extend_ring_iso ZtoQ Q_central.

(** The factorization COMPUTES: (1/2) (x) 3 goes to 3/2. *)
Example QZ_med_computes :
  cmon_map (rm_hom (extend_ring_to ZtoQ Q_central))
    (ext_gen ZtoQ (Ring_RMod Int_Ring) (1 # 2) 3%Z) = (3 # 2)%Q := eq_refl.

(** The quotient does not collapse, and the unit does not collapse: both
    are proved by mapping OUT into Q, since no induction over the
    quotienting relation could produce a negative. *)
Lemma QZ_gen_nonzero :
  ext_gen ZtoQ (Ring_RMod Int_Ring)
    (rig_one (ring_rig Q_Ring)) (rig_one (ring_rig Int_Ring))
    ≈ cmon_zero QZ_extend → False.
Proof. exact (extend_gen_nonzero ZtoQ Q_central Q_one_neq_zero). Qed.

Lemma QZ_unit_separates :
  cmon_map (rm_hom (extend_unit ZtoQ Q_central (Ring_RMod Int_Ring))) 1%Z
    ≈ cmon_map (rm_hom (extend_unit ZtoQ Q_central (Ring_RMod Int_Ring))) 2%Z
    → False.
Proof.
  intro He.
  pose proof (proper_morphism
                (cmon_map (rm_hom (extend_ring_to ZtoQ Q_central))) _ _ He)
    as Hq.
  vm_compute in Hq; discriminate.
Qed.
