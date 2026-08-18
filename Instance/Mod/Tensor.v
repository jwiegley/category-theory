Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Universal.Element.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(* The global obligation tactic is [cat_simpl], which runs wide proof
   searches on module obligations and has already introduced the
   parameters by the time an obligation is opened.  Switched off here,
   the Instance/Mod.v:104 idiom, so every obligation starts with an
   explicit [intros]. *)
#[local] Obligation Tactic := idtac.

(** * The tensor product of modules, as a universal element

    nLab:      https://ncatlab.org/nlab/show/tensor+product+of+modules
    nLab:      https://ncatlab.org/nlab/show/universal+element
    Wikipedia: https://en.wikipedia.org/wiki/Tensor_product_of_modules
    Book: Mac Lane, Categories for the Working Mathematician, 2nd ed.,
          GTM 5, §III.1, printed p. 58 (the tensor product presented as a
          universal element of the functor of bilinear maps) —
          maclane:III.1:construction6
    Book: Riehl, Category Theory in Context, Dover 2016, §2.3, printed
          p. 58 (the same content as a representation: the functor
          carrying W to the set of bilinear maps V × V' → W is
          represented by V ⊗ V') — riehl:2.3:example8

    WHY THE TENSOR PRODUCT IS THE EXAMPLE.  A bilinear map is not a
    linear map, so the assignment W ↦ Bilin(V, V'; W) is visibly not a
    hom-functor; and yet it is naturally isomorphic to one.  That is the
    entire content of the tensor product, and it is why Mac Lane reaches
    for it immediately after defining universal elements: the reader
    already knows the object, and what the definition supplies is the
    reason it exists.  Bilinearity is a two-variable notion, linearity a
    one-variable notion, and V ⊗ V' is the object that converts the first
    into the second — "the" object, because a representing object is
    determined up to a unique compatible isomorphism, which is what makes
    the familiar identifications (associativity, commutativity, the unit
    law) theorems rather than choices.  The historical order was the
    reverse: the construction is nineteenth-century, the universal
    property is Bourbaki-era, and the observation that the property is
    what matters is exactly the observation category theory contributed.

    Elementwise the object is a quotient of formal expressions, and every
    calculation with tensors is a calculation modulo bilinearity.  That
    is what is built below: the carrier [MTerm] is a plain inductive of
    formal expressions, the equality [mt_eq] is an inductive relation
    closing under exactly the abelian-group laws, the four module laws,
    additivity in each variable, the two scalar rules on generators,
    congruence for each former, saturation under the point setoids and
    under the ring's own [≈], and symmetry and transitivity.
    Reflexivity is derived ([mt_refl]).  The presentation is
    Instance/Ab/Tensor.v's, extended with a scalar former in the manner
    of Instance/Mod/Free.v's [FVTerm], and it is a setoid quotient in the
    style of Instance/Sets/Coend.v: no free module is quotiented a second
    time.  That choice is discussed under GENERALITY below.

    WHAT IS DELIVERED

    * [RBilinear V V' W] — R-bilinear maps of modules: additive in each
      variable and commuting with the scalar action in each variable.
      Respectfulness is a field; preservation of zero and of negation in
      each variable is not, being derivable exactly as for the group case
      ([rbl_zero_l], [rbl_zero_r], [rbl_neg_l], [rbl_neg_r] below are
      those four derivations).

    * [Bilin V V' : RMod R ⟶ Sets] — the bilinear-maps FUNCTOR, not
      merely the type.  Its object part is the setoid of bilinear maps
      compared pointwise; its arrow part is postcomposition.  Both
      functor laws — identity and composition — hold pointwise by
      [reflexivity].  The other two obligations, [fmap_respects] and
      respectfulness of the arrow map itself, do not: each consumes its
      hypothesis.

    * [TensorMod V V' : RModObject R] with the canonical bilinear map
      [tensor_gen : RBilinear V V' (TensorMod V V')] — the generator
      former itself.

    * THE HEADLINE: [tensor_universal_element], the statement that
      ⟨V ⊗ V', ⊗⟩ is a universal element of [Bilin V V'] in the sense of
      Theory/Universal/Element.v's [AUniversalElement], together with
      [tensor_UniversalElement], the same data in the bundled
      [UniversalElement] form (Mac Lane's pair ⟨r, e⟩).  Unique
      factorization is then the class's own [aue_universal]; it is
      restated elementwise as [tensor_factor] with
      [tensor_factor_commutes] and [tensor_factor_unique], for readers
      who want the equation f = f̄ ∘ ⊗ without unfolding the class.
      Nothing is reproved there: [tensor_factor_is_med] records by
      [eq_refl] that the mediator extracted from the class IS the
      fixpoint below.

    * The engine room: [tensor_med] (the factorizing homomorphism, whose
      underlying map is the [Fixpoint] [tensor_med_fun], so it COMPUTES —
      and so preservation of zero, of addition and of the action all hold
      by [reflexivity]), [tensor_hom_ext] (two homomorphisms out of the
      tensor agreeing on generators agree — the uniqueness half, and the
      workhorse), and the elementary consequences [tensor_zero_l],
      [tensor_zero_r], [tensor_neg_l], [tensor_neg_r], [tensor_balanced].

    * Non-degeneracy over ℤ, which is where the construction is measured
      rather than described: [Int_mul_bilinear] is multiplication as a
      bilinear map, the factorization of it through the tensor COMPUTES
      on closed generators ([int_tensor_med_computes], by [eq_refl]),
      two generators that ought to differ do ([int_tensor_gen_distinct]:
      1 ⊗ 1 is not 2 ⊗ 1), the canonical map is not the zero map
      ([int_tensor_gen_nonzero]: 1 ⊗ 1 is not 0), and
      the whole object is pinned: [Int_tensor_iso] is an isomorphism
      ℤ ⊗_ℤ ℤ ≅ ℤ in [RMod Int_Ring].

    GENERALITY, AND WHAT IT COSTS

    The construction and the universal property are stated over an
    ARBITRARY [RingObject], and commutativity of R is a hypothesis of none
    of them: it appears in neither [RBilinear], [TensorMod], [Bilin],
    [tensor_med], [tensor_hom_ext] nor [tensor_universal_element].  (The
    one general statement below that DOES assume it is
    [rbl_commutator_from_commutativity], which exists precisely to
    measure what the absence is worth, and the ℤ witnesses of course use
    ℤ's own commutativity.)

    That is a fact about the statements, and it must not be read as a
    strengthening of the classical theorem.  It is the opposite: the
    universal property holds unconditionally because the object
    constructed here satisfies MORE relations over a non-commutative ring
    than a reader of the commutative case would expect — the identity
    below is imposed on it, and nothing here says the resulting object is
    the classical one.  What gains relations is the OBJECT; the
    universal property itself is unchanged.  How much is thereby lost is
    NOT measured: see the deferral below, which records that the identity
    is never exhibited as non-vacuous at a concrete ring.

    Precisely — and this is proved, not argued: [rbl_commutator] shows
    that for EVERY R-bilinear β into ANY R-module,

        (r·s) · β(v, v')  ≈  (s·r) · β(v, v')

    since both sides equal β(r·v, s·v'); written with subtraction
    ([rbl_commutator_annihilates]) that says every commutator of R
    annihilates the image of every bilinear map.  [tensor_commutator] is
    that identity at the tensor itself, where it says that V ⊗ V' is a
    module on which the commutators of R act as zero.  Over a commutative
    ring the identity is empty, and that is also proved rather than
    asserted: [rbl_commutator_from_commutativity] derives the same
    conclusion from commutativity of R ALONE, using no bilinearity and no
    module beyond respectfulness of the action.  So the correct reading is
    that the hypothesis is absent because the object absorbs it, not that
    the theorem has been strengthened by removing it.
    Over a commutative ring — hence over a field, which is the case both
    catalogued sources state — [TensorMod] is the classical tensor
    product of modules, presented by exactly the classical generators and
    relations.

    ONE DEFERRAL BELONGS HERE.  The collapse is proved as a general
    identity and is NOT witnessed at a concrete non-commutative ring,
    because the tree has none: the only closed [RingObject]s in it are
    [Int_Ring], [Q_Ring], [Zero_Ring], [F2_Ring], [FracRing] and
    [CRingOb], all commutative; [EndRig] produces a rig rather than a
    ring, and no endomorphism-RING construction exists.  (Two
    [RingObject]-valued FORMERS also exist — [Ring_op] and [field_ring] —
    but neither can introduce non-commutativity from these inputs, the
    opposite of a commutative ring being commutative and a field being
    commutative by definition.)  So no claim is made here that
    the collapse is ever strict — only that it holds, and that it is
    vacuous wherever R is commutative.  (The converse of that last
    implication is not proved and is not true as stated: over any ring
    the identity is also vacuous when the modules are trivial.)

    WHAT WAS ALREADY IN THE TREE, since issue #306 says otherwise.  The
    issue's "Current state" reads "Absent … `rg 'bilinear|Bilin'` finds
    only prose … there is no category of vector spaces or modules … no
    bilinear-map type, and no tensor-product-by-universal-property
    construction".  Measured against this file's parent, that is wrong on
    every count but the last two words: [Record Bilinear (K : AbObject)]
    is at Instance/Ab/Tensor.v:165, with [tensor_ump], [tensor_hom_ext],
    [AbTensor] and [AbTensor_Functor] beside it, and [tensor_ump] is
    CONSUMED at Construction/Enriched/Ab.v:190 — so a bilinear-map type
    and a tensor-by-universal-property already existed for abelian
    groups.  Instance/Mod.v, Instance/Ab.v and Instance/Rng.v all exist,
    and [Vct_F] is at Instance/FdVect.v:223.  Nothing of that is rebuilt
    here.  What was genuinely absent, and is what this file supplies, is
    the module-level bilinear map over an arbitrary ring, the bilinear
    functor into [Sets], the tensor object, and the universal element.

    NAME OVERLAP WITH Instance/Ab/Tensor.v, recorded rather than
    renamed.  Four names are declared in both files — [tensor_gen],
    [tensor_hom_ext], [tensor_med_fun] and [tensor_med_respects].  No
    code is shared (this file does not [Require] that one, and only the
    design pattern is borrowed), and nothing in the tree imports both, so
    nothing is shadowed today; the overlap is recorded here because it is
    a hazard for any future file that wants both.  Instance/FdVect/Tensor.v
    ([TensorSq], the diagonal square endofunctor) shares no name with
    this file at all.

    WHAT IS NOT DELIVERED

    * NOT the balanced tensor product.  For a RIGHT module V and a LEFT
      module V' over a non-commutative ring the standard object is the
      abelian group V ⊗_R V' universal among BALANCED maps
      (β(v·r, v') ≈ β(v, r·v')), which is a different universal property
      into a different category ([Ab], not [RMod R]) and would have the
      universal element living somewhere other than where V and V' do.
      Neither catalogued source states that version, and Instance/Mod.v's
      [ModR]/[Bimodule] are left untouched by this file.  Note that
      balancedness is nevertheless AVAILABLE here as a consequence:
      [tensor_balanced] proves (r·v) ⊗ v' ≈ v ⊗ (r·v') in [TensorMod],
      which is what makes the canonical map bilinear in the two-sided
      sense at all.

    * NO BIFUNCTORIALITY.  Instance/Ab/Tensor.v's [AbTensor_Functor]
      has no counterpart here: nothing below makes ⊗ a functor
      [RMod R ∏ RMod R ⟶ RMod R], and no monoidal structure on [RMod R]
      is attempted.  (Both would be [tensor_hom_ext] plus computations on
      generators, exactly as there.)

    * NO COEFFICIENT UNIQUENESS, and no basis theory.  As in
      Instance/Mod/Free.v, the presentation is by generators and
      relations, so an element of V ⊗ V' is a formal expression up to the
      congruence and NOT a normal form; nothing here proves that a tensor
      has a unique expression as a sum of simple tensors, which is false
      in general anyway.

    * NO COMPARISON WITH Instance/Ab/Tensor.v.  Over R = ℤ the two
      constructions have the same universal property, but no
      isomorphism between [AbTensor] and [TensorMod] is stated or proved
      here; the ℤ-module structure of an [AbObject] is not in the tree.

    * NO RELATION TO Instance/FdVect/Tensor.v, which despite its name is
      the diagonal square endofunctor V ↦ StdVect F (n²) of Riehl
      Ex 1.4.4(vii) and not a tensor product of two modules at all. *)

(** ** Bilinear maps *)

Section Bilinear.

Context (R : RingObject).
Context (V V' : RModObject R).

(** An R-bilinear map into an R-module W: respectful in each variable,
    additive in each variable, and commuting with the scalar action in
    each variable.  Preservation of zero and of negation in each variable
    is derived below rather than demanded, as always for maps between
    groups. *)
Record RBilinear (W : RModObject R) := {
  rbl_map : carrier (cmon_setoid V) →
            carrier (cmon_setoid V') → carrier (cmon_setoid W);

  rbl_respects : Proper (equiv ==> equiv ==> equiv) rbl_map;

  (* (v + v') ⊗ w = v ⊗ w + v' ⊗ w *)
  rbl_add_l (v v' : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
    rbl_map (cmon_plus V v v') w
      ≈ cmon_plus W (rbl_map v w) (rbl_map v' w);
  (* v ⊗ (w + w') = v ⊗ w + v ⊗ w' *)
  rbl_add_r (v : carrier (cmon_setoid V)) (w w' : carrier (cmon_setoid V')) :
    rbl_map v (cmon_plus V' w w')
      ≈ cmon_plus W (rbl_map v w) (rbl_map v w');
  (* (r·v) ⊗ w = r·(v ⊗ w) *)
  rbl_smul_l (r : carrier (rig_setoid (ring_rig R)))
             (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
    rbl_map (rm_smul V r v) w ≈ rm_smul W r (rbl_map v w);
  (* v ⊗ (r·w) = r·(v ⊗ w) *)
  rbl_smul_r (r : carrier (rig_setoid (ring_rig R)))
             (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
    rbl_map v (rm_smul V' r w) ≈ rm_smul W r (rbl_map v w)
}.

End Bilinear.

Arguments RBilinear {R} V V' W.
Arguments rbl_map {R V V' W} _ _ _.
Arguments rbl_respects {R V V' W} _.
Arguments rbl_add_l {R V V' W} _ _ _ _.
Arguments rbl_add_r {R V V' W} _ _ _ _.
Arguments rbl_smul_l {R V V' W} _ _ _ _.
Arguments rbl_smul_r {R V V' W} _ _ _ _.

#[export] Existing Instance rbl_respects.

Section BilinearFacts.

Context {R : RingObject}.
Context {V V' W : RModObject R}.
Context (β : RBilinear V V' W).

(** 0 ⊗ w ≈ 0, by cancelling [0 ⊗ w] against itself — the argument of
    Instance/Mod.v's [rm_smul_zero_l], one level up. *)
Lemma rbl_zero_l (w : carrier (cmon_setoid V')) :
  rbl_map β (cmon_zero V) w ≈ cmon_zero W.
Proof.
  apply (ab_cancel_l W (rbl_map β (cmon_zero V) w)).
  rewrite <- (rbl_add_l β (cmon_zero V) (cmon_zero V) w).
  rewrite (cmon_plus_zero_l V (cmon_zero V)).
  symmetry.
  apply (cmon_plus_zero_r W (rbl_map β (cmon_zero V) w)).
Qed.

(** v ⊗ 0 ≈ 0, dually. *)
Lemma rbl_zero_r (v : carrier (cmon_setoid V)) :
  rbl_map β v (cmon_zero V') ≈ cmon_zero W.
Proof.
  apply (ab_cancel_l W (rbl_map β v (cmon_zero V'))).
  rewrite <- (rbl_add_r β v (cmon_zero V') (cmon_zero V')).
  rewrite (cmon_plus_zero_l V' (cmon_zero V')).
  symmetry.
  apply (cmon_plus_zero_r W (rbl_map β v (cmon_zero V'))).
Qed.

(** (−v) ⊗ w ≈ −(v ⊗ w): the left-hand side IS an additive inverse of
    v ⊗ w, and Instance/Ab.v's [ab_neg_unique] says that is enough. *)
Lemma rbl_neg_l (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  rbl_map β (ab_neg V v) w ≈ ab_neg W (rbl_map β v w).
Proof.
  apply ab_neg_unique.
  rewrite <- (rbl_add_l β (ab_neg V v) v w).
  rewrite (ab_neg_left V v).
  apply rbl_zero_l.
Qed.

Lemma rbl_neg_r (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  rbl_map β v (ab_neg V' w) ≈ ab_neg W (rbl_map β v w).
Proof.
  apply ab_neg_unique.
  rewrite <- (rbl_add_r β v (ab_neg V' w) w).
  rewrite (ab_neg_left V' w).
  apply rbl_zero_r.
Qed.

(** THE COMMUTATOR IDENTITY, and the reason the construction below needs
    no commutativity hypothesis.  Both sides are β(r·v, s·w): the left by
    peeling r off the first variable and s off the second, the right by
    peeling them off in the other order.  Stated with subtraction it says
    that every commutator of R annihilates the image of every bilinear
    map ([rbl_commutator_annihilates]), and over a non-commutative ring
    that is a genuine collapse — see the header, and
    [rbl_commutator_from_commutativity] for the proof that the identity
    says nothing when R is commutative. *)
Lemma rbl_commutator (r s : carrier (rig_setoid (ring_rig R)))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  rm_smul W (rig_mul (ring_rig R) r s) (rbl_map β v w)
    ≈ rm_smul W (rig_mul (ring_rig R) s r) (rbl_map β v w).
Proof.
  transitivity (rbl_map β (rm_smul V r v) (rm_smul V' s w)).
  - rewrite (rm_smul_assoc W r s (rbl_map β v w)).
    rewrite <- (rbl_smul_r β s v w).
    symmetry; apply (rbl_smul_l β r v (rm_smul V' s w)).
  - rewrite (rm_smul_assoc W s r (rbl_map β v w)).
    rewrite <- (rbl_smul_l β r v w).
    apply (rbl_smul_r β s (rm_smul V r v) w).
Qed.

(** The same identity written with subtraction: the commutator
    r·s − s·r acts as zero on every value of β.  This is the form the
    header's word "annihilates" refers to; it needs the ambient module's
    negation, which is why it is stated here and not for rigs. *)
Lemma rbl_commutator_annihilates (r s : carrier (rig_setoid (ring_rig R)))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  rm_smul W (rig_add (ring_rig R) (rig_mul (ring_rig R) r s)
               (ring_neg R (rig_mul (ring_rig R) s r)))
    (rbl_map β v w)
    ≈ cmon_zero W.
Proof.
  rewrite (rm_smul_distr_r W _ _ (rbl_map β v w)).
  rewrite (rm_smul_neg_l W (rig_mul (ring_rig R) s r) (rbl_map β v w)).
  rewrite (rbl_commutator r s v w).
  apply (ab_neg_right W).
Qed.

End BilinearFacts.

(** The other direction, measuring what [rbl_commutator] is worth: over a
    commutative ring its conclusion follows from commutativity alone —
    no bilinear map, no additivity, nothing but respectfulness of the
    action.  So the identity is informative only where R is
    non-commutative, which is exactly where it is a collapse. *)
Lemma rbl_commutator_from_commutativity {R : RingObject}
  (Rcomm : ∀ a b, rig_mul (ring_rig R) a b ≈ rig_mul (ring_rig R) b a)
  (W : RModObject R) (r s : carrier (rig_setoid (ring_rig R)))
  (x : carrier (cmon_setoid W)) :
  rm_smul W (rig_mul (ring_rig R) r s) x
    ≈ rm_smul W (rig_mul (ring_rig R) s r) x.
Proof.
  now rewrite (Rcomm r s).
Qed.

(** ** The tensor product

    Formal expressions in the two carriers, with zero, sum, negation and
    a formal scalar action; the equality is generated by exactly the laws
    the object must satisfy.  Nothing below is proved by hand: every
    module law of [TensorMod] is a constructor of [mt_eq], and so is
    every clause of bilinearity of the canonical map. *)

Section Tensor.

Context {R : RingObject}.
Context (V V' : RModObject R).

Inductive MTerm : Type :=
  | mt_gen  : carrier (cmon_setoid V) → carrier (cmon_setoid V') → MTerm
  | mt_zero : MTerm
  | mt_plus : MTerm → MTerm → MTerm
  | mt_neg  : MTerm → MTerm
  | mt_smul : carrier (rig_setoid (ring_rig R)) → MTerm → MTerm.

(* The quotienting relation.  Congruence for each former (saturating
   under the two point setoids and under the ring's own [≈]), the
   abelian-group laws, the four module laws, additivity of the generator
   former in each variable, and the two rules that make the formal scalar
   action agree with the actions of V and of V' on a generator.
   Reflexivity is derived ([mt_refl]), keeping the induction principle
   one case shorter everywhere it is consumed. *)
Inductive mt_eq : MTerm → MTerm → Type :=
  (* congruence *)
  | mte_gen {v v' : carrier (cmon_setoid V)} {w w' : carrier (cmon_setoid V')} :
      v ≈ v' → w ≈ w' → mt_eq (mt_gen v w) (mt_gen v' w')
  | mte_plus {s s' t t'} :
      mt_eq s s' → mt_eq t t' → mt_eq (mt_plus s t) (mt_plus s' t')
  | mte_neg {s s'} : mt_eq s s' → mt_eq (mt_neg s) (mt_neg s')
  | mte_smul {r r' : carrier (rig_setoid (ring_rig R))} {s s'} :
      r ≈ r' → mt_eq s s' → mt_eq (mt_smul r s) (mt_smul r' s')

  (* abelian group *)
  | mte_assoc (s t u : MTerm) :
      mt_eq (mt_plus (mt_plus s t) u) (mt_plus s (mt_plus t u))
  | mte_comm (s t : MTerm) : mt_eq (mt_plus s t) (mt_plus t s)
  | mte_zero_l (s : MTerm) : mt_eq (mt_plus mt_zero s) s
  | mte_neg_l (s : MTerm) : mt_eq (mt_plus (mt_neg s) s) mt_zero

  (* module *)
  | mte_smul_distr_l (r : carrier (rig_setoid (ring_rig R))) (s t : MTerm) :
      mt_eq (mt_smul r (mt_plus s t)) (mt_plus (mt_smul r s) (mt_smul r t))
  | mte_smul_distr_r (r r' : carrier (rig_setoid (ring_rig R))) (s : MTerm) :
      mt_eq (mt_smul (rig_add (ring_rig R) r r') s)
            (mt_plus (mt_smul r s) (mt_smul r' s))
  | mte_smul_assoc (r r' : carrier (rig_setoid (ring_rig R))) (s : MTerm) :
      mt_eq (mt_smul (rig_mul (ring_rig R) r r') s)
            (mt_smul r (mt_smul r' s))
  | mte_smul_one (s : MTerm) :
      mt_eq (mt_smul (rig_one (ring_rig R)) s) s

  (* bilinearity: additivity in each variable *)
  | mte_add_l (v v' : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
      mt_eq (mt_gen (cmon_plus V v v') w)
            (mt_plus (mt_gen v w) (mt_gen v' w))
  | mte_add_r (v : carrier (cmon_setoid V)) (w w' : carrier (cmon_setoid V')) :
      mt_eq (mt_gen v (cmon_plus V' w w'))
            (mt_plus (mt_gen v w) (mt_gen v w'))

  (* bilinearity: the scalar action, on each variable *)
  | mte_act_l (r : carrier (rig_setoid (ring_rig R)))
              (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
      mt_eq (mt_smul r (mt_gen v w)) (mt_gen (rm_smul V r v) w)
  | mte_act_r (r : carrier (rig_setoid (ring_rig R)))
              (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
      mt_eq (mt_smul r (mt_gen v w)) (mt_gen v (rm_smul V' r w))

  | mte_sym {s t} : mt_eq s t → mt_eq t s
  | mte_trans {s t u} : mt_eq s t → mt_eq t u → mt_eq s u.

Lemma mt_refl (s : MTerm) : mt_eq s s.
Proof.
  induction s.
  - exact (mte_gen (reflexivity _) (reflexivity _)).
  - exact (mte_trans (mte_sym (mte_zero_l mt_zero)) (mte_zero_l mt_zero)).
  - exact (mte_plus IHs1 IHs2).
  - exact (mte_neg IHs).
  - exact (mte_smul (reflexivity _) IHs).
Qed.

Lemma mt_eq_Equivalence : Equivalence mt_eq.
Proof.
  constructor.
  - exact mt_refl.
  - exact (fun s t => mte_sym).
  - exact (fun s t u => mte_trans).
Qed.

Definition mt_Setoid : Setoid MTerm := {|
  equiv        := mt_eq;
  setoid_equiv := mt_eq_Equivalence
|}.

(** The tensor product as an object of [RMod R].  Every law is a
    constructor; nothing is proved. *)
Definition TensorMod : RModObject R := {|
  rm_ab := {|
    ab_cmon := {|
      cmon_setoid := {| carrier := MTerm; is_setoid := mt_Setoid |};
      cmon_zero := mt_zero;
      cmon_plus := mt_plus;
      cmon_plus_respects := fun _ _ Hs _ _ Ht => mte_plus Hs Ht;
      cmon_plus_assoc := mte_assoc;
      cmon_plus_comm := mte_comm;
      cmon_plus_zero_l := mte_zero_l
    |};
    ab_neg := mt_neg;
    ab_neg_respects := fun _ _ Hs => mte_neg Hs;
    ab_neg_left := mte_neg_l
  |};
  rm_smul          := mt_smul;
  rm_smul_respects := fun _ _ Hr _ _ Hs => mte_smul Hr Hs;
  rm_smul_distr_l  := mte_smul_distr_l;
  rm_smul_distr_r  := mte_smul_distr_r;
  rm_smul_assoc    := mte_smul_assoc;
  rm_smul_one      := mte_smul_one
|}.

(** The canonical bilinear map: the generator former itself.  Both scalar
    clauses are the two action rules read backwards, which is precisely
    the point at which the tensor is BALANCED — see [tensor_balanced]. *)
Definition tensor_gen : RBilinear V V' TensorMod :=
  @Build_RBilinear R V V' TensorMod mt_gen
    (fun _ _ Hv _ _ Hw => mte_gen Hv Hw)
    mte_add_l
    mte_add_r
    (fun r v w => mte_sym (mte_act_l r v w))
    (fun r v w => mte_sym (mte_act_r r v w)).

(** (r·v) ⊗ w ≈ v ⊗ (r·w): the balanced law, by composing the two action
    rules through the formal scalar.  It is a THEOREM here rather than a
    generating relation, and it is what a reader coming from the
    non-commutative theory will look for. *)
Lemma tensor_balanced (r : carrier (rig_setoid (ring_rig R)))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  mt_eq (mt_gen (rm_smul V r v) w) (mt_gen v (rm_smul V' r w)).
Proof.
  exact (mte_trans (mte_sym (mte_act_l r v w)) (mte_act_r r v w)).
Qed.

(** The elementary consequences of bilinearity, at the canonical map. *)
Lemma tensor_zero_l (w : carrier (cmon_setoid V')) :
  mt_eq (mt_gen (cmon_zero V) w) mt_zero.
Proof. exact (rbl_zero_l tensor_gen w). Qed.

Lemma tensor_zero_r (v : carrier (cmon_setoid V)) :
  mt_eq (mt_gen v (cmon_zero V')) mt_zero.
Proof. exact (rbl_zero_r tensor_gen v). Qed.

Lemma tensor_neg_l (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  mt_eq (mt_gen (ab_neg V v) w) (mt_neg (mt_gen v w)).
Proof. exact (rbl_neg_l tensor_gen v w). Qed.

Lemma tensor_neg_r (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  mt_eq (mt_gen v (ab_neg V' w)) (mt_neg (mt_gen v w)).
Proof. exact (rbl_neg_r tensor_gen v w). Qed.

(** [rbl_commutator] at the tensor itself: V ⊗ V' is a module on which
    r·s and s·r act alike — equivalently, on which every commutator acts
    as zero, by instantiating [rbl_commutator_annihilates] at
    [tensor_gen].  Over a commutative ring the conclusion already follows
    from [rbl_commutator_from_commutativity] and so carries no
    information; over a non-commutative one it is the collapse the header
    describes. *)
Lemma tensor_commutator (r s : carrier (rig_setoid (ring_rig R)))
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  mt_eq (mt_smul (rig_mul (ring_rig R) r s) (mt_gen v w))
        (mt_smul (rig_mul (ring_rig R) s r) (mt_gen v w)).
Proof. exact (rbl_commutator tensor_gen r s v w). Qed.

End Tensor.

Arguments MTerm {R} V V'.
Arguments mt_gen {R V V'} v w.
Arguments mt_zero {R V V'}.
Arguments mt_plus {R V V'} s t.
Arguments mt_neg {R V V'} s.
Arguments mt_smul {R V V'} r s.
Arguments mt_eq {R V V'} s t.
Arguments mt_refl {R V V'} s.
Arguments mte_gen {R V V' v v' w w'} _ _.
Arguments mte_plus {R V V' s s' t t'} _ _.
Arguments mte_neg {R V V' s s'} _.
Arguments mte_smul {R V V' r r' s s'} _ _.
Arguments mte_assoc {R V V'} s t u.
Arguments mte_comm {R V V'} s t.
Arguments mte_zero_l {R V V'} s.
Arguments mte_neg_l {R V V'} s.
Arguments mte_smul_distr_l {R V V'} r s t.
Arguments mte_smul_distr_r {R V V'} r r' s.
Arguments mte_smul_assoc {R V V'} r r' s.
Arguments mte_smul_one {R V V'} s.
Arguments mte_add_l {R V V'} v v' w.
Arguments mte_add_r {R V V'} v w w'.
Arguments mte_act_l {R V V'} r v w.
Arguments mte_act_r {R V V'} r v w.
Arguments mte_sym {R V V' s t} _.
Arguments mte_trans {R V V' s t u} _ _.
Arguments TensorMod {R} V V'.
Arguments tensor_gen {R V V'}.
Arguments tensor_balanced {R V V'} r v w.
Arguments tensor_zero_l {R V V'} w.
Arguments tensor_zero_r {R V V'} v.
Arguments tensor_neg_l {R V V'} v w.
Arguments tensor_neg_r {R V V'} v w.
Arguments tensor_commutator {R V V'} r s v w.

(** ** The factorization *)

Section Mediator.

Context {R : RingObject}.
Context {V V' : RModObject R}.
Context {W : RModObject R}.
Context (β : RBilinear V V' W).

(* Fold a formal expression through the target module's operations.  It
   computes on constructors, which is what makes the three homomorphism
   obligations and the scalar clause below hold by [reflexivity]. *)
Fixpoint tensor_med_fun (t : MTerm V V') : carrier (cmon_setoid W) :=
  match t with
  | mt_gen v w  => rbl_map β v w
  | mt_zero     => cmon_zero W
  | mt_plus s t => cmon_plus W (tensor_med_fun s) (tensor_med_fun t)
  | mt_neg s    => ab_neg W (tensor_med_fun s)
  | mt_smul r s => rm_smul W r (tensor_med_fun s)
  end.

(* Respectfulness is one induction over the relation: eighteen cases,
   one per constructor of [mt_eq].  Eight are met by the corresponding
   law of the target module (four abelian-group, four module), four by
   the corresponding clause of bilinearity of β, and the other six are
   not laws — [mte_gen] is saturation under the two point setoids, three
   are congruence for a former, and two are the target setoid's symmetry
   and transitivity. *)
Lemma tensor_med_respects (s t : MTerm V V') :
  mt_eq s t → tensor_med_fun s ≈ tensor_med_fun t.
Proof.
  intro He; induction He; simpl.
  - exact (rbl_respects β _ _ e _ _ e0).
  - exact (cmon_plus_respects W _ _ IHHe1 _ _ IHHe2).
  - exact (ab_neg_respects W _ _ IHHe).
  - exact (rm_smul_respects W _ _ e _ _ IHHe).
  - exact (cmon_plus_assoc W _ _ _).
  - exact (cmon_plus_comm W _ _).
  - exact (cmon_plus_zero_l W _).
  - exact (ab_neg_left W _).
  - exact (rm_smul_distr_l W _ _ _).
  - exact (rm_smul_distr_r W _ _ _).
  - exact (rm_smul_assoc W _ _ _).
  - exact (rm_smul_one W _).
  - exact (rbl_add_l β _ _ _).
  - exact (rbl_add_r β _ _ _).
  - exact (symmetry (rbl_smul_l β _ _ _)).
  - exact (symmetry (rbl_smul_r β _ _ _)).
  - exact (symmetry IHHe).
  - exact (transitivity IHHe1 IHHe2).
Qed.

(** The factorizing homomorphism.  Preservation of zero, of addition and
    of the action all hold by [reflexivity], the fixpoint's clauses BEING
    those equations; only respectfulness has content.  One uniform body
    is used for the four obligations so that the proof does not depend on
    the order [Program] emits them in (the Instance/Mod/Free.v:359
    idiom). *)
Program Definition tensor_med : TensorMod V V' ~{RMod R}~> W := {|
  rm_hom := {| cmon_map := {| morphism := tensor_med_fun |} |}
|}.
Next Obligation.
  first [ (intros s t He; exact (tensor_med_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (tensor_med_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (tensor_med_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.
Next Obligation.
  first [ (intros s t He; exact (tensor_med_respects s t He))
        | (intros; simpl; reflexivity) ].
Qed.

(* It agrees with β on generators — definitionally, not up to [≈]. *)
Example tensor_med_gen (v : carrier (cmon_setoid V))
  (w : carrier (cmon_setoid V')) :
  cmon_map (rm_hom tensor_med) (mt_gen v w) = rbl_map β v w := eq_refl.

End Mediator.

Arguments tensor_med_fun {R V V' W} β t.
Arguments tensor_med {R V V' W} β.

(** Uniqueness, in its most consumable form: two homomorphisms out of the
    tensor that agree on generators agree everywhere.  The [mt_neg] case
    is Instance/Ab.v's [ab_map_neg] and the [mt_smul] case is
    Instance/Mod.v's [rm_map_smul] — which is exactly why this statement
    is about MODULE homomorphisms and would be false for maps of the
    underlying setoids. *)
Lemma tensor_hom_ext {R : RingObject} {V V' W : RModObject R}
  (f g : TensorMod V V' ~{RMod R}~> W) :
  (∀ (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')),
      cmon_map (rm_hom f) (mt_gen v w) ≈ cmon_map (rm_hom g) (mt_gen v w)) →
  ∀ t : MTerm V V', cmon_map (rm_hom f) t ≈ cmon_map (rm_hom g) t.
Proof.
  intros Hgen t; induction t.
  - exact (Hgen c c0).
  - exact (transitivity (cmon_map_zero (rm_hom f))
             (symmetry (cmon_map_zero (rm_hom g)))).
  - refine (transitivity (cmon_map_plus (rm_hom f) t1 t2) _).
    refine (transitivity _ (symmetry (cmon_map_plus (rm_hom g) t1 t2))).
    exact (cmon_plus_respects W _ _ IHt1 _ _ IHt2).
  - refine (transitivity (ab_map_neg (rm_hom f) t) _).
    refine (transitivity _ (symmetry (ab_map_neg (rm_hom g) t))).
    exact (ab_neg_respects W _ _ IHt).
  - refine (transitivity (rm_map_smul f c t) _).
    refine (transitivity _ (symmetry (rm_map_smul g c t))).
    exact (rm_smul_respects W _ _ (reflexivity c) _ _ IHt).
Qed.

(** ** The bilinear-maps functor

    Bilin(V, V'; −) : RMod R ⟶ Sets — the FUNCTOR, which is what makes
    the tensor product a universal ELEMENT rather than merely an object
    with a mapping property.  The object part is the setoid of bilinear
    maps compared pointwise; the arrow part is postcomposition, and it is
    a bilinear map again because a module homomorphism is additive and
    commutes with the action, which is exactly the two pairs of clauses
    below. *)

Section BilinFunctor.

Context {R : RingObject}.
Context (V V' : RModObject R).

Program Definition RBilinear_Setoid (W : RModObject R) :
  Setoid (RBilinear V V' W) := {|
  equiv := fun β γ => ∀ v w, rbl_map β v w ≈ rbl_map γ v w
|}.
Next Obligation.
  intros W.
  constructor.
  - intros β v w; reflexivity.
  - intros β γ Hβγ v w; symmetry; apply Hβγ.
  - intros β γ δ H1 H2 v w.
    transitivity (rbl_map γ v w); [ apply H1 | apply H2 ].
Qed.

Definition Bilin_obj (W : RModObject R) : SetoidObject := {|
  carrier   := RBilinear V V' W;
  is_setoid := RBilinear_Setoid W
|}.

(* Postcomposition with a module homomorphism. *)
Program Definition Bilin_post {W W' : RModObject R} (f : W ~{RMod R}~> W')
  (β : RBilinear V V' W) : RBilinear V V' W' := {|
  rbl_map := fun v w => cmon_map (rm_hom f) (rbl_map β v w)
|}.
Next Obligation.
  intros W W' f β v v0 Hv w w0 Hw; simpl.
  now rewrite Hv, Hw.
Qed.
Next Obligation.
  intros W W' f β v v0 w; simpl.
  rewrite (rbl_add_l β v v0 w).
  apply (cmon_map_plus (rm_hom f)).
Qed.
Next Obligation.
  intros W W' f β v w w0; simpl.
  rewrite (rbl_add_r β v w w0).
  apply (cmon_map_plus (rm_hom f)).
Qed.
Next Obligation.
  intros W W' f β r v w; simpl.
  rewrite (rbl_smul_l β r v w).
  apply (rm_map_smul f r (rbl_map β v w)).
Qed.
Next Obligation.
  intros W W' f β r v w; simpl.
  rewrite (rbl_smul_r β r v w).
  apply (rm_map_smul f r (rbl_map β v w)).
Qed.

Program Definition Bilin : RMod R ⟶ Sets := {|
  fobj := Bilin_obj;
  fmap := fun W W' f => {| morphism := Bilin_post f |}
|}.
Next Obligation.
  intros W W' f β γ Hβγ v w; simpl.
  now rewrite (Hβγ v w).
Qed.
Next Obligation.
  intros W W' f g Hfg β v w; simpl.
  exact (Hfg (rbl_map β v w)).
Qed.
Next Obligation.
  intros W β v w; simpl; reflexivity.
Qed.
Next Obligation.
  intros W W' W'' f g β v w; simpl; reflexivity.
Qed.

(** ** The headline: ⟨V ⊗ V', ⊗⟩ is a universal element of Bilin(V, V'; −)

    Mac Lane's clause "(H k) e = x for a unique k" is, unfolded here,
    "k agrees with β on generators, for a unique module homomorphism k":
    the existence half is [tensor_med] (and the equation holds by
    [reflexivity], the mediator's underlying map being a fixpoint), the
    uniqueness half is [tensor_hom_ext]. *)
Program Definition tensor_universal_element :
  AUniversalElement Bilin (TensorMod V V') := {|
  aue_elem      := tensor_gen;
  aue_universal := fun W β => {| unique_obj := tensor_med β |}
|}.
Next Obligation.
  intros W β v w; simpl; reflexivity.
Qed.
Next Obligation.
  intros W β k Hk t.
  apply (tensor_hom_ext (tensor_med β) k).
  intros v w.
  exact (symmetry (Hk v w)).
Qed.

(* Mac Lane's pair ⟨r, e⟩, the same data with the object as a field. *)
Definition tensor_UniversalElement : UniversalElement Bilin :=
  UniversalElement_of_AUniversalElement tensor_universal_element.

(* The representing object is the tensor, by [eq_refl]. *)
Example tensor_UniversalElement_obj :
  @ue_obj (RMod R) Bilin tensor_UniversalElement = TensorMod V V' := eq_refl.

(** *** Unique factorization, read off the class

    These three are the class's own fields at [tensor_universal_element],
    restated for a reader who wants f = f̄ ∘ ⊗ without unfolding
    [AUniversalElement].  Nothing is reproved: [tensor_factor] IS
    [tensor_med] by [eq_refl] ([tensor_factor_is_med]), so the
    factorization still computes. *)
Definition tensor_factor {W : RModObject R} (β : RBilinear V V' W) :
  TensorMod V V' ~{RMod R}~> W :=
  unique_obj (@aue_universal (RMod R) Bilin (TensorMod V V')
                tensor_universal_element W β).

Example tensor_factor_is_med {W : RModObject R} (β : RBilinear V V' W) :
  tensor_factor β = tensor_med β := eq_refl.

Lemma tensor_factor_commutes {W : RModObject R} (β : RBilinear V V' W)
  (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')) :
  cmon_map (rm_hom (tensor_factor β)) (mt_gen v w) ≈ rbl_map β v w.
Proof.
  exact (unique_property (@aue_universal (RMod R) Bilin (TensorMod V V')
                            tensor_universal_element W β) v w).
Qed.

Lemma tensor_factor_unique {W : RModObject R} (β : RBilinear V V' W)
  (k : TensorMod V V' ~{RMod R}~> W) :
  (∀ (v : carrier (cmon_setoid V)) (w : carrier (cmon_setoid V')),
      cmon_map (rm_hom k) (mt_gen v w) ≈ rbl_map β v w) →
  tensor_factor β ≈ k.
Proof.
  intro Hk.
  exact (uniqueness (@aue_universal (RMod R) Bilin (TensorMod V V')
                       tensor_universal_element W β) k Hk).
Qed.

End BilinFunctor.

Arguments RBilinear_Setoid {R} V V' W.
Arguments Bilin_obj {R} V V' W.
Arguments Bilin_post {R} V V' {W W'} f β.
Arguments Bilin {R} V V'.
Arguments tensor_universal_element {R} V V'.
Arguments tensor_UniversalElement {R} V V'.
Arguments tensor_factor {R V V' W} β.
Arguments tensor_factor_commutes {R V V' W} β v w.
Arguments tensor_factor_unique {R V V' W} β k _.

(** ** Non-degeneracy: ℤ ⊗_ℤ ℤ

    A universal property proved over a quotient says nothing until the
    quotient is shown not to collapse, and a factorization theorem says
    nothing until some factorization is exhibited.  Both are done here at
    the cheapest non-trivial pair of modules in the tree: ℤ over ℤ, where
    the archetypal bilinear map is multiplication.

    Three separate things are measured, because they are separate.
    First, the factorization COMPUTES: the mediator is a fixpoint, so its
    value on a closed generator reduces, by [eq_refl], and it reduces
    through the CLASS as well as through [tensor_med].  Second, the
    quotient does not collapse: distinct generators stay distinct and the
    canonical map is not the zero map — proved by mapping OUT of the
    quotient, through [tensor_med_respects].  That route is taken because
    a direct structural induction on [mt_eq] supplies no usable
    invariant, [mte_sym] and [mte_trans] quantifying over an
    unconstrained intermediate term; no claim is made that no induction
    could work, which would be an impossibility statement and is not
    proved here.  Third, the object is pinned exactly:
    [Int_tensor_iso] identifies ℤ ⊗_ℤ ℤ with ℤ in [RMod Int_Ring]. *)

(* Multiplication as a bilinear map.  Every clause is a ring law of ℤ;
   the [rbl_smul_r] clause is the one that spends commutativity of ℤ —
   as it must, being the statement that the scalar can be moved out of
   the SECOND variable. *)
Definition Int_mul_bilinear : RBilinear Int_RMod Int_RMod Int_RMod.
Proof.
  unshelve notypeclasses refine
    (@Build_RBilinear Int_Ring Int_RMod Int_RMod Int_RMod Z.mul _ _ _ _ _).
  - (* rbl_respects *)
    intros a b Hab c d Hcd; simpl in *; unfold Rig.Z_eqT in *; now subst.
  - (* rbl_add_l *)
    intros v v' w; simpl; unfold Rig.Z_eqT; ring.
  - (* rbl_add_r *)
    intros v w w'; simpl; unfold Rig.Z_eqT; ring.
  - (* rbl_smul_l *)
    intros r v w; simpl; unfold Rig.Z_eqT; ring.
  - (* rbl_smul_r: the clause that spends commutativity of ℤ *)
    intros r v w; simpl; unfold Rig.Z_eqT; ring.
Defined.

(* Index arguments supplied once, as NOTATIONS (so each unfolds to the
   constructor itself) — the device Instance/Mod/Free.v uses for its own
   witnesses. *)
Local Notation zgen  := (@mt_gen Int_Ring Int_RMod Int_RMod).
Local Notation zzero := (@mt_zero Int_Ring Int_RMod Int_RMod).
Local Notation zplus := (@mt_plus Int_Ring Int_RMod Int_RMod).
Local Notation zneg  := (@mt_neg Int_Ring Int_RMod Int_RMod).
Local Notation zsmul := (@mt_smul Int_Ring Int_RMod Int_RMod).

(* The factorization computes, through [tensor_med] and through the
   universal element's own mediator alike. *)
Example int_tensor_med_computes :
  cmon_map (rm_hom (tensor_med Int_mul_bilinear)) (zgen 2%Z 3%Z) = 6%Z
  := eq_refl.

Example int_tensor_factor_computes :
  cmon_map (rm_hom (tensor_factor Int_mul_bilinear)) (zgen 2%Z 3%Z) = 6%Z
  := eq_refl.

(* And it computes on a compound tensor, where the fold does real work. *)
Example int_tensor_med_computes_sum :
  cmon_map (rm_hom (tensor_med Int_mul_bilinear))
    (zplus (zsmul 5%Z (zgen 2%Z 3%Z)) (zneg (zgen 4%Z 1%Z)))
  = 26%Z := eq_refl.

(** The quotient does not collapse.  Both statements are proved by
    mapping OUT through [tensor_med_respects]: an inhabitant of [mt_eq]
    would give an equation in ℤ that [discriminate] refutes. *)
Lemma int_tensor_gen_nonzero : mt_eq (zgen 1%Z 1%Z) zzero → False.
Proof.
  intro He.
  pose proof (tensor_med_respects Int_mul_bilinear _ _ He) as Hz.
  simpl in Hz; unfold Rig.Z_eqT in Hz.
  discriminate Hz.
Qed.

Lemma int_tensor_gen_distinct :
  mt_eq (zgen 1%Z 1%Z) (zgen 2%Z 1%Z) → False.
Proof.
  intro He.
  pose proof (tensor_med_respects Int_mul_bilinear _ _ He) as Hz.
  simpl in Hz; unfold Rig.Z_eqT in Hz.
  discriminate Hz.
Qed.

(** The inverse comparison n ↦ n ⊗ 1.  It is a module homomorphism
    because 0 ⊗ 1 ≈ 0 ([tensor_zero_l]), because the generator former is
    additive ([mte_add_l]), and because the scalar rule [mte_act_l] is
    exactly linearity of n ↦ n ⊗ 1. *)
(* Respectfulness is supplied as a term ([mte_gen] with the second
   component reflexive) rather than left to [Program], which would fill
   it by [reflexive_proper] — sound here only because ℤ's setoid
   equality happens to be Leibniz, and not a habit worth forming.  The
   three remaining obligations are preservation of zero, of addition and
   of the action, in that order. *)
Program Definition int_tensor_unit :
  Int_RMod ~{RMod Int_Ring}~> TensorMod Int_RMod Int_RMod := {|
  rm_hom := {| cmon_map := {|
    morphism        := fun n => zgen n 1%Z;
    proper_morphism := fun a b Hab => mte_gen Hab (reflexivity 1%Z) |} |}
|}.
Next Obligation.
  exact (@tensor_zero_l Int_Ring Int_RMod Int_RMod 1%Z).
Qed.
Next Obligation.
  intros a b; exact (@mte_add_l Int_Ring Int_RMod Int_RMod a b 1%Z).
Qed.
Next Obligation.
  intros r n; exact (mte_sym (@mte_act_l Int_Ring Int_RMod Int_RMod r n 1%Z)).
Qed.

(** ℤ ⊗_ℤ ℤ ≅ ℤ in [RMod Int_Ring].  One leg is multiplication, the
    other is n ↦ n ⊗ 1; the round trip on the tensor is [tensor_hom_ext]
    plus the balanced law, which is where the whole quotient is used. *)
Program Definition Int_tensor_iso :
  @Isomorphism (RMod Int_Ring) (TensorMod Int_RMod Int_RMod) Int_RMod := {|
  to   := tensor_med Int_mul_bilinear;
  from := int_tensor_unit
|}.
Next Obligation.
  intro n; simpl; unfold Rig.Z_eqT; apply Z.mul_1_r.
Qed.
Next Obligation.
  refine (tensor_hom_ext
            (int_tensor_unit ∘ tensor_med Int_mul_bilinear)
            (@id (RMod Int_Ring) (TensorMod Int_RMod Int_RMod)) _).
  intros v w; simpl.
  (* (v·w) ⊗ 1 ≈ (w·v) ⊗ 1 ≈ w·(v ⊗ 1) ≈ v ⊗ (w·1) ≈ v ⊗ w: the middle
     two steps are the two action rules, i.e. the balanced law. *)
  refine (mte_trans (@mte_gen Int_Ring Int_RMod Int_RMod _ _ _ _
                       (Z.mul_comm v w) (reflexivity 1%Z)) _).
  refine (mte_trans (mte_sym (@mte_act_l Int_Ring Int_RMod Int_RMod w v 1%Z)) _).
  refine (mte_trans (@mte_act_r Int_Ring Int_RMod Int_RMod w v 1%Z) _).
  exact (@mte_gen Int_Ring Int_RMod Int_RMod _ _ _ _
           (reflexivity v) (Z.mul_1_r w)).
Qed.
