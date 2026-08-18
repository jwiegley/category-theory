Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Algebras.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * The polynomial ring K[x] as a universal arrow

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          GTM 5, §III.1, printed pp. 56 and 59 — the roster of free
          constructions as universal arrows (maclane:III.1:remark2) and
          Exercise 7, which asks for K[x] with the insertion of x as a
          universal construction (maclane:III.1:ex7)
    Book: Riehl, "Category Theory in Context", 2nd ed., §2.1
          Example 2.1.5(v), printed p. 56 — the forgetful functor from
          rings to sets is represented by ℤ[x] (riehl:2.1:example5)
    Book: Riehl, ibid., §2.3 Example 2.3.4, printed p. 68 — the same in
          element form, with the indeterminate as the universal element
          (riehl:2.3:example4)
    nLab:      https://ncatlab.org/nlab/show/polynomial+ring
    nLab:      https://ncatlab.org/nlab/show/free+functor
    nLab:      https://ncatlab.org/nlab/show/universal+morphism
    Wikipedia: https://en.wikipedia.org/wiki/Polynomial_ring

    WHY THE INDETERMINATE IS A UNIVERSAL PROPERTY.  "Let x be an
    indeterminate" is the oldest piece of mathematical hand-waving that
    category theory turned into a definition.  What a nineteenth-century
    algebraist meant by it was operational: x is a symbol one may
    calculate with, subject to no relation beyond the ring laws, and
    which may afterwards be REPLACED by any element of any ring
    containing the coefficients.  The replacement clause is the whole
    content, and it is a universal property in disguise — the pair
    (K[x], x) is universal among rings under K equipped with a chosen
    element, so that specifying a homomorphism out of K[x] is the same
    thing as specifying where x goes.  The substitution homomorphism that
    every algebra course introduces by formula, p ↦ p(a), is then not a
    construction at all but THE mediating arrow of that universal
    property, and its existence and uniqueness are one statement rather
    than two.  Mac Lane makes the point by listing the polynomial algebra
    alongside the free monoid, the free group and the free module in the
    §III.1 roster, and setting Exercise 7 to check that it belongs there.

    The reading has three faces, and all three are formalized below
    because they are what the three catalogued sources each ask for.  Mac
    Lane's is the universal arrow: (K[x], x) is initial among K-algebras
    with a chosen element.  Awodey's (§9.3, Instance/Rng/Pointed.v) is
    the adjunction: "adjoin an indeterminate" is left adjoint to
    forgetting a distinguished element, and the transposition IS
    evaluation.  Riehl's is representability: the underlying-set functor
    of rings is naturally isomorphic to Rng(ℤ[x], −), the isomorphism
    being "evaluate at x", and x itself is the universal element.  The
    three are interderivable through Theory/Universal/Element.v's
    subsumption theorem, and the passages are taken here rather than
    re-proved.

    MAC LANE'S ROSTER, COMPLETE.  The §III.1 examples of free
    constructions as universal arrows — as issue #309 enumerates them —
    are now all in tree, and this file is the last of the five:

      - free category on a graph — [UniversalArrowQuiverCat]
        (Construction/Free/Quiver.v:529) with [FreeForgetfulAdjunction]
        (:561);
      - free monoid — [free_monoid_universal_arrow]
        (Instance/Coq/Monoid/Free.v:297) with [free_monoid_adjunction]
        (:326);
      - free group — [free_group_universal_arrow]
        (Instance/Grp/Free.v:405) with [free_group_adjunction] (:437);
      - free R-module — [free_module_universal_arrow]
        (Instance/Mod/Free.v:487) with [free_module_adjunction] (:517),
        and the vector-space case in Instance/Vect/Free.v;
      - polynomial algebra — this file.

    A CORRECTION TO THE ISSUE'S PRIOR ART, recorded here because a
    header is where a reader looks.  Issue #309 states that "the free
    R-module and the polynomial algebra have no in-tree counterpart and
    no host categories", and its Riehl §4.1 section reports as verified
    that "rg -nw 'Ring' returns 0 hits, so there is no base ring, no
    module category, and no free module".  Both are false as of this
    writing: Instance/Rng.v is the category of unital rings,
    Instance/Mod.v the category of R-modules, and Instance/Mod/Free.v
    the free module with exactly the universal arrow and adjunction the
    issue asks for.  Only the polynomial half was genuinely absent, and
    only that half is built here.  A third stale claim is worth naming
    for the same reason: the category of commutative K-algebras was
    ALSO already in tree, as Instance/Rng/Algebras.v's [KAlg], so
    "rings under K" needed no construction and Mac Lane's Exercise 7
    lands there directly.

    HOW K[x] IS PRESENTED, AND WHAT THAT COSTS.  The construction is by
    generators and relations, in the style of Instance/Ab/Tensor.v,
    Instance/Sets/Coend.v and Instance/Mod/Free.v: [PTerm] is a plain
    inductive of formal expressions built from constants, the
    indeterminate, sum, negation and product, and [pt_eq] is an
    inductive relation closing under exactly the commutative-ring laws,
    congruence for each former, saturation under K's own [≈], the two
    clauses making the constant inclusion a homomorphism, and symmetry
    and transitivity.  Reflexivity is derived ([pt_refl]), keeping the
    relation's induction principle one case shorter wherever it is
    consumed.  As in Instance/Ab/Tensor.v, [pt_Setoid] is not registered
    as a typeclass instance; the [≈] of [PolyRing K] IS [pt_eq]
    definitionally, so the ring-level lemmas of Theory/Algebra/Rig.v
    apply to it unchanged.

    The alternative presentation — a polynomial as a finite list of
    coefficients, with convolution for the product — was considered and
    not taken, and the reason is a design judgment rather than a
    measurement: it would buy normal forms, degree and coefficient
    extraction, at the price of proving associativity and commutativity
    of convolution, which are triple-sum reindexing arguments, and none
    of what it buys is consumed by the universal property.  What is
    therefore NOT available here is
    any notion of degree, any leading coefficient, and any decision
    procedure for equality in K[x].  What IS available, and is what a
    reader of §III.1 wants, is that the construction does not collapse:
    [poly_const_injective] proves K ↪ K[x] for every commutative K, and
    [poly_x_not_constant] proves the indeterminate is not any constant
    whenever 1 ≉ 0 in K — both by evaluating in K itself, so neither
    needs a normal form.

    THE STANDING COMMUTATIVITY ASSUMPTION, and where it bites.  [PolyRing]
    is defined for an ARBITRARY [RingObject] K, because nothing in the
    construction needs more; but [pe_mul_comm] is a constructor, and with
    [pe_const_mul] it forces const(ab) ≈ const(ba) for all a, b in K.  So
    over a non-commutative K the constant inclusion is not injective and
    [PolyRing K] is not the polynomial ring over K.  What that quotient
    IS, exactly — whether the kernel of the constant inclusion is
    precisely the commutator ideal, making [PolyRing K] the polynomial
    ring over K's largest commutative quotient — is NOT proved here and
    is not claimed; the forcing direction is immediate from the two
    constructors and the converse would need a normal form.
    Commutativity of K is load-bearing in two distinct places, not one:
    [phi_image_comm] spends it so that [peval] respects the
    [pe_mul_comm] constructor, which is what makes the fold well defined
    at all, and [poly_const_injective] spends it again for
    non-degeneracy.  It is nowhere decorative.
    Every universal-property statement below carries it.

    STRENGTHS, MEASURED, and the two halves of the extension differ.

      - [eq_refl]: evaluation restricts to the structure map on constants
        and sends the indeterminate to the chosen element
        ([poly_extend_const], [poly_extend_x]); preservation of ADDITION
        and of MULTIPLICATION are clauses of the fixpoint and close by
        [reflexivity]; the universal element of [Rng_Forget] IS the
        indeterminate ([zpoly_universal_elem_is_x]); the mediating
        homomorphism sends it to the chosen element
        ([zpoly_mediator_at_x]); and evaluation COMPUTES on closed input
        over ℤ ([zpoly_eval_at_three], and two more).
      - `≈` only: preservation of ZERO and of ONE.  The zero of K[x] is
        [pt_const (rig_zero K)], so the fold returns the image of K's
        zero and reaching the target's zero is the structure map's own
        preservation law.  This is measured, not assumed: the two
        obligations are discharged by [rig_map_zero] and [rig_map_one]
        and the other two by [reflexivity].
      - `≈` only, unavoidably: the transposes obtained from
        [ump_universal_arrows], which is [Qed]-opaque and does not
        compute.  Instance/Rng/Pointed.v records the same seam for the
        adjunction's backward transpose, as Instance/Mod/Free.v does for
        the counit of the free-module adjunction.

    WHAT IS DELIVERED.

      - [PolyRing K] for any [RingObject] K, with [poly_const],
        [poly_x] and [poly_comm];
      - [poly_extend] and [poly_extend_unique]: the substitution
        homomorphism and its uniqueness, over a hypothesis pack (K
        commutative, and the chosen element commuting with the image of
        the structure map) whose SECOND half is proved NECESSARY by
        [poly_hom_value_central] -- that lemma says nothing about K's
        own commutativity, and what a hom out of K[x] actually forces on
        the coefficients is commutativity of the IMAGE of the structure
        map, which [Kcomm] implies and which does not imply [Kcomm];
      - Mac Lane's Exercise 7: [poly_universal_element], a universal
        element at [PolyAlg K] of [KAlg_Forget], the underlying-set
        functor of Instance/Rng/Algebras.v's category [KAlg] of
        commutative K-algebras — that category is Algebras.v's, the
        functor is this file's — with the natural isomorphism
        [poly_representation], the class inhabitant [poly_representable]
        and both of Theory/Universal/Arrow.v's universal-arrow encodings;
      - ℤ[x] as the free unital ring on one generator in ALL of [Rng],
        not merely in [CRng]: [zring_central] shows the integers are
        central in every unital ring, which discharges the commutation
        hypothesis for an arbitrary target, and [zpoly_universal_element],
        [zpoly_representation] and [zpoly_representable] are Riehl's two
        examples;
      - [rng_monic_injective] and [rng_monic_iff_injective]:
        monomorphisms of rings are injective, which is the result
        Instance/Rng.v:70 deferred pending the polynomial ring ℤ[x]
        (paraphrased -- that file's wording is "the polynomial ring
        ℤ[x], which does not exist in-tree");
      - the non-degeneracy results above, and computing witnesses.

    WHAT IS NOT DELIVERED.  No degree, no normal form, no coefficient
    uniqueness, and hence no decision procedure for equality in K[x] and
    no division algorithm.  No several-indeterminate polynomial ring
    (K[x][y] is constructible by iterating, but is not identified with
    a two-variable ring here).  No proof that K[x] is an integral domain
    when K is, and so no connection to Instance/Rng/Frac.v's [IntDom].
    No claim that [PolyRing] is functorial in K as a stated functor —
    that content arrives as the [fmap] of the left adjoint in
    Instance/Rng/Pointed.v. *)

(** ** Two negation laws for multiplication

    Instance/Rng.v carries [rig_mul_neg_one] — the special case at
    [-1] — and Instance/Ab.v the additive facts; the two general forms
    below are used throughout and are proved the same way, by uniqueness
    of additive inverses. *)

Lemma rng_mul_neg_r (R : RingObject) (a b : carrier (rig_setoid R)) :
  rig_mul R a (ring_neg R b) ≈ ring_neg R (rig_mul R a b).
Proof.
  apply (ab_neg_unique (ring_ab R)); simpl.
  rewrite <- rig_distr_l.
  rewrite (ring_neg_l R b).
  apply rig_mul_zero_r.
Qed.

Lemma rng_mul_neg_l (R : RingObject) (a b : carrier (rig_setoid R)) :
  rig_mul R (ring_neg R a) b ≈ ring_neg R (rig_mul R a b).
Proof.
  apply (ab_neg_unique (ring_ab R)); simpl.
  rewrite <- rig_distr_r.
  rewrite (ring_neg_l R a).
  apply rig_mul_zero_l.
Qed.

Section Polynomial.

Context (K : RingObject).

(** ** Formal polynomial expressions *)

Inductive PTerm : Type :=
  | pt_const : carrier (rig_setoid K) → PTerm
  | pt_x     : PTerm
  | pt_add   : PTerm → PTerm → PTerm
  | pt_neg   : PTerm → PTerm
  | pt_mul   : PTerm → PTerm → PTerm.

Inductive pt_eq : PTerm → PTerm → Type :=
  (* congruence for each former, saturating under K's own [≈] *)
  | pe_const {a b} : a ≈ b → pt_eq (pt_const a) (pt_const b)
  | pe_add {s s' t t'} :
      pt_eq s s' → pt_eq t t' → pt_eq (pt_add s t) (pt_add s' t')
  | pe_neg {s s'} : pt_eq s s' → pt_eq (pt_neg s) (pt_neg s')
  | pe_mul {s s' t t'} :
      pt_eq s s' → pt_eq t t' → pt_eq (pt_mul s t) (pt_mul s' t')

  (* abelian group under addition *)
  | pe_add_assoc s t u :
      pt_eq (pt_add (pt_add s t) u) (pt_add s (pt_add t u))
  | pe_add_comm s t : pt_eq (pt_add s t) (pt_add t s)
  | pe_add_zero_l s : pt_eq (pt_add (pt_const (rig_zero K)) s) s
  | pe_add_neg_l s : pt_eq (pt_add (pt_neg s) s) (pt_const (rig_zero K))

  (* commutative monoid under multiplication *)
  | pe_mul_assoc s t u :
      pt_eq (pt_mul (pt_mul s t) u) (pt_mul s (pt_mul t u))
  | pe_mul_comm s t : pt_eq (pt_mul s t) (pt_mul t s)
  | pe_mul_one_l s : pt_eq (pt_mul (pt_const (rig_one K)) s) s

  (* distributivity, on the left only: the right law is derived *)
  | pe_distr_l s t u :
      pt_eq (pt_mul s (pt_add t u)) (pt_add (pt_mul s t) (pt_mul s u))

  (* the coefficient inclusion is a homomorphism of rings *)
  | pe_const_add a b :
      pt_eq (pt_const (rig_add K a b)) (pt_add (pt_const a) (pt_const b))
  | pe_const_mul a b :
      pt_eq (pt_const (rig_mul K a b)) (pt_mul (pt_const a) (pt_const b))

  | pe_sym {s t} : pt_eq s t → pt_eq t s
  | pe_trans {s t u} : pt_eq s t → pt_eq t u → pt_eq s u.

Lemma pt_refl (s : PTerm) : pt_eq s s.
Proof.
  induction s.
  - exact (pe_const (reflexivity _)).
  - exact (pe_trans (pe_sym (pe_add_zero_l pt_x)) (pe_add_zero_l pt_x)).
  - exact (pe_add IHs1 IHs2).
  - exact (pe_neg IHs).
  - exact (pe_mul IHs1 IHs2).
Qed.

Lemma pt_eq_Equivalence : Equivalence pt_eq.
Proof.
  constructor.
  - exact pt_refl.
  - exact (fun s t => pe_sym).
  - exact (fun s t u => pe_trans).
Qed.

Definition pt_Setoid : Setoid PTerm := {|
  equiv        := pt_eq;
  setoid_equiv := pt_eq_Equivalence
|}.

(** ** Derived laws *)

Let PZ : PTerm := pt_const (rig_zero K).
Let PO : PTerm := pt_const (rig_one K).

Lemma pe_add_zero_r (s : PTerm) : pt_eq (pt_add s PZ) s.
Proof.
  exact (pe_trans (pe_add_comm s PZ) (pe_add_zero_l s)).
Qed.

Lemma pe_add_neg_r (s : PTerm) : pt_eq (pt_add s (pt_neg s)) PZ.
Proof.
  exact (pe_trans (pe_add_comm s (pt_neg s)) (pe_add_neg_l s)).
Qed.

Lemma pe_mul_one_r (s : PTerm) : pt_eq (pt_mul s PO) s.
Proof.
  exact (pe_trans (pe_mul_comm s PO) (pe_mul_one_l s)).
Qed.

Lemma pe_distr_r (s t u : PTerm) :
  pt_eq (pt_mul (pt_add s t) u) (pt_add (pt_mul s u) (pt_mul t u)).
Proof.
  refine (pe_trans (pe_mul_comm (pt_add s t) u) _).
  refine (pe_trans (pe_distr_l u s t) _).
  exact (pe_add (pe_mul_comm u s) (pe_mul_comm u t)).
Qed.

(* Cancellation: adding the negative on the left is what makes the
   annihilation law below a theorem rather than a further constructor. *)
Lemma pe_add_cancel_l (s t u : PTerm) :
  pt_eq (pt_add s t) (pt_add s u) → pt_eq t u.
Proof.
  intro H.
  refine (pe_trans (pe_sym (pe_add_zero_l t)) _).
  refine (pe_trans (pe_add (pe_sym (pe_add_neg_l s)) (pt_refl t)) _).
  refine (pe_trans (pe_add_assoc (pt_neg s) s t) _).
  refine (pe_trans (pe_add (pt_refl (pt_neg s)) H) _).
  refine (pe_trans (pe_sym (pe_add_assoc (pt_neg s) s u)) _).
  refine (pe_trans (pe_add (pe_add_neg_l s) (pt_refl u)) _).
  exact (pe_add_zero_l u).
Qed.

Lemma pe_mul_zero_l (s : PTerm) : pt_eq (pt_mul PZ s) PZ.
Proof.
  (* 0·s ≈ (0+0)·s ≈ 0·s + 0·s, so 0·s ≈ 0 by cancellation. *)
  apply (pe_add_cancel_l (pt_mul PZ s)).
  refine (pe_trans (pe_sym (pe_distr_r PZ PZ s)) _).
  refine (pe_trans (pe_mul _ (pt_refl s)) (pe_sym (pe_add_zero_r (pt_mul PZ s)))).
  refine (pe_trans (pe_sym (pe_const_add (rig_zero K) (rig_zero K))) _).
  exact (pe_const (rig_add_zero_l K (rig_zero K))).
Qed.

Lemma pe_mul_zero_r (s : PTerm) : pt_eq (pt_mul s PZ) PZ.
Proof.
  exact (pe_trans (pe_mul_comm s PZ) (pe_mul_zero_l s)).
Qed.

(* The coefficient inclusion also carries negation, by uniqueness of
   additive inverses in the term ring. *)
Lemma pe_const_neg (a : carrier (rig_setoid K)) :
  pt_eq (pt_const (ring_neg K a)) (pt_neg (pt_const a)).
Proof.
  apply (pe_add_cancel_l (pt_const a)).
  refine (pe_trans _ (pe_sym (pe_add_neg_r (pt_const a)))).
  refine (pe_trans (pe_sym (pe_const_add a (ring_neg K a))) _).
  refine (pe_const _).
  refine (transitivity (rig_add_comm K a (ring_neg K a)) _).
  exact (ring_neg_l K a).
Qed.

(** ** The ring K[x] *)

Definition PolyRig : RigObject := {|
  rig_setoid := {| carrier := PTerm; is_setoid := pt_Setoid |};
  rig_zero := PZ;
  rig_add := pt_add;
  rig_one := PO;
  rig_mul := pt_mul;
  rig_add_respects := fun _ _ Hs _ _ Ht => pe_add Hs Ht;
  rig_mul_respects := fun _ _ Hs _ _ Ht => pe_mul Hs Ht;
  rig_add_assoc := pe_add_assoc;
  rig_add_comm := pe_add_comm;
  rig_add_zero_l := pe_add_zero_l;
  rig_mul_assoc := pe_mul_assoc;
  rig_mul_one_l := pe_mul_one_l;
  rig_mul_one_r := pe_mul_one_r;
  rig_distr_l := pe_distr_l;
  rig_distr_r := pe_distr_r;
  rig_mul_zero_l := pe_mul_zero_l;
  rig_mul_zero_r := pe_mul_zero_r
|}.

Definition PolyRing : RingObject := {|
  ring_rig := PolyRig;
  ring_neg := pt_neg;
  ring_neg_respects := fun _ _ Hs => pe_neg Hs;
  ring_neg_l := pe_add_neg_l
|}.

Lemma poly_comm : ∀ a b : carrier (rig_setoid PolyRing),
  rig_mul PolyRing a b ≈ rig_mul PolyRing b a.
Proof. exact pe_mul_comm. Qed.

(** ** The coefficient inclusion and the indeterminate *)

Program Definition poly_const : K ~{Rng}~> PolyRing := {|
  rig_map := {| morphism := pt_const |}
|}.
Next Obligation. intros a b H; exact (pe_const H). Qed.
Next Obligation. simpl; exact (pt_refl PZ). Qed.
Next Obligation. intros a b; exact (pe_const_add a b). Qed.
Next Obligation. simpl; exact (pt_refl PO). Qed.
Next Obligation. intros a b; exact (pe_const_mul a b). Qed.

Definition poly_x : carrier (rig_setoid PolyRing) := pt_x.

End Polynomial.

Arguments PTerm {K}.
Arguments pt_const {K} a.
Arguments pt_x {K}.
Arguments pt_add {K} s t.
Arguments pt_neg {K} s.
Arguments pt_mul {K} s t.
Arguments pt_eq {K} s t.
Arguments pt_refl {K} s.
Arguments poly_x {K}.

(** ** Evaluation: the universal property in element form

    Given a ring [S], a homomorphism [phi : K ~> S] and an element
    [s : S] commuting with the image of [phi], every formal polynomial
    has a value in [S].  The commutation hypothesis is exactly what makes
    the fold respect [pe_mul_comm]; over a commutative target it is free,
    and the ℤ[x] instance below discharges it from the centrality of the
    integers in every ring. *)

Section Evaluation.

Context (K : RingObject).
Context (S : RingObject).
Context (phi : K ~{Rng}~> S).
Context (s : carrier (rig_setoid S)).

(* [Kcomm] and [Hcs] are explicit hypotheses of the lemmas that consume
   them rather than section variables: the file inherits Lib.v:13's
   [Default Proof Using "Type"], under which a section variable absent
   from a lemma's STATEMENT is not available to its proof, and both of
   these are used only inside proofs. *)
Notation Kcomm_hyp :=
  (∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a).
Notation Hcs_hyp :=
  (∀ a : carrier (rig_setoid K),
     rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s).

Fixpoint peval (t : @PTerm K) : carrier (rig_setoid S) :=
  match t with
  | pt_const a => rig_map phi a
  | pt_x       => s
  | pt_add u v => rig_add S (peval u) (peval v)
  | pt_neg u   => ring_neg S (peval u)
  | pt_mul u v => rig_mul S (peval u) (peval v)
  end.

(** *** The image of the evaluation is commutative

    Nothing below needs [S] itself to be commutative: what is needed is
    that any two values of [peval] commute, and that follows from the two
    hypotheses by an induction that never inspects [S] beyond its ring
    laws.  This is what lets ℤ[x] be free on one generator in the
    category of ALL unital rings, not only the commutative ones. *)

(* An element commuting with every coefficient and with [s] commutes with
   every value.  Five cases, one per former. *)
Lemma peval_comm_gen (a : carrier (rig_setoid S))
  (H1 : ∀ k, rig_mul S a (rig_map phi k) ≈ rig_mul S (rig_map phi k) a)
  (H2 : rig_mul S a s ≈ rig_mul S s a) (u : @PTerm K) :
  rig_mul S a (peval u) ≈ rig_mul S (peval u) a.
Proof.
  induction u as [ k | | u IHu v IHv | u IHu | u IHu v IHv ]; simpl.
  - exact (H1 k).
  - exact H2.
  - rewrite rig_distr_l, IHu, IHv; symmetry; apply rig_distr_r.
  - rewrite rng_mul_neg_r, IHu; symmetry; apply rng_mul_neg_l.
  - rewrite <- rig_mul_assoc, IHu, rig_mul_assoc, IHv.
    symmetry; apply rig_mul_assoc.
Qed.

(* The image of [phi] is commutative, because [K] is. *)
Lemma phi_image_comm (Kcomm : Kcomm_hyp) (k l : carrier (rig_setoid K)) :
  rig_mul S (rig_map phi k) (rig_map phi l)
    ≈ rig_mul S (rig_map phi l) (rig_map phi k).
Proof.
  rewrite <- !rig_map_mul.
  apply (proper_morphism (rig_map phi)), Kcomm.
Qed.

Lemma peval_comm (Kcomm : Kcomm_hyp) (Hcs : Hcs_hyp) (t u : @PTerm K) :
  rig_mul S (peval t) (peval u) ≈ rig_mul S (peval u) (peval t).
Proof.
  apply peval_comm_gen.
  - intro k.
    symmetry.
    exact (peval_comm_gen (rig_map phi k) (phi_image_comm Kcomm k)
             (symmetry (Hcs k)) t).
  - symmetry.
    exact (peval_comm_gen s Hcs (reflexivity _) t).
Qed.

(** *** Evaluation respects the quotienting relation

    Sixteen cases, one per constructor of [pt_eq].  Four are congruence
    for a former, the first of them saturating under K's own [≈]; seven
    are ring laws of [S], three of those additionally spending a
    preservation law of [phi], because the zero and the one of K[x] are
    constants rather than formers of their own; two are [phi]'s
    preservation of sums and of products; one — commutativity of
    multiplication — is [peval_comm]; and the last two are the target
    setoid's symmetry and transitivity. *)
Lemma peval_respects (Kcomm : Kcomm_hyp) (Hcs : Hcs_hyp) (t u : @PTerm K) :
  pt_eq t u → peval t ≈ peval u.
Proof.
  intro He.
  induction He as
    [ a b Hab
    | t t' u u' _ IHt _ IHu
    | t t' _ IHt
    | t t' u u' _ IHt _ IHu
    | t u v | t u | t | t
    | t u v | t u | t
    | t u v
    | a b | a b
    | t u _ IHtu
    | t u v _ IHtu _ IHuv ]; simpl.
  - exact (proper_morphism (rig_map phi) _ _ Hab).
  - exact (rig_add_respects S _ _ IHt _ _ IHu).
  - exact (ring_neg_respects S _ _ IHt).
  - exact (rig_mul_respects S _ _ IHt _ _ IHu).
  - exact (rig_add_assoc S _ _ _).
  - exact (rig_add_comm S _ _).
  - rewrite (rig_map_zero phi); apply rig_add_zero_l.
  - rewrite (rig_map_zero phi); apply (ring_neg_l S).
  - exact (rig_mul_assoc S _ _ _).
  - exact (peval_comm Kcomm Hcs t u).
  - rewrite (rig_map_one phi); apply rig_mul_one_l.
  - exact (rig_distr_l S _ _ _).
  - exact (rig_map_add phi a b).
  - exact (rig_map_mul phi a b).
  - exact (symmetry IHtu).
  - exact (transitivity IHtu IHuv).
Qed.

(** *** The extension, as a homomorphism of rings

    STRENGTH, MEASURED, and the two halves differ.  Preservation of
    ADDITION and of MULTIPLICATION close by [reflexivity]: those are
    clauses of the fixpoint.  Preservation of ZERO and of ONE does NOT —
    [rig_zero (PolyRing K)] is [pt_const (rig_zero K)], so the fold
    returns [phi (rig_zero K)], and reaching [rig_zero S] from there is
    [phi]'s own preservation law, an equation up to `≈`.  Only
    respectfulness has content beyond that. *)
Program Definition poly_extend (Kcomm : Kcomm_hyp) (Hcs : Hcs_hyp)
  : PolyRing K ~{Rng}~> S := {|
  rig_map := {| morphism := peval |}
|}.
Next Obligation.
  intros Kcomm Hcs t u He; exact (peval_respects Kcomm Hcs t u He).
Qed.
Next Obligation. intros Kcomm Hcs; simpl; exact (rig_map_zero phi). Qed.
Next Obligation. intros Kcomm Hcs t u; simpl; reflexivity. Qed.
Next Obligation. intros Kcomm Hcs; simpl; exact (rig_map_one phi). Qed.
Next Obligation. intros Kcomm Hcs t u; simpl; reflexivity. Qed.

(** The extension restricts to [phi] along the coefficient inclusion and
    sends the indeterminate to [s] — both DEFINITIONALLY, the fixpoint's
    first two clauses being those two equations.  This is the
    convertibility exception: the equations are between elements of [S]'s
    carrier, not between morphisms. *)
Example poly_extend_const (Kcomm : Kcomm_hyp) (Hcs : Hcs_hyp)
  (a : carrier (rig_setoid K)) :
  rig_map (poly_extend Kcomm Hcs) (pt_const a) = rig_map phi a := eq_refl.

Example poly_extend_x (Kcomm : Kcomm_hyp) (Hcs : Hcs_hyp) :
  rig_map (poly_extend Kcomm Hcs) (@poly_x K) = s := eq_refl.

(** *** Uniqueness

    Any ring homomorphism out of [K[x]] restricting to [phi] on constants
    and sending [x] to [s] IS the evaluation.  The induction has one case
    per former: the two base cases are the hypotheses, and the other
    three are the homomorphism laws of the competitor — preservation of
    sums, of negation (Rig.v's [RigHom_neg], a theorem rather than a
    field) and of products. *)
Lemma poly_extend_unique (g : PolyRing K ~{Rng}~> S)
  (Hconst : ∀ a, rig_map g (pt_const a) ≈ rig_map phi a)
  (Hx : rig_map g (@poly_x K) ≈ s) (t : @PTerm K) :
  rig_map g t ≈ peval t.
Proof.
  induction t as [ a | | t IHt u IHu | t IHt | t IHt u IHu ]; simpl.
  - exact (Hconst a).
  - exact Hx.
  - rewrite (rig_map_add g t u); exact (rig_add_respects S _ _ IHt _ _ IHu).
  - rewrite (RigHom_neg (PolyRing K) S g t).
    exact (ring_neg_respects S _ _ IHt).
  - rewrite (rig_map_mul g t u); exact (rig_mul_respects S _ _ IHt _ _ IHu).
Qed.

End Evaluation.

Arguments peval {K S} phi s t.
Arguments poly_extend {K S} phi s Kcomm Hcs.
Arguments poly_extend_unique {K S} phi s g Hconst Hx t.

(** ** The integers are central in every ring

    The evaluation hypothesis [Hcs] is discharged for ℤ[x] by this
    lemma: an integer multiple of 1 commutes with everything, so a
    homomorphism out of ℤ[x] into an ARBITRARY unital ring is available,
    not only into a commutative one. *)

Lemma rig_iter_central (S : RingObject) (n : nat)
  (b : carrier (rig_setoid S)) :
  rig_mul S (rig_iter S n) b ≈ rig_mul S b (rig_iter S n).
Proof.
  induction n as [ | n IH ]; simpl.
  - rewrite rig_mul_zero_l, rig_mul_zero_r; reflexivity.
  - rewrite rig_distr_r, rig_distr_l, IH.
    rewrite rig_mul_one_l, rig_mul_one_r; reflexivity.
Qed.

Lemma zring_central (S : RingObject) (z : Z) (b : carrier (rig_setoid S)) :
  rig_mul S (zring S z) b ≈ rig_mul S b (zring S z).
Proof.
  destruct z; simpl.
  - rewrite rig_mul_zero_l, rig_mul_zero_r; reflexivity.
  - apply rig_iter_central.
  - rewrite rng_mul_neg_l, rng_mul_neg_r, rig_iter_central; reflexivity.
Qed.

(** * Mac Lane §III.1 Exercise 7: K[x] among K-algebras *)

Section KAlgebra.

Context (K : CRng).

(** The polynomial ring, as a commutative K-algebra: the ring is
    [PolyRing], the commutativity is [poly_comm], and the structure map is
    the coefficient inclusion. *)
Definition PolyAlg : KAlgObject K := {|
  kalg_ring := PolyRing (`1 K);
  kalg_comm := poly_comm (`1 K);
  kalg_unit := poly_const (`1 K)
|}.

(** The underlying-set functor of the category of K-algebras. *)
Program Definition KAlg_Forget : KAlg K ⟶ Sets := {|
  fobj := fun A => rig_setoid (kalg_ring A);
  fmap := fun A B f => rig_map (`1 f)
|}.
Next Obligation. intros A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros A a; simpl; reflexivity. Qed.
Next Obligation. intros A B C f g a; simpl; reflexivity. Qed.

(** The K-algebra map evaluating at a chosen element of a K-algebra. *)
Definition kalg_eval (A : KAlgObject K) (a : carrier (rig_setoid (kalg_ring A)))
  : PolyAlg ~{KAlg K}~> A.
Proof.
  unshelve eexists.
  - refine (poly_extend (kalg_unit A) a (`2 K) _).
    intro c; exact (kalg_comm A a (rig_map (kalg_unit A) c)).
  - intro c; simpl; reflexivity.
Defined.

(** Mac Lane's Exercise 7, in element form: the pair ⟨K[x], x⟩ is
    universal among K-algebras with a chosen element. *)
Definition poly_universal_element : AUniversalElement KAlg_Forget PolyAlg.
Proof.
  unshelve econstructor.
  - exact (@poly_x (`1 K)).
  - intros A a.
    unshelve econstructor.
    + exact (kalg_eval A a).
    + simpl; reflexivity.
    + intros g Hg t; simpl.
      symmetry.
      apply (poly_extend_unique (kalg_unit A) a (`1 g)).
      * intro c; symmetry; exact (`2 g c).
      * exact Hg.
Defined.

(** The same content in the bundled form, and hence as a representation:
    the underlying-set functor of K-algebras is represented by K[x]. *)
Definition poly_universal_element_bundled : UniversalElement KAlg_Forget :=
  UniversalElement_of_AUniversalElement poly_universal_element.

Definition poly_representation
  : @Curried_Hom (KAlg K) PolyAlg ≅[[KAlg K, Sets]] KAlg_Forget :=
  ue_representation KAlg_Forget PolyAlg poly_universal_element.

Definition poly_representable : Representable KAlg_Forget :=
  Representable_of_UniversalElement poly_universal_element_bundled.

(** ... and as a universal arrow from the one-point setoid, in both of
    Theory/Universal/Arrow.v's encodings. *)
Definition poly_auniversal_arrow
  : AUniversalArrow SetsOne KAlg_Forget PolyAlg :=
  AUniversalArrow_of_AUniversalElement KAlg_Forget PolyAlg
    poly_universal_element.

Definition poly_universal_arrow : UniversalArrow SetsOne KAlg_Forget.
Proof.
  unshelve eapply (universal_arrow_from_UMP SetsOne KAlg_Forget PolyAlg).
  - exact (@universal_arrow _ _ _ _ _ poly_auniversal_arrow).
  - intros A f.
    unshelve econstructor.
    + exact (unique_obj (@universal_arrow_universal _ _ _ _ _
                           poly_auniversal_arrow A f)).
    + symmetry.
      exact (unique_property (@universal_arrow_universal _ _ _ _ _
                                poly_auniversal_arrow A f)).
    + intros v Hv.
      exact (uniqueness (@universal_arrow_universal _ _ _ _ _
                           poly_auniversal_arrow A f) v (symmetry Hv)).
Defined.

End KAlgebra.

(** * ℤ[x]: the free unital ring on one generator *)

Definition ZPoly : RingObject := PolyRing Int_Ring.

(** Evaluation at an element of an ARBITRARY unital ring: the
    commutation hypothesis is discharged by [zring_central], so no
    commutativity of the target is required. *)
Definition zpoly_eval (S : RingObject) (b : carrier (rig_setoid S))
  : ZPoly ~{Rng}~> S.
Proof.
  refine (poly_extend (rng_from_Z S) b Int_Ring_commutative _).
  intro z; simpl; symmetry; apply zring_central.
Defined.

(** Every homomorphism out of ℤ[x] agrees with [zring] on the constants,
    because ℤ is initial: the restriction along [poly_const] is a
    homomorphism out of ℤ, and there is only one of those. *)
Lemma zpoly_hom_const (S : RingObject) (g : ZPoly ~{Rng}~> S) (z : Z) :
  rig_map g (@pt_const Int_Ring z) ≈ zring S z.
Proof.
  exact (rng_from_Z_unique S (rig_hom_compose g (poly_const Int_Ring)) z).
Qed.

(** Riehl §2.3 Example 2.3.4: the indeterminate as a universal element of
    the underlying-set functor of rings. *)
Definition zpoly_universal_element : AUniversalElement Rng_Forget ZPoly.
Proof.
  unshelve econstructor.
  - exact (@poly_x Int_Ring).
  - intros S b.
    unshelve econstructor.
    + exact (zpoly_eval S b).
    + simpl; reflexivity.
    + intros g Hg t; simpl.
      symmetry.
      apply (poly_extend_unique (rng_from_Z S) b g).
      * intro z; exact (zpoly_hom_const S g z).
      * exact Hg.
Defined.

Definition zpoly_universal_element_bundled : UniversalElement Rng_Forget :=
  UniversalElement_of_AUniversalElement zpoly_universal_element.

(** Riehl §2.1 Example 2.1.5(v): the forgetful functor Rng ⟶ Sets is
    represented by ℤ[x] — a natural isomorphism in [[Rng, Sets]], not
    merely the ∃! factorization property. *)
Definition zpoly_representation
  : @Curried_Hom Rng ZPoly ≅[[Rng, Sets]] Rng_Forget :=
  ue_representation Rng_Forget ZPoly zpoly_universal_element.

Definition zpoly_representable : Representable Rng_Forget :=
  Representable_of_UniversalElement zpoly_universal_element_bundled.

(** ... and as a universal arrow from the one-point setoid. *)
Definition zpoly_auniversal_arrow
  : AUniversalArrow SetsOne Rng_Forget ZPoly :=
  AUniversalArrow_of_AUniversalElement Rng_Forget ZPoly
    zpoly_universal_element.

Definition zpoly_universal_arrow : UniversalArrow SetsOne Rng_Forget.
Proof.
  unshelve eapply (universal_arrow_from_UMP SetsOne Rng_Forget ZPoly).
  - exact (@universal_arrow _ _ _ _ _ zpoly_auniversal_arrow).
  - intros S f.
    unshelve econstructor.
    + exact (unique_obj (@universal_arrow_universal _ _ _ _ _
                           zpoly_auniversal_arrow S f)).
    + symmetry.
      exact (unique_property (@universal_arrow_universal _ _ _ _ _
                                zpoly_auniversal_arrow S f)).
    + intros v Hv.
      exact (uniqueness (@universal_arrow_universal _ _ _ _ _
                           zpoly_auniversal_arrow S f) v (symmetry Hv)).
Defined.

(** * Monomorphisms of rings are injective *)

(** The probe Instance/Rng.v:70 records as missing.  Two elements of R
    are separated by the two homomorphisms out of ℤ[x] that send x to
    them; a monomorphism identifies those homomorphisms only if it
    identifies the elements. *)
Theorem rng_monic_injective {R S : RingObject} (f : R ~{Rng}~> S) :
  Monic f → ∀ a b : carrier (rig_setoid R),
    rig_map f a ≈ rig_map f b → a ≈ b.
Proof.
  intros Hm a b Hab.
  destruct Hm as [Hcancel].
  assert (Heq : f ∘ zpoly_eval R a ≈ f ∘ zpoly_eval R b).
  { intro t.
    transitivity (peval (rng_from_Z S) (rig_map f a) t).
    - apply (poly_extend_unique (rng_from_Z S) (rig_map f a)
               (f ∘ zpoly_eval R a)).
      + intro z; exact (zpoly_hom_const S (f ∘ zpoly_eval R a) z).
      + simpl; reflexivity.
    - symmetry.
      apply (poly_extend_unique (rng_from_Z S) (rig_map f a)
               (f ∘ zpoly_eval R b)).
      + intro z; exact (zpoly_hom_const S (f ∘ zpoly_eval R b) z).
      + simpl; symmetry; exact Hab. }
  exact (Hcancel ZPoly (zpoly_eval R a) (zpoly_eval R b) Heq (@poly_x Int_Ring)).
Qed.

(** Both directions, the forward one being Instance/Rng.v's. *)
Theorem rng_monic_iff_injective {R S : RingObject} (f : R ~{Rng}~> S) :
  Monic f ↔ (∀ a b : carrier (rig_setoid R),
               rig_map f a ≈ rig_map f b → a ≈ b).
Proof.
  split.
  - exact (rng_monic_injective f).
  - exact (rng_injective_monic f).
Qed.

(** * The commutation hypothesis is necessary

    [poly_extend] requires the chosen element to commute with the image
    of the structure map.  That is not an artifact of the fold: the
    indeterminate is central in K[x] by construction, so its image under
    ANY ring homomorphism out of K[x] commutes with the image of every
    coefficient.  This is what makes Awodey's adjunction a statement
    about COMMUTATIVE rings (Instance/Rng/Pointed.v), and it is proved
    rather than asserted. *)

Lemma poly_hom_value_central (K S : RingObject)
  (g : PolyRing K ~{Rng}~> S) (c : carrier (rig_setoid K)) :
  rig_mul S (rig_map g (@poly_x K)) (rig_map g (@pt_const K c))
    ≈ rig_mul S (rig_map g (@pt_const K c)) (rig_map g (@poly_x K)).
Proof.
  rewrite <- !rig_map_mul.
  apply (proper_morphism (rig_map g)).
  exact (pe_mul_comm K _ _).
Qed.

(** The same, read through the structure map a K-algebra hom restricts
    to: the value at x commutes with everything coming from K. *)
Corollary poly_extend_commutation_necessary (K S : RingObject)
  (g : PolyRing K ~{Rng}~> S) (c : carrier (rig_setoid K)) :
  rig_mul S (rig_map g (@poly_x K))
            (rig_map (rig_hom_compose g (poly_const K)) c)
    ≈ rig_mul S (rig_map (rig_hom_compose g (poly_const K)) c)
                (rig_map g (@poly_x K)).
Proof. exact (poly_hom_value_central K S g c). Qed.

(** * Non-degeneracy *)

(** ** The coefficient inclusion is injective

    Evaluating in K itself — [phi] the identity, [s] the zero — returns a
    constant's coefficient, so no two coefficients are identified.  The
    only hypothesis is commutativity of K, which is what makes [K[x]] the
    polynomial ring rather than a quotient of it: over a NON-commutative
    K the constructor [pe_mul_comm] forces [const (ab) ≈ const (ba)], so
    this is the one place where the standing assumption is load-bearing
    rather than decorative. *)

Lemma poly_const_injective (K : RingObject)
  (Kcomm : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (a b : carrier (rig_setoid K)) :
  pt_eq (@pt_const K a) (@pt_const K b) → a ≈ b.
Proof.
  intro H.
  refine (peval_respects K K (@rig_hom_id K) (rig_zero K) Kcomm _
            (@pt_const K a) (@pt_const K b) H).
  intro c; simpl.
  rewrite rig_mul_zero_l, rig_mul_zero_r; reflexivity.
Qed.

Corollary poly_const_monic (K : CRng) : Monic (kalg_unit (PolyAlg K)).
Proof.
  apply rng_injective_monic.
  exact (poly_const_injective (`1 K) (`2 K)).
Qed.

(** ** The indeterminate is not a constant

    If x were the constant k, then in EVERY commutative K-algebra every
    chosen element would equal the image of k; taking the algebra to be K
    itself and the chosen element to be 0 and then 1 collapses the ring.
    The hypothesis is exactly non-triviality of K. *)

Lemma poly_x_not_constant (K : RingObject)
  (Kcomm : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hnt : rig_one K ≈ rig_zero K → False)
  (k : carrier (rig_setoid K)) :
  pt_eq (@poly_x K) (@pt_const K k) → False.
Proof.
  intro H.
  assert (H0 : rig_zero K ≈ k).
  { refine (peval_respects K K (@rig_hom_id K) (rig_zero K) Kcomm _
              (@poly_x K) (@pt_const K k) H).
    intro c; simpl.
    rewrite rig_mul_zero_l, rig_mul_zero_r; reflexivity. }
  assert (H1 : rig_one K ≈ k).
  { refine (peval_respects K K (@rig_hom_id K) (rig_one K) Kcomm _
              (@poly_x K) (@pt_const K k) H).
    intro c; simpl.
    rewrite rig_mul_one_l, rig_mul_one_r; reflexivity. }
  apply Hnt.
  rewrite H1, <- H0; reflexivity.
Qed.

(** ** The witnesses over ℤ *)

Definition zconst (z : Z) : carrier (rig_setoid ZPoly) := @pt_const Int_Ring z.

Lemma Int_nontrivial : rig_one Int_Ring ≈ rig_zero Int_Ring → False.
Proof. simpl; unfold Z_eqT; discriminate. Qed.

Corollary zpoly_x_not_constant (k : Z) :
  pt_eq (@poly_x Int_Ring) (zconst k) → False.
Proof.
  exact (poly_x_not_constant Int_Ring Int_Ring_commutative Int_nontrivial k).
Qed.

Corollary zpoly_x_nonzero :
  pt_eq (@poly_x Int_Ring) (rig_zero ZPoly) → False.
Proof. exact (zpoly_x_not_constant 0%Z). Qed.

Corollary zpoly_x_not_one :
  pt_eq (@poly_x Int_Ring) (rig_one ZPoly) → False.
Proof. exact (zpoly_x_not_constant 1%Z). Qed.

(** Evaluation COMPUTES: the polynomial x² + 2x + 1 at 3 is 16.  This is
    the convertibility exception — an equation between elements of ℤ, not
    between morphisms. *)
Definition zpoly_sample : carrier (rig_setoid ZPoly) :=
  pt_add (pt_add (pt_mul (@poly_x Int_Ring) poly_x)
                 (pt_mul (zconst 2%Z) poly_x))
         (zconst 1%Z).

Example zpoly_eval_at_three :
  rig_map (zpoly_eval Int_Ring 3%Z) zpoly_sample = 16%Z := eq_refl.

Example zpoly_eval_at_zero :
  rig_map (zpoly_eval Int_Ring 0%Z) zpoly_sample = 1%Z := eq_refl.

Example zpoly_eval_at_neg_one :
  rig_map (zpoly_eval Int_Ring (-1)%Z) zpoly_sample = 0%Z := eq_refl.

(** The universal element is the indeterminate, and the mediating
    homomorphism sends it to the chosen element — both by [eq_refl]. *)
Example zpoly_universal_elem_is_x :
  @aue_elem Rng Rng_Forget ZPoly zpoly_universal_element = @poly_x Int_Ring
  := eq_refl.

Example zpoly_mediator_at_x (S : RingObject) (b : carrier (rig_setoid S)) :
  rig_map (zpoly_eval S b) (@poly_x Int_Ring) = b := eq_refl.
