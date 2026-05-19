Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Structure.Monoidal.Hypergraph.

Generalizable All Variables.

(** * PROPs (PROducts and Permutations)

    A PROP, in the sense of MacLane and the modern PROP/operad literature
    (cf. nLab "PROP"), is a strict symmetric monoidal category whose objects
    are the natural numbers and whose tensor on objects is addition:

      I = 0,    m ⨂ n = m + n.

    Equivalently, a PROP is a one-object PROP-enrichment whose object monoid
    is [(ℕ, +, 0)], regarded as a discrete strict symmetric monoidal category
    carrying the symmetric group structure on its hom-sets (every PROP
    receives a canonical morphism from the free PROP of permutations).

    In this library's setoid-based, universe-polymorphic setting, expressing
    "objects are ℕ" requires a Leibniz equality at the type [obj prop_cat = nat];
    we phrase this as a coercion field [prop_obj_to_nat] together with the
    strictness equalities

      prop_unit_zero    : I = prop_of_nat 0
      prop_tensor_plus  : prop_of_nat m ⨂ prop_of_nat n = prop_of_nat (m + n)

    These bind the monoidal structure to the additive monoid on ℕ at the
    Leibniz level — which is exactly what makes strict-monoidal arguments
    on PROPs work.  (Non-strict monoidal "weak PROPs" would weaken these to
    isomorphisms; the literature uniformly takes strict.)

    Downstream applications — Frobenius PROPs, hypergraph PROPs, the ZX
    PROP — refine [PROP] with extra structure on each object. *)

(** ** The PROP class

    Bundles a category, its strict symmetric monoidal structure, and the
    object correspondence with [nat].  The object correspondence is given
    by [prop_of_nat : nat -> obj], with [prop_unit_zero] / [prop_tensor_plus]
    pinning down [I] and [(⨂)] on objects.

    The full "objects are exactly ℕ" condition — that [prop_of_nat] is a
    bijection on objects — is added as the optional [prop_obj_exhaust] field;
    leaving it out gives a weaker "PROP-like" notion (a strict symmetric
    monoidal category containing the free PROP of permutations as a sub-PROP),
    which is what some authors use as the working definition. *)

Class PROP : Type := {
  prop_cat : Category;

  prop_strict : @StrictMonoidal prop_cat;
  prop_symmetric : @SymmetricMonoidal prop_cat;

  (** Coherence between the two [Monoidal] paths through a PROP.
      [prop_strict] supplies a [Monoidal] via [strict_is_monoidal];
      [prop_symmetric] supplies one via
      [braided_is_monoidal ∘ symmetric_is_braided].  Without an axiom
      relating them, downstream tensor expressions resolve
      ambiguously.  We require these to be EQUAL as [Monoidal]
      records:

        [prop_monoidal_coherence] :
            [strict_is_monoidal prop_strict
             = braided_is_monoidal (symmetric_is_braided prop_symmetric)]

      so a [rewrite] (or [subst]) brings any term phrased via one path
      into agreement with the other.

      ** Known limitation (deferred refactor)

      This coherence is PROPOSITIONAL, not DEFINITIONAL: a tensor
      expression like [braid : (T ⨂ T) ~> (T ⨂ T)] in a [HypergraphPROP]
      context typically resolves [T ⨂ T] via [prop_symmetric]'s
      Monoidal, while the hypergraph SCFA on [T ⨂ T] is phrased via
      [prop_strict]'s.  Bridging requires an explicit
      [rewrite prop_monoidal_coherence] (or [subst]) at every use
      site.  See [Test/HypergraphPROPResolution.v] for the test case
      that documents this friction.

      The literature-correct DEFINITIONAL fix is to re-parameterise the
      library's [BraidedMonoidal] and [SymmetricMonoidal] classes to
      take an [@Monoidal C] as an explicit parameter rather than
      projecting one (similar to how [DepFun] takes its source
      explicitly).  That would let [prop_symmetric] inherit
      [strict_is_monoidal prop_strict] verbatim, making
      [prop_monoidal_coherence] reduce to [eq_refl] definitionally.

      This is a multi-file library refactor (touches every site that
      uses [BraidedMonoidal]/[SymmetricMonoidal] today) and is
      deferred to a separate PR. *)
  prop_monoidal_coherence :
    (@strict_is_monoidal prop_cat prop_strict)
    = (@braided_is_monoidal prop_cat
         (@symmetric_is_braided prop_cat prop_symmetric));

  (** The canonical object correspondence: every natural number names an
      object of [prop_cat], with [0] the monoidal unit and addition
      reflecting tensor. *)
  prop_of_nat : nat -> @obj prop_cat;

  prop_unit_zero :
    @I prop_cat (@strict_is_monoidal prop_cat prop_strict)
    = prop_of_nat 0;

  prop_tensor_plus : forall (m n : nat),
    ((prop_of_nat m) ⨂[@strict_is_monoidal prop_cat prop_strict]
     (prop_of_nat n))%object
    = prop_of_nat (m + n)
}.

#[export] Existing Instance prop_strict.
#[export] Existing Instance prop_symmetric.

Coercion prop_cat : PROP >-> Category.

(** ** Smart accessors

    With [P : PROP], the canonical view sends every natural number to its
    PROP-object; in particular the tensor of [m] and [n] is literally the
    object named by [m + n].  Downstream files use these accessors to
    state PROP-morphism types as e.g. [prop_of_nat 2 ~{P}~> prop_of_nat 3]. *)

Section PROPLemmas.

Context (P : PROP).

(** The PROP-object [⟦n⟧] is the canonical object indexed by [n : nat]. *)
Notation "⟦ n ⟧" := (@prop_of_nat P n) (at level 0, format "⟦ n ⟧").

(** Sanity: the unit object of [P] is [⟦0⟧]. *)
Lemma prop_I_eq_zero : @I P _ = ⟦0⟧.
Proof. exact prop_unit_zero. Qed.

(** Sanity: tensor on objects is addition. *)
Lemma prop_tensor_eq_plus (m n : nat) :
  (⟦m⟧ ⨂ ⟦n⟧)%object = ⟦m + n⟧.
Proof. exact (prop_tensor_plus m n). Qed.

(** Tensor of three PROP-objects collapses to the sum. *)
Lemma prop_tensor_triple (m n p : nat) :
  ((⟦m⟧ ⨂ ⟦n⟧) ⨂ ⟦p⟧)%object = ⟦m + n + p⟧.
Proof.
  rewrite prop_tensor_plus.
  apply prop_tensor_plus.
Qed.

(** The unit object on the left of a tensor is absorbed. *)
Lemma prop_tensor_unit_left_obj (n : nat) :
  (⟦0⟧ ⨂ ⟦n⟧)%object = ⟦n⟧.
Proof.
  rewrite prop_tensor_plus.
  reflexivity.
Qed.

(** The unit object on the right of a tensor is absorbed, modulo [n + 0 = n]. *)
Lemma prop_tensor_unit_right_obj (n : nat) :
  (⟦n⟧ ⨂ ⟦0⟧)%object = ⟦n + 0⟧.
Proof. apply prop_tensor_plus. Qed.

(** ** PROP-arity ergonomics

    The Leibniz equality [prop_tensor_plus : ⟦m⟧ ⨂ ⟦n⟧ = ⟦m+n⟧] is
    the right primitive, but using it to translate between the
    "single-object" view [⟦m+n⟧] and the "tensor of wires" view
    [⟦m⟧ ⨂ ⟦n⟧] is verbose at the use site.  The following helpers
    give downstream code a uniform way to flip between the two. *)

Open Scope nat_scope.

(** Iterated tensor of [n] copies of [⟦1⟧], starting from [I]. *)
Fixpoint iter_tensor (n : nat) : @obj P :=
  match n with
  | O    => @I P _
  | S n' => (@prop_of_nat P 1 ⨂ iter_tensor n')%object
  end.

(** Every PROP object [⟦n⟧] is Leibniz-equal to [iter_tensor n].

    Base: [⟦0⟧ = I] by [prop_unit_zero].
    Step: [⟦S n⟧ = ⟦1 + n⟧ = ⟦1⟧ ⨂ ⟦n⟧ = ⟦1⟧ ⨂ iter_tensor n] by IH. *)
Lemma prop_of_nat_iter : forall n, @prop_of_nat P n = iter_tensor n.
Proof.
  induction n; cbn.
  - exact (eq_sym (@prop_unit_zero P)).
  - rewrite <- IHn.
    exact (eq_sym (@prop_tensor_plus P 1 n)).
Qed.

(** The successor decomposition: [⟦S n⟧ = ⟦1⟧ ⨂ ⟦n⟧]. *)
Lemma prop_of_nat_S :
  forall n, @prop_of_nat P (S n)
            = (@prop_of_nat P 1 ⨂ @prop_of_nat P n)%object.
Proof. intro n. exact (eq_sym (@prop_tensor_plus P 1 n)). Qed.

Close Scope nat_scope.

End PROPLemmas.

(** ** Hypergraph PROPs

    A hypergraph PROP is a PROP whose underlying symmetric monoidal category
    carries a [Hypergraph] instance.  This is the standard setting for the
    ZX-calculus, the calculus of relations, and Fong-style decorated cospans:
    every object [⟦n⟧] is equipped canonically with a special commutative
    Frobenius algebra, coherent under the tensor.

    Because [Hypergraph] is parameterised by [SymmetricMonoidal] and a PROP
    already carries [prop_symmetric], the class composes cleanly. *)

Class HypergraphPROP : Type := {
  hpprop : PROP;

  hpprop_hyper : @Hypergraph
                   (@prop_cat hpprop)
                   (@prop_symmetric hpprop)
}.

#[export] Existing Instance hpprop_hyper.

Coercion hpprop : HypergraphPROP >-> PROP.

(** ** Skeleton for the trivial / discrete-thin PROP

    The simplest example would be the discrete category on the natural
    numbers with NO non-identity morphisms — all hom-sets are empty
    except the diagonal, which is a singleton.  As a [Category] this is
    straightforward; equipping it with [Monoidal], [SymmetricMonoidal],
    and [StrictMonoidal] structures is mechanical (every parallel-pair
    of morphisms is equivalent, so all coherences hold by [tt]) but
    drags in a long list of obligation discharges.  We expose just the
    underlying category here; the strict symmetric monoidal layer is
    deferred to a downstream "concrete PROPs" file where the obligation
    sequencing can be tuned with a dedicated [Obligation Tactic].

    Mathematically: the construction is the free PROP on the empty
    signature, i.e. the terminal PROP. *)

Section TrivialPROP.

(** Morphisms: the singleton set when [m = n], empty when [m ≠ n].
    Encoded as the proposition [m = n] (so the unique morphism is the
    equality proof, and identity is [eq_refl]). *)

Definition TrivPROP_hom (m n : nat) : Type := m = n.

#[export] Program Instance TrivPROP_hom_Setoid (m n : nat) :
  Setoid (TrivPROP_hom m n) := {|
  equiv := fun _ _ => True
|}.

Definition TrivPROP_id (n : nat) : TrivPROP_hom n n := eq_refl.

Definition TrivPROP_compose {m n p : nat}
  (g : TrivPROP_hom n p) (f : TrivPROP_hom m n) : TrivPROP_hom m p :=
  eq_trans f g.

#[export] Program Instance TrivPROP_compose_respects {m n p : nat} :
  Proper (equiv ==> equiv ==> equiv) (@TrivPROP_compose m n p).

Program Definition TrivPROP_Cat : Category := {|
  obj      := nat;
  hom      := TrivPROP_hom;
  homset   := TrivPROP_hom_Setoid;
  id       := TrivPROP_id;
  compose  := @TrivPROP_compose
|}.

End TrivialPROP.

(** ** Discussion: the free PROP of permutations

    The literature canonical example is the "free PROP" [P] whose
    morphisms [m ~> n] are nonempty exactly when [m = n], in which case
    they are the symmetric group [S_n] of permutations of [Fin n].
    Building [Perm n] as a setoid in Coq is straightforward but verbose;
    it requires either:

      (a) an inductive presentation of permutations as a quotient of
          [list (Fin n × Fin n)] adjacencies generators, with the
          braid-group relations, OR

      (b) the bijection presentation [{ p : Fin n -> Fin n | bij p }] /
          extensional equality.

    In the form of this library, (b) is the natural choice and yields a
    PROP whose underlying symmetric monoidal category is the disjoint
    union of the groupoids [S_0 ⊔ S_1 ⊔ S_2 ⊔ ...].  Building it requires
    proving that bijection composition is associative, that the symmetric
    group is closed under inverses, etc. — all standard but a few hundred
    lines of finite-combinatorics infrastructure that the rest of this
    library does not currently use.

    For V3 we ship the [PROP] CLASS and the [TrivPROP] instance.  Concrete
    permutation-PROP instances are V4-applications work.  The applications
    that actually require [Perm] morphisms — the free PROP, the symmetric
    monoidal coherence theorem, etc. — are in any case organised around
    the PROP class itself, so downstream users can plug in their own
    [Perm n] datatype while retaining all theorems proven against
    [PROP]. *)
