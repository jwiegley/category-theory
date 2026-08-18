Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
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
Require Import Category.Instance.Rng.Polynomial.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * Pointed rings, and the polynomial functor as a left adjoint

    Book: Awodey, "Category Theory", §9.3, Example 9.10, printed
          pp. 226-227 (PDF pp. 235-236) — awodey:9.3:example10
    nLab:      https://ncatlab.org/nlab/show/free+functor
    nLab:      https://ncatlab.org/nlab/show/pointed+object
    Wikipedia: https://en.wikipedia.org/wiki/Polynomial_ring

    THE STATEMENT.  A pointed ring is a ring together with a
    distinguished element; a homomorphism of pointed rings is a ring
    homomorphism carrying the point to the point.  Awodey's example says
    that the forgetful functor which drops the point has a left adjoint,
    sending a ring R to R[x] pointed at the indeterminate, and that the
    transposition is EVALUATION at the point: a homomorphism R ⟶ S and a
    choice of s in S amount to the same thing as a homomorphism of
    pointed rings (R[x], x) ⟶ (S, s), namely the one substituting s for
    x.  This is the adjunction whose unit is the coefficient inclusion
    and whose counit is evaluation, and it is the reason "adjoin an
    indeterminate" is a free construction.

    A SCOPE CORRECTION, DISCLOSED, AND PROVED NECESSARY.  The adjunction
    is stated here over COMMUTATIVE rings — Instance/Rng.v's [CRng] — and
    not over all of [Rng].  It is not a matter of taste.  Over an
    arbitrary ring the backward transpose does not exist: a homomorphism
    R[x] ⟶ S over R must send x to an element commuting with the whole
    image of R, since x is central in R[x] by construction, whereas an
    arbitrary point of an arbitrary ring commutes with nothing in
    particular.  That obstruction is a theorem and not an aside:
    Instance/Rng/Polynomial.v's [poly_hom_value_central] proves that
    EVERY ring homomorphism out of K[x] has its value at x commuting with
    the image of the coefficients, so the hypothesis discharged here by
    commutativity of the target is necessary and not an artifact of the
    proof.

    WHAT THE NON-COMMUTATIVE CASE WOULD NEED, named so that its absence
    is not read as an oversight.  The forgetful functor from pointed
    unital rings to unital rings does have a left adjoint; what it is
    NOT is R ↦ R[x].  The free object there is the free algebra on one
    NON-COMMUTING generator, R⟨x⟩ — the ring of words in x with
    coefficients from R, in which x is not required to commute with the
    coefficients — and that is a different construction from the one
    below, not a relaxation of it: its underlying object is a free
    R-bimodule on the words in x rather than a quotient of formal
    expressions by commutative-ring laws, and [pe_mul_comm] would have to
    be deleted from Instance/Rng/Polynomial.v's relation and the
    coefficient interchange rewritten around its absence.  It is a
    separate issue and no part of it is attempted here.

    (What IS available over all of [Rng] is the ONE-generator case with
    ℤ as the base, where the two constructions coincide: a single
    generator commutes with itself, and the integers are central in
    every unital ring, so ℤ⟨x⟩ IS ℤ[x] and it is free on one generator
    in the category of all unital rings.  That statement lives in
    Instance/Rng/Polynomial.v as [zpoly_universal_element], with
    [zring_central] supplying the centrality, and it is Riehl's Example
    2.1.5(v).)

    THE CATEGORY OF POINTED RINGS IS NOT NEW MACHINERY.  A pointed object
    of a category C with respect to an underlying-set functor
    U : C ⟶ Sets is precisely an object of Construction/Elements.v's
    category of elements of U: its objects are the pairs (A, a) with a an
    element of U A, and its morphisms are the C-morphisms f with
    U f a ≈ b — which is the point-preservation condition, verbatim.  So
    [CRngPt] is [Elements CRng_Forget], the forgetful functor is
    [Elements_proj], and both come with their laws already proved.  The
    hom-setoid of [Elements] compares only the underlying morphism, which
    is the right convention here: two homomorphisms of pointed rings are
    equal when they are equal as homomorphisms.

    WHAT IS DELIVERED.

      - [CRng_Forget], [CRngPt], [CRngPt_Forget];
      - [poly_pointed_universal_arrow], a universal arrow from every
        commutative ring to the forgetful functor, in the comma-packaged
        encoding of Theory/Universal/Arrow.v;
      - [PolyPointed], the left adjoint it induces, and
        [poly_pointed_adjunction : PolyPointed ⊣ CRngPt_Forget];
      - evaluation as the transpose: [poly_pointed_transpose_is_evaluation]
        identifies any morphism realizing the transposition with the
        evaluation homomorphism, and [poly_pointed_adj_transpose_evaluates]
        instantiates that at the adjunction's own backward transpose;
      - strength measurements, and a ℤ witness that computes.

    STRENGTHS, MEASURED.

      - [eq_refl]: the left adjoint's object part is the pointed
        polynomial ring ([PolyPointed_obj]); the universal arrow IS the
        coefficient inclusion ([poly_pointed_arrow_is_const]); the unit
        ACTS as that inclusion on every coefficient
        ([poly_pointed_unit_is_const]); and the point of the free object
        is the indeterminate ([poly_pointed_point_is_x]).
      - NOT [eq_refl], measured: the unit as a MORPHISM.
        [poly_pointed_unit A = poly_pointed_arrow A] is rejected — the
        unit's underlying homomorphism is a composite record, not the
        inclusion's record — so the [eq_refl] claim above is about the
        action and is stated that way.  Test/ProbePolynomial.v pins it.
      - `≈` only: the backward transpose.  It is
        [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows]
        is [Qed]-opaque, so it does not compute; what is proved is that
        it evaluates ([poly_pointed_adj_transpose_evaluates]).  This is
        the same seam Instance/Mod/Free.v records for the counit of the
        free-module adjunction.
      - `≈` only, and not for want of trying: the action of [PolyPointed]
        on a morphism, which [LeftAdjointFunctorFromUniversalArrows]
        defines by universal factorization rather than by a formula.
        That it relabels coefficients is [poly_pointed_fmap_const], a
        theorem.

    WHAT IS NOT DELIVERED.  No pointed-ring analogue for [Rng] — that
    needs R⟨x⟩, the free algebra on a non-commuting generator, which is a
    different construction and is described but not built (see above); no
    monad or Eilenberg-Moore reading of the induced
    comonad/monad; no statement that [PolyPointed] is faithful or that
    the adjunction is monadic; and no several-indeterminate version —
    R[x, y] would be the free pointed ring on R[x], which follows by
    composing the adjunction with itself, but the resulting object is not
    identified with a two-variable polynomial ring here. *)

(** ** The underlying-set functor of commutative rings *)

Program Definition CRng_Forget : CRng ⟶ Sets := {|
  fobj := fun A => rig_setoid (`1 A);
  fmap := fun A B f => rig_map (`1 f)
|}.
Next Obligation. intros A B f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros A a; simpl; reflexivity. Qed.
Next Obligation. intros A B C f g a; simpl; reflexivity. Qed.

(** ** Pointed commutative rings *)

(** Objects are pairs (A, a); morphisms are the ring homomorphisms
    carrying the point.  This is Construction/Elements.v's category of
    elements, not a fresh construction. *)
Definition CRngPt : Category := Elements CRng_Forget.

Definition CRngPt_Forget : CRngPt ⟶ CRng := Elements_proj CRng_Forget.

(** The hom-type is the point-preservation condition, definitionally. *)
Example CRngPt_hom_unfold (P Q : CRngPt) :
  (P ~{CRngPt}~> Q)
    = ∃ f : `1 P ~{CRng}~> `1 Q, rig_map (`1 f) (`2 P) ≈ `2 Q
  := eq_refl.

(** ** The polynomial ring, pointed at the indeterminate *)

Definition PolyCRng (A : CRng) : CRng := (PolyRing (`1 A); poly_comm (`1 A)).

Definition PolyPt (A : CRng) : CRngPt := (PolyCRng A; @poly_x (`1 A)).

(** The coefficient inclusion, as a morphism of commutative rings.  The
    membership witness of [CRng_Sub] is trivial. *)
Definition poly_pointed_arrow (A : CRng)
  : A ~{CRng}~> CRngPt_Forget (PolyPt A) :=
  (poly_const (`1 A); I).

(** The two packagings of the same construction agree on the nose: Mac
    Lane's K-algebra [PolyAlg] (Instance/Rng/Polynomial.v) and Awodey's
    pointed ring [PolyPt] are built on one [PolyRing], with one
    coefficient inclusion.  What differs is the category the universal
    property is stated in, not the object. *)
Example poly_packagings_agree_ring (A : CRng) :
  kalg_ring (PolyAlg A) = `1 (`1 (PolyPt A)) := eq_refl.

Example poly_packagings_agree_unit (A : CRng) :
  kalg_unit (PolyAlg A) = `1 (poly_pointed_arrow A) := eq_refl.

(** ** Awodey's universal property

    Given a pointed commutative ring (B, b) and a homomorphism h : A ⟶ B,
    substituting b for x is the one and only homomorphism of pointed
    rings (A[x], x) ⟶ (B, b) restricting to h on the coefficients.  The
    commutation hypothesis that [poly_extend] requires is discharged by
    commutativity of B. *)
Lemma poly_pointed_universal (A : CRng) (Q : CRngPt)
  (h : A ~{CRng}~> CRngPt_Forget Q) :
  ∃! g : PolyPt A ~{CRngPt}~> Q,
    h ≈ fmap[CRngPt_Forget] g ∘ poly_pointed_arrow A.
Proof.
  unshelve econstructor.
  - unshelve refine ((_; I); _).
    + refine (poly_extend (`1 h) (`2 Q) (`2 A) _).
      intro c; exact (`2 (`1 Q) (`2 Q) (rig_map (`1 h) c)).
    + simpl; reflexivity.
  - intro c; simpl; reflexivity.
  - intros v Hv t; simpl.
    symmetry.
    apply (poly_extend_unique (`1 h) (`2 Q) (`1 (`1 v))).
    + intro c; symmetry; exact (Hv c).
    + exact (`2 v).
Defined.

Definition poly_pointed_universal_arrow (A : CRng)
  : UniversalArrow A CRngPt_Forget :=
  universal_arrow_from_UMP A CRngPt_Forget (PolyPt A)
    (poly_pointed_arrow A) (poly_pointed_universal A).

(** ** The left adjoint and the adjunction

    Both come out of the generic machinery with no further proof — the
    route Construction/Free/Quiver.v and Instance/Mod/Free.v take. *)

Definition PolyPointed : CRng ⟶ CRngPt :=
  LeftAdjointFunctorFromUniversalArrows CRngPt_Forget
    poly_pointed_universal_arrow.

Definition poly_pointed_adjunction : PolyPointed ⊣ CRngPt_Forget :=
  AdjunctionFromUniversalArrows CRngPt_Forget poly_pointed_universal_arrow.

(** The left adjoint's object part is the pointed polynomial ring, and
    the universal arrow is the coefficient inclusion — both on the nose. *)
Example PolyPointed_obj (A : CRng) : PolyPointed A = PolyPt A := eq_refl.

Example poly_pointed_point_is_x (A : CRng) :
  `2 (PolyPointed A) = @poly_x (`1 A) := eq_refl.

Example poly_pointed_arrow_is_const (A : CRng) :
  @arrow _ _ A CRngPt_Forget (poly_pointed_universal_arrow A)
    = poly_pointed_arrow A := eq_refl.

(** The unit is DERIVED in Theory/Adjunction.v (it is the transpose of
    the identity), not a field, so what it computes to has to be checked
    — and the answer is a measurement, not a slogan.  What holds by
    [eq_refl] is its ACTION: the unit sends each coefficient to the
    corresponding constant.  What does NOT hold by [eq_refl] is the
    equation of MORPHISMS [poly_pointed_unit A = poly_pointed_arrow A]:
    the unit is [fmap[U] id ∘ arrow], whose underlying ring homomorphism
    is the record [rig_hom_compose rig_hom_id (poly_const _)], and that
    record is not the term [poly_const _] however equal the two maps are
    on elements.  Test/ProbePolynomial.v pins both sides. *)
Definition poly_pointed_unit (A : CRng)
  : A ~{CRng}~> CRngPt_Forget (PolyPointed A) :=
  @Category.Theory.Adjunction.unit _ _ _ _ poly_pointed_adjunction A.

Example poly_pointed_unit_is_const (A : CRng)
  (c : carrier (rig_setoid (`1 A))) :
  rig_map (`1 (poly_pointed_unit A)) c = @pt_const (`1 A) c := eq_refl.

(** ** Evaluation is the transpose

    Awodey's clause in the form the setoid presentation permits: any
    morphism of pointed rings realizing the transposition of h IS the
    evaluation homomorphism.  The backward transpose of the adjunction
    satisfies its hypothesis, so the corollary below applies it there. *)
Theorem poly_pointed_transpose_is_evaluation (A : CRng) (Q : CRngPt)
  (h : A ~{CRng}~> CRngPt_Forget Q)
  (g : PolyPt A ~{CRngPt}~> Q)
  (Hg : h ≈ fmap[CRngPt_Forget] g ∘ poly_pointed_arrow A)
  (t : @PTerm (`1 A)) :
  rig_map (`1 (`1 g)) t ≈ peval (`1 h) (`2 Q) t.
Proof.
  apply (poly_extend_unique (`1 h) (`2 Q) (`1 (`1 g))).
  - intro c; symmetry; exact (Hg c).
  - exact (`2 g).
Qed.

Corollary poly_pointed_adj_transpose_evaluates (A : CRng) (Q : CRngPt)
  (h : A ~{CRng}~> CRngPt_Forget Q) (t : @PTerm (`1 A)) :
  rig_map (`1 (`1 (from (@adj _ _ _ _ poly_pointed_adjunction A Q) h))) t
    ≈ peval (`1 h) (`2 Q) t.
Proof.
  apply poly_pointed_transpose_is_evaluation.
  symmetry.
  exact (iso_to_from (@adj _ _ _ _ poly_pointed_adjunction A Q) h).
Qed.

(** ** The left adjoint relabels coefficients

    [LeftAdjointFunctorFromUniversalArrows] defines [fmap] by universal
    factorization, not by a formula, so what the functor does to a
    constant has to be proved. *)
Lemma poly_pointed_fmap_const {A B : CRng} (u : A ~{CRng}~> B)
  (c : carrier (rig_setoid (`1 A))) :
  rig_map (`1 (`1 (fmap[PolyPointed] u))) (@pt_const (`1 A) c)
    ≈ @pt_const (`1 B) (rig_map (`1 u) c).
Proof.
  symmetry.
  exact (unique_property
           (ump_universal_arrows (poly_pointed_universal_arrow A)
              (@arrow _ _ B CRngPt_Forget
                 (poly_pointed_universal_arrow B) ∘ u)) c).
Qed.

(** ** The witness over ℤ

    The free pointed commutative ring on ℤ is ℤ[x] pointed at x, and
    substituting 3 for x evaluates polynomials.  The evaluation
    homomorphism is Instance/Rng/Polynomial.v's, exhibited here as an
    arrow of [CRngPt]. *)

Definition Int_pointed (b : Z) : CRngPt := (Int_CRng; b).

Definition zpoly_pointed_eval (b : Z)
  : PolyPt Int_CRng ~{CRngPt}~> Int_pointed b.
Proof.
  unshelve refine ((_; I); _).
  - exact (zpoly_eval Int_Ring b).
  - simpl; reflexivity.
Defined.

Example zpoly_pointed_eval_computes :
  rig_map (`1 (`1 (zpoly_pointed_eval 3%Z))) zpoly_sample = 16%Z := eq_refl.

Example zpoly_pointed_eval_at_x (b : Z) :
  rig_map (`1 (`1 (zpoly_pointed_eval b))) (@poly_x Int_Ring) = b := eq_refl.
