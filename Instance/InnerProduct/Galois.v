(** * The orthogonal complement as a Galois connection *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Limit.
Require Import Category.Instance.Grp.Galois.
Require Import Category.Adjunction.Right.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

(* The same two as Instance/Powerset.v:26-27 and Instance/Grp/Galois.v:26-27,
   in the same position and for the same reason: [relation] and [PreOrder]
   below must be the stdlib Prop-valued ones rather than Category.Lib's
   [crelation] ones, so they are required LAST. *)
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.5,
    book p. 97 (PDF p. 106), Exercise 1.  Item covered:
    [maclane:IV.5:ex1].  Read from the page image, verbatim:

      "1. Let H be a space with an inner product (e.g., Hilbert space).
       If P = Q is the set of all subsets S of H, ordered by inclusion,
       show that LS = RS = the orthogonal complement of S gives a Galois
       connection."

    ** WHICH ABSTRACTION OF "INNER PRODUCT", AND WHY

    None.  The exercise's content is the Galois connection, not the
    analysis, and the ONLY property of an inner product that the
    connection consumes is that the derived relation "x is orthogonal to
    y" is SYMMETRIC.  So the ambient structure taken here is a
    [PerpRel X]: a [Prop]-valued binary relation on the carrier of a
    setoid, symmetric, and respecting the setoid's own [≈].  Nothing
    else -- no addition, no scalars, no positivity, no completeness, no
    bilinearity -- appears anywhere below, and the issue's own Work item 1
    names this as the recommended scope ("an abstract 'orthogonality
    relation' satisfying the two properties actually used ... much
    cheaper").

    Two remarks on the fidelity of that abstraction.  First, symmetry is
    the right demand even in the complex case: a Hermitian form is
    conjugate-symmetric rather than symmetric, but the RELATION
    "⟨x,y⟩ = 0" is symmetric all the same, since a complex number
    vanishes exactly when its conjugate does.  Second, nothing here
    demands that the relation be irreflexive, or that only the zero
    vector be orthogonal to itself: over a field of characteristic two
    the standard form has isotropic vectors, and the development is
    indifferent to that.  The ℤ² witness in section (G) is chosen
    precisely so that the non-degenerate reading can be exhibited.

    ** THE NAME COLLISION, DISCLOSED

    Theory/Orthogonality.v:43 declares [Class Orthogonal] with the
    notation [e ⫫ m], for the unique-lifting relation between a morphism
    and a morphism in a factorization system.  That is a DIFFERENT
    notion -- a property of a commuting square in a category, with no
    perpendicularity operator and no power set anywhere near it -- and it
    is a homonym only.  Consequently no name in this file is spelled
    [Orthogonal], [orthogonal] or [⫫]; everything is spelled [perp].  At
    the base commit the tokens [perp], [Perp], [PerpRel], [perp_set],
    [ClosedPerp], [perp_galois], [PerpOp] and [InnerProduct] each occur in
    ZERO [.v] files, and the tokens "inner product", "orthogonal
    complement" and "sesquilinear" occur in none; the only "Hilbert" hits
    are four lines of prose (Theory/Algebra/Frobenius.v:95,
    Structure/Dagger.v:25, Theory/Adjunction.v:38,
    Structure/Monoidal/Symmetric.v:92).  So the issue's "Current state" is
    accurate on the ambient structure, and its two named dependencies have
    since landed and are CONSUMED here rather than rebuilt.

    ** WHAT IS CONSUMED

    From #380 (Instance/Proset/Galois.v:118): the record
    [GaloisConnection] with its six fields, [gal_unit] (:284) and
    [gal_counit] (:287), the two functors
    [GaloisFunctor_l]/[GaloisFunctor_r] and [GaloisAdjunction].  From #382
    (Instance/Powerset.v:285, :288, :295): [subset_le],
    [subset_le_preorder] and the thin category [Subsets X], over
    Instance/Sets/Powerset.v:981's [Powerset_Prop_obj X], the
    [≈]-respecting [Prop]-valued predicates.  From
    Instance/Proset/Limit.v:135: [op_rel], the reversed preorder, which is
    how Mac Lane's [Q^op] is written here.  From Instance/Grp/Galois.v:
    six constants of its section (A) (:430-498) -- [gal_lrl_below] (:441),
    [gal_lrl_above] (:445), [GalClosed_l] (:461), [GalClosed_r] (:462),
    [gal_closed_r_image] (:467) and [gal_closed_r_iff] (:485) -- which is
    general over an arbitrary Galois connection and mentions no group,
    together with [subset_le_antisym] (:508).  Those are APPLIED at the new
    connection; not one of them is restated.  Section (A) carries four
    constants besides those six ([gal_rlr_below], [gal_rlr_above],
    [gal_closed_l_image], [gal_closed_l_iff]); this connection needs none
    of them, because [gal_l] and [gal_r] here are ONE map, so each
    left-handed statement and its right-handed twin have become the same
    statement.

    That last [Require] is the expensive one, and the header gives the
    number rather than leaving a reader to discover it.  The transitive
    in-project closure of this file, excluding itself, is 130 modules; with
    Instance/Grp/Galois dropped it is 91, so consuming #381's section (A)
    costs 39 modules, and every other [Require] in the list costs zero
    (each was dropped alone and measured).  Section (A) is group-free, so
    its natural home is Instance/Proset/Galois.v beside the record it is
    about; but [subset_le_antisym] (:508) sits OUTSIDE that section and
    is used in the proofs below, so moving section (A) alone would return
    NONE of the 39 -- the [Require] would stay for that one lemma (an
    audit caught an earlier draft saying it would return them all).
    Returning them needs [subset_le_antisym] moved too, its natural home
    being Instance/Powerset.v beside [subset_le], or written inline as
    Instance/Powerset/Quantifier.v does.  Nothing is moved
    here: editing a merged module is out of scope for this issue, and the
    alternative -- restating those six short general lemmas under fresh
    names -- is what consuming a donor is supposed to avoid.

    ** THE SELF-DUALITY, WHICH IS WHAT MAKES THIS EXERCISE SHORT

    Mac Lane writes [L S = R S].  Here that is not a remark but an
    equation between the two fields of one record: [perp_galois_l_is_r]
    closes by [eq_refl].  Three further coincidences follow and are each
    pinned, because each of them is the kind of thing a reader would
    otherwise have to take on trust.

      - The two halves of the displayed biconditional are ONE function at
        swapped arguments.  [perp_transpose] carries [S ⊆ T^perp] to
        [T ⊆ S^perp]; [gal_to] and [gal_from] of the connection are that
        same term with its two subset arguments exchanged, and
        [perp_to_is_from_swapped] records it at [eq_refl].  The whole
        content of the biconditional is one permutation of two universal
        quantifiers followed by one appeal to symmetry of the relation.

      - The unit and the counit inhabit the SAME type and are the SAME
        term ([perp_unit_is_counit], [eq_refl]).  Read at the reversed
        order the counit inequality IS the unit inequality, which is why
        [S ⊆ S^⊥⊥] is the only closure inequality this connection has.

      - [GalClosed_l] and [GalClosed_r] of the connection are the same
        proposition ([ClosedPerp_is_GalClosed_l] and [_r], both
        [eq_refl]), so there is one notion of closedness rather than two.

    ** NO TRUNCATION IS NEEDED, WHICH IS A DIFFERENCE FROM #381

    Instance/Grp/Galois.v's [fixes] has to squash its defining condition,
    because that condition is [act A s x ≈ x] and [≈] is [Type]-valued
    while a member of [Powerset_Prop_obj] must be a [Prop].  Here the
    orthogonality relation is [Prop]-valued BY DECLARATION -- that is one
    of the two design decisions the [PerpRel] record makes -- so
    [Powerset_squash] appears nowhere in this file and every membership
    argument is a plain implication.  The setoid discipline is paid for
    instead by the [perp_respects] field, which is exactly what makes
    [perp_set S] a [SetoidMorphism] and hence an element of the power
    set.

    ** WHAT THE WITNESS IS, AND WHAT IT IS NOT

    Mac Lane's Hilbert space is out of reach: the tree carries no
    inner-product structure of any kind, and building one over the
    standard library reals would buy nothing the exercise asks for while
    costing the two reals axioms.  The witness in section (G) is ℤ² with
    the ordinary dot product [⟨(a,b),(c,d)⟩ = a·c + b·d], over stdlib [Z],
    axiom-free and computing.  It is a genuine bilinear form on a free
    module of rank two; what it is not is a Hilbert space, and no claim is
    made that it is.

    The alternative [bool × bool] over the two-element field was
    considered and not used, as a matter of illustration rather than
    necessity: over ℤ the values of the form are integers a reader can
    compute, and every negative closes by arithmetic.  Over F₂ the same
    statements are provable (measured out of tree by an audit, at the
    analogue of e₁), but there the isotropic vector [(1,1)] lies in the
    complement of its own singleton, which makes that base a poorer
    picture of an orthogonal complement.  Read [zz_e1_not_self_perp] at
    its strength: it is a statement about ONE point, and over ℤ the
    origin does lie in the complement of [{(0,0)}], so no universal
    "no point lies in its own complement" is claimed on either base.
    An earlier draft of this paragraph said the F₂ statement "would be
    refuted", contradicting the remark on isotropic vectors above; an
    audit measured it, and it was false.

    Every negative in section (G) is obtained by COMPUTATION on [Z]
    followed by [lia] or [injection], never by induction over a
    quotienting relation -- there is no such relation here, the power set
    being a predicate setoid rather than a quotient.

    ** UNIVERSES

    The general development binds [X : SetoidObject@{o o}] explicitly,
    with [Set < o] declared at section level.  That identification of a
    setoid's carrier and relation levels is the DONORS' and not this
    file's: [Powerset_Prop_obj@{o}] is declared over [SetoidObject@{o o}],
    and [Subsets] over the same, as #381 and #384 both measure.  [Set < o]
    is [Powerset_Prop_obj]'s own, its truth object having carrier [Prop].
    No constraint block below carries a universe EQUATION.

    ** WHAT IS NOT DELIVERED

    No inner product, no bilinear form as a structure, no vector space and
    no analysis; no completeness, no closed SUBSPACES (the closed elements
    here are closed subsets in the Galois sense, which over a genuine
    inner-product space would be the closed linear subspaces -- that
    identification needs the linear structure and is not attempted); no
    antisymmetric quotient, so [Subsets X] is a preorder and two
    [≈]-equal complements are distinct isomorphic objects; no lattice of
    closed elements and no orthomodularity; no naturality of any
    identification in [X] or in [P]; no functoriality of [perp_set] in the
    relation; no comparison with Structure/Dagger.v's dagger categories;
    and nothing is registered as an [Instance] -- a chosen orthogonality
    relation must not become globally resolvable, matching
    Instance/Powerset.v's own note on its meets and joins. *)

(* ------------------------------------------------------------------------ *)
(** ** (A) The orthogonality relation *)

(* The whole of the ambient structure.  [perp] is [Prop]-valued, so a
   membership condition built from it needs no truncation; [perp_sym] is
   the one property of an inner product the exercise consumes; and
   [perp_respects] is the setoid discipline, stated as the single
   implication that suffices -- the converse implication is that same
   field read at the two SYMMETRIC equivalences, so nothing is lost, and
   [perp_respects_iff] below states the biconditional the [Proper]
   spelling would give.  Note what that derivation does NOT spend:
   symmetry of [≈], not [perp_sym], is what turns one implication into
   two. *)
Record PerpRel@{o} (X : SetoidObject@{o o}) := {
  perp : carrier X → carrier X → Prop;
  perp_sym : ∀ x y, perp x y → perp y x;
  perp_respects : ∀ x x' y y', x ≈ x' → y ≈ y' → perp x y → perp x' y'
}.

Arguments perp {X} p x y.
Arguments perp_sym {X} p x y _.
Arguments perp_respects {X} p x x' y y' _ _ _.

(* The [Proper (equiv ==> equiv ==> iff)] reading, as a theorem rather
   than as a field: the record carries one implication, and both
   directions follow from it by symmetry of [≈]. *)
Lemma perp_respects_iff@{o +} {X : SetoidObject@{o o}} (P : PerpRel@{o} X)
  (x x' y y' : carrier X) (Hx : x ≈ x') (Hy : y ≈ y') :
  perp P x y ↔ perp P x' y'.
Proof.
  split; intro H.
  - exact (perp_respects P x x' y y' Hx Hy H).
  - refine (perp_respects P x' x y' y _ _ H); now symmetry.
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (B) The orthogonal complement, and the transposition *)

Section Perp.

(* [o] is the level at which the setoid, its power set and the inclusion
   preorder all live; [Subsets] demands [SetoidObject@{o o}], which is
   what identifies the carrier and relation levels, and [Set < o] is
   [Powerset_Prop_obj]'s.  [u] is the hom level of the thin categories,
   free of [o]. *)
Universe o u.
Constraint Set < o.

Context {X : SetoidObject@{o o}}.
Context (P : PerpRel@{o} X).

(* Mac Lane's orthogonal complement: the points orthogonal to every member
   of [S].  Respectfulness in the point is [perp_respects] read forward and
   backward, which is where [≈] of the ambient setoid is paid for. *)
Definition perp_set (S : carrier (Powerset_Prop_obj@{o} X)) :
  carrier (Powerset_Prop_obj@{o} X).
Proof using P.
  unshelve refine (@Build_SetoidMorphism@{o o o}
    (carrier X) (is_setoid X) Prop (is_setoid Powerset_Prop_truth@{o})
    (fun x => ∀ s, S s → perp P s x) _).
  intros x y Hxy; split; intros H s Hs.
  - refine (perp_respects P s s x y _ Hxy (H s Hs)); reflexivity.
  - refine (perp_respects P s s y x _ _ (H s Hs));
      [ reflexivity | now symmetry ].
Defined.

(* Membership, on the nose.  An equation between [Prop]s, that is between
   OBJECTS of the power set, not between morphisms. *)
Example perp_set_mem (S : carrier (Powerset_Prop_obj@{o} X))
  (x : carrier X) : perp_set S x = (∀ s, S s → perp P s x) := eq_refl.

(* THE TRANSPOSITION.  Its whole content is a permutation of the two
   universal quantifiers followed by one appeal to [perp_sym]; supplied by
   [:=] with no tactic.  Note that the statement is symmetric in [S] and
   [T], so this ONE term serves both halves of Mac Lane's biconditional
   and both legs of every packaging below. *)
Definition perp_transpose (S T : carrier (Powerset_Prop_obj@{o} X))
  (H : subset_le@{o} S (perp_set T)) : subset_le@{o} T (perp_set S) :=
  fun y Hy s Hs => perp_sym P y s (H s Hs y Hy).

(* Order-reversal, in the elementary form.  The connection reads it at
   [op_rel], where it becomes the covariant field the donor record asks
   for. *)
Lemma perp_set_antitone (S T : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le@{o} S T → subset_le@{o} (perp_set T) (perp_set S).
Proof using P. intros H x Hx s Hs; exact (Hx s (H s Hs)). Qed.

(* Both operators of a Galois connection respect the carriers' own [≈];
   here there is one operator, and order-reversal read both ways gives
   it. *)
Lemma perp_set_respects (S T : carrier (Powerset_Prop_obj@{o} X))
  (H : S ≈ T) : perp_set S ≈ perp_set T.
Proof using P.
  apply subset_le_antisym.
  - exact (perp_set_antitone T S (fun x Hx => proj2 (H x) Hx)).
  - exact (perp_set_antitone S T (fun x Hx => proj1 (H x) Hx)).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (C) The Galois connection *)

(* All six fields by name.  The second relation is the REVERSED inclusion,
   which is Mac Lane's [Q^op]: [L] and [R] are order-REVERSING maps, so
   the covariant record of #380 is inhabited only at the reversed order,
   exactly as Instance/Grp/Galois.v's connection is. *)
Definition perp_galois :
  GaloisConnection (@subset_le@{o} X) (op_rel (@subset_le@{o} X)) :=
  {| gal_l := perp_set
   ; gal_r := perp_set
   ; gal_mono_l := perp_set_antitone
   ; gal_mono_r := fun S T H => perp_set_antitone T S H
   ; gal_to   := fun S T H => perp_transpose T S H
   ; gal_from := fun S T H => perp_transpose S T H |}.

(* MAC LANE'S [L S = R S], as an equation between the two fields. *)
Example perp_galois_l_is_r :
  gal_l perp_galois = gal_r perp_galois := eq_refl.

Example perp_galois_l_is_perp_set :
  gal_l perp_galois = perp_set := eq_refl.

(* The two halves of the biconditional are the same function at swapped
   arguments -- so "if and only if" costs one term, not two. *)
Example perp_to_is_from_swapped (S T : carrier (Powerset_Prop_obj@{o} X))
  (H : subset_le@{o} T (perp_set S)) :
  gal_to perp_galois S T H = gal_from perp_galois T S H := eq_refl.

(* The two preorders the connection is read at. *)
Definition perp_PreOrder_l : PreOrder (@subset_le@{o} X) :=
  subset_le_preorder@{o} X.

Definition perp_PreOrder_r : PreOrder (op_rel (@subset_le@{o} X)) :=
  op_PreOrder (subset_le_preorder@{o} X).

(* ------------------------------------------------------------------------ *)
(** ** (D) Mac Lane's display (2), at this connection *)

(* [S] is contained in its double complement.  This is #380's [gal_unit]
   applied; no argument is written here. *)
Definition perp_unit (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le@{o} S (perp_set (perp_set S)) :=
  gal_unit perp_galois perp_PreOrder_r S.

(* The counit, at the SAME type: reading [gal_counit] at the reversed
   order turns it into the very inequality [gal_unit] gives, and the two
   are the same term. *)
Definition perp_counit (S : carrier (Powerset_Prop_obj@{o} X)) :
  subset_le@{o} S (perp_set (perp_set S)) :=
  gal_counit perp_galois perp_PreOrder_l S.

Example perp_unit_is_counit (S : carrier (Powerset_Prop_obj@{o} X)) :
  perp_unit S = perp_counit S := eq_refl.

(* The triple complement collapses.  In a preorder that is not a partial
   order the conclusion is mutual inclusion, which for these carriers IS
   the setoid's own [≈]: Instance/Grp/Galois.v:508 converts.  Both halves
   are #381's section (A) applied. *)
Lemma perp_triple (S : carrier (Powerset_Prop_obj@{o} X)) :
  perp_set (perp_set (perp_set S)) ≈ perp_set S.
Proof using P.
  apply subset_le_antisym.
  - exact (gal_lrl_above perp_PreOrder_r perp_galois S).
  - exact (gal_lrl_below perp_PreOrder_l perp_galois S).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (E) The closed elements *)

(* One inclusion of [S ≈ S^⊥⊥] is free ([perp_unit]), so the predicate
   records only the direction that is not. *)
Definition ClosedPerp (S : carrier (Powerset_Prop_obj@{o} X)) : Prop :=
  subset_le@{o} (perp_set (perp_set S)) S.

(* Section (A)'s two predicates coincide here, since [gal_l] and [gal_r]
   are one map and the second order is the first reversed. *)
Example ClosedPerp_is_GalClosed_r (S : carrier (Powerset_Prop_obj@{o} X)) :
  ClosedPerp S = GalClosed_r perp_galois S := eq_refl.

Example ClosedPerp_is_GalClosed_l (S : carrier (Powerset_Prop_obj@{o} X)) :
  ClosedPerp S = GalClosed_l perp_galois S := eq_refl.

(* Every complement is closed. *)
Definition perp_set_closed (S : carrier (Powerset_Prop_obj@{o} X)) :
  ClosedPerp (perp_set S) :=
  gal_closed_r_image perp_PreOrder_l perp_galois S.

(* The characterisation: the closed subsets are EXACTLY the orthogonal
   complements.  Section (A) supplies the mutual-inclusion form and
   [subset_le_antisym] upgrades it to the carriers' own [≈]. *)
Lemma closed_perp_iff (S : carrier (Powerset_Prop_obj@{o} X)) :
  ClosedPerp S ↔ ∃ T, perp_set T ≈ S.
Proof using P.
  split.
  - intro H.
    destruct (fst (gal_closed_r_iff perp_PreOrder_l perp_PreOrder_r
                     perp_galois S) H) as [T [H1 H2]].
    exists T; exact (subset_le_antisym H2 H1).
  - intros [T HT].
    refine (snd (gal_closed_r_iff perp_PreOrder_l perp_PreOrder_r
                   perp_galois S) _).
    exists T; exact (fun x Hx => proj2 (HT x) Hx,
                     fun x Hx => proj1 (HT x) Hx).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** (F) The two packagings *)

(* #380 applied: the functors and the adjunction are [:=] terms, and every
   coherence obligation of [Adjunction] is an equation between parallel
   arrows in a thin category, hence discharged uniformly there. *)
Definition PerpFunctor : Subsets@{o u} X ⟶ Proset@{o u} perp_PreOrder_r :=
  GaloisFunctor_l perp_PreOrder_l perp_PreOrder_r perp_galois.

Definition PerpFunctor_r : Proset@{o u} perp_PreOrder_r ⟶ Subsets@{o u} X :=
  GaloisFunctor_r perp_PreOrder_l perp_PreOrder_r perp_galois.

Definition perp_adjunction : PerpFunctor ⊣ PerpFunctor_r :=
  GaloisAdjunction perp_PreOrder_l perp_PreOrder_r perp_galois.

Example PerpFunctor_obj (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[PerpFunctor] S = perp_set S := eq_refl.

Example PerpFunctor_r_obj (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[PerpFunctor_r] S = perp_set S := eq_refl.

(* Mac Lane's own typing.  Theorem 1 types the two maps as [L : P → Q^op]
   and [R : Q^op → P], and Adjunction/Right.v:342's [AdjointOnTheRight S T]
   -- for [S : A^op ⟶ X] and [T : X^op ⟶ A], with the hom-set isomorphism
   [A(a, T x) ≅ X(x, S a)] -- is exactly that shape.  With [P = Q] and
   [L = R] both slots are filled by ONE functor, so the pair is adjoint to
   itself on the right, which is the categorical reading of "LS = RS".

   Prior art, measured, and the tree-wide list is complete: this is NOT the
   class's first inhabitant with the two slots equal.  Adjunction/Right.v
   carries three -- [Id_AdjointOnTheRight] (:583, labelled DEGENERATE
   there, and its two slots are [Id[C^op]] and [Id[C]], which are not the
   same term), [Chain3_AdjointOnTheRight] (:651, whose two functors
   differ) and [Powerset_AdjointOnTheRight] (:717, at a coinciding pair);
   Structure/Monoidal/Dual.v:441's [dual_self_adjoint_on_the_right] is a
   fourth, also at a coinciding pair; and Instance/Grp/Galois.v:883's
   [group_action_AdjointOnTheRight] -- in a file this one REQUIRES -- is a
   fifth, whose slots [StabOp] and [FixedOp] differ.  So two of the five
   precede this one at a coinciding pair.  What is new here is a
   self-adjoint witness in a THIN category arising from a symmetric
   RELATION, and the observation that both legs of its hom-set isomorphism
   are one term. *)

#[local] Obligation Tactic := simpl; repeat intro; exact I.

Program Definition PerpOp :
  (Subsets@{o u} X)^op ⟶ Subsets@{o u} X := {|
  fobj := perp_set;
  fmap := fun S T f => perp_set_antitone T S f
|}.

Program Definition perp_AdjointOnTheRight :
  AdjointOnTheRight PerpOp PerpOp := {|
  aor := fun S T =>
    {| to   := {| morphism := fun h => perp_transpose S T h |}
     ; from := {| morphism := fun h => perp_transpose T S h |} |}
|}.

Example PerpOp_obj (S : carrier (Powerset_Prop_obj@{o} X)) :
  fobj[PerpOp] S = perp_set S := eq_refl.

(* Both legs of the hom-set isomorphism are [perp_transpose], at swapped
   indices.  Off the diagonal the two do not share a type, so this is the
   sharpest form the statement takes; compare
   Structure/Monoidal/Dual.v's [aor_to_is_from_swapped]. *)
Example perp_aor_to (S T : carrier (Powerset_Prop_obj@{o} X))
  (h : subset_le@{o} S (perp_set T)) :
  @to Sets _ _ (@aor _ _ _ _ perp_AdjointOnTheRight S T) h
    = perp_transpose S T h := eq_refl.

Example perp_aor_from (S T : carrier (Powerset_Prop_obj@{o} X))
  (h : subset_le@{o} T (perp_set S)) :
  @from Sets _ _ (@aor _ _ _ _ perp_AdjointOnTheRight S T) h
    = perp_transpose T S h := eq_refl.

End Perp.

Arguments perp_set {X} P S.
Arguments ClosedPerp {X} P S.

(* ------------------------------------------------------------------------ *)
(** ** (G) A witness: ℤ² with the dot product *)

(* The setoid of integer pairs, at ONE universe.  [eq_Setoid]
   (Lib/Setoid.v:65) is polymorphic in exactly the level [Subsets] needs,
   so [≈] here is Leibniz equality and every respectfulness obligation
   below is a substitution. *)
Definition zz_setoid@{wo} : SetoidObject@{wo wo} :=
  {| carrier := (Z * Z)%type ; is_setoid := eq_Setoid@{wo} (Z * Z)%type |}.

(* The ordinary dot product, and the orthogonality relation it induces. *)
Definition zdot (p q : Z * Z) : Prop :=
  (fst p * fst q + snd p * snd q = 0)%Z.

Definition ZZPerp@{wo} : PerpRel@{wo} zz_setoid@{wo}.
Proof.
  unshelve refine (@Build_PerpRel@{wo} zz_setoid@{wo} zdot _ _).
  - intros x y H; unfold zdot in *.
    rewrite (Z.mul_comm (fst y) (fst x)), (Z.mul_comm (snd y) (snd x));
      exact H.
  - intros x x' y y' Hx Hy H; simpl in Hx, Hy; subst; exact H.
Defined.

Example zz_perp_is_dot : perp ZZPerp = zdot := eq_refl.

(* Subsets of ℤ².  Respectfulness is a substitution, [≈] being [eq]. *)
Definition zz_sub@{wo} (p : Z * Z → Prop) :
  carrier (Powerset_Prop_obj@{wo} zz_setoid@{wo}).
Proof.
  unshelve refine (@Build_SetoidMorphism@{wo wo wo}
    (Z * Z)%type (is_setoid zz_setoid@{wo})
    Prop (is_setoid Powerset_Prop_truth@{wo}) p _).
  intros x y Hxy; simpl in Hxy; subst; split; exact (fun h => h).
Defined.

Definition zz_e1@{wo} : carrier (Powerset_Prop_obj@{wo} zz_setoid@{wo}) :=
  zz_sub@{wo} (fun v => v = (1%Z, 0%Z)).

Definition zz_yaxis@{wo} : carrier (Powerset_Prop_obj@{wo} zz_setoid@{wo}) :=
  zz_sub@{wo} (fun v => fst v = 0%Z).

Definition zz_xaxis@{wo} : carrier (Powerset_Prop_obj@{wo} zz_setoid@{wo}) :=
  zz_sub@{wo} (fun v => snd v = 0%Z).

(* THE COMPLEMENT OF THE SINGLETON {(1,0)} IS THE SECOND AXIS.  Both
   inclusions are one instantiation and one arithmetic step. *)
Lemma zz_perp_e1_is_yaxis : perp_set ZZPerp zz_e1 ≈ zz_yaxis.
Proof.
  apply subset_le_antisym.
  - intros x Hx; change (fst x = 0%Z).
    specialize (Hx (1%Z, 0%Z) eq_refl).
    change ((1 * fst x + 0 * snd x)%Z = 0%Z) in Hx; lia.
  - intros x Hx s Hs; change (fst x = 0%Z) in Hx.
    change (s = (1%Z, 0%Z)) in Hs; subst s.
    change ((1 * fst x + 0 * snd x)%Z = 0%Z); lia.
Qed.

(* Two named points, one in the complement and one out of it. *)
Example zz_perp_e1_contains : perp_set ZZPerp zz_e1 (0%Z, 5%Z).
Proof.
  intros s Hs; change (s = (1%Z, 0%Z)) in Hs; subst s.
  change ((1 * 0 + 0 * 5)%Z = 0%Z); reflexivity.
Qed.

Example zz_perp_e1_excludes :
  perp_set ZZPerp zz_e1 (2%Z, 0%Z) → False.
Proof.
  intro H; specialize (H (1%Z, 0%Z) eq_refl).
  change ((1 * 2 + 0 * 0)%Z = 0%Z) in H; lia.
Qed.

(* NON-DEGENERACY: a point is not orthogonal to itself, so the relation is
   not the total one and the connection is not the trivial one.  This is
   the statement the two-element field would refute. *)
Example zz_e1_not_self_perp :
  perp_set ZZPerp zz_e1 (1%Z, 0%Z) → False.
Proof.
  intro H; specialize (H (1%Z, 0%Z) eq_refl).
  change ((1 * 1 + 0 * 0)%Z = 0%Z) in H; lia.
Qed.

(* THE SINGLETON IS NOT CLOSED: its double complement is the first axis,
   which contains [(2,0)]. *)
Lemma zz_double_perp_e1_has_20 :
  perp_set ZZPerp (perp_set ZZPerp zz_e1) (2%Z, 0%Z).
Proof.
  intros s Hs.
  assert (fst s = 0%Z) as Hfs
    by (exact (proj1 (zz_perp_e1_is_yaxis s) Hs)).
  change ((fst s * 2 + snd s * 0)%Z = 0%Z); rewrite Hfs; lia.
Qed.

Theorem zz_e1_not_ClosedPerp : ClosedPerp ZZPerp zz_e1 → False.
Proof.
  intro H; pose proof (H (2%Z, 0%Z) zz_double_perp_e1_has_20) as Hin.
  change ((2%Z, 0%Z) = (1%Z, 0%Z)) in Hin.
  injection Hin; intros; lia.
Qed.

(* THE AXIS IS CLOSED, and the proof exercises the general
   characterisation rather than recomputing: it is a complement, and every
   complement is closed. *)
Theorem zz_yaxis_ClosedPerp : ClosedPerp ZZPerp zz_yaxis.
Proof.
  refine (snd (closed_perp_iff ZZPerp zz_yaxis) _).
  exists zz_e1; exact zz_perp_e1_is_yaxis.
Qed.

(* The complement of the second axis is the first, which pins the double
   complement of the singleton exactly. *)
Lemma zz_perp_yaxis_is_xaxis : perp_set ZZPerp zz_yaxis ≈ zz_xaxis.
Proof.
  apply subset_le_antisym.
  - intros x Hx; change (snd x = 0%Z).
    specialize (Hx (0%Z, 1%Z) eq_refl).
    change ((0 * fst x + 1 * snd x)%Z = 0%Z) in Hx; lia.
  - intros x Hx s Hs; change (snd x = 0%Z) in Hx.
    change (fst s = 0%Z) in Hs.
    change ((fst s * fst x + snd s * snd x)%Z = 0%Z).
    rewrite Hs, Hx; lia.
Qed.

(* The two axes are distinct subsets, so the witness is not degenerate on
   the axis that matters: the complement moves. *)
Example zz_axes_differ : zz_yaxis ≈ zz_xaxis → False.
Proof.
  intro H; pose proof (proj1 (H (0%Z, 1%Z)) eq_refl) as Hin.
  change (1%Z = 0%Z) in Hin; lia.
Qed.
