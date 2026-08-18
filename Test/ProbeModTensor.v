(** * Boundary probe: what is and is not definitional in the tensor
      product of modules

    Companion to Instance/Mod/Tensor.v and Instance/Vect/Tensor.v (Mac
    Lane §III.1, Riehl §2.3).  Those files make several strength claims —
    some things hold at Leibniz [=] or by [eq_refl], others only up to
    [≈] — and a strength claim that lives only in a header is a claim
    nothing in the build would notice losing.  This file pins the
    boundary in the manner of Test/ProbeFreeVect.v: **if the [Fail]
    commands here stop failing, this file breaks the build.**

    Both sides are pinned deliberately.  A [Fail] alone proves very
    little — it passes just as happily when the term is ill-typed for
    some unrelated reason, or when a name has been renamed out from under
    it.  So each negative probe is paired with a positive control which
    must SUCCEED, and the controls are the claims themselves.

    The instrument was checked before being trusted: wrapping [Fail]
    around a command that succeeds reports "The command has not failed!"
    and aborts compilation, so [Fail] here is not a no-op.  Each negative
    below was also run with the [Fail] stripped, and the error confirmed
    to be a genuine unification error rather than a syntax, scope or
    universe error; the diagnoses are recorded beside each probe.

    The four negatives and their causes:

      - THE QUOTIENT IS GENUINE.  Commutativity of a formal sum is a step
        of the generated congruence [mt_eq] and not a definitional
        equality of the underlying inductive: the two formal sums are
        distinct terms of [MTerm].  The positive control is [mte_comm].
        This is what makes the setoid presentation a quotient rather than
        a renaming, and it is why the mediator needs
        [tensor_med_respects] before it is a morphism at all.

      - THE BALANCED LAW IS NOT DEFINITIONAL EITHER.  (r·v) ⊗ w and
        v ⊗ (r·w) are distinct terms even at closed ℤ scalars, where both
        sides' scalar products reduce to numerals; they are identified
        only by [tensor_balanced], which composes the two action rules
        through the formal scalar.  Since it is exactly this law that
        makes the canonical map bilinear in the two-sided sense, the
        probe records that the whole of bilinearity in the second
        variable is quotient content, not computation.

      - THE FACTORIZATION'S VALUE IS ONLY UP TO [≈] WHEN THE TARGET'S
        SETOID SAYS SO.  Over ℤ the mediator's value at a closed
        generator IS a numeral, by [eq_refl] ([probe_med_computes]).
        Over ℚ it is not: [Qmult (1#2) (4#1)] reduces to the
        term [4#2], which is [Qeq]-equal to [2] and not Leibniz-equal to
        it.  The two probes together locate the boundary precisely — it
        is the SCALAR SETOID, not the mediator, that decides.

      - THE TRIANGLE IS AN EQUATION OF SETOIDS, NOT OF RECORDS.
        [fmap[Bilin] (tensor_med β) tensor_gen] and β agree at every
        argument, by [eq_refl] on the VALUE ([probe_triangle_value]), but
        the two [RBilinear] records are not the same term: postcomposition
        rebuilds the four law fields from [Program] obligations, which
        are [Qed]-opaque.  So the universal element's [unique_property]
        is stated, and can only be stated, in the hom-setoid of [Sets].

    Two strict successes ABOUT THE CLASS are pinned as well, because
    they are the unusual ones and a later refactor could silently lose
    them: the universal element's element IS [tensor_gen]
    ([probe_universal_element_is_gen]), and the mediator extracted from
    the class IS the fixpoint [tensor_med] ([probe_factor_is_med]).  Contrast
    Test/ProbeFreeVect.v, where the corresponding data (the counit, the
    free functor's action on arrows) does NOT compute, [ump_universal_arrows]
    being opaque; here the [Unique] record is built directly, so
    [unique_obj] reduces. *)

Require Import Coq.QArith.QArith.
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
Require Import Category.Instance.FdVect.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Vect.Tensor.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(* Index arguments supplied once, as NOTATIONS (so each unfolds to the
   constructor itself) — the device Instance/Mod/Free.v uses for its own
   witnesses; [Local Notation] does not cross files. *)
Local Notation zgen  := (@mt_gen Int_Ring Int_RMod Int_RMod).
Local Notation zplus := (@mt_plus Int_Ring Int_RMod Int_RMod).
Local Notation qgen  := (@mt_gen (field_ring Q_Field) Q_Vct Q_Vct).

(** ** Positive control: the mediator computes over ℤ

    [tensor_med] is a [Fixpoint] on formal expressions, so its value on a
    closed expression reduces all the way to a value of the target
    module's carrier. *)
Example probe_med_computes :
  cmon_map (rm_hom (tensor_med Int_mul_bilinear)) (zgen 2%Z 3%Z) = 6%Z
  := eq_refl.

(** ** Positive control: the class's mediator IS the fixpoint

    [tensor_factor] is [unique_obj] of the [Unique] record supplied to
    [tensor_universal_element], and that record is built directly rather
    than extracted from an opaque proof, so the projection reduces. *)
Example probe_factor_is_med :
  tensor_factor Int_mul_bilinear = tensor_med Int_mul_bilinear := eq_refl.

(** ** Positive control: the universal element's element IS ⊗ *)
Example probe_universal_element_is_gen :
  @aue_elem (RMod Int_Ring) (Bilin Int_RMod Int_RMod)
    (TensorMod Int_RMod Int_RMod)
    (tensor_universal_element Int_RMod Int_RMod) = tensor_gen := eq_refl.

(** ** Positive control: the triangle's VALUE computes

    Paired with the fourth negative below: what does not hold at Leibniz
    equality is the equation of RECORDS, not the equation of values. *)
Example probe_triangle_value (v w : carrier (cmon_setoid Int_RMod)) :
  rbl_map (fmap[Bilin Int_RMod Int_RMod]
             (tensor_med Int_mul_bilinear) tensor_gen) v w
    = rbl_map Int_mul_bilinear v w := eq_refl.

(** ** Negative: commutativity of a formal sum is not definitional

    The carrier is a plain inductive; commutativity is a constructor of
    the quotienting relation, which is the positive control. *)
Fail Example probe_plus_comm_definitional :
  zplus (zgen 1%Z 1%Z) (zgen 2%Z 2%Z)
    = zplus (zgen 2%Z 2%Z) (zgen 1%Z 1%Z) := eq_refl.

Example probe_plus_comm_up_to_equiv :
  mt_eq (zplus (zgen 1%Z 1%Z) (zgen 2%Z 2%Z))
        (zplus (zgen 2%Z 2%Z) (zgen 1%Z 1%Z)) :=
  mte_comm _ _.

(** ** Negative: the balanced law is not definitional

    3·2 and 3·1 both reduce to numerals here, so the two sides are the
    closed terms 6 ⊗ 1 and 2 ⊗ 3 — distinct constructors' arguments, and
    identified only by [tensor_balanced]. *)
Fail Example probe_balanced_definitional :
  zgen 6%Z 1%Z = zgen 2%Z 3%Z := eq_refl.

Example probe_balanced_up_to_equiv :
  mt_eq (zgen 6%Z 1%Z) (zgen 2%Z 3%Z) :=
  @tensor_balanced Int_Ring Int_RMod Int_RMod 3%Z 2%Z 1%Z.

(** ** Negative: over ℚ the mediator's value is only [Qeq]-equal

    [Qmult (1#2) (4#1)] reduces to [4#2].  The scalar setoid, not the
    mediator, is what makes this weaker than the ℤ case above. *)
Fail Example probe_q_med_definitional :
  cmon_map (rm_hom (tensor_med Q_mul_bilinear)) (qgen (1#2) (4#1)) = 2
  := eq_refl.

Example probe_q_med_up_to_equiv :
  cmon_map (rm_hom (tensor_med Q_mul_bilinear)) (qgen (1#2) (4#1)) ≈ 2.
Proof. exact q_tensor_med_computes. Qed.

(** ** Negative: the triangle is not an equality of records

    Postcomposition rebuilds [RBilinear]'s four law fields from
    [Program] obligations, which are [Qed]-opaque, so the two records
    are distinct terms with equal values. *)
Fail Example probe_triangle_definitional :
  fmap[Bilin Int_RMod Int_RMod] (tensor_med Int_mul_bilinear) tensor_gen
    = Int_mul_bilinear := eq_refl.

Example probe_triangle_up_to_equiv :
  fmap[Bilin Int_RMod Int_RMod] (tensor_med Int_mul_bilinear) tensor_gen
    ≈ Int_mul_bilinear.
Proof.
  exact (unique_property
           (@aue_universal (RMod Int_Ring) (Bilin Int_RMod Int_RMod)
              (TensorMod Int_RMod Int_RMod)
              (tensor_universal_element Int_RMod Int_RMod)
              Int_RMod Int_mul_bilinear)).
Qed.
