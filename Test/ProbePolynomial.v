(** * Boundary probes for the polynomial ring

    Companion to Instance/Rng/Polynomial.v and Instance/Rng/Pointed.v
    (issue #309, Mac Lane §III.1 Exercise 7, Awodey §9.3 Example 9.10,
    Riehl §2.1 Example 2.1.5(v) and §2.3 Example 2.3.4).  Those files
    make strength claims of two different grades — some definitional,
    some only up to [≈] — and the negative side of each is a boundary no
    in-tree consumer would notice breaking.  They are pinned here.  **If
    the [Fail] commands below stop failing, this file breaks the build.**

    Every negative is paired with a positive control that must SUCCEED: a
    [Fail] alone passes just as happily when a name has been renamed out
    from under it.  The instrument itself was checked out of band —
    wrapping [Fail] around a succeeding command reports "The command has
    not failed!" and stops compilation — and each negative below was
    compiled once with the [Fail] stripped, to confirm the error is the
    intended one and not a syntax, scope or resolution error.  Where the
    stripped error is NOT of the form "cannot unify" or "Unable to
    unify", the actual message is quoted at the probe.

    The import list below is Instance/Rng/Pointed.v's, in that file's
    order: a shortened or reordered prefix produces different errors and
    would make the probes report the wrong thing.

    THE THREE BOUNDARIES.

    (1) THE EXTENSION PRESERVES + AND · DEFINITIONALLY, BUT 0 AND 1 ONLY
    UP TO [≈].  [peval] is a fixpoint whose clauses ARE the additive and
    multiplicative homomorphism laws, so those two obligations close by
    [reflexivity].  The zero of K[x] is [pt_const (rig_zero K)], not a
    former of its own, so the fold returns the structure map's value at
    K's zero and reaching the target's zero is that map's own
    preservation law.  The header of Instance/Rng/Polynomial.v measures
    this; §1 pins it.  NOTE the probe is stated at a VARIABLE ring and
    structure map: over ℤ with the initial map the equation does close by
    [eq_refl], because [zring S 0] reduces to [rig_zero S], so a probe
    instantiated at ℤ would report the opposite of the truth.

    (2) THE ADJUNCTION'S BACKWARD TRANSPOSE DOES NOT COMPUTE.  It is
    [unique_obj (ump_universal_arrows …)] and [ump_universal_arrows]
    (Theory/Universal/Arrow.v) is [Qed]-opaque, so
    [poly_pointed_adj_transpose_evaluates] is stated up to [≈] and no
    [eq_refl] is claimed.  This is the same seam Instance/Mod/Free.v
    records for the counit of the free-module adjunction.

    (3) THE FREE OBJECT COMPUTES; THE UNIT COMPUTES ONLY IN ITS ACTION.
    The other side of the same boundary, and the reason (2) is a
    measurement rather than a blanket disclaimer: the left adjoint's
    object part, the point it carries and the universal arrow are all
    [eq_refl].  The unit is not — [poly_pointed_unit A] is
    [fmap[U] id ∘ arrow], a composite record — but its value at every
    coefficient is, which is the strength Instance/Rng/Pointed.v claims
    and no more. *)

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
Require Import Category.Instance.Rng.Pointed.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(** ** Instrument check

    A deliberately true conversion in the very context the negatives use.
    If this stops holding, the negatives below are measuring the context
    and not the boundary. *)

Example probe_instrument (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s) :
  rig_map (poly_extend phi s Kc Hc) (@poly_x K) = s := eq_refl.

(** ** (1) Addition and multiplication compute; zero and one do not *)

(* POSITIVE CONTROLS. *)

Example probe_extend_add (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s)
  (t u : @PTerm K) :
  rig_map (poly_extend phi s Kc Hc) (rig_add (PolyRing K) t u)
    = rig_add S (rig_map (poly_extend phi s Kc Hc) t)
                (rig_map (poly_extend phi s Kc Hc) u) := eq_refl.

Example probe_extend_mul (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s)
  (t u : @PTerm K) :
  rig_map (poly_extend phi s Kc Hc) (rig_mul (PolyRing K) t u)
    = rig_mul S (rig_map (poly_extend phi s Kc Hc) t)
                (rig_map (poly_extend phi s Kc Hc) u) := eq_refl.

(* NEGATIVES.  Stripped of [Fail], the first reports
     (cannot unify "poly_extend phi s Kc Hc (rig_zero (PolyRing K))" and
     "rig_zero S")
   and the second the corresponding statement for [rig_one].  What is on
   the left of each is the fold's value, [phi (rig_zero K)] after one
   step of reduction; what is on the right is the target's own zero. *)

Fail Example probe_extend_zero_not_eq_refl
  (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s) :
  rig_map (poly_extend phi s Kc Hc) (rig_zero (PolyRing K))
    = rig_zero S := eq_refl.

Fail Example probe_extend_one_not_eq_refl
  (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s) :
  rig_map (poly_extend phi s Kc Hc) (rig_one (PolyRing K))
    = rig_one S := eq_refl.

(* ... and both DO hold up to [≈], which is what the file claims. *)

Example probe_extend_zero_up_to_equiv
  (K S : RingObject) (phi : K ~{Rng}~> S)
  (s : carrier (rig_setoid S))
  (Kc : ∀ a b : carrier (rig_setoid K), rig_mul K a b ≈ rig_mul K b a)
  (Hc : ∀ a : carrier (rig_setoid K),
          rig_mul S s (rig_map phi a) ≈ rig_mul S (rig_map phi a) s) :
  rig_map (poly_extend phi s Kc Hc) (rig_zero (PolyRing K)) ≈ rig_zero S.
Proof. exact (rig_map_zero (poly_extend phi s Kc Hc)). Qed.

(* The ℤ instance behaves the OTHER way, which is why the probes above
   are stated at a variable ring: [zring S 0] reduces to [rig_zero S]. *)

Example probe_zpoly_zero_does_compute :
  rig_map (zpoly_eval Int_Ring 3%Z) (rig_zero ZPoly) = rig_zero Int_Ring
  := eq_refl.

(** ** (2) The backward transpose does not compute *)

(* Stripped of [Fail], this reports
     (cannot unify "projT1 (projT1 ((adj[poly_pointed_adjunction])⁻¹ h)) t"
     and "peval `1 (h) `2 (Q) t")
   — the opaque transpose against the evaluation fixpoint. *)

Fail Example probe_transpose_not_eq_refl (A : CRng) (Q : CRngPt)
  (h : A ~{CRng}~> CRngPt_Forget Q) (t : @PTerm (`1 A)) :
  rig_map (`1 (`1 (from (@adj _ _ _ _ poly_pointed_adjunction A Q) h))) t
    = peval (`1 h) (`2 Q) t := eq_refl.

(* POSITIVE CONTROL: the same statement up to [≈] is a theorem. *)

Example probe_transpose_up_to_equiv (A : CRng) (Q : CRngPt)
  (h : A ~{CRng}~> CRngPt_Forget Q) (t : @PTerm (`1 A)) :
  rig_map (`1 (`1 (from (@adj _ _ _ _ poly_pointed_adjunction A Q) h))) t
    ≈ peval (`1 h) (`2 Q) t.
Proof. exact (poly_pointed_adj_transpose_evaluates A Q h t). Qed.

(** ** (3) The free object, its point, the arrow and the unit do compute *)

Example probe_free_object (A : CRng) : PolyPointed A = PolyPt A := eq_refl.

Example probe_free_point (A : CRng) :
  `2 (PolyPointed A) = @poly_x (`1 A) := eq_refl.

Example probe_universal_arrow (A : CRng) :
  @arrow _ _ A CRngPt_Forget (poly_pointed_universal_arrow A)
    = poly_pointed_arrow A := eq_refl.

Example probe_unit (A : CRng) (c : carrier (rig_setoid (`1 A))) :
  rig_map (`1 (poly_pointed_unit A)) c = @pt_const (`1 A) c := eq_refl.

(* ... but only its ACTION.  The unit is [fmap[U] id ∘ arrow], whose
   underlying homomorphism is the composite RECORD
   [rig_hom_compose rig_hom_id (poly_const _)], and no amount of
   agreement on elements makes that the inclusion's own record.
   Stripped of [Fail] this reports
     (cannot unify "poly_pointed_unit A" and "poly_pointed_arrow A"). *)

Fail Example probe_unit_not_the_arrow (A : CRng) :
  poly_pointed_unit A = poly_pointed_arrow A := eq_refl.

(* POSITIVE CONTROL for that negative: the two ARE equal as morphisms of
   [CRng], which is an equation up to [≈] and holds. *)

Example probe_unit_equiv_arrow (A : CRng) :
  poly_pointed_unit A ≈ poly_pointed_arrow A.
Proof. intro c; reflexivity. Qed.

(** ** A closing negative of a different kind

    The universal element of [Rng_Forget] is the indeterminate on the
    nose, but the indeterminate is NOT the zero of ℤ[x] — the
    construction does not collapse.  The first is [eq_refl]; the second
    is a refutation, not a conversion, so it is stated as a theorem and
    not as a [Fail]: a [Fail] would only record that the two terms are
    not convertible, which is far weaker than their being provably
    distinct in the setoid. *)

Example probe_universal_element_is_x :
  @aue_elem Rng Rng_Forget ZPoly zpoly_universal_element = @poly_x Int_Ring
  := eq_refl.

Example probe_x_is_not_zero :
  (@poly_x Int_Ring ≈ rig_zero ZPoly) → False.
Proof. exact zpoly_x_nonzero. Qed.
