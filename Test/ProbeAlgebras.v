(* Probe file for the monoid ring, the tensor algebra and the exterior
   algebra: Instance/Rng/MonoidRing.v, Instance/Rng/GroupRing.v,
   Instance/Rng/Algebras/Associative.v and Instance/Vect/TensorAlgebra.v.

   Convention: Test/ProbeFunnyPoly.v, Test/ProbeSquare.v,
   Test/ProbeFreeGroupoid.v, Test/ProbePolynomial.v.  Each NEGATIVE is a
   [Fail] guarding a strength claim made in one of those files, and each
   is paired with a POSITIVE CONTROL that must succeed, so that a rename
   or a definitional change breaks this file loudly instead of turning the
   [Fail]s vacuously green.

   PROBE HYGIENE.  The import list below is the union of the four target
   files' imports, in their order, because a short prefix is exactly what
   makes a probe pass for the wrong reason: a missing coercion turns a
   [Fail] green with an "Illegal application" that has nothing to do with
   the claim being guarded (the episode recorded in
   Test/ProbeFieldFrac.v).  Each negative below was stripped of its [Fail]
   during development and the resulting error inspected: negatives 1 and 2
   are genuine universe inconsistencies naming the declared level
   ("Cannot enforce Set = big"), and negatives 3 to 6 are genuine
   conversion failures. *)

Require Import Coq.ZArith.ZArith.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Construction.Elements.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Rng.Algebras.
Require Import Category.Instance.Rng.Polynomial.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Matr.GL.
Require Import Category.Instance.Rng.MonoidRing.
Require Import Category.Instance.Rng.GroupRing.
Require Import Category.Instance.Vect.TensorAlgebra.

Monomorphic Universe big.
Monomorphic Constraint Set < big.

(** * 1-2: the [Set] pin on the multiplicative-monoid forgetful functor

    Instance/Rng/MonoidRing.v's header states that [Rig_Forget_Mon] —
    hence the [Rng_Forget_Mon] built from it — is instantiable only at
    rigs whose carrier and [≈] live in [Set], and that the restriction is
    the DONOR'S rather than one introduced there.  Both halves are pinned
    here.  The instrument is sanity-checked first: the large instance of
    the integers is itself well formed, so the rejections below are about
    the functor and not about the ring. *)

(* instrument check *)
Check (Int_Rig@{big big big} : RigObject@{big big big}).
Check (Int_Ring@{big big big} : RingObject@{big big big}).

(* positive control: the donor applies at the Set-level instance *)
Check (Rig_Forget_Mon (Int_Rig@{Set Set Set})).
Check (Rng_Forget_Mon (Int_Ring@{Set Set Set})).

(* NEGATIVE 1: the donor itself does not reach one universe up *)
Fail Check (Rig_Forget_Mon (Int_Rig@{big big big})).

(* NEGATIVE 2: and neither does the ring-level functor built from it *)
Fail Check (Rng_Forget_Mon (Int_Ring@{big big big})).

(** * 3-4: preservation of zero and one by the monoid ring's extension is
      NOT definitional

    Instance/Rng/MonoidRing.v records that the extension's action on
    SCALARS and on GENERATORS holds by [eq_refl] while its preservation of
    ZERO and of ONE holds only up to [≈].  The reason is that the zero and
    the one of R[M] are scalars, so the fold returns the structure map's
    value there.  Both halves are pinned.

    The statements below are at a VARIABLE ring, deliberately: at a
    concrete structure map the same equations can close by computation,
    and the claim being guarded is about the general case. *)

(* Written as top-level lambdas rather than in a [Section]: a section
   variable [S : RingObject] has its universes fixed at the [Context]
   command, and a later mention of [Rng_Forget_Mon S] in the same section
   is then rejected by the very pin that negatives 1 and 2 guard.  That
   structural consequence is exactly what Instance/Rng/MonoidRing.v's
   header records, and it is why the evaluation development in that file
   is at top level too. *)

(* positive controls: scalars and generators DO close by [eq_refl] *)
Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
           (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
           (Hcomm : MRComm phi psi) =>
         eq_refl : rig_map (mring_extend phi psi Hcomm) (mr_scal (rig_zero R))
                     = rig_map phi (rig_zero R)).

Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
           (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
           (Hcomm : MRComm phi psi) (m : carrier (mcar M)) =>
         eq_refl : rig_map (mring_extend phi psi Hcomm) (mr_gen m)
                     = mmap psi m).

(* NEGATIVE 3: preservation of zero is not definitional *)
Fail Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
                (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
                (Hcomm : MRComm phi psi) =>
              eq_refl
                : rig_map (mring_extend phi psi Hcomm)
                    (rig_zero (MonoidRing R M)) = rig_zero S).

(* NEGATIVE 4: nor is preservation of one *)
Fail Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
                (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
                (Hcomm : MRComm phi psi) =>
              eq_refl
                : rig_map (mring_extend phi psi Hcomm)
                    (rig_one (MonoidRing R M)) = rig_one S).

(* ...and both DO hold up to [≈], which is what the file claims *)
Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
           (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
           (Hcomm : MRComm phi psi) =>
         rig_map_zero (mring_extend phi psi Hcomm)).

Check (fun (R : RingObject) (M : MonSets) (S : RingObject)
           (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
           (Hcomm : MRComm phi psi) =>
         rig_map_one (mring_extend phi psi Hcomm)).

(** * 5-6: the same seam in the tensor algebra

    Instance/Vect/TensorAlgebra.v makes the identical claim for
    [tensor_extend], for the identical reason. *)

Section TensorStrictness.

Context (K : CRng) (V : RModObject (`1 K)) (A : AAlgObject K).
Context (f : AAlgLinear V A).

(* positive controls *)
Check (fun v => eq_refl
        : rig_map (`1 (tensor_extend A f)) (tt_gen v) = alin_map f v).
Check (fun a => eq_refl
        : rig_map (`1 (tensor_extend A f)) (tt_scal a)
            = rig_map (aalg_unit A) a).

(* NEGATIVE 5: preservation of zero is not definitional *)
Fail Check (eq_refl
  : rig_map (`1 (tensor_extend A f)) (rig_zero (TensorRing V))
      = rig_zero (aalg_ring A)).

(* NEGATIVE 6: nor is preservation of one *)
Fail Check (eq_refl
  : rig_map (`1 (tensor_extend A f)) (rig_one (TensorRing V))
      = rig_one (aalg_ring A)).

(* ...and both DO hold up to [≈] *)
Check (rig_map_zero (`1 (tensor_extend A f))).
Check (rig_map_one (`1 (tensor_extend A f))).

End TensorStrictness.

(** * Positive controls for the strict claims that DID close

    These are the claims the three files make at [eq_refl]; restated here
    so that a change breaking any of them breaks this file too. *)

Check (fun (K : CRng) (V : RModObject (`1 K)) (t : TTerm V) =>
         eq_refl : rig_map (`1 (ext_proj V)) t = t).

Check (fun (K : CRng) (V : RMod (`1 K)) =>
         eq_refl : fobj[TensorFunctor K] V = TensorAlg V).

Check (fun (M : MonSets) =>
         eq_refl : fobj[MonoidRingFunctor] M = ZMonRing M).

Check (fun (G : Grp) =>
         eq_refl : fobj[GroupRingFunctor] G = GrpRing G).

Check (fun (G : Grp) (g : carrier (grp_setoid G)) =>
         eq_refl : `1 (grp_map (grp_ring_insert G) g)
                     = @mr_gen Int_Ring (Grp_MonSets G) g).
