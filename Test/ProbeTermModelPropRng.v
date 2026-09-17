(* The six term-model congruences of the RING layer are [Prop] inductives,
   and the quotient-ring relation is a propositional truncation.

   Since the PR "algebraic carriers are sets" (2026-09-17) every [RigObject]
   carries [rig_prop] (Theory/Algebra/Rig.v), the property that its carrier's
   `≈` is logically equivalent to a [Prop]-valued relation.  The six
   relations that a free, monoid, polynomial, tensor, exterior or enveloping
   construction quotients by --

     [mr_eq]   Instance/Rng/MonoidRing.v,   [fr_eq]   Instance/Rng/Free.v,
     [pt_eq]   Instance/Rng/Polynomial.v,   [tt_eq]   Instance/Vect/TensorAlgebra.v,
     [et_eq]   Instance/Vect/TensorAlgebra.v, [uenv_eq] Adjunction/Enveloping.v

   -- ARE the [Prop]-valued relations those six rings supply.  Being in
   [Prop] they ELIMINATE ONLY INTO [Prop], which is the whole content of the
   change and is what the negatives below pin.

   THE POSITIVES ARE OF TWO KINDS, and the comments distinguish them rather
   than letting the reader assume.  NINE are CONTROLS OF THE CHANGE: the six
   [pequiv] readbacks, [rquot_of_mem_control], [rquot_zero_iff_control] and
   [rquot_pequiv_control].  None of them can even be STATED against the
   baseline -- [rig_prop], [pequiv] and [rquot_rel_of_mem] do not exist
   there, and [rquot_rel_zero_iff] concludes against the bare membership --
   which was measured by compiling them in
   `/Users/johnw/Products/category-theory/base-27f68f10` (master 27f68f10),
   where each is refused.  SEVEN are NOT-LOST CHECKS: the six mediator
   [_respects] lemmas APPLIED, and [lquot_is_rquot_control].  Those compile
   against the baseline unchanged -- measured in the same tree, rc=0 -- so
   what they show is that the statements did not move, not that the change
   is visible in them.  Both purposes are legitimate; only the second is
   what the word "control" would otherwise suggest.

   The seventh pair covers Instance/Rng/Quotient.v's [rquot_rel], which is
   NOT a moved inductive but a TRUNCATION: [idl_mem] stays [Type]-valued and
   the quotient's equality is [inhabited] of it, so a witness cannot be read
   back out into a [Type] goal (negative) while congruence to zero and the
   ring's own [pequiv] are unaffected (controls).

   WHY A SEPARATE FILE from Test/ProbeTermModelProp.v, which pins the same
   property for the five CMon-tower relations.  Its import list is the union
   of five files under Instance/Ab/ and Instance/Mod/; this one's is the
   union of six under Instance/Rng/, Instance/Vect/ and Adjunction/, and
   reaches Instance/Lie.v.  Merging them would put two different [te_*]
   constructor families (Instance/Ab/Tensor.v's and
   Instance/Vect/TensorAlgebra.v's) in one scope, and a Coq refusal is
   rendered with the short names in scope -- so the merged file's negatives
   would report different text than the one measured here, for no gain.

   METHOD.  A [Fail Lemma <statement>] would be vacuous: the statement of
   each [_respects] lemma is well formed whatever the relation's sort, and
   only the ELIMINATION is refused.  Each negative is therefore a
   [Fail Definition … := ltac:(induction He)], carrying the proof.  Each was
   stripped once, in a copy of this whole file, and confirmed to report

     Error: Cannot find the elimination combinator <rel>_rect, the
     elimination of the inductive definition <rel> on sort Type is probably
     not allowed.

   except the two [rquot_rel] negatives, whose measured texts are quoted at
   their own section below.

   The import list is the union of the six target files' own, plus
   Instance/Rng/Quotient.v's. *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Elements.
Require Import Category.Adjunction.Compose.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Fun.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Algebras.
Require Import Category.Instance.Rng.Algebras.Associative.
Require Import Category.Instance.Rng.Polynomial.
Require Import Category.Instance.Rng.MonoidRing.
Require Import Category.Instance.Rng.Free.
Require Import Category.Instance.Rng.Quotient.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Vect.TensorAlgebra.
Require Import Category.Instance.Lie.
Require Import Category.Adjunction.Enveloping.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(** ** 1. [mr_eq], Instance/Rng/MonoidRing.v *)

(* NEGATIVE.  The elimination into an arbitrary [Type]. *)
Fail Definition mr_eq_type_elim {R : RingObject} {M : MonSets}
  (s t : MRTerm R M) (He : mr_eq s t) : MRTerm R M :=
  ltac:(induction He; exact (mr_scal (rig_zero R))).

(* CONTROL.  The relation IS the monoid ring's `≈`, and is its own [Prop]
   mirror. *)
Example mr_pequiv_control {R : RingObject} {M : MonSets}
  (s t : MRTerm R M) (He : mr_eq s t) :
  @pequiv _ _ (rig_prop (MonoidRing R M)) s t := He.

(* NOT-LOST CHECK (measured: it also compiles against the baseline tree
   master 27f68f10, so it is not a control OF the change): the file's own
   [mreval_respects], APPLIED.  Its STATEMENT did not move -- respectfulness
   still reaches a [Type]-valued `≈` -- and only its proof now goes through
   [pequiv_to] at the target, which is exactly what this checks was not
   lost. *)
Example mr_respects_control {R : RingObject} {M : MonSets} {S : RingObject}
  (phi : R ~{Rng}~> S) (psi : M ~{MonSets}~> Rng_Forget_Mon S)
  (Hcomm : MRComm phi psi) (s t : MRTerm R M) (He : mr_eq s t) :
  mreval phi psi s ≈ mreval phi psi t :=
  mreval_respects phi psi Hcomm s t He.

(** ** 2. [fr_eq], Instance/Rng/Free.v *)

Fail Definition fr_eq_type_elim {A : AbObject}
  (s t : FRTerm A) (He : fr_eq s t) : FRTerm A :=
  ltac:(induction He; exact fr_zero).

(* NEGATIVE.  The mediator's respectfulness with the elimination attempted
   directly at the [Type]-valued `≈`, i.e. the script the file carried before
   the relation moved. *)
Fail Definition fr_eval_type_elim {A : AbObject} (R : RingObject)
  (h : A ~{Ab}~> Rng_Forget_Ab R) (s t : FRTerm A) (He : fr_eq s t) :
  fr_eval h s ≈ fr_eval h t :=
  ltac:(induction He).

Example fr_pequiv_control {A : AbObject} (s t : FRTerm A) (He : fr_eq s t) :
  @pequiv _ _ (rig_prop (FreeRngAbObject A)) s t := He.

(* NOT-LOST CHECK, as [mr_respects_control] above: measured to compile
   against the baseline tree too. *)
Example fr_respects_control {A : AbObject} (R : RingObject)
  (h : A ~{Ab}~> Rng_Forget_Ab R) (s t : FRTerm A) (He : fr_eq s t) :
  fr_eval h s ≈ fr_eval h t :=
  fr_eval_respects R h s t He.

(** ** 3. [pt_eq], Instance/Rng/Polynomial.v *)

Fail Definition pt_eq_type_elim {K : RingObject}
  (s t : @PTerm K) (He : pt_eq s t) : @PTerm K :=
  ltac:(induction He; exact pt_x).

Fail Definition peval_type_elim (K S : RingObject) (phi : K ~{Rng}~> S)
  (x : carrier (rig_setoid S)) (t u : @PTerm K) (He : pt_eq t u) :
  peval phi x t ≈ peval phi x u :=
  ltac:(induction He).

Example pt_pequiv_control {K : RingObject} (s t : @PTerm K)
  (He : pt_eq s t) :
  @pequiv _ _ (rig_prop (PolyRing K)) s t := He.

(* NOT-LOST CHECK, as [mr_respects_control] above. *)
Example pt_respects_control (K S : RingObject) (phi : K ~{Rng}~> S)
  (x : carrier (rig_setoid S))
  (Kcomm : ∀ a b : carrier (rig_setoid K),
     rig_mul K a b ≈ rig_mul K b a)
  (Hcs : ∀ a : carrier (rig_setoid K),
     rig_mul S x (rig_map phi a) ≈ rig_mul S (rig_map phi a) x)
  (t u : @PTerm K) (He : pt_eq t u) :
  peval phi x t ≈ peval phi x u :=
  peval_respects K S phi x Kcomm Hcs t u He.

(** ** 4. [tt_eq], Instance/Vect/TensorAlgebra.v *)

Fail Definition tt_eq_type_elim {K : CRng} {V : RModObject (`1 K)}
  (s t : TTerm V) (He : tt_eq s t) : TTerm V :=
  ltac:(induction He; exact (tt_scal (rig_zero (`1 K)))).

Fail Definition teval_type_elim (K : CRng) (V : RModObject (`1 K))
  (A : AAlgObject K) (f : AAlgLinear V A) (s t : TTerm V)
  (He : tt_eq s t) : teval A f s ≈ teval A f t :=
  ltac:(induction He).

Example tt_pequiv_control {K : CRng} {V : RModObject (`1 K)}
  (s t : TTerm V) (He : tt_eq s t) :
  @pequiv _ _ (rig_prop (TensorRing V)) s t := He.

(* NOT-LOST CHECK, as [mr_respects_control] above. *)
Example tt_respects_control (K : CRng) (V : RModObject (`1 K))
  (A : AAlgObject K) (f : AAlgLinear V A) (s t : TTerm V)
  (He : tt_eq s t) : teval A f s ≈ teval A f t :=
  teval_respects K V A f s t He.

(** ** 5. [et_eq], Instance/Vect/TensorAlgebra.v

    Moved in LOCKSTEP with [tt_eq]: [ee_base] embeds a whole [tt_eq], so the
    exterior relation could not stay in [Type] over a [Prop]-valued tensor
    relation and still make Λ(V) a quotient of T(V). *)

Fail Definition et_eq_type_elim {K : CRng} {V : RModObject (`1 K)}
  (s t : TTerm V) (He : et_eq s t) : TTerm V :=
  ltac:(induction He; exact (tt_scal (rig_zero (`1 K)))).

Example et_pequiv_control {K : CRng} {V : RModObject (`1 K)}
  (s t : TTerm V) (He : et_eq s t) :
  @pequiv _ _ (rig_prop (ExtRing V)) s t := He.

(* NOT-LOST CHECK, as [mr_respects_control] above. *)
Example et_respects_control (K : CRng) (V : RModObject (`1 K))
  (A : AAlgObject K) (f : AltLinear V A) (s t : TTerm V)
  (He : et_eq s t) : teval A (alt_lin f) s ≈ teval A (alt_lin f) t :=
  exteval_respects K V A f s t He.

(** ** 6. [uenv_eq], Adjunction/Enveloping.v *)

Fail Definition uenv_eq_type_elim {K : CRng} {L : LieObject K}
  (s t : UEnvTerm L) (He : uenv_eq s t) : UEnvTerm L :=
  ltac:(induction He; exact (uen_scal (rig_zero (`1 K)))).

Example uenv_pequiv_control {K : CRng} {L : LieObject K}
  (s t : UEnvTerm L) (He : uenv_eq s t) :
  @pequiv _ _ (rig_prop (UEnvRing L)) s t := He.

(* NOT-LOST CHECK, as [mr_respects_control] above. *)
Example uenv_respects_control (K : CRng) (L : LieObject K)
  (A : AAlgObject K) (f : LieHom L (lie_of_aalg A)) (s t : UEnvTerm L)
  (He : uenv_eq s t) : uenv_eval A f s ≈ uenv_eval A f t :=
  uenv_eval_respects K L A f s t He.

(** ** 7. [rquot_rel], Instance/Rng/Quotient.v: the TRUNCATION

    Unlike the six above, this relation is not a moved inductive.  [idl_mem]
    stays [Type]-valued -- its consumers read witnesses out of it -- and the
    quotient ring's equality is [inhabited] of it.  So the witness cannot be
    recovered into a [Type]-valued goal, and [rquot_rel_zero_iff] is stated
    up to [inhabited] rather than against the bare membership.

    NEGATIVE 7a was stripped and reports

      Error:
      Incorrect elimination in the inductive type "inhabited":
      the return type has sort "Type" while it should be SProp or Prop.
      Elimination of an inductive object of sort Prop
      is not allowed on a predicate in sort "Type"
      because proofs can be eliminated only to build proofs.

    NEGATIVE 7b was stripped and reports

      Error: In environment
      R : RingObject
      I : Ideal R
      x : R
      The term "rquot_rel_zero_iff I x" has type
       "rquot_rel I x (rig_zero R) ↔ inhabited (idl_mem I x)"
      while it is expected to have type
       "rquot_rel I x (rig_zero R) ↔ idl_mem I x". *)

(* NEGATIVE 7a.  The witness cannot be read back out. *)
Fail Definition rquot_rel_type_elim {R : RingObject} (I : Ideal R)
  (x y : carrier (rig_setoid R)) (H : rquot_rel I x y) :
  idl_mem I (ab_sub (ring_ab R) x y) :=
  ltac:(destruct H as [K]; exact K).

(* NEGATIVE 7b.  The biconditional is NOT available against the bare
   membership; it holds only up to the truncation. *)
Fail Definition rquot_zero_iff_untruncated {R : RingObject} (I : Ideal R)
  (x : carrier (rig_setoid R)) :
  rquot_rel I x (rig_zero R) ↔ idl_mem I x :=
  rquot_rel_zero_iff I x.

(* CONTROL.  The direction that loses nothing keeps its [Type]-valued
   hypothesis. *)
Example rquot_of_mem_control {R : RingObject} (I : Ideal R)
  (x : carrier (rig_setoid R)) (Hx : idl_mem I x) :
  rquot_rel I x (rig_zero R) := rquot_rel_of_mem I x Hx.

(* CONTROL.  The truncated biconditional, APPLIED. *)
Example rquot_zero_iff_control {R : RingObject} (I : Ideal R)
  (x : carrier (rig_setoid R)) :
  rquot_rel I x (rig_zero R) ↔ inhabited (idl_mem I x) :=
  rquot_rel_zero_iff I x.

(* CONTROL.  The quotient's `≈` IS [rquot_rel], and is its own [Prop]
   mirror. *)
Example rquot_pequiv_control {R : RingObject} (I : Ideal R)
  (x y : carrier (rig_setoid R)) (H : rquot_rel I x y) :
  @pequiv _ _ (rig_prop (QuotientRing I)) x y := H.

(* NOT-LOST CHECK (measured: it compiles against the baseline tree too,
   where both relations were [Type]-valued).  [lquot_rel] is truncated in
   lockstep with [rquot_rel], and this is the convertibility that lockstep
   preserves -- the one Instance/Rng/Quotient/OneSided.v's refutation rests
   on.  What it checks is that the lockstep did not break it, not that the
   change is visible in it. *)
Example lquot_is_rquot_control {R : RingObject} (I : Ideal R)
  (x y : carrier (rig_setoid R)) :
  lquot_rel (Ideal_LeftIdeal I) x y = rquot_rel I x y := eq_refl.

(** ** Instrument check, scope-free *)

Fail Example probe_term_model_rng_instrument : true = false := eq_refl.
