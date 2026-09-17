(* The five term-model congruences of the CMon tower are [Prop] inductives.

   Since the PR "algebraic carriers are sets" (2026-09-17) every [CMonObject]
   carries [cmon_prop] (Instance/CMon.v), the property that its carrier's `≈`
   is logically equivalent to a [Prop]-valued relation, and the five relations
   that a free or tensor construction quotients by --

     [ts_eq] Instance/Ab/Tensor.v,   [fa_eq] Instance/Ab/Free.v,
     [fv_eq] Instance/Mod/Free.v,    [mt_eq] Instance/Mod/Tensor.v,
     [bs_eq] Instance/Mod/Bimodule.v

   -- are the [Prop]-valued relations those five objects supply.  Being in
   [Prop] they ELIMINATE ONLY INTO [Prop], which is the whole content of the
   change and is what the negatives below pin.  The positive controls show
   that nothing is lost: each mediator's respectfulness is still one
   induction over the relation, run under [pequiv] and converted back with
   [pequiv_to], and each is APPLIED here rather than merely mentioned.

   METHOD.  A [Fail Lemma <statement>] would be vacuous: the statement of
   each [_respects] lemma is well formed whatever the relation's sort, and
   only the ELIMINATION is refused.  Each negative is therefore a
   [Fail Definition … := ltac:(induction He)], carrying the proof.  Each was
   stripped once, in a copy of this whole file, and confirmed to report

     Error: Cannot find the elimination combinator <rel>_rect, the
     elimination of the inductive definition <rel> on sort Type is probably
     not allowed.

   The import list is the union of the five target files' own. *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Adjunction.Parameter.
Require Import Category.Adjunction.Additive.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Continuity.
Require Import Category.Adjunction.Right.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.AbCategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Tensor.
Require Import Category.Instance.Ab.Free.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Free.
Require Import Category.Instance.Mod.Tensor.
Require Import Category.Instance.Mod.Bimodule.
Require Import Category.Theory.Algebra.Rig.
Require Import Coq.ZArith.ZArith.

Generalizable All Variables.

(** ** 1. [ts_eq], Instance/Ab/Tensor.v *)

(* Instance/Ab/Tensor.v and Instance/Mod/Tensor.v both export
   [tensor_med_fun] and [tensor_med_respects]; the abelian-group ones are
   qualified here because the module-level import order shadows them. *)

(* NEGATIVE.  The elimination into an arbitrary [Type]. *)
Fail Definition ts_eq_type_elim {G H : AbObject} (s t : tsum G H)
  (He : ts_eq s t) : tsum G H :=
  ltac:(induction He; exact ts_zero).

(* NEGATIVE.  The mediator's respectfulness with the elimination attempted
   directly at the [Type]-valued `≈`, i.e. the script the file carried before
   the relation moved. *)
Fail Definition ts_med_type_elim {G H K : AbObject}
  (β : Ab.Tensor.Bilinear G H K)
  (s t : tsum G H) (He : ts_eq s t) :
  Ab.Tensor.tensor_med_fun β s ≈ Ab.Tensor.tensor_med_fun β t :=
  ltac:(induction He).

(* NOT-LOST CHECK (it also compiles in the unchanged tree, so it is not a
   control of the change): the same conclusion, reached through [pequiv]
   inside the file's own [tensor_med_respects], APPLIED. *)
Example ts_control {G H K : AbObject} (β : Ab.Tensor.Bilinear G H K)
  (s t : tsum G H) (He : ts_eq s t) :
  Ab.Tensor.tensor_med_fun β s ≈ Ab.Tensor.tensor_med_fun β t :=
  Ab.Tensor.tensor_med_respects G H β s t He.

(* CONTROL.  The relation IS the tensor's `≈`, and is its own [Prop]
   mirror. *)
Example ts_pequiv_control {G H : AbObject} (s t : tsum G H)
  (He : ts_eq s t) :
  @pequiv _ _ (cmon_prop (AbTensor G H)) s t := He.

(** ** 2. [fa_eq], Instance/Ab/Free.v *)

Fail Definition fa_eq_type_elim {X : SetoidObject} (s t : FATerm X)
  (He : fa_eq s t) : FATerm X :=
  ltac:(induction He; exact fa_zero).

Fail Definition fa_eval_type_elim {X : SetoidObject} {A : AbObject}
  (h : X ~{Sets}~> cmon_setoid A) (s t : FATerm X) (He : fa_eq s t) :
  fa_eval h s ≈ fa_eval h t :=
  ltac:(induction He).

(* NOT-LOST CHECK, as [ts_control] above. *)
Example fa_control {X : SetoidObject} {A : AbObject}
  (h : X ~{Sets}~> cmon_setoid A) (s t : FATerm X) (He : fa_eq s t) :
  fa_eval h s ≈ fa_eval h t :=
  fa_eval_respects A h s t He.

Example fa_pequiv_control {X : SetoidObject} (s t : FATerm X)
  (He : fa_eq s t) :
  @pequiv _ _ (cmon_prop (FreeAbObject X)) s t := He.

(** ** 3. [fv_eq], Instance/Mod/Free.v *)

Fail Definition fv_eq_type_elim {R : RingObject} {X : SetoidObject}
  (s t : @FVTerm R X) (He : fv_eq s t) : @FVTerm R X :=
  ltac:(induction He; exact fv_zero).

Example fv_pequiv_control {R : RingObject} {X : SetoidObject}
  (s t : @FVTerm R X) (He : fv_eq s t) :
  @pequiv _ _ (cmon_prop (@FreeModObject R X)) s t := He.

(** ** 4. [mt_eq], Instance/Mod/Tensor.v *)

Fail Definition mt_eq_type_elim {R : RingObject} {V V' : RModObject R}
  (s t : MTerm V V') (He : mt_eq s t) : MTerm V V' :=
  ltac:(induction He; exact mt_zero).

Example mt_pequiv_control {R : RingObject} {V V' : RModObject R}
  (s t : MTerm V V') (He : mt_eq s t) :
  @pequiv _ _ (cmon_prop (TensorMod V V')) s t := He.

(** ** 5. [bs_eq], Instance/Mod/Bimodule.v *)

Fail Definition bs_eq_type_elim {X : RingObject}
  {N : RModObject (Ring_op X)} {M : RModObject X}
  (s t : bsum N M) (He : bs_eq s t) : bsum N M :=
  ltac:(induction He; exact bs_zero).

Example bs_pequiv_control {X : RingObject}
  {N : RModObject (Ring_op X)} {M : RModObject X}
  (s t : bsum N M) (He : bs_eq s t) :
  @pequiv _ _ (cmon_prop (BalTensor N M)) s t := He.

(** ** Instrument check, scope-free *)

Fail Example probe_term_model_instrument : true = false := eq_refl.
