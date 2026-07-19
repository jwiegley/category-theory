Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Equivalence.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Karoubi.
Require Import Category.Construction.Karoubi.Universal.

Generalizable All Variables.

(** Sets is Cauchy complete: every idempotent splits. *)

(* nLab:      https://ncatlab.org/nlab/show/Cauchy+complete+category
   nLab:      https://ncatlab.org/nlab/show/split+idempotent
   Wikipedia: https://en.wikipedia.org/wiki/Karoubi_envelope

   An idempotent setoid map e : X ~> X in [Sets] — pointwise,
   e (e a) ≈ e a — splits through the sub-setoid of its fixed points,

      { a : X & e a ≈ a },  compared under X's ≈ on underlying elements.

   The retraction X ~> Y sends a to e a, a fixed point by idempotency; the
   section Y ~> X is the underlying-element projection.  Section after
   retraction on X is a ↦ e a, which is e on the nose; retraction after
   section carries (a; h) to (e a; _), equal to (a; h) in Y because
   e a ≈ a is exactly h.  Both splitting laws thus hold pointwise.

   Packaged through the [IdempotentsSplit] class of
   Construction/Karoubi/Universal.v this makes [Sets] Cauchy complete
   ([Sets_IdempotentsSplit]), whence by [cauchy_complete_embed_equiv] the
   embedding of [Sets] into its own Karoubi envelope is an equivalence of
   categories ([Sets_Cauchy]). *)

#[local] Obligation Tactic := idtac.

(* The splitting object for an idempotent e on X: the sub-setoid of elements
   held fixed by e, compared under X's equivalence on underlying elements
   (the fixedness proofs are irrelevant). *)
Program Definition sets_split_obj {X : SetoidObject} (e : X ~{Sets}~> X) :
  SetoidObject := {|
  carrier := ∃ a : X, e a ≈ a;
  is_setoid := {| equiv := fun p q => `1 p ≈ `1 q |}
|}.
Next Obligation.
  intros X e.
  equivalence.
Qed.

(* The idempotent law of e, read pointwise through the hom-setoid of Sets:
   e a is a fixed point of e. *)
Lemma sets_split_fixed {X : SetoidObject} (e : X ~{Sets}~> X)
      (H : Idempotent e) (a : X) : e (e a) ≈ e a.
Proof.
  exact (@idem Sets X e H a).
Qed.

(* The retraction X ~> Y: send a to the fixed point e a. *)
Program Definition sets_split_r {X : SetoidObject} (e : X ~{Sets}~> X)
        (H : Idempotent e) : X ~{Sets}~> sets_split_obj e := {|
  morphism := fun a => (e a; sets_split_fixed e H a)
|}.
Next Obligation.
  intros X e H a b Hab; simpl.
  now rewrite Hab.
Qed.

(* The section Y ~> X: the underlying element, discarding fixedness. *)
Program Definition sets_split_s {X : SetoidObject} (e : X ~{Sets}~> X) :
  sets_split_obj e ~{Sets}~> X := {|
  morphism := fun p => `1 p
|}.
Next Obligation.
  intros X e p q Hpq.
  exact Hpq.
Qed.

(* The splitting of e through its fixed-point object. *)
Program Definition sets_split {X : SetoidObject} (e : X ~{Sets}~> X)
        (H : Idempotent e) :
  @SplitIdempotent Sets X (sets_split_obj e) := {|
  split_idem   := e;
  split_idem_r := sets_split_r e H;
  split_idem_s := sets_split_s e
|}.
Next Obligation.
  (* s ∘ r ≈ e : pointwise, the underlying element of (e a; _) is e a *)
  intros X e H a; simpl.
  reflexivity.
Qed.
Next Obligation.
  (* r ∘ s ≈ id : pointwise on (a; h), the goal e a ≈ a is exactly h *)
  intros X e H p; simpl.
  exact (`2 p).
Qed.

(* Every idempotent of Sets splits: Sets is Cauchy complete.  The splitting
   chosen for e has e itself as the split idempotent, so agreement with e is
   reflexivity. *)
#[export] Instance Sets_IdempotentsSplit : IdempotentsSplit Sets.
Proof.
  constructor.
  intros X e H.
  exists (sets_split_obj e).
  exists (sets_split e H).
  reflexivity.
Defined.

(* Since Sets has split idempotents, its embedding into its own Karoubi
   envelope is full, faithful and essentially surjective, hence an
   equivalence of categories: Sets is equivalent to Split(Sets). *)
Corollary Sets_Cauchy : EquivalenceOfCategories (@Karoubi_Embed Sets).
Proof.
  exact (cauchy_complete_embed_equiv Sets_IdempotentsSplit).
Defined.
