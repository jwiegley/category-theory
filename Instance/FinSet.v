Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(** * FinSet, the skeletal category of finite sets *)

(* nLab:      https://ncatlab.org/nlab/show/FinSet
   Wikipedia: https://en.wikipedia.org/wiki/FinSet

   The skeleton of the category of finite sets: the objects are the natural
   numbers, with [n] standing for the canonical n-element set [Fin.t n], and
   the morphisms [m ~> n] are all functions [Fin.t m → Fin.t n].  Hom-setoids
   are pointwise Leibniz equality (via [fun_setoid] over the discrete
   [Fin_Setoid]), so this is an ordinary — non-quotient — category presented
   in the library's setoid discipline.

   FinSet is the PROP for commutative monoids: its coproduct-induced monoidal
   structure (tensor on objects is [plus]) makes every object a commutative
   monoid via the codiagonal [id ▽ id] and the empty map.  That monoidal
   assembly, and the [PROP] instance riding on it, need the coherence
   machinery and are not yet built; this file delivers their intended
   inputs:

   - the category itself, with Initial (0), Terminal (1) and COMPUTING
     coproducts: [fin_split] is a structural fixpoint dispatching through
     [Fin.caseS'], so copairings evaluate on closed inputs by [eq_refl]
     (see [fin_split_computes] and [merge_computes] below);
   - the [HomEqProp] and [ObjDecEq] side conditions from
     [Construction/Quotient.v], which universal-property proofs against
     FinSet-like targets require ([Prop]-reflected hom equivalence, and
     axiom-free UIP on objects via [Nat.eq_dec]).

   NOTE on names: [Structure/Cocartesian.v] defines [inl], [inr], [left]
   and [right] for the coproduct calculus, shadowing the sum-type
   constructors, which are therefore qualified [Datatypes.inl] and
   [Datatypes.inr] throughout this file. *)

Program Definition FinSet : Category := {|
  obj := nat;
  hom := fun m n => Fin.t m → Fin.t n;
  homset := fun m n => fun_setoid (Fin.t m) (Fin.t n);
  id := fun _ i => i;
  compose := fun _ _ _ f g i => f (g i)
|}.
Next Obligation.
  (* compose respects pointwise equality in both arguments. *)
  intros f f' Hf g g' Hg i.
  rewrite (Hg i); apply Hf.
Qed.

(** ** Side conditions for universal properties

    The hom equivalence of [FinSet] is already a [Prop]-valued pointwise
    equality, so the [Prop] reflection required by soundness inductions is
    the identity in both directions; and objects are natural numbers, whose
    equality is decidable, giving axiom-free UIP on objects. *)

#[export] Instance FinSet_HomEqProp : HomEqProp FinSet :=
  Build_HomEqProp FinSet
    (fun m n (f g : Fin.t m → Fin.t n) => ∀ i, f i = g i)
    (fun _ _ _ _ H => H)
    (fun _ _ _ _ H => H).

#[export] Instance FinSet_ObjDecEq : ObjDecEq FinSet := Nat.eq_dec.

(** ** The computing split/join toolkit on [Fin.t (m + n)]

    [fin_split] analyses an element of the canonical (m + n)-element set as
    either an element of the first m or of the last n; [fin_join] is its
    two-sided inverse, built from the standard library's injections [Fin.L]
    and [Fin.R].  [fin_split] is a structural fixpoint on [m] whose
    successor case dispatches through [Fin.caseS'], re-tagging the
    recursive result along [Fin.FS] — deliberately built from primitives
    common to every supported version, avoiding the [Fin.case_L_R'] family
    that only the Rocq 9.x standard library provides, so the file also
    compiles on Coq 8.19/8.20.  Both directions REDUCE on closed input —
    the coproduct structure below computes by [eq_refl]. *)

Fixpoint fin_split {m n : nat} {struct m} :
  Fin.t (m + n) -> (Fin.t m + Fin.t n)%type :=
  match m return Fin.t (m + n) -> (Fin.t m + Fin.t n)%type with
  | O => fun p => Datatypes.inr p
  | S m' => fun p =>
      Fin.caseS' p (fun _ => (Fin.t (S m') + Fin.t n)%type)
        (Datatypes.inl Fin.F1)
        (fun q =>
           match @fin_split m' n q with
           | Datatypes.inl a => Datatypes.inl (Fin.FS a)
           | Datatypes.inr b => Datatypes.inr b
           end)
  end.

Definition fin_join {m n : nat} (s : (Fin.t m + Fin.t n)%type) :
  Fin.t (m + n) :=
  match s with
  | Datatypes.inl a => Fin.L n a
  | Datatypes.inr b => Fin.R m b
  end.

Lemma fin_split_L {m n : nat} (a : Fin.t m) :
  fin_split (Fin.L n a) = Datatypes.inl a.
Proof.
  induction a as [m | m a IH]; simpl.
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

Lemma fin_split_R {m n : nat} (b : Fin.t n) :
  fin_split (Fin.R m b) = Datatypes.inr b.
Proof.
  (* Induction on the amount [m] prepended: [Fin.R 0 b] is definitionally
     [b], and the successor case re-tags along [Fin.FS]. *)
  induction m as [| m IH]; simpl.
  - reflexivity.
  - rewrite IH; reflexivity.
Qed.

Lemma fin_join_split {m n : nat} (p : Fin.t (m + n)) :
  fin_join (fin_split p) = p.
Proof.
  revert p; induction m as [| m IH]; intro p.
  - reflexivity.
  - apply (Fin.caseS' p
             (fun p : Fin.t (S m + n) =>
                fin_join (@fin_split (S m) n p) = p)).
    + reflexivity.
    + intro q; specialize (IH q); simpl; revert IH.
      destruct (fin_split q) as [a|b]; simpl; intro IH;
        rewrite IH; reflexivity.
Qed.

Lemma fin_split_join {m n : nat} (s : (Fin.t m + Fin.t n)%type) :
  fin_split (fin_join s) = s.
Proof. destruct s; [apply fin_split_L | apply fin_split_R]. Qed.

(* The computability acceptance test: the analysis reduces by [eq_refl]. *)
Example fin_split_computes :
  @fin_split 2 2 (Fin.FS (Fin.FS Fin.F1)) = Datatypes.inr Fin.F1 := eq_refl.

(** ** Initial and terminal objects *)

(* Initiality is terminality in [FinSet^op], so the fields carry the
   [Terminal] names: [one {x}] here lands in [Fin.t 0 → Fin.t x], the unique
   (empty) map out of the empty set. *)
#[export] Instance FinSet_Initial : Initial FinSet :=
  @Build_Terminal (FinSet^op) 0%nat
    (fun x (v : Fin.t 0) => Fin.case0 (fun _ => Fin.t x) v)
    (fun x f g i => Fin.case0 (fun j => f j = g j) i).

(* The one-element set is a singleton: every inhabitant is [Fin.F1]. *)
Lemma fin1_unique (j : Fin.t 1) : j = Fin.F1.
Proof.
  apply (Fin.caseS' j (fun j => j = Fin.F1)).
  - reflexivity.
  - intro j'; exact (Fin.case0 (fun j' => Fin.FS j' = Fin.F1) j').
Qed.

#[export] Instance FinSet_Terminal : @Terminal FinSet :=
  @Build_Terminal FinSet 1%nat
    (fun x (_ : Fin.t x) => Fin.F1)
    (fun x f g i =>
       eq_trans (fin1_unique (f i)) (eq_sym (fin1_unique (g i)))).

(** ** Computable coproducts

    Being cocartesian is being cartesian in [FinSet^op], so the fields reuse
    the [Cartesian] names: [product_obj] is the coproduct object [m + n],
    [fork] is the copairing by case analysis through [fin_split], and
    [exl]/[exr] are the injections [Fin.L]/[Fin.R] (the projections read in
    the opposite category). *)

#[export] Program Instance FinSet_Cocartesian : @Cocartesian FinSet := {|
  product_obj := fun m n => (m + n)%nat;
  fork := fun x y z (f : Fin.t y → Fin.t x) (g : Fin.t z → Fin.t x) p =>
    match fin_split p with
    | Datatypes.inl a => f a
    | Datatypes.inr b => g b
    end;
  exl := fun x y => Fin.L y;
  exr := fun x y => Fin.R x
|}.
Next Obligation.
  (* The copairing respects pointwise equality in both arguments. *)
  intros f f' Hf g g' Hg p.
  destruct (fin_split p); [apply Hf | apply Hg].
Qed.
Next Obligation.
  (* The universal property: h ≈ f ▽ g exactly when h recovers f along
     Fin.L and g along Fin.R. *)
  split.
  - intros Hh; split; intro q; simpl.
    + rewrite (Hh (Fin.L _ q)), fin_split_L; reflexivity.
    + rewrite (Hh (Fin.R _ q)), fin_split_R; reflexivity.
  - intros [Hl Hr] p.
    destruct (fin_split p) as [a|b] eqn:Hs.
    + assert (Hp : p = Fin.L z a)
        by (rewrite <- (fin_join_split p), Hs; reflexivity).
      rewrite Hp; apply Hl.
    + assert (Hp : p = Fin.R y b)
        by (rewrite <- (fin_join_split p), Hs; reflexivity).
      rewrite Hp; apply Hr.
Qed.

(* Closed copairings evaluated at concrete elements of Fin.t 3, by
   [eq_refl]: the derived merge (▽) of Structure/Cocartesian.v computes over
   this instance.  The two components are chosen to DISAGREE at the routed
   values, so each Example certifies its routing and not merely reduction:
   [Fin.FS Fin.F1] lies in the [Fin.R]-image, and only routing to the
   second component (the identity) returns [Fin.F1] — the first component
   would return [Fin.FS Fin.F1]; dually, [Fin.F1] lies in the
   [Fin.L]-image and must reach the first component to return
   [Fin.FS Fin.F1]. *)
Example merge_computes :
  @merge FinSet FinSet_Cocartesian 2%nat 1%nat 2%nat
    (fun _ : Fin.t 1 => Fin.FS Fin.F1) (fun i : Fin.t 2 => i)
    (Fin.FS Fin.F1) = Fin.F1 := eq_refl.

Example merge_computes_inl :
  @merge FinSet FinSet_Cocartesian 2%nat 1%nat 2%nat
    (fun _ : Fin.t 1 => Fin.FS Fin.F1) (fun i : Fin.t 2 => i)
    Fin.F1 = Fin.FS Fin.F1 := eq_refl.
