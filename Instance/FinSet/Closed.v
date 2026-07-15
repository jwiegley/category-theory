Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Instance.Sets.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(** * Computable exponentials on skeletal FinSet

    The exponential of the canonical m-element and n-element sets is the
    canonical (n ^ m)-element set: a function [Fin.t m → Fin.t n] is a
    string of m digits in base n, and [Nat.pow] recurses as
    [n ^ S m = n * n ^ m], so tabulating one more argument is exactly one
    [fin_pair] digit step from [Instance/FinSet/Product.v].  Both codec
    directions are structural fixpoints in the closed-computation style of
    [fin_split]/[fin_pair], so evaluation and currying REDUCE on closed
    inputs by [eq_refl].

    The hom-setoid of [FinSet] is pointwise Leibniz equality, so the
    POINTWISE round trip [fin_apply_tabulate] is exactly what the Closed
    laws consume — no function extensionality is needed anywhere; the
    congruence [fin_tabulate_ext] replaces it at the single place a
    rewrite must cross the [fin_tabulate] binder. *)

(** [fin_tabulate f] encodes the function [f] as its digit string
    [f F1, f (FS F1), …], by structural recursion on the arity [m]: the
    head digit is [f F1] and the tail is the tabulation of [f ∘ FS]. *)
Fixpoint fin_tabulate {m n : nat} {struct m} :
  (Fin.t m → Fin.t n) → Fin.t (n ^ m) :=
  match m return (Fin.t m → Fin.t n) → Fin.t (n ^ m) with
  | O => fun _ => Fin.F1
  | S m' => fun f =>
      fin_pair (f Fin.F1) (fin_tabulate (fun i => f (Fin.FS i)))
  end.

(** [fin_apply c] decodes the code [c] back into a function, by structural
    recursion on the arity [m]: [fin_unpair] splits off the head digit,
    and [Fin.caseS'] dispatches the argument. *)
Fixpoint fin_apply {m n : nat} {struct m} :
  Fin.t (n ^ m) → Fin.t m → Fin.t n :=
  match m return Fin.t (n ^ m) → Fin.t m → Fin.t n with
  | O => fun _ i => Fin.case0 (fun _ => Fin.t n) i
  | S m' => fun c i =>
      Fin.caseS' i (fun _ => Fin.t n)
        (fst (fin_unpair c))
        (fun i' => fin_apply (snd (fin_unpair c)) i')
  end.

(* The computability acceptance test: with m = 2, n = 3 the function
   sending F1 ↦ 2 and FS F1 ↦ 1 is the digit string "2 then 1", i.e. the
   code 2·3 + 1 = 7; both directions reduce by [eq_refl]. *)
Example fin_tabulate_computes :
  @fin_tabulate 2 3
    (fun i => Fin.caseS' i (fun _ => Fin.t 3)
                (Fin.FS (Fin.FS Fin.F1)) (fun _ => Fin.FS Fin.F1))
    = Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))))
    := eq_refl.

Example fin_apply_computes :
  @fin_apply 2 3
    (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))))
    (Fin.FS Fin.F1)
    = Fin.FS Fin.F1 := eq_refl.

(** ** The round trips

    Stated POINTWISE, matching the pointwise-[eq] hom-setoid of [FinSet]:
    this is precisely the form the Closed laws below consume, which is why
    no function extensionality ever enters. *)

Lemma fin_apply_tabulate {m n : nat} (f : Fin.t m → Fin.t n) (i : Fin.t m) :
  fin_apply (fin_tabulate f) i = f i.
Proof.
  revert f; induction i as [m' | m' i IH]; intros f; simpl.
  - (* The head digit is recovered by the first projection. *)
    rewrite fin_unpair_pair; reflexivity.
  - (* The tail digits are recovered recursively. *)
    rewrite fin_unpair_pair; simpl.
    apply (IH (fun j => f (Fin.FS j))).
Qed.

Lemma fin_tabulate_apply {m n : nat} (c : Fin.t (n ^ m)) :
  fin_tabulate (fin_apply c) = c.
Proof.
  induction m as [| m' IH]; simpl.
  - (* n ^ 0 = 1: every code is F1. *)
    symmetry; apply fin1_unique.
  - (* Re-tabulating head and tail recovers the digit pair, which
       [fin_pair_unpair] identifies with c.  The tail step is the IH at
       [snd (fin_unpair c)], to which the goal's subterm is definitionally
       equal ([Fin.caseS'] reduces on [Fin.FS], plus eta). *)
    transitivity (fin_pair (fst (fin_unpair c)) (snd (fin_unpair c))).
    + f_equal.
      exact (IH (snd (fin_unpair c))).
    + apply fin_pair_unpair.
Qed.

(** Tabulation only inspects its argument pointwise, so it respects the
    pointwise hom-equivalence of [FinSet] — the funext-free congruence
    used to rewrite under the [fin_tabulate] binder. *)
Lemma fin_tabulate_ext {m n : nat} (f g : Fin.t m → Fin.t n) :
  (∀ i, f i = g i) → fin_tabulate f = fin_tabulate g.
Proof.
  intros Hfg; induction m as [| m' IH]; simpl.
  - reflexivity.
  - rewrite (Hfg Fin.F1).
    rewrite (IH (fun i => f (Fin.FS i)) (fun i => g (Fin.FS i))
               (fun i => Hfg (Fin.FS i))).
    reflexivity.
Qed.

(** ** The cartesian closed structure

    Per the argument-order note of [Structure/Cartesian/Closed.v]:
    [exponent_obj x y] is displayed y ^ x, the object of functions FROM x
    TO y, so on skeletal objects it is the nat power [(y ^ x)%nat].
    Currying is pointwise tabulation over the [fin_pair] product codec,
    uncurrying is pointwise application, and [exp_iso] holds by the two
    round trips — pointwise, which is all the [fun_setoid] hom-equivalence
    of [FinSet] asks. *)

#[local] Obligation Tactic := idtac.

#[export] Program Instance FinSet_Closed : @Closed FinSet FinSet_Cartesian := {
  exponent_obj := fun m n => (n ^ m)%nat;

  exp_iso := fun x y z =>
    {| to   := {| morphism := fun (f : Fin.t (x * y) → Fin.t z)
                                  (i : Fin.t x) =>
                    fin_tabulate (fun j : Fin.t y => f (fin_pair i j)) |}
     ; from := {| morphism := fun (g : Fin.t x → Fin.t (z ^ y)%nat)
                                  (p : Fin.t (x * y)) =>
                    fin_apply (g (fst (fin_unpair p))) (snd (fin_unpair p)) |}
    |}
}.
Next Obligation.
  (* Currying respects pointwise equality, via [fin_tabulate_ext]. *)
  intros x y z f f' Hf i; simpl in Hf.
  apply fin_tabulate_ext; intro j; apply Hf.
Qed.
Next Obligation.
  (* Uncurrying respects pointwise equality. *)
  intros x y z g g' Hg p; simpl in Hg.
  rewrite (Hg (fst (fin_unpair p))); reflexivity.
Qed.
Next Obligation.
  (* curry ∘ uncurry ≈ id: tabulating the application of each digit code
     recovers the code, after the product round trip under the binder. *)
  intros x y z g i; simpl.
  transitivity (fin_tabulate (fin_apply (g i))).
  - apply fin_tabulate_ext; intro j.
    rewrite fin_unpair_pair; reflexivity.
  - apply fin_tabulate_apply.
Qed.
Next Obligation.
  (* uncurry ∘ curry ≈ id: applying a tabulation is the original function,
     then the product round trip reassembles the argument. *)
  intros x y z f p; simpl.
  rewrite fin_apply_tabulate, fin_pair_unpair; reflexivity.
Qed.
Next Obligation.
  (* The beta law: eval ∘ first (curry f) ≈ f, pointwise. *)
  intros x y z f; unfold first; intro p; simpl.
  rewrite fin_unpair_pair; simpl.
  rewrite fin_apply_tabulate, fin_pair_unpair; reflexivity.
Qed.

(* Closed evaluation at concrete elements, by [eq_refl]: the derived [eval]
   of Structure/Cartesian/Closed.v computes over this instance.  With
   x = y = 2 the exponential 2^2 is Fin.t 4, and the code 2 = "digits 1, 0"
   is the function F1 ↦ FS F1, FS F1 ↦ F1; the two Examples check both
   argument routings, which return DIFFERENT values. *)
Example eval_computes :
  @eval FinSet FinSet_Cartesian FinSet_Closed 2%nat 2%nat
    (fin_pair (Fin.FS (Fin.FS Fin.F1) : Fin.t 4) (Fin.F1 : Fin.t 2))
    = Fin.FS Fin.F1 := eq_refl.

Example eval_computes_snd :
  @eval FinSet FinSet_Cartesian FinSet_Closed 2%nat 2%nat
    (fin_pair (Fin.FS (Fin.FS Fin.F1) : Fin.t 4) (Fin.FS Fin.F1 : Fin.t 2))
    = Fin.F1 := eq_refl.
