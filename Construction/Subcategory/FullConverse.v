(** * The converse of [Full_Implies_Full_Functor] needs its hypothesis *)

(* Construction/Subcategory.v proves [Full_Functor_Implies_Full] under the
   hypothesis [ShomRespects] — that the selected-morphism predicate is closed
   under the hom-setoid equivalence — and explains why the [Subcategory]
   record does not supply it.  That explanation was a diagnosis of why one
   proof does not go through, not a proof that no proof does.

   This file closes the gap with a counterexample, so the hypothesis is now
   known to be NECESSARY rather than merely convenient.  (The construction is
   due to an audit of the first commit of this work.)

   The ambient category has one object and the natural numbers as its
   morphisms, composed by addition, with two arrows identified exactly when
   both are zero or both are nonzero.  That is a genuine congruence for
   addition and it has two classes, so the hom-setoid is NOT the total
   relation — the counterexample does not cheat by making everything equal.
   The subcategory selects every morphism except 1.  Its inclusion is full as
   a FUNCTOR, because 1 can be replaced by 2, which is retained and
   equivalent to it; but the subcategory is not full as DATA, because 1
   itself is not retained.  That is exactly the failure of [ShomRespects]. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Subcategory.

Generalizable All Variables.

Definition nz (n : nat) : bool := match n with O => true | S _ => false end.

Lemma nz_add : forall m n, nz (m + n) = andb (nz m) (nz n).
Proof. destruct m; simpl; auto. Qed.

#[local] Obligation Tactic := idtac.

Program Definition NZ : Category := {|
  obj     := unit;
  hom     := fun _ _ => nat;
  homset  := fun _ _ => {| equiv := fun m n => nz m = nz n |};
  id      := fun _ => 0%nat;
  compose := fun _ _ _ f g => (f + g)%nat
|}.
Next Obligation.
  intros _ _; constructor; congruence.
Qed.
Next Obligation.
  intros a b c ?? H ?? H0; simpl in *; rewrite !nz_add; congruence.
Qed.
Next Obligation. intros ?? f; simpl; reflexivity. Qed.
Next Obligation. intros ?? f; simpl; rewrite PeanoNat.Nat.add_0_r; reflexivity. Qed.
Next Obligation. intros ???? f g h; simpl; rewrite PeanoNat.Nat.add_assoc; reflexivity. Qed.
Next Obligation. intros ???? f g h; simpl; rewrite PeanoNat.Nat.add_assoc; reflexivity. Qed.

(* The selection data: every object; the morphisms are every natural number
   EXCEPT 1.  That is closed under + (a sum is 1 only if one summand is 1 and
   the other 0) and contains id = 0. *)

Lemma not_one_add : forall m n, m <> 1%nat -> n <> 1%nat -> (m + n)%nat <> 1%nat.
Proof.
  intros [|[|m]] [|[|n]]; simpl; intros H1 H2 Hc;
    try discriminate;
    try (apply H1; reflexivity);
    try (apply H2; reflexivity).
Qed.

Definition NotOne : Subcategory NZ :=
  @Build_Subcategory NZ (fun _ => unit)
    (fun _ _ _ _ f => f <> 1%nat)
    (fun _ _ _ _ _ _ f g Hf Hg => not_one_add f g Hf Hg)
    (fun _ _ => ltac:(discriminate)).

(* The inclusion is FULL as a functor: given any f : nat, send it to 2 when it
   is 1 and to itself otherwise.  The result is never 1, and it is ≈ f because
   2 and 1 are both nonzero. *)
Definition pick (f : nat) : nat := if Nat.eqb f 1 then 2%nat else f.

Lemma pick_not_one : forall f, pick f <> 1%nat.
Proof.
  intro f; unfold pick; destruct (Nat.eqb f 1) eqn:E.
  - discriminate.
  - intro Hf; subst f; simpl in E; discriminate.
Qed.

Lemma pick_equiv : forall f, nz (pick f) = nz f.
Proof.
  intro f; unfold pick; destruct (Nat.eqb f 1) eqn:E; auto.
  apply PeanoNat.Nat.eqb_eq in E; subst; reflexivity.
Qed.

Program Definition NotOne_Incl_Full : Functor.Full (Incl NZ NotOne) := {|
  prefmap := fun _ _ g => (pick g; pick_not_one g)
|}.
Next Obligation. intros ?? g; simpl; apply pick_equiv. Qed.

(* But the subcategory is NOT Full as data: 1 is a morphism of NZ between
   selected objects that the subcategory does not retain. *)
Theorem NotOne_not_Full : Subcategory.Full NZ NotOne -> False.
Proof.
  intro HF.
  exact (HF tt tt tt tt 1%nat eq_refl).
Qed.

(* Therefore the converse of Full_Implies_Full_Functor is FALSE for a general
   Subcategory record, and ShomRespects (or some equivalent) is genuinely
   required.  Stated as a refutation of the unhypothesised statement: *)
Theorem converse_without_ShomRespects_is_false :
  (forall (C : Category) (S : Subcategory C),
      Functor.Full (Incl C S) -> Subcategory.Full C S) -> False.
Proof.
  intro Hbad.
  exact (NotOne_not_Full (Hbad NZ NotOne NotOne_Incl_Full)).
Qed.

(* Sanity: the hom-setoid of NZ really is non-degenerate — 0 and 1 are NOT
   identified — so the counterexample is not the indiscrete cheat. *)
Lemma NZ_setoid_nondegenerate :
  @equiv _ (@homset NZ tt tt) 0%nat 1%nat -> False.
Proof. simpl; discriminate. Qed.

(* And NotOne really fails ShomRespects, as the commit's diagnosis says: 1 ≈ 2
   yet 2 is retained and 1 is not. *)
Lemma NotOne_not_ShomRespects : ShomRespects NZ NotOne -> False.
Proof.
  intro HR.
  assert (Hne : 2%nat <> 1%nat) by discriminate.
  exact (HR tt tt tt tt 2%nat 1%nat eq_refl Hne eq_refl).
Qed.

