(* AUDIT PROBE for defect S8.

   Claim under test: in Theory/Metacategory.v the predicate

     identity (u : arr) := (forall f, composite f u f) /\ (forall g, composite u g g)

   is UNSATISFIABLE, because [arr := nat] is infinite while [pairs : M.t arr]
   is a finite map.  If so, [FromArrows]'s object type [exists i, identity M i]
   is uninhabited and [Three := FromArrows ThreeArrows] is the EMPTY category.

   The campaign reported it could not build a probe because [Metacategory] is a
   module functor never instantiated outside its own file.  It CAN be
   instantiated: the functor takes any [WSfun PNN], and [FMapWeakList.Make PNN]
   is one. *)

From Coq Require Import FMapWeakList.
From Coq Require Import List.
From Coq Require Import PeanoNat.
From Coq Require Import Lia.
From Coq Require Import SetoidList.
Import ListNotations.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Metacategory.

(* Instantiate the functor the file never applies. *)
Module MyMap := FMapWeakList.Make PNN.
Module Import MC := Metacategory MyMap.

Section S8.

Local Open Scope nat_scope.

(* A bound strictly above every first-coordinate of a key occurring in l. *)
Definition keybound (l : list ((nat * nat) * nat)) : nat :=
  S (fold_right (fun p acc => Nat.max (fst (fst p)) acc) 0%nat l).

Lemma keybound_gt : forall l p, In p l -> fst (fst p) < keybound l.
Proof.
  unfold keybound; induction l as [|q l IH]; simpl; intros p Hin.
  - contradiction.
  - destruct Hin as [->|Hin].
    + lia.
    + specialize (IH p Hin). unfold keybound in IH. lia.
Qed.

(* THE MAIN CLAIM: no arrow of any metacategory satisfies [identity]. *)
Theorem identity_unsatisfiable (M : Metacategory) (u : arr M) :
  identity M u -> False.
Proof.
  intros [Hl _].
  set (l := MyMap.elements (pairs M)).
  set (n := keybound l).
  (* [identity] demands a binding for EVERY f, in particular for f = n. *)
  assert (HM : MyMap.MapsTo (n, u) n (pairs M)) by exact (Hl n).
  apply MyMap.elements_1 in HM.
  (* ... but n exceeds every first-coordinate present in the finite [elements]. *)
  apply SetoidList.InA_alt in HM.
  destruct HM as [p [Heq Hin]].
  destruct p as [[a b] c].
  destruct Heq as [Hk _]; simpl in Hk.
  assert (Hlt : a < n) by (apply (keybound_gt l (a, b, c)); exact Hin).
  (* PNN.eq is Logic.eq, so the key of p really is (n, u). *)
  assert (Hk' : (n, u) = (a, b)) by exact Hk.
  inversion Hk' as [[Hna Hub]].
  lia.
Qed.

(* Consequence 1: the object type of every [FromArrows] category is empty. *)
Theorem FromArrows_no_objects (M : Metacategory) : @obj (FromArrows M) -> False.
Proof.
  intros [i Hi]; exact (identity_unsatisfiable M i Hi).
Qed.

(* Consequence 2: [Three] -- presented in the header as the three-object
   category -- has NO objects at all. *)
Theorem Three_is_empty : @obj Three -> False.
Proof. exact (FromArrows_no_objects ThreeArrows). Qed.

End S8.

(* ---- ex3.10 OVERTURN adjudication: is the surviving content NON-VACUOUS? ---- *)
Section Ex310.
Local Open Scope nat_scope.

(* The table really is inhabited: generator 3 : 1 -> 0, generator 4 : 2 -> 1,
   and the composite 5 = 3 o 4.  So composition_law is not vacuously satisfied. *)
Example tbl_0_3 : composite ThreeArrows 0 3 3.
Proof. apply MyMap.find_2. vm_compute. reflexivity. Qed.

Example tbl_3_4 : composite ThreeArrows 3 4 5.
Proof. apply MyMap.find_2. vm_compute. reflexivity. Qed.

Example tbl_4_2 : composite ThreeArrows 4 2 4.
Proof. apply MyMap.find_2. vm_compute. reflexivity. Qed.

(* composition_law fires on a genuine composable triple: real, non-vacuous content. *)
Definition composition_law_live :=
  composition_law ThreeArrows 3 4 2 5 4 tbl_3_4 tbl_4_2.

End Ex310.

Print Assumptions identity_unsatisfiable.
Print Assumptions Three_is_empty.
Print Assumptions composition_law_live.
