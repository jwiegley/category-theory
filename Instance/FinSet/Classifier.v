Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.

Require Import Coq.Vectors.Fin.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(** * The subobject classifier of skeletal FinSet

    This file equips [FinSet] with computed pullbacks and the subobject
    classifier Ω = 2.

    The pullback of f : m ~> k and g : n ~> k is the subset of the
    canonical (m · n)-element set consisting of the (encoded) pairs (a, b)
    with f a = g b.  "Subset" is realized by a COUNT codec: [fin_countP P]
    counts the elements of [Fin.t N] satisfying a boolean predicate [P],
    [fin_select] tabulates the satisfying elements in order (unrank), and
    [fin_rank] sends a satisfying element to its index.  All three are
    structural fixpoints in the closed-computation style of [fin_split] /
    [fin_pair], so pullback objects and projections REDUCE on closed
    inputs by [eq_refl].

    Truth-value convention: Ω is the object [2]; the element [Fin.F1]
    represents TRUE and [Fin.FS Fin.F1] represents FALSE ([fin_true] and
    [fin_false] below).  [truth : 1 ~> Ω] is the constant [fin_true] map,
    and the characteristic morphism of a mono m sends b to [fin_true]
    exactly when b lies in the image of m — decided by the finite search
    [fin_existsb] over the decidable equality [fin_eqb]. *)

(** ** Decidable equality on the canonical finite sets

    [fin_eqb] is heterogeneous — comparing positions of possibly different
    canonical sets — so that it recurses structurally with no dependent
    typing; soundness is then stated at a common index. *)

Fixpoint fin_eqb {m n : nat} (i : Fin.t m) (j : Fin.t n) : bool :=
  match i, j with
  | Fin.F1, Fin.F1 => true
  | Fin.FS i', Fin.FS j' => fin_eqb i' j'
  | _, _ => false
  end.

Lemma fin_eqb_refl {n : nat} (i : Fin.t n) : fin_eqb i i = true.
Proof. induction i; simpl; auto. Qed.

Lemma fin_eqb_eq {n : nat} (i j : Fin.t n) : fin_eqb i j = true → i = j.
Proof.
  revert j; induction i as [n' | n' i' IH]; intro j.
  - apply (Fin.caseS' j (fun j => fin_eqb Fin.F1 j = true → Fin.F1 = j)).
    + reflexivity.
    + intros j' H; discriminate H.
  - apply (Fin.caseS' j
             (fun j => fin_eqb (Fin.FS i') j = true → Fin.FS i' = j)).
    + intro H; discriminate H.
    + intros j' H; simpl in H.
      now rewrite (IH j' H).
Qed.

(** ** Bounded existential search

    [fin_existsb P] decides whether some element of the canonical n-element
    set satisfies [P], by structural recursion on [n].  Soundness returns
    the least witness as DATA (a [sigT]), so it can build mediating
    morphisms below; hence it ends in [Defined]. *)

Fixpoint fin_existsb {n : nat} : (Fin.t n → bool) → bool :=
  match n return (Fin.t n → bool) → bool with
  | O => fun _ => false
  | S n' => fun P => (P Fin.F1 || fin_existsb (fun i => P (Fin.FS i)))%bool
  end.

Lemma fin_existsb_sound {n : nat} (P : Fin.t n → bool) :
  fin_existsb P = true → ∃ i : Fin.t n, P i = true.
Proof.
  revert P; induction n as [| n' IH]; intros P H.
  - discriminate H.
  - simpl in H; destruct (P Fin.F1) eqn:E.
    + exact (Fin.F1; E).
    + simpl in H.
      destruct (IH (fun i => P (Fin.FS i)) H) as [i Hi].
      exact (Fin.FS i; Hi).
Defined.

Lemma fin_existsb_complete {n : nat} (P : Fin.t n → bool) (i : Fin.t n) :
  P i = true → fin_existsb P = true.
Proof.
  revert P; induction i as [n' | n' i' IH]; intros P H; simpl.
  - now rewrite H.
  - rewrite (IH (fun j => P (Fin.FS j)) H).
    now destruct (P Fin.F1).
Qed.

(** ** The count codec

    [fin_countP P] is the number of elements satisfying [P]; the canonical
    set of that size is the "subset cut out by P".  [fin_select] is the
    order-preserving tabulation (unrank) of the satisfying elements, and
    [fin_rank] is its inverse on satisfying elements.  Both dispatch on
    [P Fin.F1] by a convoy so that goals mentioning them can abstract that
    boolean cleanly; the impossible branch of [fin_rank] (the element is
    satisfying, but the head test came out [false]) is eliminated by
    transporting along the resulting [false = true]. *)

Fixpoint fin_countP {n : nat} : (Fin.t n → bool) → nat :=
  match n return (Fin.t n → bool) → nat with
  | O => fun _ => 0%nat
  | S n' => fun P =>
      ((if P Fin.F1 then 1 else 0) + fin_countP (fun i => P (Fin.FS i)))%nat
  end.

Fixpoint fin_select {n : nat} :
  ∀ P : Fin.t n → bool, Fin.t (fin_countP P) → Fin.t n :=
  match n return ∀ P : Fin.t n → bool, Fin.t (fin_countP P) → Fin.t n with
  | O => fun _ k => Fin.case0 (fun _ => Fin.t 0) k
  | S n' => fun P =>
      match P Fin.F1 as b return
        Fin.t ((if b then 1 else 0) + fin_countP (fun i => P (Fin.FS i)))%nat
          → Fin.t (S n')
      with
      | true => fun k =>
          match @fin_split 1 (fin_countP (fun i => P (Fin.FS i))) k with
          | Datatypes.inl _ => Fin.F1
          | Datatypes.inr k' =>
              Fin.FS (fin_select (fun i => P (Fin.FS i)) k')
          end
      | false => fun k => Fin.FS (fin_select (fun i => P (Fin.FS i)) k)
      end
  end.

Fixpoint fin_rank {n : nat} :
  ∀ (P : Fin.t n → bool) (i : Fin.t n), P i = true → Fin.t (fin_countP P) :=
  match n return
    ∀ (P : Fin.t n → bool) (i : Fin.t n), P i = true → Fin.t (fin_countP P)
  with
  | O => fun P i => Fin.case0 (fun i => P i = true → Fin.t (fin_countP P)) i
  | S n' => fun P i =>
      Fin.caseS' i (fun i => P i = true → Fin.t (fin_countP P))
        (fun H =>
           match P Fin.F1 as b return
             P Fin.F1 = b →
             Fin.t ((if b then 1 else 0)
                    + fin_countP (fun j => P (Fin.FS j)))%nat
           with
           | true => fun _ => Fin.F1
           | false => fun E =>
               match eq_trans (eq_sym H) E in _ = y
                 return (if y then True
                         else Fin.t (fin_countP (fun j => P (Fin.FS j))))
               with eq_refl => I end
           end eq_refl)
        (fun i' (H : P (Fin.FS i') = true) =>
           match P Fin.F1 as b return
             Fin.t ((if b then 1 else 0)
                    + fin_countP (fun j => P (Fin.FS j)))%nat
           with
           | true => Fin.R 1 (fin_rank (fun j => P (Fin.FS j)) i' H)
           | false => fin_rank (fun j => P (Fin.FS j)) i' H
           end)
  end.

(* The computability acceptance test: with P selecting the odd positions of
   the canonical 4-element set, the count is 2 and the codec tabulates the
   second satisfying element — position 3 — by [eq_refl]. *)
Example fin_select_computes :
  @fin_select 4 (fun i => fin_eqb i (Fin.FS Fin.F1 : Fin.t 4)
                          || fin_eqb i (Fin.FS (Fin.FS (Fin.FS Fin.F1))
                                        : Fin.t 4))%bool
    (Fin.FS Fin.F1 : Fin.t 2)
    = Fin.FS (Fin.FS (Fin.FS Fin.F1)) := eq_refl.

(** ** The codec laws

    Selection lands in the subset ([fin_select_sat]); ranking a satisfying
    element and selecting recovers it ([fin_select_rank]); and selection is
    injective ([fin_select_inj], via the [Fin.FS] projection
    [fin_FS_inj]).  Together these give the pullback UMP below. *)

Lemma fin_select_sat {n : nat} (P : Fin.t n → bool)
      (k : Fin.t (fin_countP P)) :
  P (fin_select P k) = true.
Proof.
  revert P k; induction n as [| n' IH]; intros P k.
  - exact (Fin.case0 (fun k : Fin.t 0 => _) k).
  - revert k; simpl; destruct (P Fin.F1) eqn:E; intro k.
    + pattern k; apply (Fin.caseS' k); simpl.
      * exact E.
      * intro k'; apply (IH (fun i => P (Fin.FS i)) k').
    + apply (IH (fun i => P (Fin.FS i)) k).
Qed.

Lemma fin_select_rank {n : nat} (P : Fin.t n → bool) (i : Fin.t n)
      (H : P i = true) :
  fin_select P (fin_rank P i H) = i.
Proof.
  revert P i H; induction n as [| n' IH]; intros P i.
  - exact (Fin.case0
             (fun i => ∀ H : P i = true, fin_select P (fin_rank P i H) = i)
             i).
  - apply (Fin.caseS' i
             (fun i => ∀ H : P i = true,
                fin_select P (fin_rank P i H) = i)).
    + simpl; destruct (P Fin.F1) eqn:E; intro H.
      * reflexivity.
      * discriminate H.
    + intro i'; simpl; destruct (P Fin.F1) eqn:E; intro H; simpl.
      * now rewrite (IH (fun j => P (Fin.FS j)) i' H).
      * now rewrite (IH (fun j => P (Fin.FS j)) i' H).
Qed.

(* [Fin.FS] is injective, by applying the evident retraction (with default
   [d] at [Fin.F1]) to the equation — built from [Fin.caseS'] only, so it
   stays within the primitives available on every supported version. *)
Definition fin_pred {n : nat} (d : Fin.t n) (i : Fin.t (S n)) : Fin.t n :=
  Fin.caseS' i (fun _ => Fin.t n) d (fun j => j).

Lemma fin_FS_inj {n : nat} (x y : Fin.t n) : Fin.FS x = Fin.FS y → x = y.
Proof. intro H; exact (f_equal (fin_pred x) H). Qed.

Lemma fin_select_inj {n : nat} (P : Fin.t n → bool)
      (a b : Fin.t (fin_countP P)) :
  fin_select P a = fin_select P b → a = b.
Proof.
  revert P a b; induction n as [| n' IH]; intros P a b.
  - exact (Fin.case0 (fun a : Fin.t 0 => _) a).
  - revert a b; simpl; destruct (P Fin.F1) eqn:E; intros a b.
    + (* head satisfied: analyse both indices as F1 / FS *)
      pattern a; apply (Fin.caseS' a); [| intro a'];
        (pattern b; apply (Fin.caseS' b); [| intro b']); simpl;
        intro Heq.
      * reflexivity.
      * discriminate Heq.
      * discriminate Heq.
      * apply fin_FS_inj in Heq.
        now rewrite (IH (fun i => P (Fin.FS i)) a' b' Heq).
    + intro Heq; apply fin_FS_inj in Heq.
      apply (IH (fun i => P (Fin.FS i)) a b Heq).
Qed.

(** ** Computed pullbacks

    The pullback of f : m ~> k and g : n ~> k is the subset of the encoded
    pairs — [Fin.t (m * n)] under the positional codec of
    [Instance/FinSet/Product.v] — on which f and g agree, realized through
    the count codec.  The projections decode-then-project; the mediator
    ranks the encoded pair, which is satisfying by the cone equation. *)

Definition finset_pb_pred {m n k : nat}
           (f : Fin.t m → Fin.t k) (g : Fin.t n → Fin.t k) :
  Fin.t (m * n) → bool :=
  fun p => fin_eqb (f (fst (fin_unpair p))) (g (snd (fin_unpair p))).

Local Obligation Tactic := idtac.

#[export] Program Instance FinSet_Pullbacks : HasPullbacks FinSet := {
  pullback := fun m n k (f : Fin.t m → Fin.t k) (g : Fin.t n → Fin.t k) =>
    {| Pull         := fin_countP (finset_pb_pred f g);
       pullback_fst := fun q =>
         fst (fin_unpair (fin_select (finset_pb_pred f g) q));
       pullback_snd := fun q =>
         snd (fin_unpair (fin_select (finset_pb_pred f g) q))
    |}
}.
Next Obligation.
  (* the square commutes: selection satisfies the agreement predicate *)
  intros m n k f g q.
  apply fin_eqb_eq.
  exact (fin_select_sat (finset_pb_pred f g) q).
Qed.
Next Obligation.
  (* the universal property, via rank/select *)
  intros m n k f g Q q1 q2 Hq.
  assert (prf : ∀ i : Fin.t Q,
             finset_pb_pred f g (fin_pair (q1 i) (q2 i)) = true). {
    intro i.
    unfold finset_pb_pred.
    rewrite fin_unpair_pair; simpl.
    assert (Hqi := Hq i); simpl in Hqi.
    rewrite Hqi.
    apply fin_eqb_refl.
  }
  unshelve refine
    {| unique_obj :=
         fun i => fin_rank (finset_pb_pred f g)
                    (fin_pair (q1 i) (q2 i)) (prf i) |}.
  - split; intro i; simpl;
      now rewrite fin_select_rank, fin_unpair_pair.
  - intros v [Hv1 Hv2] i.
    apply fin_select_inj.
    rewrite fin_select_rank.
    rewrite <- (fin_pair_unpair (fin_select (finset_pb_pred f g) (v i))).
    assert (H1 := Hv1 i); assert (H2 := Hv2 i); simpl in H1, H2.
    now rewrite H1, H2.
Qed.

(** ** Truth values

    Ω is the two-element set; [Fin.F1] is TRUE and [Fin.FS Fin.F1] is
    FALSE, mediated from [bool] by [fin_of_bool]. *)

Definition fin_true  : Fin.t 2 := Fin.F1.
Definition fin_false : Fin.t 2 := Fin.FS Fin.F1.

Definition fin_of_bool (b : bool) : Fin.t 2 :=
  if b then fin_true else fin_false.

Lemma fin_of_bool_true (b : bool) : fin_of_bool b = fin_true → b = true.
Proof.
  destruct b; [reflexivity | intro H; discriminate H].
Qed.

Lemma fin2_cases (j : Fin.t 2) : (j = fin_true) + (j = fin_false).
Proof.
  apply (Fin.caseS' j (fun j => ((j = fin_true) + (j = fin_false))%type)).
  - now left.
  - intro j'; right; unfold fin_false.
    now rewrite (fin1_unique j').
Defined.

(** ** Monomorphisms in FinSet are exactly the injections

    Mirrors [injectivity_is_monic] of [Instance/Sets.v]: the non-trivial
    direction probes the mono with the two constant maps out of the
    one-element set [1]. *)

Lemma finset_monic_iff_injective {m n : nat} (f : m ~{FinSet}~> n) :
  (∀ a b : Fin.t m, f a = f b → a = b) ↔ Monic f.
Proof.
  split.
  - intro inj.
    constructor; intros z g1 g2 Hg i.
    apply inj; exact (Hg i).
  - intros M a b Hab.
    exact (monic (Monic:=M) 1%nat
             (fun _ => a) (fun _ => b) (fun _ => Hab) Fin.F1).
Qed.

(** ** The subobject classifier

    Ω = 2 with [truth = fin_true]; the characteristic morphism of a mono
    m : u ~> x sends b to [fin_true] exactly when b lies in the image of
    m, decided by [fin_existsb]. *)

#[export] Program Instance FinSet_Classifier :
  @SubobjectClassifier FinSet FinSet_Terminal := {|
  Ω     := 2%nat;
  truth := fun _ => fin_true;
  char  := fun u x (m : u ~{FinSet}~> x) (_ : Monic m) (b : Fin.t x) =>
    fin_of_bool (fin_existsb (fun a => fin_eqb (m a) b))
|}.
Next Obligation.
  (* char_respects: an isomorphic subobject has the same image *)
  intros u u' x m M m' M' [i Hi] b; simpl.
  f_equal.
  destruct (fin_existsb (fun a => fin_eqb (m a) b)) eqn:E1;
    destruct (fin_existsb (fun a' => fin_eqb (m' a') b)) eqn:E2;
    try reflexivity.
  - (* the left witness transports along [to i] *)
    destruct (fin_existsb_sound _ E1) as [a Ha].
    apply fin_eqb_eq in Ha.
    assert (Hia := Hi a); simpl in Hia.
    assert (Ht : fin_eqb (m' (to i a)) b = true)
      by (rewrite Hia, Ha; apply fin_eqb_refl).
    rewrite (fin_existsb_complete _ (to i a) Ht) in E2.
    discriminate E2.
  - (* the right witness transports back along [from i] *)
    destruct (fin_existsb_sound _ E2) as [a' Ha'].
    apply fin_eqb_eq in Ha'.
    assert (Hia := Hi (from i a')); simpl in Hia.
    assert (Hii := iso_to_from i a'); simpl in Hii.
    rewrite Hii in Hia.
    assert (Ht : fin_eqb (m (from i a')) b = true)
      by (rewrite <- Hia, Ha'; apply fin_eqb_refl).
    rewrite (fin_existsb_complete _ (from i a') Ht) in E1.
    discriminate E1.
Qed.
Next Obligation.
  (* char_pullback: u is the preimage of fin_true under char m *)
  intros u x m M.
  unshelve econstructor.
  - (* the classifying square commutes *)
    intro a; simpl.
    now rewrite (fin_existsb_complete (fun a' => fin_eqb (m a') (m a)) a
                   (fin_eqb_refl (m a))).
  - (* the universal property *)
    intros Q q1 q2 Hq.
    assert (Hb : ∀ i : Fin.t Q,
               fin_existsb (fun a => fin_eqb (m a) (q1 i)) = true). {
      intro i.
      apply fin_of_bool_true.
      assert (Hqi := Hq i); simpl in Hqi.
      exact Hqi.
    }
    unshelve refine
      {| unique_obj := fun i => `1 (fin_existsb_sound _ (Hb i)) |}.
    + split; intro i; simpl.
      * apply fin_eqb_eq.
        exact (`2 (fin_existsb_sound _ (Hb i))).
      * (* both sides live in the one-element set *)
        exact (eq_trans (fin1_unique _) (eq_sym (fin1_unique _))).
    + intros v [Hv1 _] i.
      apply (snd (finset_monic_iff_injective m) M).
      assert (H1 := Hv1 i); simpl in H1.
      rewrite H1.
      apply fin_eqb_eq.
      exact (`2 (fin_existsb_sound _ (Hb i))).
Qed.
Next Obligation.
  (* char_unique: any classifying square determines char m on both cases *)
  intros u x m M h HP b; simpl.
  destruct (fin_existsb (fun a => fin_eqb (m a) b)) eqn:E.
  - (* b in the image: the commuting square forces fin_true *)
    destruct (fin_existsb_sound _ E) as [a Ha].
    apply fin_eqb_eq in Ha.
    assert (Hc := is_pullback_commutes HP a); simpl in Hc.
    rewrite <- Ha.
    exact Hc.
  - (* b not in the image: fin_true would lift b through the square *)
    destruct (fin2_cases (h b)) as [Ht | Hf]; [| exact Hf].
    pose proof (is_pullback_ump HP 1%nat (fun _ => b) (fun _ => Fin.F1)
                  (fun _ => Ht)) as U.
    destruct (unique_property U) as [Hw1 _].
    assert (H1 := Hw1 Fin.F1); simpl in H1.
    assert (Ht' : fin_eqb (m (unique_obj U Fin.F1)) b = true)
      by (rewrite H1; apply fin_eqb_refl).
    rewrite (fin_existsb_complete _ (unique_obj U Fin.F1) Ht') in E.
    discriminate E.
Qed.
