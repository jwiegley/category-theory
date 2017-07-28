Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.omega.Omega.

Generalizable All Variables.

Open Scope lazy_bool_scope.

Definition rev_list_rect (A : Type) (P : list A → Type) (H : P [])
           (H0 : ∀ (a : A) (l : list A), P (rev l) → P (rev (a :: l)))
           (l : list A) : P (rev l) :=
  list_rect (λ l0 : list A, P (rev l0)) H
            (λ (a : A) (l0 : list A) (IHl : P (rev l0)), H0 a l0 IHl) l.

Definition rev_rect (A : Type) (P : list A → Type)
           (H : P []) (H0 : ∀ (x : A) (l : list A), P l → P (l ++ [x]))
           (l : list A) : P l :=
  (λ E : rev (rev l) = l,
     eq_rect (rev (rev l)) (λ l0 : list A, P l0)
        (rev_list_rect A P H
        (λ (a : A) (l0 : list A) (H1 : P (rev l0)), H0 a (rev l0) H1)
        (rev l)) l E) (rev_involutive l).

Lemma last_rcons A (x y : A) l :
  last (l ++ [x]) y = x.
Proof.
  induction l; simpl.
    reflexivity.
  rewrite IHl; clear IHl.
  destruct l; auto.
Qed.

Lemma last_app_cons A (x : A) xs y ys :
  last (xs ++ y :: ys) x = last (y :: ys) x.
Proof.
  generalize dependent y.
  generalize dependent xs.
  induction ys using rev_ind; simpl; intros.
    apply last_rcons.
  rewrite last_rcons.
  rewrite app_comm_cons.
  rewrite app_assoc.
  rewrite last_rcons.
  destruct ys; auto.
Qed.

Lemma last_cons A (x : A) y ys :
  last (y :: ys) x = last ys y.
Proof.
  generalize dependent x.
  induction ys using rev_ind; simpl; intros.
    reflexivity.
  rewrite !last_rcons.
  destruct ys; auto.
Qed.

Lemma match_last {A} {a : A} {xs x} :
  match xs with
  | [] => a
  | _ :: _ => last xs x
  end = last xs a.
Proof.
  induction xs; auto.
  rewrite !last_cons; reflexivity.
Qed.

Lemma Forall_app {A} p (l1 l2: list A) :
  Forall p (l1 ++ l2) <-> (Forall p l1 /\ Forall p l2).
Proof.
  intros.
  rewrite !Forall_forall.
  split; intros.
    split; intros;
    apply H; apply in_or_app.
      left; trivial.
    right; trivial.
  apply in_app_or in H0.
  destruct H, H0; eauto.
Qed.

Lemma last_Forall A (x y : A) l P :
  last l x = y -> Forall P l -> P x -> P y.
Proof.
  generalize dependent x.
  destruct l using rev_ind; simpl; intros.
    now subst.
  rewrite last_rcons in H; subst.
  apply Forall_app in H0.
  destruct H0.
  now inversion H0.
Qed.

Fixpoint list_beq {A : Type} (eq_A : A → A → bool) (X Y : list A)
         {struct X} : bool :=
  match X with
  | [] => match Y with
          | [] => true
          | _ :: _ => false
          end
  | x :: x0 =>
      match Y with
      | [] => false
      | x1 :: x2 => eq_A x x1 &&& list_beq eq_A x0 x2
      end
  end.

Lemma list_beq_eq {A} (R : A -> A -> bool) xs ys :
  (∀ x y, R x y = true -> x = y) ->
  list_beq R xs ys = true -> xs = ys.
Proof.
  generalize dependent ys.
  induction xs; simpl; intros.
    destruct ys; congruence.
  destruct ys.
    discriminate.
  destruct (R a a0) eqn:Heqe.
    apply H in Heqe; subst.
    erewrite IHxs; eauto.
  discriminate.
Qed.

Lemma list_beq_refl {A} (R : A -> A -> bool) xs :
  (∀ x, R x x = true) -> list_beq R xs xs = true.
Proof.
  intros.
  induction xs; auto; simpl.
  now rewrite H.
Qed.

Lemma K_dec_on_type A (x : A) (eq_dec : ∀ y : A, x = y \/ x ≠ y)
      (P : x = x -> Type) :
  P (eq_refl x) -> forall p:x = x, P p.
Proof.
  intros.
  elim (@Eqdep_dec.eq_proofs_unicity_on A _) with x (eq_refl x) p.
    trivial.
  exact eq_dec.
Qed.

Lemma Nat_eq_dec' : ∀ (x y : nat), x = y \/ x ≠ y.
Proof. intros; destruct (Nat.eq_dec x y); auto. Qed.

Lemma Nat_eq_dec_refl (x : nat) :
  Nat.eq_dec x x = left (@eq_refl (nat) x).
Proof.
  destruct (Nat.eq_dec x x); [| contradiction].
  refine (K_dec_on_type (nat) x (Nat_eq_dec' x)
            (fun H => @left _ _ H = @left _ _ (@eq_refl (nat) x)) _ _); auto.
Qed.

Lemma Nat_eqb_refl (x : nat) : Nat.eqb x x = true.
Proof. now apply Nat.eqb_eq. Qed.

Lemma Pos_eq_dec' : ∀ x y : positive, x = y \/ x ≠ y.
Proof.
  intros.
  destruct (Pos.eq_dec x y); auto.
Qed.

Lemma Pos_eq_dec_refl n : Pos.eq_dec n n = left (@eq_refl positive n).
Proof.
  destruct (Pos.eq_dec n n).
    refine (K_dec_on_type positive n (Pos_eq_dec' n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl positive n)) _ _).
    reflexivity.
  contradiction.
Qed.

Fixpoint Pos_eqb_refl (x : positive) : Pos.eqb x x = true :=
  match x with
  | xI x => Pos_eqb_refl x
  | xO x => Pos_eqb_refl x
  | xH => eq_refl
  end.

Definition nth_safe {a} (xs : list a) (n : nat) (H : (n < length xs)%nat) : a.
Proof.
  induction xs; simpl in *; auto.
  contradiction (Nat.nlt_0_r n).
Defined.

Definition nth_pos {a} (xs : list a) (n : positive) (default : a) : a.
Proof.
  generalize dependent n.
  induction xs; intros.
    exact default.
  destruct n using Pos.peano_rect.
    exact a0.
  exact (IHxs n).
Defined.

Definition within_bounds {A} (x : positive) (xs : list A) : Prop :=
  (Nat.pred (Pos.to_nat x) < length xs)%nat.

Definition Pos_to_fin {n} (x : positive) :
  (Nat.pred (Pos.to_nat x) < n)%nat -> Fin.t n := Fin.of_nat_lt.

Definition nth_pos_bounded {a} (xs : list a) (n : positive)
           (H : within_bounds n xs) : a.
Proof.
  generalize dependent n.
  induction xs; intros.
    unfold within_bounds in H; simpl in H; omega.
  destruct n using Pos.peano_rect.
    exact a0.
  clear IHn.
  apply IHxs with (n:=n).
  unfold within_bounds in *.
  simpl in H.
  rewrite Pos2Nat.inj_succ in H.
  simpl in H.
  apply lt_S_n.
  rewrite Nat.succ_pred_pos; auto.
  apply Pos2Nat.is_pos.
Defined.

Lemma Fin_eq_dec' : ∀ n (x y : Fin.t n), x = y \/ x ≠ y.
Proof. intros; destruct (Fin.eq_dec x y); auto. Qed.

Lemma Fin_eq_dec_refl n (x : Fin.t n) :
  Fin.eq_dec x x = left (@eq_refl (Fin.t n) x).
Proof.
  destruct (Fin.eq_dec x x).
    refine (K_dec_on_type (Fin.t n) x (Fin_eq_dec' n x)
              (fun H => @left _ _ H = @left _ _ (@eq_refl (Fin.t n) x)) _ _).
    reflexivity.
  contradiction.
Qed.

Fixpoint Fin_eqb_refl n (x : Fin.t n) : Fin.eqb x x = true :=
  match x with
  | @Fin.F1 m'    => Nat_eqb_refl m'
  | @Fin.FS n0 p' => Fin_eqb_refl n0 _
  end.

Lemma Fin_eqb_eq n (x y : Fin.t n) (H : Fin.eqb x y = true) : x = y.
Proof.
  induction x.
    revert H.
    apply Fin.caseS with (p:=y); intros; eauto.
    simpl in H; discriminate.
  revert H.
  apply Fin.caseS' with (p:=y); intros; eauto.
    simpl in H; discriminate.
  simpl in H.
  f_equal.
  now apply IHx.
Defined.

Import EqNotations.

Fixpoint nth_fin {a} (xs : list a) (n : Fin.t (length xs)) : a :=
  match xs as xs' return length xs = length xs' -> a with
  | nil => fun H => Fin.case0 _ (rew H in n)
  | cons x xs' => fun H =>
    match n in Fin.t n' return length xs = n' -> a with
    | Fin.F1 => fun _ => x
    | @Fin.FS n0 x => fun H0 =>
        nth_fin
          xs' (rew (eq_add_S n0 (length xs')
                             (rew [fun n => n = S (length xs')] H0 in H)) in x)
    end eq_refl
  end eq_refl.

Class Equality (A : Type) := {
  Eq_eq := @eq A;
  Eq_eq_refl x := eq_refl;

  Eq_eqb : A -> A -> bool;
  Eq_eqb_refl x : Eq_eqb x x = true;

  Eq_eqb_eq x y : Eq_eqb x y = true -> x = y;

  Eq_eq_decP (x y : A) : x = y \/ x <> y;
  Eq_eq_dec  (x y : A) : { x = y } + { x ≠ y };

  Eq_eq_dec_refl x : Eq_eq_dec x x = left (@Eq_eq_refl x)
}.

Program Instance pos_Eq : Equality positive := {
  Eq_eqb         := Pos.eqb;
  Eq_eqb_refl    := Pos_eqb_refl;

  Eq_eqb_eq x y  := proj1 (Pos.eqb_eq x y);

  Eq_eq_decP     := Pos_eq_dec';
  Eq_eq_dec      := Pos.eq_dec;

  Eq_eq_dec_refl := Pos_eq_dec_refl
}.

Ltac equalities' :=
  match goal with
  | [ H : (_ &&& _) = true |- _ ]      => rewrite <- andb_lazy_alt in H
  | [ |- (_ &&& _) = true ]            => rewrite <- andb_lazy_alt
  | [ H : (_ && _) = true |- _ ]       => apply andb_true_iff in H
  | [ |- (_ && _) = true ]             => apply andb_true_iff; split
  | [ H : _ /\ _ |- _ ]                => destruct H
  | [ H : _ ∧ _ |- _ ]                 => destruct H
  | [ H : ∃ _, _ |- _ ]                => destruct H

  | [ H : context[Pos.eq_dec ?N ?M] |- _ ] =>
    replace (Pos.eq_dec N M) with (Eq_eq_dec N M) in H
  | [ |- context[Pos.eq_dec ?N ?M] ] =>
    replace (Pos.eq_dec N M) with (Eq_eq_dec N M)
  | [ H : context[(?N =? ?M)%positive] |- _ ] =>
    replace ((N =? M)%positive) with (Eq_eqb N M) in H
  | [ |- context[(?N =? ?M)%positive] ] =>
    replace ((N =? M)%positive) with (Eq_eqb N M)

  | [ |- Eq_eqb ?X ?X = true ]     => apply Eq_eqb_refl
  | [ H : Eq_eqb _ _ = true |- _ ] => apply Eq_eqb_eq in H
  | [ |- Eq_eqb _ _ = true ]       => apply Eq_eqb_eq

  | [ H : context[match @Eq_eq_dec ?X ?X with _ => _ end] |- _ ] =>
    rewrite (@Eq_eq_dec_refl X) in H
  | [ |- context[match @Eq_eq_dec ?X ?X with _ => _ end] ] =>
    rewrite (@Eq_eq_dec_refl X)
  | [ H : context[match @Eq_eq_dec ?X ?Y with _ => _ end] |- _ ] =>
    destruct (@Eq_eq_dec X Y); subst
  | [ |- context[match Eq_eq_dec ?X ?Y with _ => _ end] ] =>
    destruct (@Eq_eq_dec X Y); subst

  | [ H : list_beq _ _ _ = true |- _ ] => apply list_beq_eq in H
  | [ |- list_beq _ _ _ = true ]       => apply list_beq_eq
  end.

Ltac equalities :=
  try equalities';
  repeat (
    equalities';
    subst; simpl; auto;
    try discriminate;
    try tauto;
    try intuition idtac;
    subst; simpl; auto).

Set Universe Polymorphism.

Program Instance option_setoid `{Setoid A} : Setoid (option A) := {
  equiv := fun x y => match x, y with
    | Some x, Some y => x ≈ y
    | None, None => True
    | _, _ => False
    end
}.
Next Obligation. intuition; discriminate. Qed.
Next Obligation. intuition; discriminate. Qed.
Next Obligation.
  equivalence.
  - destruct x; reflexivity.
  - destruct x, y; auto.
    symmetry; auto.
  - destruct x, y, z; auto.
      transitivity a0; auto.
    contradiction.
Qed.

Unset Universe Polymorphism.

Section Representation.

Definition cat_idx := positive.
Definition obj_idx := positive.
Definition arr_idx := positive.

Variable arr_def : arr_idx -> obj_idx * obj_idx.

Definition arr_dom (f : arr_idx) := fst (arr_def f).
Definition arr_cod (f : arr_idx) := snd (arr_def f).

Variable c : cat_idx.

(* This describes the morphisms of a magmoid, which forms a quotient category
   under denotation. *)
Inductive Term : Set :=
  | Identity (o : obj_idx)
  | Morph    (a : arr_idx)
  | Compose  (f g : Term).

Fixpoint TermDom (e : Term) : obj_idx :=
  match e with
  | Identity x  => x
  | Morph x     => arr_dom x
  | Compose _ g => TermDom g
  end.

Fixpoint TermCod (e : Term) : obj_idx :=
  match e with
  | Identity x  => x
  | Morph x     => arr_cod x
  | Compose f _ => TermCod f
  end.

Definition Arrow := arr_idx.

(* This describes the morphisms of a path, or free, category over a quiver of
   Arrows, while our environment describes a quiver (where vertices are all
   object indices, and edges are all arrow indices associated pairs of object
   indices). The denotation of an ArrowList to some category C is a forgetful
   functor from the path category over this quiver to C. Note that this
   functor is only total if the denotation of the quiver itself is total. *)
Inductive ArrowList : Set :=
  | IdentityOnly : obj_idx -> ArrowList
  | ArrowChain   : Arrow -> list Arrow -> ArrowList.

Fixpoint ArrowList_beq (x y : ArrowList) {struct x} : bool :=
  match x with
  | IdentityOnly cod =>
      match y with
      | IdentityOnly cod' => Eq_eqb cod cod'
      | ArrowChain _ _ => false
      end
  | ArrowChain x x0 =>
      match y with
      | IdentityOnly _ => false
      | ArrowChain x1 x2 => Eq_eqb x x1 &&& list_beq Eq_eqb x0 x2
      end
  end.

Definition ArrowList_cod (xs : ArrowList) : obj_idx :=
  match xs with
  | IdentityOnly x => x
  | ArrowChain f _ => arr_cod f
  end.

Definition ArrowList_dom (xs : ArrowList) : obj_idx :=
  match xs with
  | IdentityOnly x => x
  | ArrowChain f xs => arr_dom (last xs f)
  end.

Inductive ForallAligned : list Arrow → Prop :=
    Align_nil : ForallAligned []
  | Align_singleton : ∀ (a : Arrow), ForallAligned [a]
  | Align_cons2 : ∀ (a b : Arrow) (l : list Arrow),
      arr_dom a = arr_cod b ->
      ForallAligned (b :: l) → ForallAligned (a :: b :: l).

Lemma ForallAligned_inv {x xs y} :
  ForallAligned (x :: y :: xs)
    -> arr_dom x = arr_cod y /\
       ForallAligned (y :: xs).
Proof.
  generalize dependent x.
  generalize dependent y.
  induction xs; intros;
  inversion H; subst; intuition.
Qed.

Lemma ForallAligned_app {x xs y ys} :
  ForallAligned (x :: xs ++ y :: ys)
    <-> ForallAligned (x :: xs) /\ ForallAligned (y :: ys) /\
        arr_cod y = arr_dom (last xs x).
Proof.
  generalize dependent x.
  generalize dependent y.
  generalize dependent ys.
  induction xs; simpl; intros.
    split; intros.
      inversion H.
      split; constructor; auto.
    constructor; auto; intuition.
  specialize (IHxs ys y a).
  intuition;
  try (apply ForallAligned_inv in H0;
       destruct H0;
       specialize (H H2)).
  - constructor; intuition.
  - intuition.
  - rewrite match_last; intuition.
  - inversion H2.
    rewrite match_last in H4.
    constructor; intuition.
Qed.

Definition ArrowList_well_typed dom cod (xs : ArrowList) : Prop :=
  match xs with
  | IdentityOnly x => x = dom /\ x = cod
  | ArrowChain f xs =>
    arr_cod f = cod /\
    arr_dom (last xs f) = dom /\
    (* Ensure that it is a correctly type-aligned list *)
    ForallAligned (f :: xs)
  end.

Corollary ArrowList_well_typed_dom {f dom cod } :
  ArrowList_well_typed dom cod f -> ArrowList_dom f = dom.
Proof. induction f; simpl; intuition. Qed.

Corollary ArrowList_well_typed_cod {f dom cod} :
  ArrowList_well_typed dom cod f -> ArrowList_cod f = cod.
Proof. induction f; simpl; intuition. Qed.

Definition ArrowList_list_rect : ∀ (P : ArrowList → Type),
  (∀ (x : obj_idx), P (IdentityOnly x)) →
  (∀ (a : Arrow), P (ArrowChain a [])) →
  (∀ (a1 a2 : Arrow) (l : list Arrow),
      P (ArrowChain a2 l) → P (ArrowChain a1 (a2 :: l))) →
  ∀ l : ArrowList, P l.
Proof.
  intros.
  destruct l; auto.
  generalize dependent a.
  induction l; auto.
Defined.

Lemma ArrowList_beq_eq x y :
  ArrowList_beq x y = true <-> x = y.
Proof.
  generalize dependent y.
  induction x using ArrowList_list_rect;
  destruct y; simpl; split; intros;
  try discriminate; equalities;
  try inversion_clear H;
  equalities; auto; equalities.
  - destruct l; congruence.
  - destruct l0; equalities; intuition.
  - rewrite list_beq_refl; auto; intros; equalities.
Qed.

Definition ListOfArrows_rect : ∀ (P : Arrow -> list Arrow → Type),
  (∀ (x : Arrow), P x []) →
  (∀ (x y : Arrow) (l : list Arrow), P y l → P x (y :: l)) →
  ∀ (x : Arrow) (l : list Arrow), P x l.
Proof.
  intros.
  generalize dependent x.
  induction l; auto.
Defined.

Definition ArrowList_append (xs ys : ArrowList) : ArrowList :=
  match xs, ys with
  | IdentityOnly f,  IdentityOnly g  => IdentityOnly g
  | IdentityOnly f,  ArrowChain g xs => ArrowChain g xs
  | ArrowChain f xs, IdentityOnly g  => ArrowChain f xs
  | ArrowChain f xs, ArrowChain g ys => ArrowChain f (xs ++ g :: ys)
  end.

Lemma ArrowList_append_chains a a0 l l0 :
  ArrowList_dom (ArrowChain a l) = ArrowList_cod (ArrowChain a0 l0) ->
  ArrowList_append (ArrowChain a l) (ArrowChain a0 l0) =
  ArrowChain a (l ++ a0 :: l0).
Proof.
  generalize dependent a0.
  generalize dependent l0.
  simpl.
  induction l using rev_ind; simpl; intros; auto.
Qed.

Lemma ArrowList_append_well_typed {dom mid cod f1 f2} :
  ArrowList_dom f1 = mid ->
  ArrowList_cod f2 = mid ->
  ArrowList_well_typed mid cod f1 ->
  ArrowList_well_typed dom mid f2 ->
    ArrowList_well_typed dom cod (ArrowList_append f1 f2).
Proof.
  generalize dependent mid.
  generalize dependent f2.
  induction f1 using ArrowList_list_rect; intros.
  - simpl in *.
    equalities; subst.
    destruct f2 using ArrowList_list_rect; simpl in *; auto.
  - simpl in *; equalities; subst.
    destruct f2.
      simpl in *; subst; intuition.
    simpl in *; equalities.
    + induction l using rev_ind.
        simpl in *; equalities.
        inversion H2; subst.
        now inversion H.
      rewrite !last_app_cons in *; simpl in *.
      replace (match l ++ [x] with
               | [] => a0
               | _ :: _ => x
               end) with x by (destruct l; auto); auto.
    + constructor; auto.
  - clear IHf1.
    equalities; subst.
    destruct f2.
      constructor; simpl in H1; intuition.
      simpl in *; subst; intuition.
    rewrite ArrowList_append_chains by congruence.
    simpl; constructor.
      simpl in H1; intuition.
    rewrite last_app_cons, last_cons.
    pose proof (ArrowList_well_typed_dom H2) as H5.
    simpl in H5.
    replace (match l ++ a :: l0 with
             | [] => a2
             | _ :: _ => last l0 a
             end) with (last l0 a) by (destruct l; auto);
    intuition; rewrite !app_comm_cons.
    apply ForallAligned_app.
    inversion H1.
    inversion H2.
    intuition.
Qed.

(* A term is valid constructed if composition composes compatible types. *)

(*
Inductive Term_well_typed' dom cod : Term -> Prop :=
  | Identity_wt x : x = dom -> x = cod
      -> Term_well_typed' dom cod (Identity x)
  | Morph_wt f : arr_dom f = dom -> arr_cod f = cod
      -> Term_well_typed' dom cod (Morph f)
  | Compose_wt f g : TermCod g = TermDom f
      -> Term_well_typed' (TermCod g) cod f
      -> Term_well_typed' dom (TermCod g) g
      -> Term_well_typed' dom cod (Compose f g).
*)

Fixpoint Term_well_typed dom cod (e : Term) : Prop :=
  match e with
  | Identity x => x = dom /\ x = cod
  | Morph f => arr_dom f = dom /\ arr_cod f = cod
  | Compose f g =>
    TermCod g = TermDom f /\
    Term_well_typed (TermCod g) cod f /\
    Term_well_typed dom (TermCod g) g
  end.

Fixpoint Term_well_typed_bool dom cod (e : Term) : bool :=
  match e with
  | Identity x => (Eq_eqb x dom) &&& (Eq_eqb x cod)
  | Morph f => (Eq_eqb (arr_dom f) dom) &&& (Eq_eqb (arr_cod f) cod)
  | Compose f g =>
    (Eq_eqb (TermCod g) (TermDom f)) &&&
    Term_well_typed_bool (TermCod g) cod f &&&
    Term_well_typed_bool dom (TermCod g) g
  end.

Lemma Term_well_typed_bool_sound dom cod e :
  Term_well_typed_bool dom cod e = true <-> Term_well_typed dom cod e.
Proof.
  generalize dependent dom.
  generalize dependent cod.
  induction e; simpl; intros; repeat equalities.
  split; intros; equalities; firstorder auto.
  rewrite H0; equalities.
Qed.

Corollary Term_well_typed_dom {f dom cod } :
  Term_well_typed dom cod f -> TermDom f = dom.
Proof.
  generalize dependent cod.
  induction f; simpl; intros; intuition.
  eapply IHf2; eauto.
Qed.

Corollary Term_well_typed_cod {f dom cod} :
  Term_well_typed dom cod f -> TermCod f = cod.
Proof.
  generalize dependent dom.
  induction f; simpl; intros; intuition.
  eapply IHf1; eauto.
Qed.

Fixpoint normalize (p : Term) : ArrowList :=
  match p with
  | Identity x  => IdentityOnly x
  | Morph f     => ArrowChain f []
  | Compose f g => ArrowList_append (normalize f) (normalize g)
  end.

Lemma ArrowList_append_dom f g :
  ArrowList_dom f = ArrowList_cod g ->
  ArrowList_dom (ArrowList_append f g) = ArrowList_dom g.
Proof.
  destruct g, f; simpl; intros; auto.
  now rewrite last_app_cons, last_cons.
Qed.

Lemma ArrowList_append_cod f g :
  ArrowList_dom f = ArrowList_cod g ->
  ArrowList_cod (ArrowList_append f g) = ArrowList_cod f.
Proof.
  destruct f, g; simpl; intros; auto.
Qed.

Lemma ArrowList_normalize_dom_cod_sound {p dom cod} :
  Term_well_typed dom cod p ->
  ArrowList_dom (normalize p) = dom /\
  ArrowList_cod (normalize p) = cod.
Proof.
  generalize dependent dom.
  generalize dependent cod.
  induction p; simpl; intros; intuition; subst;
  rewrite H0 in H;
  rewrite ArrowList_append_dom ||
  rewrite ArrowList_append_cod; auto;
  specialize (IHp1 _ _ H);
  specialize (IHp2 _ _ H2);
  intuition; congruence.
Qed.

Corollary ArrowList_specific_sound p :
  Term_well_typed (TermDom p) (TermCod p) p ->
  ArrowList_dom (normalize p) = TermDom p /\
  ArrowList_cod (normalize p) = TermCod p.
Proof. apply ArrowList_normalize_dom_cod_sound. Qed.

Lemma ArrowList_id_left x y :
  ArrowList_append (IdentityOnly x) y = y.
Proof.
  simpl.
  destruct y; simpl; intros; subst; auto.
Qed.

Lemma ArrowList_id_right f y :
  ArrowList_dom f = y ->
  ArrowList_append f (IdentityOnly y) = f.
Proof.
  destruct f; simpl; intros; subst; auto.
Qed.

Lemma ArrowList_append_assoc x y z :
  ArrowList_append (ArrowList_append x y) z =
  ArrowList_append x (ArrowList_append y z).
Proof.
  destruct x, y, z; simpl; auto; intros;
  try destruct a;
  try destruct a0; subst; auto;
  now rewrite <- app_assoc.
Qed.

(* We show here that ArrowList morphisms are just one way of representing a
   free category. However, we still forget identities and which way
   composition was associated, so really it's a normalized free category. *)
Program Definition ArrowList_Category : Category := {|
  obj := obj_idx;
  hom := fun x y =>
    ∃ l : ArrowList, ArrowList_well_typed x y l;
  homset := fun x y => {| equiv := fun f g => `1 f = `1 g |};
  id := fun x => (IdentityOnly x; _);
  compose := fun _ _ _ f g => (ArrowList_append (`1 f) (`1 g); _);
  id_left := fun _ y f => ArrowList_id_left y (`1 f);
  id_right := fun x _ f => ArrowList_id_right (`1 f) _ _;
  comp_assoc := fun x y z w f g h =>
    ArrowList_append_assoc (`1 f) (`1 g) (`1 h)
|}.
Next Obligation. equivalence; simpl in *; congruence. Qed.
Next Obligation.
  pose proof (ArrowList_well_typed_dom X0).
  pose proof (ArrowList_well_typed_cod X).
  eapply ArrowList_append_well_typed; eauto.
Qed.
Next Obligation. proper; simpl in *; subst; reflexivity. Qed.
Next Obligation.
  now apply ArrowList_well_typed_dom in X.
Qed.
Next Obligation. apply ArrowList_append_assoc; congruence. Qed.
Next Obligation. rewrite ArrowList_append_assoc; auto; congruence. Qed.
Next Obligation. rewrite ArrowList_append_assoc; auto; congruence. Qed.

(* In the category whose morphisms are Terms, homset equivalence is up to
   normalized terms. *)
Program Definition Term_Category : Category := {|
  obj := obj_idx;
  hom := fun x y => ∃ l : Term, Term_well_typed x y l;
  homset := fun x y => {| equiv := fun f g =>
    normalize (`1 f) = normalize (`1 g) |};
  id := fun x => (Identity x; _);
  compose := fun _ _ _ f g => (Compose (`1 f) (`1 g); _);
  id_left := fun _ y f => ArrowList_id_left y (normalize (`1 f));
  id_right := fun x _ f => ArrowList_id_right (normalize (`1 f)) _ _;
  comp_assoc := fun x y z w f g h =>
    ArrowList_append_assoc
      (normalize (`1 f)) (normalize (`1 g)) (normalize (`1 h))
|}.
Next Obligation.
  pose proof (Term_well_typed_dom X).
  pose proof (Term_well_typed_dom X0).
  pose proof (Term_well_typed_cod X).
  pose proof (Term_well_typed_cod X0).
  destruct f, g; simpl in *; intuition idtac; congruence.
Qed.
Next Obligation.
  eapply ArrowList_normalize_dom_cod_sound; eauto.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.

Lemma ArrowList_well_typed_sound {f dom cod} :
  Term_well_typed dom cod f
    -> ArrowList_well_typed dom cod (normalize f).
Proof.
  generalize dependent dom.
  generalize dependent cod.
  induction f; simpl; intros; intuition.
    constructor; constructor.
  specialize (IHf1 _ _ H).
  specialize (IHf2 _ _ H2).
  pose proof (ArrowList_well_typed_dom IHf1).
  pose proof (ArrowList_well_typed_cod IHf2).
  apply (ArrowList_append_well_typed H1 H3 IHf1 IHf2).
Qed.

Set Transparent Obligations.

Program Instance Term_to_ArrowList :
  Term_Category ⟶ ArrowList_Category := {
  fobj := fun x => x;
  fmap := fun x y f => (normalize _; _)
}.
Next Obligation. now apply ArrowList_well_typed_sound. Qed.

Fixpoint denormalize (f : ArrowList) : Term :=
  match f with
  | IdentityOnly x => Identity x
  | ArrowChain f xs =>
    fold_left (fun acc x => (fun y => Compose y x) \o acc)
              (map Morph xs) Datatypes.id (Morph f)
  end.

Lemma normalize_denormalize {dom cod f} :
  ArrowList_well_typed dom cod f
    -> normalize (denormalize f) = f.
Proof.
  destruct f; auto.
  generalize dependent a.
  generalize dependent dom.
  induction l using rev_ind; intros; auto.
  rewrite <- ArrowList_append_chains at 2.
  - rewrite <- (IHl (arr_cod x)); clear IHl.
    + simpl.
      now rewrite map_app, fold_left_app.
    + simpl in H |- *;
      equalities.
      * rewrite app_comm_cons in H1.
        now apply ForallAligned_app in H1.
      * rewrite app_comm_cons in H1.
        now apply ForallAligned_app in H1.
  - simpl in *; equalities.
    rewrite app_comm_cons in H1.
    now apply ForallAligned_app in H1.
Qed.

Theorem denormalize_well_typed dom cod f :
  ArrowList_well_typed dom cod f
    -> Term_well_typed dom cod (denormalize f).
Proof.
  destruct f; auto.
  generalize dependent a.
  generalize dependent dom.
  induction l using rev_ind; intros.
    simpl in *; intuition.
  assert (ArrowList_well_typed
            (arr_cod x) cod (ArrowChain a l)). {
    clear IHl.
    simpl in *; equalities.
    - rewrite app_comm_cons in H1.
      now apply ForallAligned_app in H1.
    - rewrite app_comm_cons in H1.
      now apply ForallAligned_app in H1.
  }
  rewrite <- ArrowList_append_chains by (simpl in *; intuition).
  specialize (IHl (arr_cod x) a H0).
  simpl in *; equalities.
  rewrite app_comm_cons in H4.
  apply ForallAligned_app in H4; equalities.
  rewrite map_app, fold_left_app; simpl.
  rewrite H4.
  intuition; subst.
  - clear -H.
    induction l using rev_ind; simpl; auto.
    rewrite map_app, fold_left_app; simpl.
    now rewrite last_rcons in *.
  - now rewrite H4 in IHl.
  - now rewrite last_rcons.
Qed.

Program Instance ArrowList_to_Term :
  ArrowList_Category ⟶ Term_Category := {
  fobj := fun x => x;
  fmap := fun x y f => (denormalize (`1 f); _)
}.
Next Obligation. apply denormalize_well_typed; auto. Qed.
Next Obligation.
  proper.
  simpl in *; subst.
  reflexivity.
Qed.
Next Obligation.
  erewrite !normalize_denormalize; eauto.
  pose proof (ArrowList_well_typed_dom X0).
  pose proof (ArrowList_well_typed_cod X).
  eapply ArrowList_append_well_typed; eauto.
Qed.

End Representation.

Section Denotation.

Set Transparent Obligations.

Record Vars : Type := {
  vars_cat  : Category;
  vars_objs : list vars_cat;
  vars_arrs : list (∃ (dom cod : Fin.t (length vars_objs)),
    nth_fin vars_objs dom ~{vars_cat}~> nth_fin vars_objs cod);
}.

Program Definition Unused : Category := {|
  obj     := unit : Type;
  hom     := fun _ _ => True;
  homset  := Morphism_equality;
  id      := fun x => _;
  compose := fun x y z f g => _
|}.
Next Obligation.
  unfold Unused_obligation_1.
  unfold Unused_obligation_2.
  now destruct f.
Defined.

Program Definition UnusedVars : Vars := {|
  (* vars_mvars := {| mvars_objs := 1 *)
  (*                ; mvars_arrs := [ (@Fin.F1 0, @Fin.F1 0) ] |}; *)
  vars_cat   := Unused;
  vars_objs  := [tt];
  vars_arrs  := [ (@Fin.F1 0; (@Fin.F1 0; I)) ];
|}.
(* Next Obligation. *)
(*   unfold UnusedVars_obligation_1. *)
(*   apply Fin.caseS' with (p:=i); simpl; auto. *)
(*   inversion p. *)
(* Qed. *)
(* Next Obligation. *)
(*   unfold UnusedVars_obligation_1. *)
(*   apply Fin.caseS' with (p:=i); simpl; auto. *)
(*   inversion p. *)
(* Qed. *)

Record Environment := {
  meta : MetaEnv;

  _cat_i := positive;

  vars : list Vars;

  get_cat  (c : _cat_i) := vars_cat (nth_pos vars c UnusedVars);
  get_vars (c : _cat_i) := nth_pos vars c UnusedVars;

  _obj_i (c : _cat_i) := Fin.t (length (vars_objs (get_vars c)));

  get_obj_cat  c (o : _obj_i c) := c;
  get_obj      c (o : _obj_i c) := nth_fin (vars_objs (get_vars c)) o;

  _arr_i (c : _cat_i) := Fin.t (length (vars_arrs (get_vars c)));

  get_arr_def  c (a : _arr_i c) := nth_fin (vars_arrs (get_vars c)) a;

  get_arr_cat  c (a : _arr_i c) := c;
  get_arr_dom  c (a : _arr_i c) := `1 (get_arr_def c a);
  get_arr_cod  c (a : _arr_i c) := `1 `2 (get_arr_def c a);
  get_arr      c (a : _arr_i c) := `2 `2 (get_arr_def c a)
}.

Variable env : Environment.

Notation cat_idx := positive.

Inductive WellTyped {c : positive} {m : MetaEnv} dom cod : Term c m -> Type :=
  | Identity_wt x :
      Term_well_typed c m dom cod (Identity c m x) ->
      within_bounds x (vars_objs (get_vars env c)) ->
        WellTyped dom cod (Identity c m x)

  | Morph_wt f
      (Hf : within_bounds f (vars_arrs (get_vars env c)))
      (Hd : within_bounds (arr_dom m c f) (vars_objs (get_vars env c)))
      (Hc : within_bounds (arr_cod m c f) (vars_objs (get_vars env c))) :
      Term_well_typed c m dom cod (Morph c m f) ->
      Pos_to_fin (arr_dom m c f) Hd = get_arr_dom env c (Pos_to_fin f Hf) ->
      Pos_to_fin (arr_cod m c f) Hc = get_arr_cod env c (Pos_to_fin f Hf) ->
       WellTyped dom cod (Morph c m f)

  | Compose_wt f g :
      Term_well_typed c m dom cod (Compose c m f g) ->
      WellTyped (TermCod c m g) cod f ->
      WellTyped dom (TermCod c m g) g ->
        WellTyped dom cod (Compose c m f g).

Variable c : cat_idx.

Arguments get_cat {_} _.
Arguments get_obj_cat {_ _} _.
Arguments get_obj {_ _} _.
Arguments get_arr_cat {_ _} _.
Arguments get_arr_dom {_ _} _.
Arguments get_arr_cod {_ _} _.
Arguments get_arr {_ _} _.

Notation Term    := (Term    c (meta env)).
Notation TermDom := (TermDom c (meta env)).
Notation TermCod := (TermCod c (meta env)).

Definition getTermDom `(w : @WellTyped c (meta_env env) dom' cod' e) :
  _obj_i env c.
Proof.
  generalize dependent cod'.
  generalize dependent dom'.
  induction e; intros; inversion w; simpl in H0; subst.
  - apply Pos_to_fin with (x:=o).
    apply H1.
  - apply Pos_to_fin with (x:=arr_dom (meta_env env) c a).
    apply Hd.
  - apply (IHe2 _ _ H3).
Defined.

Definition getTermCod `(w : @WellTyped c (meta_env env) dom' cod' e) :
  _obj_i env c.
Proof.
  generalize dependent cod'.
  generalize dependent dom'.
  induction e; intros; inversion w; simpl in H0; subst.
  - apply Pos_to_fin with (x:=o).
    apply H1.
  - apply Pos_to_fin with (x:=arr_cod (meta_env env) c a).
    apply Hc.
  - apply (IHe1 _ _ H2).
Defined.

Fixpoint denote' `(w : @WellTyped c (meta_env env) dom' cod' e) :
  option (get_obj dom' ~{ get_cat c }~> get_obj (getTermCod w)).
Proof.
  destruct e as [o|a|f g].
  - (* destruct (Nat.eq_dec o dom); [|exact None]. *)
    (* destruct (Nat.eq_dec o cod); [|exact None]. *)
    subst; exact (Some id).
  - (* destruct (Nat.eq_dec (get_arr_dom a) dom); [|exact None]. *)
    (* destruct (Nat.eq_dec (get_arr_cod a) cod); [|exact None]. *)
    inversion w; subst.
    pose (get_arr (Pos_to_fin (n:=length (vars_arrs (get_vars env c))) a Hf)).
    subst; exact (Some h).
  - destruct (denote' f); [|exact None].
    destruct (denote' g); [|exact None].
    destruct (Fin.eq_dec (TermCod g) (TermDom f)); [|exact None].
    rewrite e in h0.
    exact (Some (h ∘ h0)).
Defined.

Fixpoint denote dom cod (e : Term) :
  option (get_obj dom ~{ get_cat c }~> get_obj cod).
Proof.
  destruct e as [o|a|f g].
  - destruct (Fin.eq_dec o dom); [|exact None].
    destruct (Fin.eq_dec o cod); [|exact None].
    subst; exact (Some id).
  - destruct (Fin.eq_dec (get_arr_dom a) dom); [|exact None].
    destruct (Fin.eq_dec (get_arr_cod a) cod); [|exact None].
    subst; exact (Some (get_arr a)).
  - destruct (denote (TermCod g) cod f); [|exact None].
    destruct (denote dom (TermCod g) g); [|exact None].
    exact (Some (h ∘ h0)).
Defined.

Lemma denote_dom_cod {f dom cod f'} :
  denote dom cod f = Some f' ->
  TermDom f = dom /\ TermCod f = cod.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  induction f; intros dom cod; simpl; intros; equalities.
  specialize (IHf2 dom (TermCod f2)).
  specialize (IHf1 (TermCod f2) cod).
  equalities; intros.
  destruct (denote (TermCod f2) cod f1) eqn:?; try discriminate.
  destruct (denote dom (TermCod f2) f2) eqn:?; try discriminate.
  destruct (IHf1 _ eq_refl).
  destruct (IHf2 _ eq_refl).
  intuition.
Qed.

Definition Term_well_defined' (e : Term) : Type :=
  ∃ f, denote' e = Some f.

Definition Term_well_defined dom cod (e : Term) : Type :=
  ∃ f, denote dom cod e = Some f.

Theorem Term_well_defined_is_well_typed {e dom cod} :
  Term_well_defined dom cod e ->
  Term_well_typed dom cod e.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  induction e; simpl in *;
  intros dom cod [f H]; simpl in H; equalities.
  destruct (denote _ _ e1) eqn:?; try discriminate.
  destruct (denote _ _ e2) eqn:?; try discriminate.
  specialize (IHe1 (TermCod e2) cod (h; Heqo)).
  specialize (IHe2 dom (TermCod e2) (h0; Heqo0)).
  intuition.
  symmetry.
  eapply Term_well_typed_dom; eauto.
Qed.

Lemma denote_well_typed {p dom cod f} :
  denote dom cod p = Some f -> Term_well_typed dom cod p.
Proof.
  generalize dependent f.
  generalize dependent dom.
  generalize dependent cod.
  induction p; simpl; intros ????; equalities.
  destruct (denote _ _ p2) eqn:?;
  destruct (denote _ _ p1) eqn:?; intros; try discriminate.
  pose proof (denote_dom_cod Heqo).
  pose proof (denote_dom_cod Heqo0).
  intuition.
    eapply IHp1; eauto.
  eapply IHp2; eauto.
Qed.

Program Definition TermDef_Category : Category := {|
  obj := obj_i;
  hom := fun x y => ∃ l : Term, Term_well_defined x y l;
  homset := fun x y => {| equiv := fun f g =>
    normalize (`1 f) = normalize (`1 g) |};
  id := fun x => (Identity x; _);
  compose := fun _ _ _ f g => (Compose (`1 f) (`1 g); _);
  id_left := fun _ y f => ArrowList_id_left y (normalize (`1 f));
  id_right := fun x _ f => ArrowList_id_right (normalize (`1 f)) _ _;
  comp_assoc := fun x y z w f g h =>
    ArrowList_append_assoc
      (normalize (`1 f)) (normalize (`1 g)) (normalize (`1 h))
|}.
Next Obligation.
  eexists; simpl; equalities.
Defined.
Next Obligation.
  destruct X, X0.
  unshelve eexists; eauto.
    exact (x0 ∘ x).
  simpl.
  destruct (denote_dom_cod e).
  destruct (denote_dom_cod e0).
  equalities; subst.
  now rewrite e, e0.
Defined.
Next Obligation.
  eapply ArrowList_normalize_dom_cod_sound; eauto.
  eapply Term_well_defined_is_well_typed; eauto.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.
Next Obligation.
  rewrite ArrowList_append_assoc; auto;
  unfold Term_valid in *;
  equalities; congruence.
Qed.

Fixpoint normalize_denote_chain dom cod (a : Arrow) (gs : list Arrow) :
  option (get_obj dom ~{ get_cat c }~> get_obj cod).
Proof.
  destruct gs as [|g gs].
    destruct (Fin.eq_dec (@get_arr_dom env c a) dom); [|exact None].
    destruct (Fin.eq_dec (@get_arr_cod env c a) cod); [|exact None].
    subst; exact (Some (get_arr a)).
  destruct (Fin.eq_dec (@get_arr_cod env c a) cod); [|exact None].
  destruct (normalize_denote_chain dom (@get_arr_dom env c a) g gs); [|exact None].
  subst; exact (Some (get_arr a ∘ h)).
Defined.

(*
Fixpoint normalize_denote_chain dom cod
         (g : Arrow) (gs : list Arrow) {struct gs} :
  option (get_obj dom ~{ get_cat c }~> get_obj cod) :=
  match g, gs with
  | h, nil =>
    match get_arr h with
    | Some p =>
      match Pos.eq_dec c cat,
            Pos.eq_dec x dom, Pos.eq_dec y cod with
      | left Hcat, left Hdom, left Hcod =>
        Some (eq_rect y (fun z => objs env dom ~> objs env z cat)
                      (eq_rect x (fun z => objs env z ~> objs env y cat)
                               (eq_rect c (fun c => objs env x c ~> objs env y c)
                                        p Hcat) dom Hdom) cod Hcod)
      | _, _, _ => None
      end
    | _ => None
    end
  | Arr c1 x y h, Arr c2 z w j :: js =>
    match arrs env h c1 x y with
    | Some p =>
      match Pos.eq_dec c1 cat, Pos.eq_dec y cod with
      | left Hcat, left Hcod =>
        match normalize_denote_chain dom x (Arr c2 z w j) js with
        | Some q =>
          Some (eq_rect y (fun y => objs env dom ~> objs env y cat)
                        (eq_rect c1 (fun c => objs env x c ~> objs env y c)
                                 p Hcat ∘ q) cod Hcod)
        | _ => None
        end
      | _, _ => None
      end
    | _ => None
    end
  end.
*)

Corollary normalize_denote_chain_cod :
  ∀ (gs : list Arrow) f dom cod f',
    normalize_denote_chain dom cod f gs = Some f' ->
    cod = @get_arr_cod env c f.
Proof. destruct gs; simpl; intros; equalities. Qed.

Theorem normalize_denote_chain_compose {x xs y ys dom cod f} :
  normalize_denote_chain dom cod x (xs ++ y :: ys) = Some f ->
  ∃ mid g h, f ≈ g ∘ h ∧
    @get_arr_dom env c (last xs x) = mid ∧
    @get_arr_cod env c y = mid ∧
    normalize_denote_chain mid cod x xs = Some g ∧
    normalize_denote_chain dom mid y ys = Some h.
Proof.
  generalize dependent f.
  generalize dependent cod.
  generalize dependent y.
  apply ListOfArrows_rect with (x:=x) (l:=xs); simpl; intros.
  - equalities.
    destruct (normalize_denote_chain dom (get_arr_dom x0) y ys) eqn:?;
    try discriminate.
    exists _, (get_arr x0), h.
    inversion_clear H.
    rewrite Eq_eq_dec_refl; simpl.
    intuition.
    pose proof (normalize_denote_chain_cod _ _ _ _ _ Heqo); auto.
  - equalities.
    destruct (normalize_denote_chain
                dom (get_arr_dom x0) y (l ++ y0 :: ys)) eqn:?;
    try discriminate.
    destruct (X _ _ _ Heqo), s, s.
    equalities; subst.
    inversion_clear H.
    exists _, (get_arr x0 ∘ x2), x3.
    clear X.
    intuition.
    + now rewrite e, comp_assoc.
    + pose proof (normalize_denote_chain_cod _ _ _ _ _ Heqo); subst.
      replace (match l with
               | [] => y
               | _ :: _ => last l x0
               end) with (last l y); auto.
      induction l; auto.
      now rewrite !last_cons.
    + now rewrite a1.
Qed.

Lemma normalize_denote_chain_dom_cod :
  ∀ (gs : list Arrow) f dom cod f',
    normalize_denote_chain dom cod f gs = Some f' ->
    cod = @get_arr_cod env c f /\
    dom = @get_arr_dom env c (last gs f).
Proof.
  induction gs using rev_ind; intros.
    simpl in *.
    now equalities.
  rewrite last_rcons.
  apply normalize_denote_chain_compose in H.
  equalities; subst.
    now specialize (IHgs _ _ _ _ a2).
  simpl in b0.
  now equalities.
Qed.

Theorem normalize_denote_chain_append_dom_cod : ∀ x xs y ys dom cod f,
  normalize_denote_chain dom cod x (xs ++ y :: ys) = Some f ->
  @get_arr_dom env c (last xs x) = @get_arr_cod env c y.
Proof.
  intros.
  destruct (normalize_denote_chain_compose H).
  equalities; subst.
  now rewrite a1.
Qed.

(* The list [f; g; h] maps to [f ∘ g ∘ h]. *)
Definition normalize_denote dom cod (xs : ArrowList) :
  option (get_obj dom ~{ get_cat c }~> get_obj cod).
Proof.
  destruct xs as [o|f fs].
  - destruct (Fin.eq_dec o dom); [|exact None].
    destruct (Fin.eq_dec o cod); [|exact None].
    subst; exact (Some id).
  - exact (normalize_denote_chain dom cod f fs).
Defined.

Theorem normalize_list_cod {p dom cod f} :
  normalize_denote dom cod p = Some f -> ArrowList_cod p = cod.
Proof.
  intros; destruct p as [o|g []]; simpl in *; equalities.
Qed.

Theorem normalize_list_dom {p dom cod f} :
  normalize_denote dom cod p = Some f -> ArrowList_dom p = dom.
Proof.
  generalize dependent f.
  generalize dependent cod.
  induction p using ArrowList_list_rect; simpl in *; intros; equalities.
  destruct (normalize_denote_chain _ _ _ _) eqn:Heqe; try discriminate.
  rewrite <- (IHp _ _ Heqe); clear IHp.
  induction l using rev_ind; simpl in *; equalities.
  rewrite !last_rcons.
  destruct l; auto.
Qed.

Theorem normalize_denote_well_typed {p dom cod f} :
  normalize_denote dom cod p = Some f
    -> ∃ p', p = normalize p' ∧ Term_well_typed dom cod p'.
Proof.
  generalize dependent f.
  generalize dependent cod.
  induction p using ArrowList_list_rect; simpl in *; intros; equalities.
  - exists (Identity cod).
    simpl; intuition.
  - exists (Morph a).
    simpl; intuition.
  - destruct (normalize_denote_chain _ _ _ _) eqn:?; try discriminate.
    destruct (IHp _ _ Heqo), p.
    exists (Compose (Morph a1) x).
    simpl.
    inversion_clear H.
    intuition.
    + now rewrite <- e.
    + eapply Term_well_typed_cod; eauto.
    + symmetry.
      eapply Term_well_typed_cod; eauto.
    + erewrite Term_well_typed_cod; eauto.
Qed.

Theorem normalize_compose {x y dom cod f} :
  ArrowList_cod y = ArrowList_dom x ->
  normalize_denote dom cod (ArrowList_append x y) = Some f ->
  ∃ mid g h, f ≈ g ∘ h ∧
    ArrowList_dom x = mid ∧
    ArrowList_cod y = mid ∧
    normalize_denote mid cod x = Some g ∧
    normalize_denote dom mid y = Some h.
Proof.
  generalize dependent f.
  generalize dependent cod.
  induction x using ArrowList_list_rect; intros.
  - simpl in H.
    rewrite <- H.
    exists cod, (@id (get_cat c) _), f.
    rewrite ArrowList_id_left in H0; auto.
    rewrite (normalize_list_cod H0) in *.
    cat; simpl; equalities.
  - destruct y using ArrowList_list_rect; simpl in H.
    + exists dom, f, (@id (get_cat c) _).
      rewrite <- H0.
      pose proof (normalize_list_dom H0).
      rewrite ArrowList_id_right in * by auto.
      rewrite H, H1; clear H H1.
      cat; simpl in *; equalities.
    + rewrite ArrowList_append_chains in H0 by auto.
      apply (normalize_denote_chain_compose H0).
    + rewrite ArrowList_append_chains in H0 by auto.
      apply (normalize_denote_chain_compose H0).
  - destruct y using ArrowList_list_rect; simpl in H.
    + exists dom, f, (@id (get_cat c) _).
      rewrite ArrowList_id_right in H0 by auto.
      rewrite (normalize_list_dom H0); subst.
      rewrite H0.
      pose proof (normalize_list_dom H0).
      cat; simpl in *; equalities.
    + rewrite ArrowList_append_chains in H0 by auto.
      apply (normalize_denote_chain_compose H0).
    + rewrite ArrowList_append_chains in H0 by auto.
      apply (normalize_denote_chain_compose H0).
Qed.

Theorem normalize_sound {p dom cod f} :
  Term_well_typed dom cod p ->
  normalize_denote dom cod (normalize p) = Some f ->
  ∃ f', f ≈ f' ∧ denote dom cod p = Some f'.
Proof.
  generalize dependent dom.
  generalize dependent cod.
  induction p as [o|a|]; simpl in *; intros; equalities.
  - now exists f.
  - now exists f.
  - apply normalize_compose in H0; equalities; subst.
    + destruct (Fin.eq_dec (ArrowList_dom (normalize p1)) (TermCod p2)).
      * rewrite <- e in *.
        destruct (IHp1 _ _ _ H2 a2), (IHp2 _ _ _ H3 b0).
        equalities.
        rewrite b, e1.
        eexists; intuition.
        now rewrite <- e0, <- a0.
      * pose proof (ArrowList_normalize_dom_cod_sound H2);
        equalities;
        now rewrite a1 in H4.
    + clear IHp1 IHp2.
      pose proof (ArrowList_normalize_dom_cod_sound H2).
      pose proof (ArrowList_normalize_dom_cod_sound H3).
      equalities.
      now rewrite H4.
Qed.

Theorem normalize_apply dom cod : ∀ f g,
  Term_well_typed_bool dom cod f = true ->
  Term_well_typed_bool dom cod g = true ->
  ArrowList_beq (normalize f) (normalize g) = true ->
  normalize_denote dom cod (normalize f) ||| false = true ->
  denote dom cod f ≈ denote dom cod g.
Proof.
  intros.
  apply Term_well_typed_bool_sound in H.
  apply Term_well_typed_bool_sound in H0.
  pose proof (ArrowList_well_typed_sound H).
  apply ArrowList_beq_eq in H1.
  destruct (normalize_denote dom cod (normalize f)) eqn:?;
  try discriminate.
  destruct (normalize_sound H Heqo), p.
  rewrite e0; clear e0.
  rewrite H1 in Heqo; clear H1.
  destruct (normalize_sound H0 Heqo), p.
  rewrite e1; clear e1.
  red.
  rewrite <- e, <- e0.
  reflexivity.
Qed.

Corollary normalize_denote_terms dom cod : ∀ f g,
  Term_well_typed_bool dom cod f = true ->
  Term_well_typed_bool dom cod g = true ->
  ArrowList_beq (normalize f) (normalize g) = true ->
  normalize_denote dom cod (normalize f) ||| false = true ->
  normalize_denote dom cod (normalize f)
    ≈ normalize_denote dom cod (normalize g) ->
  denote dom cod f ≈ denote dom cod g.
Proof. intros; apply normalize_apply; auto. Qed.

Corollary normalize_denote_terms_impl dom cod : ∀ f g,
  ArrowList_beq (normalize f) (normalize g) = true ->
  normalize_denote dom cod (normalize f)
    ≈ normalize_denote dom cod (normalize g).
Proof.
  intros.
  apply ArrowList_beq_eq in H.
  now rewrite H.
Qed.

End Denotation.

Import ListNotations.

(** Lists in Ltac *)

Ltac addToList x xs :=
  let rec go ys :=
    lazymatch ys with
    | tt => constr:((x, xs))
    | (x, _) => xs
    | (_, ?ys') => go ys'
    end in
  go xs.

Ltac listSize xs :=
  lazymatch xs with
  | tt => constr:(0%nat)
  | (_, ?xs') =>
    let n := listSize xs' in
    constr:((S n)%nat)
  end.

Ltac lookup n x xs :=
  match n with
  | O => constr:(@Fin.F1 0)
  | S ?n' =>
    lazymatch xs with
    | (x, _) => constr:(@Fin.F1 n')
    | (_, ?xs') =>
      let xn := lookup n' x xs' in
      constr:(@Fin.FS n' xn)
    end
  end.

Ltac lookupCat c cs :=
  lazymatch cs with
  | ((c, _, _), _) => constr:(0%nat)
  | (_, ?cs') =>
    let cn := lookupCat c cs' in
    constr:(S cn)
  end.

(** Lists of lists in Ltac *)

Ltac addToCatList c cs :=
  let rec go xs :=
    lazymatch xs with
    | tt => constr:(((c, tt, tt), cs))
    | ((c, _, _), _) => constr:(cs)
    | (_, ?xs') => go xs'
    end in
  go cs.

Ltac catLists c cs :=
  lazymatch cs with
  | ((c, ?os, ?fs), _) => constr:((os, fs))
  | (_, ?cs') => catLists c cs'
  end.

Ltac updateCat c cs os fs :=
  let rec go xs :=
    lazymatch xs with
    | ((c, _, _), ?xs') => constr:(((c, os, fs), xs'))
    | tt => constr:(tt)
    | (?x, ?xs') =>
      let xs' := go xs' in
      constr:((x, xs'))
    end in
  go cs.

Ltac addToObjList c cs o :=
  let res := catLists c cs in
  match res with
  | (?os, ?fs) =>
    let os' := addToList o os in
    updateCat c cs os' fs
  end.

Ltac addToArrList c cs f :=
  let res := catLists c cs in
  match res with
  | (?os, ?fs) =>
    let fs' := addToList f fs in
    updateCat c cs os fs'
  end.

Ltac lookupObj c cs o :=
  let res := catLists c cs in
  match res with
  | (?os, _) =>
    let len := listSize os in
    lookup len o os
  end.

Ltac lookupArr c cs f :=
  let res := catLists c cs in
  match res with
  | (_, ?fs) =>
    let len := listSize fs in
    lookup len f fs
  end.

(** Variable capture *)

Ltac allVars cs e :=
  lazymatch e with
  | @id ?c ?o => let cs := addToCatList c cs in addToObjList c cs o
  | ?f ∘ ?g   => let cs := allVars cs f in allVars cs g
  | ?P -> ?Q  => let cs := allVars cs P in allVars cs Q
  | ?X ≈ ?Y   => let cs := allVars cs X in allVars cs Y
  | ?f => lazymatch type of f with
    | ?x ~{?c}~> ?y =>
      let cs := addToCatList c cs in
      let cs := addToObjList c cs x in
      let cs := addToObjList c cs y in
      addToArrList c cs f
    end
  end.

(** Term capture *)

Ltac reifyTerm env cs t :=
  lazymatch t with
  | @id ?c ?x =>
    let cn := lookupCat c cs in
    let xn := lookupObj c cs x in
    constr:(Identity env cn xn)
  | @compose ?c _ _ _ ?f ?g =>
    let cn := lookupCat c cs in
    let ft := reifyTerm env cs f in
    let gt := reifyTerm env cs g in
    constr:(Compose env cn ft gt)
  | ?f =>
    lazymatch type of f with
    | ?x ~{?c}~> ?y =>
      let cn := lookupCat c cs in
      let fn := lookupArr c cs f in
      constr:(Morph env cn fn)
    end
  end.

(** Build environment *)

Ltac listify xs ty f :=
  lazymatch xs with
  | tt => constr:(@nil ty)
  | (?x, ?xs') =>
    let x'  := f x in
    let xs' := listify xs' ty f in
    constr:(x' :: xs')
  end.

Ltac vectorize xs ty f :=
  let l := listify xs ty f in
  constr:(l).

Ltac build_env cs :=
  let cs' := vectorize cs Vars ltac:(fun x =>
    match x with
    | (?c, ?os, ?fs) =>
      let os' := vectorize os c ltac:(fun x => x) in
      let fs' := vectorize fs
        (∃ (dom cod : Fin.t (length os')),
           nth_fin os' dom ~{c}~> nth_fin os' cod)
        ltac:(fun f => match type of f with
          | ?x ~{c}~> ?y =>
            let xn := lookupObj c cs x in
            let yn := lookupObj c cs y in
            constr:(existT
                      (fun dom => ∃ (cod : Fin.t (length os')),
                           nth_fin os' dom ~{c}~> nth_fin os' cod) xn
                   (existT
                      (fun cod =>
                         nth_fin os' xn ~{c}~> nth_fin os' cod) yn
                    f))
          end) in
      constr:({| vars_cat  := c
               ; vars_objs := os'
               ; vars_arrs := fs' |})
    end) in
  constr:({| num_cats := length cs'; cats := cs' |}).

Ltac find_vars :=
  lazymatch goal with
  | [ |- ?G ] =>
    let cs := allVars tt G in
    pose cs;
    let env := build_env cs in
    pose env
  end.

Goal ∀ (C : Category) (x y : C) (f : x ~> y),
    @nth_fin C [y; x] (@Fin.FS 1 (@Fin.F1 0)) ~{ C}~> @nth_fin C [y; x] (@Fin.F1 1).
  simpl.

Example sample_1 : ∀ (C : Category) (x y : C) (f : x ~> y),
  f ≈ f.
Proof.
  intros.
  find_vars.
Abort.

Definition term_wrapper {A : Type} (x : A) : A := x.

Ltac reify_terms_and_then tacHyp tacGoal :=
  repeat match goal with
  | [ H : ?S ≈ ?T |- _ ] =>
    let cs  := allVars tt S in
    let cs  := allVars cs T in
    let env := build_env cs in
    let env := eval compute [length] in env in
    let r1  := reifyTerm env cs S in
    let r2  := reifyTerm env cs T in
    change (denote env (TermCat env _ r1)
                   (TermDom env _ r1) (TermCod env _ r1) r1 ≈
            denote env (TermCat env _ r2)
                   (TermDom env _ r2) (TermCod env _ r2) r2) in H;
    tacHyp env r1 r2 H;
    lazymatch type of H with
    | ?U ≈ ?V => change (term_wrapper (U ≈ V)) in H
    end
  | [ |- ?S ≈ ?T ] =>
    let cs  := allVars tt S in
    let cs  := allVars cs T in
    let env := build_env cs in
    let env := eval compute [length] in env in
    let r1  := reifyTerm env cs S in
    let r2  := reifyTerm env cs T in
    change (denote env (TermCat env _ r1)
                   (TermDom env _ r1) (TermCod env _ r1) r1 ≈
            denote env (TermCat env _ r2)
                   (TermDom env _ r2) (TermCod env _ r2) r2);
    tacGoal env r1 r2
  end.

Ltac reify :=
  reify_terms_and_then
    ltac:(fun env r1 r2 H => pose env; pose r1; pose r2; pose H)
    ltac:(fun env r1 r2   => pose env; pose r1; pose r2).

Ltac categorical :=
  reify_terms_and_then
    ltac:(fun env r1 r2 H => idtac)
    ltac:(fun env r1 r2 =>
      apply (normalize_apply env (TermCat env _ r1)
                             (TermDom env _ r1) (TermCod env _ r1) r1 r2);
      vm_compute; reflexivity).

Ltac normalize :=
  reify_terms_and_then
    ltac:(fun env r1 r2 H =>
      let H1 := fresh "H" in
      assert (H1 : ArrowList_beq (normalize r1) (normalize r2) = true)
        by (vm_compute; reflexivity);
      (* If we reorganize the arguments and "apply .. in H", this operation is
         about 8% slower than if we pose it in the context and clear H. *)
      let N := fresh "N" in
      pose proof (normalize_denote_terms_impl
                    env (TermCat env _ r1)
                    (TermDom env _ r1) (TermCod env _ r1) r1 r2 H1) as N;
      clear H H1;
      cbv beta iota zeta delta
        [ normalize normalize_denote normalize_denote_chain
          ArrowList_append
          TermCat TermDom TermCod
          sumbool_rec sumbool_rect
          eq_rect eq_ind_r eq_ind eq_sym ] in N;
      red in N;
      rename N into H)
    ltac:(fun env r1 r2 =>
      apply (normalize_denote_terms
               env (TermCat env _ r1)
               (TermDom env _ r1) (TermCod env _ r1) r1 r2);
      [ vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | idtac ]);
  unfold term_wrapper in *; simpl in *.

Example sample_2 :
  ∀ (C : Category) (x y z w : C) (f : z ~> w) (g : y ~> z) (h : x ~> y),
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    g ∘ id ∘ id ∘ id ∘ h ≈ g ∘ h ->
    f ∘ (id ∘ g ∘ h) ≈ (f ∘ g) ∘ h.
Proof.
  intros.
  match goal with
  | [ |- ?S ≈ ?T ] =>
    let cs  := allVars tt S in
    let cs  := allVars cs T in
    let env := build_env cs in
    let env := eval compute [length] in env in
    let r1  := reifyTerm env cs S in
    let r2  := reifyTerm env cs T in
    pose (denote env (TermCat env _ r1)
                 (TermDom env _ r1) (TermCod env _ r1) r1)(* ; *)
    (* pose (denote env (TermCat env _ r2) *)
    (*              (TermDom env _ r2) (TermCod env _ r2) r2) *)
  end.
  compute [get_obj get_cat get_vars cats
           get_arr_dom get_arr_cod get_arr_def
           TermCat TermCod TermDom
           vars_objs vars_arrs vars_cat nth] in o.
  simpl nth_fin in o.
  simpl projT1 in o.
  simpl projT2 in o.
  compute [get_obj get_cat get_vars cats
           get_arr_dom get_arr_cod get_arr_def
           TermCat TermCod TermDom
           vars_objs vars_arrs vars_cat nth] in o.
  simpl nth_fin in o.
  simpl projT1 in o.
  simpl projT2 in o.
  unfold eq_rect in o.
  (* Time normalize. *)
  (* categorical. *)
Abort.

(* Print Assumptions sample_2. *)

Require Import Category.Theory.Adjunction.

Local Obligation Tactic :=
  cat_simpl; proper; simpl in *;
  try erewrite !normalize_denormalize; eauto;
  try (eapply ArrowList_append_well_typed;
       [ eapply ArrowList_well_typed_dom
       | eapply ArrowList_well_typed_cod | | ]); eauto.

Hint Resolve ArrowList_well_typed_sound.
Hint Resolve denormalize_well_typed.

(* This adjunction establishes that Term is our free category, with ArrowList
   equivalent up to normalization of terms with a canonical mapping back into
   Term by "denormalization".

   Since the objects of both categories are the same, the monad this gives
   rise to is uninteresting. *)
Program Instance Term_ArrowList_Adjunction (env : Environment) (c : _cat_i env) :
  ArrowList_to_Term env c ⊣ Term_to_ArrowList env c := {
  adj := fun x y =>
    {| to   := {| morphism := fun f => (normalize env c (_ f); _) |}
     ; from := {| morphism := _ |} |}
}.

Print Assumptions Term_ArrowList_Adjunction.
