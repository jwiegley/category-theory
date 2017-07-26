Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.quote.Quote.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.PArith.PArith.

Generalizable All Variables.

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

Definition cat_idx := positive.
Definition obj_idx := positive.
Definition arr_idx := positive.

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

Open Scope positive_scope.

(* This describes the morphisms of a magmoid, which forms a quotient category
   under denotation. *)
Inductive Term : Set :=
  | Identity : cat_idx -> obj_idx -> Term
  | Morph    : cat_idx -> obj_idx -> obj_idx -> arr_idx -> Term
  | Compose  : Term -> Term -> Term.

Fixpoint TermCat (e : Term) : cat_idx :=
  match e with
  | Identity x _  => x
  | Morph x _ _ _ => x
  | Compose f _ => TermCat f
  end.

Fixpoint TermDom (e : Term) : obj_idx :=
  match e with
  | Identity _ x  => x
  | Morph _ x _ _ => x
  | Compose _ g => TermDom g
  end.

Fixpoint TermCod (e : Term) : obj_idx :=
  match e with
  | Identity _ x  => x
  | Morph _ _ x _ => x
  | Compose f _ => TermCod f
  end.

Section Denotation.

Inductive Arrow : Set :=
  | Arr : cat_idx -> obj_idx -> obj_idx -> arr_idx -> Arrow.

Open Scope lazy_bool_scope.

Fixpoint Arrow_beq (x y : Arrow) {struct x} : bool :=
  match x with
  | Arr cat dom cod arr =>
      match y with
      | Arr cat' dom' cod' arr' =>
        (cat =? cat') &&& (dom =? dom') &&& (cod =? cod') &&& (arr =? arr')
      end
  end.

Lemma Arrow_beq_eq x y :
  Arrow_beq x y = true -> x = y.
Proof.
  destruct x, y; simpl.
  intros.
  destruct (c  =? c0) eqn:?; [|discriminate].
  destruct (o  =? o1) eqn:?; [|discriminate].
  destruct (o0 =? o2) eqn:?; [|discriminate].
  destruct (a  =? a0) eqn:?; [|discriminate].
  apply Peqb_true_eq in Heqb.
  apply Peqb_true_eq in Heqb0.
  apply Peqb_true_eq in Heqb1.
  apply Peqb_true_eq in Heqb2.
  subst; reflexivity.
Qed.

Definition Arrow_cat (f : Arrow) : cat_idx :=
  match f with Arr x _ _ _ => x end.

Definition Arrow_dom (f : Arrow) : obj_idx :=
  match f with Arr _ x _ _ => x end.

Definition Arrow_cod (f : Arrow) : obj_idx :=
  match f with Arr _ _ y _ => y end.

(* This describes the morphisms of a path, or free, category over a quiver of
   Arrows, while our environment describes a quiver (where vertices are all
   object indices, and edges are all arrow indices associated pairs of object
   indices). The denotation of an ArrowList to some category C is a forgetful
   functor from the path category over this quiver to C. Note that this
   functor is only total if the denotation of the quiver itself is total. *)
Inductive ArrowList : Set :=
  | IdentityOnly : cat_idx -> obj_idx -> ArrowList
  | ArrowChain   : Arrow -> list Arrow -> ArrowList.

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

Fixpoint ArrowList_beq  (x y : ArrowList) {struct x} : bool :=
  match x with
  | IdentityOnly cat cod =>
      match y with
      | IdentityOnly cat' cod' => (cat =? cat') &&& (cod =? cod')
      | ArrowChain _ _ => false
      end
  | ArrowChain x x0 =>
      match y with
      | IdentityOnly _ _ => false
      | ArrowChain x1 x2 => Arrow_beq x x1 &&& list_beq Arrow_beq x0 x2
      end
  end.

Definition ArrowList_cat (xs : ArrowList) : cat_idx :=
  match xs with
  | IdentityOnly x _ => x
  | ArrowChain (Arr x _ _ _) _ => x
  end.

Definition ArrowList_cod (xs : ArrowList) : obj_idx :=
  match xs with
  | IdentityOnly _ x => x
  | ArrowChain (Arr _ x y f) _ => y
  end.

Definition ArrowList_dom (xs : ArrowList) : obj_idx :=
  match xs with
  | IdentityOnly _ x => x
  | ArrowChain f xs =>
    match last xs f with
    | Arr _ x y m => x
    end
  end.

Inductive ForallAligned : list Arrow → Prop :=
    Align_nil : ForallAligned []
  | Align_singleton : ∀ (a : Arrow), ForallAligned [a]
  | Align_cons2 : ∀ (a b : Arrow) (l : list Arrow),
      Arrow_dom a = Arrow_cod b ->
      ForallAligned (b :: l) → ForallAligned (a :: b :: l).

Lemma ForallAligned_inv {x xs y} :
  ForallAligned (x :: y :: xs)
    -> Arrow_dom x = Arrow_cod y /\ ForallAligned (y :: xs).
Proof.
  generalize dependent x.
  generalize dependent y.
  induction xs; intros;
  inversion H; subst; intuition.
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

Lemma ForallAligned_app {x xs y ys} :
  ForallAligned (x :: xs ++ y :: ys)
    <-> ForallAligned (x :: xs) /\ ForallAligned (y :: ys) /\
        Arrow_cod y = Arrow_dom (last xs x).
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

Definition ArrowList_well_typed cat dom cod (xs : ArrowList) : Prop :=
  match xs with
  | IdentityOnly c x => c = cat /\ x = dom /\ x = cod
  | ArrowChain (Arr c x y f) xs =>
    y = cod /\
    match last xs (Arr c x y f) with
      Arr c' a b g => c = c' /\ a = dom
    end /\
    (* Ensure that it is a correctly type-aligned list *)
    Forall (fun '(Arr c x y f) => c = cat) (Arr c x y f :: xs) /\
    ForallAligned (Arr c x y f :: xs)
  end.

Lemma K_dec_on_type A (x : A) (eq_dec : ∀ y : A, x = y \/ x ≠ y)
      (P : x = x -> Type) :
  P (eq_refl x) -> forall p:x = x, P p.
Proof.
  intros.
  elim (@Eqdep_dec.eq_proofs_unicity_on A _) with x (eq_refl x) p.
    trivial.
  exact eq_dec.
Qed.

Lemma Neq_dec' : ∀ x y : positive, x = y \/ x ≠ y.
Proof.
  intros.
  destruct (Pos.eq_dec x y); auto.
Qed.

Lemma Neq_dec_refl n : Pos.eq_dec n n = left (@eq_refl positive n).
Proof.
  destruct (Pos.eq_dec n n).
    refine (K_dec_on_type positive n (Neq_dec' n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl positive n)) _ _).
    reflexivity.
  contradiction.
Qed.

Ltac equalities :=
  repeat (
    lazymatch goal with
    | [ H : context[match Pos.eq_dec ?N ?N with _ => _ end] |- _ ] =>
      rewrite Neq_dec_refl in H
    | [ |- context[match Pos.eq_dec ?N ?N with _ => _ end] ] =>
      rewrite Neq_dec_refl
    | [ H : context[match Pos.eq_dec ?N ?M with _ => _ end] |- _ ] =>
      destruct (Pos.eq_dec N M); subst
    | [ |- context[match Pos.eq_dec ?N ?M with _ => _ end] ] =>
      destruct (Pos.eq_dec N M); subst
    | [ |- context[if ?N =? ?N then _ else _] ] =>
      rewrite Pos.eqb_refl
    | [ |- context[if ?N =? ?M then _ else _] ] =>
      let Heqe := fresh "Heqe" in
      destruct (N =? M) eqn:Heqe
    | [ H : (_ &&& _) = true |- _ ] =>
      rewrite <- andb_lazy_alt in H
    | [ H : (_ && _) = true |- _ ] =>
      apply andb_true_iff in H;
      destruct H
    | [ H : _ /\ _ |- _ ] =>
      destruct H
    | [ H : _ ∧ _ |- _ ] =>
      destruct H
    | [ H : (_ =? _) = true |- _ ] =>
      apply Pos.eqb_eq in H; subst
    | [ H : (_ =? _) = false |- _ ] =>
      apply Pos.eqb_neq in H
    end;
    subst; simpl; auto;
    simpl TermDom in *;
    simpl TermCod in *;
    try discriminate;
    try tauto;
    try intuition idtac).

Corollary ArrowList_well_typed_cat {f cat dom cod } :
  ArrowList_well_typed cat dom cod f ->
    match f with
    | IdentityOnly c _ => c = cat
    | ArrowChain (Arr c _ _ _) xs =>
      c = cat /\ Forall (fun '(Arr c x y f) => c = cat) xs
    end.
Proof.
  induction f; simpl; intros; intuition.
  destruct a; equalities.
    destruct (last l (Arr c o cod a)); auto.
    now inversion H0.
  now inversion H0.
Qed.

Corollary ArrowList_well_typed_dom {f cat dom cod } :
  ArrowList_well_typed cat dom cod f -> ArrowList_dom f = dom.
Proof.
  induction f; simpl; intros; intuition.
  destruct a; equalities.
  destruct (last l (Arr c o cod a)); intuition.
Qed.

Corollary ArrowList_well_typed_cod {f cat dom cod} :
  ArrowList_well_typed cat dom cod f -> ArrowList_cod f = cod.
Proof.
  induction f; simpl; intros; intuition.
  destruct a; equalities.
Qed.

Definition ArrowList_list_rect : ∀ (P : ArrowList → Type),
  (∀ (c : cat_idx) (x : obj_idx), P (IdentityOnly c x)) →
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
  destruct y; simpl; split; intros; try discriminate.
  - equalities.
  - inversion_clear H.
    equalities.
    now apply Pos.eqb_eq.
  - destruct (Arrow_beq a a0) eqn:?; [|discriminate].
    apply Arrow_beq_eq in Heqb; subst.
    destruct l; now auto.
  - inversion_clear H.
    assert (∀ x, Arrow_beq x x = true).
      destruct x; simpl.
      now rewrite !Pos.eqb_refl.
    now rewrite H.
  - destruct (Arrow_beq a1 a) eqn:?; [|discriminate].
    apply Arrow_beq_eq in Heqb; subst.
    destruct l0; [discriminate|].
    destruct (Arrow_beq a2 a0) eqn:?; [|discriminate].
    apply Arrow_beq_eq in Heqb; subst.
    apply list_beq_eq in H; subst; auto.
    apply Arrow_beq_eq.
  - inversion_clear H.
    assert (∀ x, Arrow_beq x x = true).
      destruct x; simpl.
      now rewrite !Pos.eqb_refl.
    rewrite !H.
    clear -H.
    induction l; simpl; auto.
    now rewrite H.
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
  | IdentityOnly _ f, IdentityOnly c r =>
    IdentityOnly c r
  | IdentityOnly _ f, ArrowChain (Arr c x y g) xs =>
    ArrowChain (Arr c x y g) xs
  | ArrowChain f xs, IdentityOnly _ g =>
    ArrowChain f xs
  | ArrowChain f xs, ArrowChain (Arr c z w g) ys =>
    ArrowChain f (xs ++ Arr c z w g :: ys)
  end.

Lemma ArrowList_append_chains a a0 l l0 :
  ArrowList_dom (ArrowChain a l) = ArrowList_cod (ArrowChain a0 l0) ->
  ArrowList_append (ArrowChain a l) (ArrowChain a0 l0) =
  ArrowChain a (l ++ a0 :: l0).
Proof.
  generalize dependent a0.
  generalize dependent l0.
  simpl.
  induction l using rev_ind; simpl; intros.
    destruct a0, a; subst.
    reflexivity.
  rewrite last_app_cons in H; simpl in H.
  destruct x, a0, a.
  reflexivity.
Qed.

Lemma ArrowList_append_well_typed {cat dom mid cod f1 f2} :
  ArrowList_dom f1 = mid ->
  ArrowList_cod f2 = mid ->
  ArrowList_well_typed cat mid cod f1 ->
  ArrowList_well_typed cat dom mid f2 ->
    ArrowList_well_typed cat dom cod (ArrowList_append f1 f2).
Proof.
  generalize dependent mid.
  generalize dependent f2.
  induction f1 using ArrowList_list_rect; intros.
  - simpl in *.
    equalities; subst.
    destruct f2 using ArrowList_list_rect; simpl in *; auto.
      destruct a; auto.
    destruct a1, a2; auto.
  - destruct a.
    simpl in *; equalities; subst.
    destruct f2.
      simpl in *; subst; intuition.
    destruct a0.
    simpl in *; equalities.
    + induction l using rev_ind.
        simpl in *; equalities.
        inversion H2; subst.
        now inversion H.
      destruct x.
      rewrite !last_app_cons in *; simpl in *.
      intuition.
        replace (match l ++ [Arr c1 o1 o2 a1] with
                 | [] => Arr c0 o o0 a0
                 | _ :: _ => Arr c1 o1 o2 a1
                 end) with (Arr c1 o1 o2 a1) by (destruct l; auto).
      constructor; auto.
      inversion H2; subst.
      now inversion H.
    + constructor; auto.
      now inversion H.
    + constructor; auto.
  - clear IHf1.
    destruct a1, a2.
    equalities; subst.
    destruct f2.
      constructor; simpl in H1; intuition.
      simpl in *; subst.
      intuition.
      rewrite <- H2.
      destruct l; auto.
    rewrite ArrowList_append_chains by congruence.
    simpl; constructor.
      simpl in H1; intuition.
    rewrite last_app_cons, last_cons.
    pose proof (ArrowList_well_typed_cat H1) as H3.
    pose proof (ArrowList_well_typed_cat H2) as H4.
    pose proof (ArrowList_well_typed_dom H2) as H5.
    simpl in H3, H4, H5.
    replace (match l ++ a1 :: l0 with
             | [] => Arr c0 o1 o2 a0
             | _ :: _ => last l0 a1
             end) with (last l0 a1) by (destruct l; auto).
    split.
      destruct (last l0 a1) eqn:?c, a1; intuition; subst.
      symmetry.
      now sapply (last_Forall _ _ _ _ _ c1 H7).
    split.
      clear -H3 H4.
      destruct a1; intuition; subst.
      inversion H0; subst.
      do 2 constructor; auto.
      apply Forall_app.
      split; auto.
    clear -H1 H2.
    inversion H1.
    simpl in H2.
    rewrite 2!app_comm_cons.
    apply ForallAligned_app.
    destruct a1; intuition; subst.
Qed.

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

(* A term is valid constructed if composition composes compatible types. *)
Fixpoint Term_well_typed cat dom cod (e : Term) : Prop :=
  match e with
  | Identity c x  => c = cat /\ x = dom /\ x = cod
  | Morph c x y f => c = cat /\ x = dom /\ y = cod
  | Compose f g =>
    (* TermDom g = dom /\ *)
    (* TermCod f = cod /\ *)
    TermCod g = TermDom f /\
    Term_well_typed cat (TermCod g) cod f /\
    Term_well_typed cat dom (TermCod g) g
  end.

Fixpoint Term_well_typed_bool cat dom cod (e : Term) : bool :=
  match e with
  | Identity c x  => (c =? cat) &&& (x =? dom) &&& (x =? cod)
  | Morph c x y f => (c =? cat) &&& (x =? dom) &&& (y =? cod)
  | Compose f g =>
    (* (TermDom g =? dom) &&& *)
    (* (TermCod f =? cod) &&& *)
    (TermCod g =? TermDom f) &&&
    Term_well_typed_bool cat (TermCod g) cod f &&&
    Term_well_typed_bool cat dom (TermCod g) g
  end.

Lemma Term_well_typed_bool_sound cat dom cod e :
  Term_well_typed_bool cat dom cod e = true <-> Term_well_typed cat dom cod e.
Proof.
  generalize dependent dom.
  generalize dependent cod.
  induction e; simpl; intuition; equalities.
  - apply Pos.eqb_refl.
  - apply IHe1; auto.
  - apply IHe2; auto.
  - apply IHe1 in H.
    apply IHe2 in H2.
    rewrite H, H2; reflexivity.
Qed.

Corollary Term_well_typed_cat {f cat dom cod } :
  Term_well_typed cat dom cod f -> TermCat f = cat.
Proof.
  generalize dependent dom.
  induction f; simpl; intros; intuition.
  eapply IHf1; eauto.
Qed.

Corollary Term_well_typed_dom {f cat dom cod } :
  Term_well_typed cat dom cod f -> TermDom f = dom.
Proof.
  generalize dependent cod.
  induction f; simpl; intros; intuition.
  eapply IHf2; eauto.
Qed.

Corollary Term_well_typed_cod {f cat dom cod} :
  Term_well_typed cat dom cod f -> TermCod f = cod.
Proof.
  generalize dependent dom.
  induction f; simpl; intros; intuition.
  eapply IHf1; eauto.
Qed.

Fixpoint normalize (p : Term) : ArrowList :=
  match p with
  | Identity c x  => IdentityOnly c x
  | Morph c x y f => ArrowChain (Arr c x y f) []
  | Compose f g => ArrowList_append (normalize f) (normalize g)
  end.

Lemma ArrowList_append_cat f g :
  ArrowList_cat f = ArrowList_cat g ->
  ArrowList_cat (ArrowList_append f g) = ArrowList_cat g.
Proof.
  destruct g, f; simpl; intros; auto.
  - destruct a; subst; reflexivity.
  - destruct a; simpl.
    assumption.
Qed.

Lemma ArrowList_append_dom f g :
  ArrowList_dom f = ArrowList_cod g ->
  ArrowList_dom (ArrowList_append f g) = ArrowList_dom g.
Proof.
  destruct g, f; simpl; intros; auto.
  - destruct a; subst; reflexivity.
  - destruct a; simpl.
    rewrite last_app_cons.
    rewrite last_cons.
    reflexivity.
Qed.

Lemma ArrowList_append_cod f g :
  ArrowList_dom f = ArrowList_cod g ->
  ArrowList_cod (ArrowList_append f g) = ArrowList_cod f.
Proof.
  destruct f, g; simpl; intros; auto.
  - destruct a; subst; reflexivity.
  - destruct a0; reflexivity.
Qed.

Lemma ArrowList_normalize_cat_dom_cod_sound {p cat dom cod} :
  Term_well_typed cat dom cod p ->
  ArrowList_cat (normalize p) = cat /\
  ArrowList_dom (normalize p) = dom /\
  ArrowList_cod (normalize p) = cod.
Proof.
  generalize dependent cat.
  generalize dependent dom.
  generalize dependent cod.
  induction p; simpl; intros; intuition; subst;
  rewrite H0 in H;
  rewrite ArrowList_append_cat ||
  rewrite ArrowList_append_dom ||
  rewrite ArrowList_append_cod; auto;
  specialize (IHp1 _ _ _ H);
  specialize (IHp2 _ _ _ H2);
  intuition; congruence.
Qed.

Corollary ArrowList_specific_sound p :
  Term_well_typed (TermCat p) (TermDom p) (TermCod p) p ->
  ArrowList_cat (normalize p) = TermCat p /\
  ArrowList_dom (normalize p) = TermDom p /\
  ArrowList_cod (normalize p) = TermCod p.
Proof. apply ArrowList_normalize_cat_dom_cod_sound. Qed.

Lemma ArrowList_id_left c x y :
  ArrowList_cat y = c ->
  ArrowList_append (IdentityOnly c x) y = y.
Proof.
  simpl.
  destruct y; simpl; intros; subst; auto.
  destruct a; reflexivity.
Qed.

Lemma ArrowList_id_right f c y :
  ArrowList_cat f = c ->
  ArrowList_dom f = y ->
  ArrowList_append f (IdentityOnly c y) = f.
Proof.
  destruct f; simpl; intros; subst; auto.
Qed.

Lemma ArrowList_append_assoc x y z :
  ArrowList_append (ArrowList_append x y) z =
  ArrowList_append x (ArrowList_append y z).
Proof.
  destruct x, y, z; simpl; auto; intros;
  try destruct a;
  try destruct a0; subst; auto.
  destruct a1; simpl in *.
  rewrite <- app_assoc.
  reflexivity.
Qed.

(* We show here that ArrowList morphisms are just one way of representing a
   free category. However, we still forget identities and which way
   composition was associated, so really it's a normalized free category. *)
Program Definition ArrowList_Category (cat : cat_idx) : Category := {|
  obj := obj_idx;
  hom := fun x y =>
    ∃ l : ArrowList, ArrowList_well_typed cat x y l;
  homset := fun x y => {| equiv := fun f g => `1 f = `1 g |};
  id := fun x => (IdentityOnly cat x; _);
  compose := fun _ _ _ f g => (ArrowList_append (`1 f) (`1 g); _);
  id_left := fun _ y f => ArrowList_id_left cat y (`1 f) _;
  id_right := fun x _ f => ArrowList_id_right (`1 f) cat _ _ _;
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
  apply ArrowList_well_typed_cat in X.
  destruct f; simpl; auto.
  destruct a; intuition.
Qed.
Next Obligation.
  apply ArrowList_well_typed_cat in X.
  destruct f; simpl; auto.
  destruct a; intuition.
Qed.
Next Obligation.
  now apply ArrowList_well_typed_dom in X.
Qed.
Next Obligation. apply ArrowList_append_assoc; congruence. Qed.
Next Obligation. rewrite ArrowList_append_assoc; auto; congruence. Qed.
Next Obligation. rewrite ArrowList_append_assoc; auto; congruence. Qed.

(* In the category whose morphisms are Terms, homset equivalence is up to
   normalized terms. *)
Program Definition Term_Category (cat : cat_idx) : Category := {|
  obj := obj_idx;
  hom := fun x y => ∃ l : Term, Term_well_typed cat x y l;
  homset := fun x y => {| equiv := fun f g =>
    normalize (`1 f) = normalize (`1 g) |};
  id := fun x => (Identity cat x; _);
  compose := fun _ _ _ f g => (Compose (`1 f) (`1 g); _);
  id_left := fun _ y f => ArrowList_id_left cat y (normalize (`1 f)) _;
  id_right := fun x _ f => ArrowList_id_right (normalize (`1 f)) cat _ _ _;
  comp_assoc := fun x y z w f g h =>
    ArrowList_append_assoc
      (normalize (`1 f)) (normalize (`1 g)) (normalize (`1 h))
|}.
Next Obligation.
  pose proof (Term_well_typed_cat X).
  pose proof (Term_well_typed_cat X0).
  pose proof (Term_well_typed_dom X).
  pose proof (Term_well_typed_dom X0).
  pose proof (Term_well_typed_cod X).
  pose proof (Term_well_typed_cod X0).
  destruct f, g; simpl in *; intuition idtac; congruence.
Qed.
Next Obligation.
  eapply ArrowList_normalize_cat_dom_cod_sound; eauto.
Qed.
Next Obligation.
  eapply ArrowList_normalize_cat_dom_cod_sound; eauto.
Qed.
Next Obligation.
  eapply ArrowList_normalize_cat_dom_cod_sound; eauto.
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

Lemma ArrowList_well_typed_sound {f cat dom cod} :
  Term_well_typed cat dom cod f
    -> ArrowList_well_typed cat dom cod (normalize f).
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

Program Instance Term_to_ArrowList (cat : cat_idx) :
  Term_Category cat ⟶ ArrowList_Category cat := {
  fobj := fun x => x;
  fmap := fun x y f => (normalize _; _)
}.
Next Obligation. apply ArrowList_well_typed_sound; auto. Qed.

Fixpoint denormalize (f : ArrowList) : Term :=
  match f with
  | IdentityOnly c x  => Identity c x
  | ArrowChain (Arr c x y f) xs =>
    (fold_left (fun acc x => (fun y => Compose y x) \o acc)
               (map (fun x => match x with
                                Arr c x y f => Morph c x y f
                              end) xs)
               Datatypes.id) (Morph c x y f)
  end.

Lemma normalize_denormalize {cat dom cod f} :
  ArrowList_well_typed cat dom cod f
    -> normalize (denormalize f) = f.
Proof.
  destruct f; auto.
  generalize dependent a.
  generalize dependent dom.
  induction l using rev_ind; intros.
    destruct a; auto.
  rewrite <- ArrowList_append_chains at 2.
    rewrite <- (IHl (Arrow_cod x)); clear IHl.
      destruct a; simpl.
      rewrite map_app.
      rewrite fold_left_app.
      simpl.
      f_equal.
      destruct x; reflexivity.
    destruct a; simpl in *.
    destruct H, H0, H1.
    apply ForallAligned_app in H2.
    destruct H2, H3.
    intuition.
      destruct (last l (Arr c o o0 a)) eqn:?.
      simpl in H4.
      intuition.
      inversion H1; subst.
      apply Forall_app in H8.
      destruct H8.
      symmetry.
      now sapply (last_Forall _ _ _ _ _ Heqa0 H).
    constructor; inversion H1; subst; auto.
    now apply Forall_app in H8.
  destruct a; simpl in *.
  destruct H, H0.
  destruct H1.
  apply ForallAligned_app in H2.
  destruct H2, H3; intuition.
Qed.

Theorem denormalize_well_typed cat dom cod f :
  ArrowList_well_typed cat dom cod f
    -> Term_well_typed cat dom cod (denormalize f).
Proof.
  destruct f; auto.
  generalize dependent a.
  generalize dependent dom.
  induction l using rev_ind; intros.
    destruct a; simpl in *; intuition.
    now inversion H.
  assert (ArrowList_well_typed cat (Arrow_cod x) cod (ArrowChain a l)). {
    clear IHl.
    destruct a; simpl in *.
    destruct H, H0.
    destruct H1.
    apply ForallAligned_app in H2.
    destruct H2, H3; subst.
    rewrite last_app_cons in H0; simpl in H0.
    destruct x; intuition; subst.
      simpl in *.
      destruct (last l (Arr c0 o cod a)) eqn:?; auto.
      simpl in H4.
      inversion H1; subst; split; auto.
      apply Forall_app in H6.
      symmetry.
      now sapply (last_Forall _ _ _ _ _ Heqa1 (proj1 H6)).
    inversion H1; subst.
    constructor; auto.
    now apply Forall_app in H6.
  }
  rewrite <- ArrowList_append_chains.
  - specialize (IHl (Arrow_cod x) a H0).
    simpl in H, H0.
    destruct x, a; simpl.
    rewrite last_app_cons in H; simpl in H.
    equalities; subst.
    apply ForallAligned_app in H7.
    equalities.
    clear H0.
    rewrite map_app.
    rewrite fold_left_app.
    simpl in *.
    rewrite H7.
    intuition; subst.
    + clear -H.
      induction l using rev_ind; simpl; auto.
      rewrite map_app.
      rewrite fold_left_app; simpl in *.
      rewrite last_rcons in *.
      now destruct x.
    + induction l using rev_ind; simpl; auto.
    + now inversion H2.
  - destruct a; simpl in *.
    equalities; subst.
    apply ForallAligned_app in H6.
    equalities; intuition.
Qed.

Program Instance ArrowList_to_Term (cat : cat_idx) :
  ArrowList_Category cat ⟶ Term_Category cat := {
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

Record Environment := {
  cats : cat_idx -> Category;
  objs : obj_idx -> ∀ c : cat_idx, cats c;
  arrs : arr_idx -> ∀ (c : cat_idx) (a b : obj_idx),
           option (objs a c ~{cats c}~> objs b c)
}.

Variable env : Environment.

Fixpoint denote cat dom cod (e : Term) :
  option (objs env dom cat ~> objs env cod cat) :=
  match e with
  | Identity cat' t =>
    match Pos.eq_dec cat cat',
          Pos.eq_dec t dom, Pos.eq_dec t cod with
    | left pf_cat, left pf_dom, left pf_cod =>
      Some (match pf_cat, pf_dom, pf_cod with
            | eq_refl, eq_refl, eq_refl =>
              @id (cats env cat) (objs env t cat)
            end)
    | _, _ , _ => None
    end
  | Morph cat' dom' cod' n =>
    match Pos.eq_dec cat cat',
          Pos.eq_dec dom' dom, Pos.eq_dec cod' cod, arrs env n cat dom' cod' with
    | left pf_cat, left pf_dom, left pf_cod, Some arr =>
      Some (match pf_cat, pf_dom, pf_cod with
            | eq_refl, eq_refl, eq_refl => arr
            end)
    | _, _, _, _ => None
    end
  | Compose g f =>
    match denote cat dom (TermCod f) f, denote cat _ cod g with
    | Some farr, Some garr => Some (garr ∘ farr)
    | _ , _ => None
    end
  end.

Lemma denote_cat_dom_cod {f cat dom cod f'} :
  denote cat dom cod f = Some f' ->
  TermCat f = cat /\ TermDom f = dom /\ TermCod f = cod.
Proof.
  generalize dependent cod.
  generalize dependent dom.
  induction f; intros dom cod; simpl; intros; equalities.
  specialize (IHf2 dom (TermCod f2)).
  specialize (IHf1 (TermCod f2) cod).
  equalities.
  intros.
  destruct (denote cat dom (TermCod f2) f2) eqn:?; try discriminate.
  destruct (denote cat (TermCod f2) cod f1) eqn:?; try discriminate.
  destruct (IHf1 _ eq_refl).
  destruct (IHf2 _ eq_refl).
  tauto.
Qed.

Definition Term_well_defined cat dom cod (e : Term) : Type :=
  ∃ f, denote cat dom cod e = Some f.

Theorem Term_well_defined_is_well_typed {e cat dom cod} :
  Term_well_defined cat dom cod e ->
  Term_well_typed cat dom cod e.
Proof.
  generalize dependent dom.
  generalize dependent cod.
  generalize dependent cat.
  induction e; simpl in *;
  intros cat dom cod [f H]; simpl in H.
  - revert H; equalities.
  - revert H; equalities.
  - destruct (denote cat _ _ e2) eqn:?; try discriminate.
    destruct (denote cat _ _ e1) eqn:?; try discriminate.
    specialize (IHe1 cat dom (TermCod e2) (h0; Heqo0)).
    specialize (IHe2 cat (TermCod e2) cod (h; Heqo)).
    intuition.
    symmetry.
    eapply Term_well_typed_dom; eauto.
Qed.

Lemma denote_well_typed {p cat dom cod f} :
  denote cat dom cod p = Some f -> Term_well_typed cat dom cod p.
Proof.
  generalize dependent f.
  generalize dependent dom.
  generalize dependent cod.
  generalize dependent cat.
  induction p; simpl; intros ????; equalities.
  destruct (denote cat _ _ p2) eqn:?.
    destruct (denote cat _ _ p1) eqn:?.
      pose proof (denote_cat_dom_cod Heqo).
      pose proof (denote_cat_dom_cod Heqo0).
      firstorder eauto.
    intros; discriminate.
  intros; discriminate.
Qed.

Program Definition TermDef_Category (cat : cat_idx) : Category := {|
  obj := obj_idx;
  hom := fun x y => ∃ l : Term, Term_well_defined cat x y l;
  homset := fun x y => {| equiv := fun f g =>
    normalize (`1 f) = normalize (`1 g) |};
  id := fun x => (Identity cat x; _);
  compose := fun _ _ _ f g => (Compose (`1 f) (`1 g); _);
  id_left := fun _ y f => ArrowList_id_left cat y (normalize (`1 f)) _;
  id_right := fun x _ f => ArrowList_id_right (normalize (`1 f)) cat _ _ _;
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
  destruct (denote_cat_dom_cod e).
  destruct (denote_cat_dom_cod e0).
  equalities; subst.
  rewrite H1.
  rewrite e, e0.
  reflexivity.
Defined.
Next Obligation.
  eapply ArrowList_normalize_cat_dom_cod_sound; eauto.
  eapply Term_well_defined_is_well_typed; eauto.
Qed.
Next Obligation.
  eapply ArrowList_normalize_cat_dom_cod_sound; eauto.
  eapply Term_well_defined_is_well_typed; eauto.
Qed.
Next Obligation.
  eapply ArrowList_normalize_cat_dom_cod_sound; eauto.
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

Fixpoint normalize_denote_chain cat dom cod
         (g : Arrow) (gs : list Arrow) {struct gs} :
  option (objs env dom cat ~{ cats env cat }~> objs env cod cat) :=
  match g, gs with
  | Arr c x y h, nil =>
    match arrs env h c x y with
    | Some p =>
      match Pos.eq_dec c cat,
            Pos.eq_dec x dom, Pos.eq_dec y cod with
      | left Hcat, left Hdom, left Hcod =>
        Some (eq_rect y (fun z => objs env dom cat ~> objs env z cat)
                      (eq_rect x (fun z => objs env z cat ~> objs env y cat)
                               (eq_rect c (fun c => objs env x c ~> objs env y c)
                                        p cat Hcat) dom Hdom) cod Hcod)
      | _, _, _ => None
      end
    | _ => None
    end
  | Arr c1 x y h, Arr c2 z w j :: js =>
    match arrs env h c1 x y with
    | Some p =>
      match Pos.eq_dec c1 cat, Pos.eq_dec y cod with
      | left Hcat, left Hcod =>
        match normalize_denote_chain cat dom x (Arr c2 z w j) js with
        | Some q =>
          Some (eq_rect y (fun y => objs env dom cat ~> objs env y cat)
                        (eq_rect c1 (fun c => objs env x c ~> objs env y c)
                                 p cat Hcat ∘ q) cod Hcod)
        | _ => None
        end
      | _, _ => None
      end
    | _ => None
    end
  end.

Lemma normalize_denote_chain_cat :
  ∀ (gs : list Arrow) c x y f cat dom cod f',
    normalize_denote_chain cat dom cod (Arr c x y f) gs = Some f' ->
    cat = c.
Proof.
  destruct gs; simpl; intros.
    destruct (arrs _ _ _).
      revert H; equalities.
    discriminate.
  destruct a.
  destruct (arrs _ _ _); try discriminate;
  revert H; equalities.
Qed.

Lemma normalize_denote_chain_cod :
  ∀ (gs : list Arrow) c x y f cat dom cod f',
    normalize_denote_chain cat dom cod (Arr c x y f) gs = Some f' ->
    cod = y.
Proof.
  destruct gs; simpl; intros.
    destruct (arrs _ _ _).
      revert H; equalities.
    discriminate.
  destruct a.
  destruct (arrs _ _ _); try discriminate;
  revert H; equalities.
Qed.

Theorem normalize_denote_chain_compose {x xs y ys cat dom cod f} :
  normalize_denote_chain cat dom cod x (xs ++ y :: ys) = Some f ->
  ∃ mid g h, f ≈ g ∘ h ∧
    Arrow_dom (last xs x) = mid ∧
    Arrow_cod y = mid ∧
    normalize_denote_chain cat mid cod x xs = Some g ∧
    normalize_denote_chain cat dom mid y ys = Some h.
Proof.
  generalize dependent f.
  generalize dependent cod.
  generalize dependent y.
  apply ListOfArrows_rect with (x:=x) (l:=xs); simpl; intros;
  destruct x, x0, y; simpl.
  - destruct (arrs _ _ _); try discriminate.
    revert H; equalities.
    destruct (normalize_denote_chain cat dom o1 (Arr c1 o3 o4 a1) ys) eqn:?;
    try discriminate.
    exists _, h, h0.
    inversion_clear H.
    rewrite Neq_dec_refl; simpl.
    intuition.
    pose proof (normalize_denote_chain_cod _ _ _ _ _ _ _ _ _ Heqo2); auto.
  - destruct (arrs _ _ _) eqn:?; try discriminate.
    revert H; equalities.
    destruct (normalize_denote_chain cat dom o1 (Arr c1 o3 o4 a1)
                                     (l ++ y0 :: ys)) eqn:?;
    try discriminate.
    destruct (X _ _ _ Heqo2), s, s.
    equalities.
    subst.
    inversion_clear H.
    exists _, (h ∘ x0), x1.
    split.
      rewrite e.
      rewrite comp_assoc.
      reflexivity.
    rewrite a3, b.
    clear X.
    intuition.
    + pose proof (normalize_denote_chain_cat _ _ _ _ _ _ _ _ _ Heqo2); subst.
      pose proof (normalize_denote_chain_cod _ _ _ _ _ _ _ _ _ Heqo2); subst.
      admit.
      (* replace (match l with *)
      (*          | [] => Arr c1 o3 o4 a1 *)
      (*          | _ :: _ => last l (Arr c1 o4 cod a0) *)
      (*          end) with (last l (Arr c1 o4 cod a0)). *)
      (* * admit. *)
      (* * clear. *)
      (*   now induction l. *)
    + now rewrite a4.
Admitted.

Lemma normalize_denote_chain_cat_dom_cod :
  ∀ (gs : list Arrow) c x y f cat dom cod f',
    normalize_denote_chain cat dom cod (Arr c x y f) gs = Some f' ->
    cat = c /\
    cod = y /\
    dom = match last gs (Arr c x y f) with Arr _ z _ _ => z end.
Proof.
  induction gs using rev_ind; intros.
    simpl in H.
    destruct (arrs _ _ _).
      revert H; equalities.
    discriminate.
  rewrite last_rcons.
  destruct x.
  apply normalize_denote_chain_compose in H.
  destruct H, s, s.
  equalities; simpl in *;
  destruct (arrs _ _ _); try discriminate;
  revert b; equalities;
  specialize (IHgs _ _ _ _ _ _ _ _ a2);
  intuition.
Qed.

Theorem normalize_denote_chain_append_dom_cod : ∀ x xs y ys cat dom cod f,
  normalize_denote_chain cat dom cod x (xs ++ y :: ys) = Some f ->
  Arrow_dom (last xs x) = Arrow_cod y.
Proof.
  intros.
  destruct (normalize_denote_chain_compose H).
  firstorder.
  rewrite a0, a1.
  reflexivity.
Qed.

(* The list [f; g; h] maps to [f ∘ g ∘ h]. *)
Definition normalize_denote cat dom cod (xs : ArrowList) :
  option (objs env dom cat ~> objs env cod cat) :=
  match xs with
  | IdentityOnly c x =>
    match Pos.eq_dec c cat,
          Pos.eq_dec x dom, Pos.eq_dec x cod with
    | left Hcat, left Hdom, left Hcod =>
      Some (eq_rect x (fun z => objs env dom cat ~> objs env z cat)
              (eq_rect x (fun z => objs env z cat ~> objs env x cat)
                 (eq_rect c (fun z => objs env x z ~> objs env x z)
                          (@id (cats env c) (objs env x c)) cat Hcat)
                 dom Hdom)
              cod Hcod)
    | _, _, _ => None
    end
  | ArrowChain f fs => normalize_denote_chain cat dom cod f fs
  end.

Theorem normalize_list_cat {p cat dom cod f} :
  normalize_denote cat dom cod p = Some f -> ArrowList_cat p = cat.
Proof.
  intros.
  destruct p.
  - simpl in H; equalities.
  - destruct l; intros.
      simpl in *.
      destruct a.
      destruct (arrs _ _ _ _); equalities.
      discriminate.
    simpl in *.
    destruct a;
    equalities;
    destruct a0;
    destruct (arrs _ _ _ _); discriminate.
Qed.

Theorem normalize_list_cod {p cat dom cod f} :
  normalize_denote cat dom cod p = Some f -> ArrowList_cod p = cod.
Proof.
  intros.
  destruct p.
  - simpl in H; equalities.
  - destruct l; intros.
      simpl in *.
      destruct a.
      destruct (arrs _ _ _ _); equalities.
      discriminate.
    simpl in *.
    destruct a;
    equalities;
    destruct a0;
    destruct (arrs _ _ _ _); discriminate.
Qed.

Theorem normalize_list_dom {p cat dom cod f} :
  normalize_denote cat dom cod p = Some f -> ArrowList_dom p = dom.
Proof.
  generalize dependent f.
  generalize dependent cod.
  induction p using ArrowList_list_rect; intros.
  - simpl in H; equalities.
  - simpl in *.
    destruct a.
    destruct (arrs _ _ _ _); equalities.
    discriminate.
  - simpl in *.
    destruct a1, a2.
    destruct (arrs _ _ _); try discriminate.
    revert H; equalities.
    destruct (normalize_denote_chain cat dom o (Arr c0 o1 o2 a0) l) eqn:Heqe;
    try discriminate.
    rewrite <- (IHp _ _ Heqe); clear IHp.
    induction l using rev_ind.
      simpl in *.
      destruct (arrs _ _ _); try discriminate.
      revert H; equalities.
    rewrite !last_rcons.
    destruct l; auto.
Qed.

Theorem normalize_denote_well_typed {p cat dom cod f} :
  normalize_denote cat dom cod p = Some f
    -> ∃ p', p = normalize p' ∧ Term_well_typed cat dom cod p'.
Proof.
  generalize dependent f.
  generalize dependent cod.
  induction p using ArrowList_list_rect; simpl; intros.
  - revert H; equalities.
    exists (Identity cat cod).
    simpl; intuition.
  - destruct a.
    destruct (arrs _ _ _); try discriminate.
    revert H; equalities.
    exists (Morph cat dom cod a).
    simpl; intuition.
  - destruct a1, a2.
    destruct (arrs _ _ _); try discriminate.
    revert H; equalities.
    destruct (normalize_denote_chain cat dom o (Arr c0 o1 o2 a0) l) eqn:?;
    try discriminate.
    destruct (IHp _ _ Heqo0), p.
    exists (Compose (Morph cat o cod a) x).
    simpl.
    inversion_clear H.
    intuition.
    + rewrite <- e.
      reflexivity.
    + eapply Term_well_typed_cod; eauto.
    + symmetry.
      eapply Term_well_typed_cod; eauto.
    + erewrite Term_well_typed_cod; eauto.
Qed.

Theorem normalize_compose {x y cat dom cod f} :
  ArrowList_cat y = ArrowList_cat x ->
  ArrowList_cod y = ArrowList_dom x ->
  normalize_denote cat dom cod (ArrowList_append x y) = Some f ->
  ∃ mid g h, f ≈ g ∘ h ∧
    ArrowList_dom x = mid ∧
    ArrowList_cod y = mid ∧
    normalize_denote cat mid cod x = Some g ∧
    normalize_denote cat dom mid y = Some h.
Proof.
  generalize dependent f.
  generalize dependent cod.
  generalize dependent cat.
  induction x using ArrowList_list_rect; intros.
  - simpl in H.
    rewrite <- H0.
    simpl in H0.
    exists cod, (@id (cats env cat) _), f.
    pose proof (normalize_list_cat H1).
    rewrite ArrowList_id_left in H1, H2; auto.
    rewrite (normalize_list_cod H1) in *; subst.
    rewrite H1; clear H1.
    cat; simpl; equalities.
  - destruct y using ArrowList_list_rect; simpl in H.
    + destruct a; subst.
      exists dom, f, (@id (cats env cat) _).
      pose proof (normalize_list_cat H1).
      rewrite <- H0.
      rewrite ArrowList_id_right in H1 by auto.
      rewrite H1.
      pose proof (normalize_list_dom H1).
      simpl in H; subst.
      cat; simpl; equalities.
    + rewrite ArrowList_append_chains in H1 by auto.
      apply (normalize_denote_chain_compose H1).
    + rewrite ArrowList_append_chains in H1 by auto.
      apply (normalize_denote_chain_compose H1).
  - destruct y using ArrowList_list_rect; simpl in H.
    + destruct a1, a2.
      exists dom, f, (@id (cats env cat) _).
      rewrite ArrowList_id_right in H1 by auto.
      pose proof (normalize_list_cat H1).
      rewrite (normalize_list_dom H1); subst.
      rewrite H1.
      pose proof (normalize_list_dom H1).
      simpl in H; subst.
      cat; simpl; equalities.
    + rewrite ArrowList_append_chains in H1 by auto.
      apply (normalize_denote_chain_compose H1).
    + rewrite ArrowList_append_chains in H1 by auto.
      apply (normalize_denote_chain_compose H1).
Qed.

Theorem normalize_sound {p cat dom cod f} :
  Term_well_typed cat dom cod p ->
  normalize_denote cat dom cod (normalize p) = Some f ->
  ∃ f', f ≈ f' ∧ denote cat dom cod p = Some f'.
Proof.
  generalize dependent dom.
  generalize dependent cod.
  induction p; intros.
  - simpl in *; exists f; subst.
    split; [reflexivity|].
    equalities.
  - simpl in *; exists f; subst.
    split; [reflexivity|].
    equalities;
    destruct (arrs _ _ _); discriminate.
  - simpl in H.
    apply normalize_compose in H0;
    fold @normalize in *.
    + destruct H0, s, s.
      equalities.
      destruct (Pos.eq_dec x (TermCod p2)).
      * rewrite <- e in *.
        destruct (IHp1 _ _ _ H1 a2), (IHp2 _ _ _ H2 b0), p, p0.
        rewrite e3, e1.
        exists (x2 ∘ x3).
        split; auto.
        now rewrite <- e0, <- e2.
      * pose proof (ArrowList_normalize_cat_dom_cod_sound H2);
        equalities;
        now rewrite a1 in H4.
    + clear IHp1 IHp2.
      equalities.
      pose proof (ArrowList_normalize_cat_dom_cod_sound H2).
      pose proof (ArrowList_normalize_cat_dom_cod_sound H3).
      equalities.
      now rewrite H4.
    + clear IHp1 IHp2.
      equalities.
      pose proof (ArrowList_normalize_cat_dom_cod_sound H2).
      pose proof (ArrowList_normalize_cat_dom_cod_sound H3).
      equalities.
      now rewrite H5, H7.
Qed.

Theorem normalize_apply cat dom cod : ∀ f g,
  Term_well_typed_bool cat dom cod f = true ->
  Term_well_typed_bool cat dom cod g = true ->
  ArrowList_beq (normalize f) (normalize g) = true ->
  normalize_denote cat dom cod (normalize f) ||| false = true ->
  denote cat dom cod f ≈ denote cat dom cod g.
Proof.
  intros.
  apply Term_well_typed_bool_sound in H.
  apply Term_well_typed_bool_sound in H0.
  pose proof (ArrowList_well_typed_sound H).
  apply ArrowList_beq_eq in H1.
  destruct (normalize_denote cat dom cod (normalize f)) eqn:?;
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

Corollary normalize_denote_terms cat dom cod : ∀ f g,
  Term_well_typed_bool cat dom cod f = true ->
  Term_well_typed_bool cat dom cod g = true ->
  ArrowList_beq (normalize f) (normalize g) = true ->
  normalize_denote cat dom cod (normalize f) ||| false = true ->
  normalize_denote cat dom cod (normalize f)
    ≈ normalize_denote cat dom cod (normalize g) ->
  denote cat dom cod f ≈ denote cat dom cod g.
Proof. intros; apply normalize_apply; auto. Qed.

Corollary normalize_denote_terms_impl cat dom cod : ∀ f g,
  ArrowList_beq (normalize f) (normalize g) = true ->
  normalize_denote cat dom cod (normalize f)
    ≈ normalize_denote cat dom cod (normalize g).
Proof.
  intros.
  apply ArrowList_beq_eq in H.
  now rewrite H.
Qed.

End Denotation.

Import ListNotations.

(** Lists in Ltac *)

Ltac inList x xs :=
  lazymatch xs with
  | tt => false
  | (x, _) => true
  | (_, ?xs') => inList x xs'
  end.

Ltac addToList x xs :=
  let b := inList x xs in
  lazymatch b with
  | true => xs
  | false => constr:((x, xs))
  end.

Ltac lookup x xs :=
  lazymatch xs with
  | (x, _) => constr:(1)
  | (_, ?xs') =>
    let n := lookup x xs' in
    constr:(Pos.succ n)
  end.

(** Variable capture *)

Ltac allVars cs fs xs e :=
  lazymatch e with
  | @id ?c ?x =>
    let cs := addToList c cs in
    let xs := addToList x xs in
    constr:((cs, fs, xs))
  | ?e1 ∘ ?e2 =>
    let res := allVars cs fs xs e1 in
    lazymatch res with
      (?cs, ?fs, ?xs) => allVars cs fs xs e2
    end
  | ?f =>
    lazymatch type of f with
    | ?x ~{?c}~> ?y =>
      let cs := addToList c cs in
      let xs := addToList x xs in
      let xs := addToList y xs in
      let fs := addToList f fs in
      constr:((cs, fs, xs))
    end
  end.

(** Term capture *)

Ltac reifyTerm cs fs xs t :=
  lazymatch t with
  | @id ?C ?X =>
    let c := lookup C cs in
    let x := lookup X xs in
    constr:(Identity c x)
  | ?X1 ∘ ?X2 =>
    let r1 := reifyTerm cs fs xs X1 in
    let r2 := reifyTerm cs fs xs X2 in
    constr:(Compose r1 r2)
  | ?F =>
    let n := lookup F fs in
    lazymatch type of F with
    | ?X ~{?C}~> ?Y =>
      let c := lookup C cs in
      let x := lookup X xs in
      let y := lookup Y xs in
      constr:(Morph c x y n)
    end
  end.

(** Build environment *)

Ltac cats_function cs :=
  let rec loop i cs' :=
    lazymatch cs' with
    | (?c, tt) => constr:(fun (_ : cat_idx) => c)
    | (?c, ?cs'') =>
      let f := loop (Pos.succ i) cs'' in
      constr:(fun (i' : cat_idx) =>
                if i =? i' then c else f i')
    end in
  loop 1 cs.

Ltac objects_function xs :=
  let rec loop o xs' :=
    lazymatch xs' with
    | (?x, tt) => constr:(fun (_ : obj_idx) (_ : cat_idx) => x)
    | (?x, ?xs'') =>
      let f := loop (Pos.succ o) xs'' in
      constr:(fun (o' : obj_idx) (c' : cat_idx) =>
                if o =? o' then x else f o' c')
    end in
  loop 1 xs.

Ltac observe n f cs cats xs objs k :=
  lazymatch type of f with
  | ?X ~{?C}~> ?Y =>
    let cn := lookup C cs in
    let xn := lookup X xs in
    let yn := lookup Y xs in
    constr:(fun (i : arr_idx) (c : cat_idx) (x y : obj_idx) =>
      (* It's unfortunate that we have to carry this structure in the type; if
         we moved to a typed representation of arrows (where they return
         appropriate object types), we won't need to do this here. *)
      if i =? n
      then (match Pos.eq_dec cn c, Pos.eq_dec xn x, Pos.eq_dec yn y with
            | left Hc, left Hx, left Hy =>
              @Some (objs x c ~{cats c}~> objs y c)
                    (eq_rect yn (fun y => objs x c ~{cats c}~> objs y c)
                       (eq_rect xn (fun x => objs x c ~{cats c}~> objs yn c)
                          (eq_rect cn (fun c => objs xn c ~{cats c}~> objs yn c)
                                   f c Hc)
                          x Hx)
                       y Hy)
            | _, _, _ => k i c x y
            end)
      else k i c x y)
  end.

Ltac arrows_function fs cs cats xs objs :=
  let rec loop n fs' :=
    lazymatch fs' with
    | tt =>
      constr:(fun _ c x y : obj_idx => @None (objs x c ~{cats c}~> objs y c))
    | (?f, tt) =>
      observe n f cs cats xs objs
              (fun _ c x y : obj_idx => @None (objs x c ~{cats c}~> objs y c))
    | (?f, ?fs'') =>
      let k := loop (Pos.succ n) fs'' in
      observe n f cs cats xs objs k
    end in
  loop 1 fs.

Definition term_wrapper {A : Type} (x : A) : A := x.

Ltac reify_terms_and_then tacHyp tacGoal :=
  repeat match goal with
  | [ H : ?S ≈ ?T |- _ ] =>
    let env := allVars tt tt tt S in
    lazymatch env with
      (?cs, ?fs, ?xs) =>
      let env := allVars cs fs xs T in
      lazymatch env with
        (?cs, ?fs, ?xs) =>
        let cats := cats_function cs in
        let objs := objects_function xs in
        let arrs := arrows_function fs cs cats xs objs in
        let env  := constr:({| cats := cats; objs := objs; arrs := arrs |}) in
        let env  := eval compute[Pos.succ] in env in
        let r1  := reifyTerm cs fs xs S in
        let r2  := reifyTerm cs fs xs T in
        change (denote env (TermCat r1) (TermDom r1) (TermCod r1) r1 ≈
                denote env (TermCat r2) (TermDom r2) (TermCod r2) r2) in H;
        tacHyp env r1 r2 H;
        lazymatch type of H with
        | ?U ≈ ?V => change (term_wrapper (U ≈ V)) in H
        end
      end
    end
  | [ |- ?S ≈ ?T ] =>
    let env := allVars tt tt tt S in
    lazymatch env with
      (?cs, ?fs, ?xs) =>
      let env := allVars cs fs xs T in
      lazymatch env with
        (?cs, ?fs, ?xs) =>
        let cats := cats_function cs in
        let objs := objects_function xs in
        let arrs := arrows_function fs cs cats xs objs in
        let env  := constr:({| cats := cats; objs := objs; arrs := arrs |}) in
        let env  := eval compute[Pos.succ] in env in
        let r1  := reifyTerm cs fs xs S in
        let r2  := reifyTerm cs fs xs T in
        change (denote env (TermCat r1) (TermDom r1) (TermCod r1) r1 ≈
                denote env (TermCat r2) (TermDom r2) (TermCod r2) r2);
        tacGoal env r1 r2
      end
    end
  end.

Ltac reify :=
  reify_terms_and_then
    ltac:(fun env r1 r2 H => pose env; pose r1; pose r2; pose H)
    ltac:(fun env r1 r2 => pose env; pose r1; pose r2).

Ltac categorical :=
  reify_terms_and_then
    ltac:(fun env r1 r2 H => idtac)
    ltac:(fun env r1 r2 =>
      apply (normalize_apply env (TermCat r1) (TermDom r1) (TermCod r1) r1 r2);
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
                    env (TermCat r1) (TermDom r1) (TermCod r1) r1 r2 H1) as N;
      clear H H1;
      cbv beta iota zeta delta
        [ normalize normalize_denote normalize_denote_chain
          ArrowList_append
          TermCat TermDom TermCod
          Pos.succ app Pos.eqb Pos.eq_dec positive_rec positive_rect
          sumbool_rec sumbool_rect
          eq_rect eq_ind_r eq_ind eq_sym ] in N;
      red in N;
      rename N into H)
    ltac:(fun env r1 r2 =>
      apply (normalize_denote_terms
               env (TermCat r1) (TermDom r1) (TermCod r1) r1 r2);
      [ vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | vm_compute; reflexivity
      | idtac ]);
  unfold term_wrapper in *; simpl in *.

Example sample_1 : ∀ (C : Category) (x : C) (f : x ~> x),
  f ∘ f ≈ f ∘ f ->
  f ∘ (id ∘ f) ≈ f ∘ f.
Proof.
  intros.
  reify.
  normalize.
  categorical.
Qed.

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
  (* Time normalize. *)
  Time categorical.
Qed.

Print Assumptions sample_2.

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
Program Instance Term_ArrowList_Adjunction (cat : cat_idx) :
  ArrowList_to_Term cat ⊣ Term_to_ArrowList cat := {
  adj := fun x y =>
    {| to   := {| morphism := fun f => (normalize (_ f); _) |}
     ; from := {| morphism := _ |} |}
}.

Print Assumptions Term_ArrowList_Adjunction.
