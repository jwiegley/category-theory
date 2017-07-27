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

Lemma Fin_eq_dec' : ∀ n (x y : Fin.t n), x = y \/ x ≠ y.
Proof.
  intros.
  destruct (Fin.eq_dec x y); auto.
Qed.

Lemma Fin_eq_dec_refl n (x : Fin.t n) :
  Fin.eq_dec x x = left (@eq_refl (Fin.t n) x).
Proof.
  destruct (Fin.eq_dec x x).
    refine (K_dec_on_type (Fin.t n) x (Fin_eq_dec' n x)
              (fun H => @left _ _ H = @left _ _ (@eq_refl (Fin.t n) x)) _ _).
    reflexivity.
  contradiction.
Qed.

Lemma Fin_eqb_refl n (x : Fin.t n) : Fin.eqb x x = true.
Proof.
  now apply Fin.eqb_eq.
Qed.

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

Section Denotation.

Import EqNotations.

Record Vars := {
  vars_cat : Category;

  vars_num_objs : nat;
  vars_num_arrs : nat;

  vars_objs : Vector.t vars_cat vars_num_objs;

  vars_arrs :
    Vector.t (∃ (dom cod : Fin.t vars_num_objs),
                 Vector.nth vars_objs dom ~{vars_cat}~>
                 Vector.nth vars_objs cod)
             vars_num_arrs
}.

Record Environment := {
  num_cats : nat;
  _cat_idx := Fin.t num_cats;

  cats : Vector.t Vars num_cats;

  get_cat (c : _cat_idx) := Vector.nth cats c;

  _obj_idx (c : _cat_idx) := Fin.t (vars_num_objs (get_cat c));
  _arr_idx (c : _cat_idx) := Fin.t (vars_num_arrs (get_cat c));

  get_obj_cat c (o : _obj_idx c) := c;
  get_obj     c (o : _obj_idx c) := Vector.nth (vars_objs (get_cat c)) o;

  get_arr_cat c (a : _arr_idx c) := c;
  get_arr_dom c (a : _arr_idx c) := `1 (Vector.nth (vars_arrs (get_cat c)) a);
  get_arr_cod c (a : _arr_idx c) := `1 `2 (Vector.nth (vars_arrs (get_cat c)) a);
  get_arr     c (a : _arr_idx c) := `2 `2 (Vector.nth (vars_arrs (get_cat c)) a)
}.

Variable env : Environment.
Variable c : _cat_idx env.

Arguments num_cats {_}.
Notation cat_idx := (_cat_idx env).
Arguments cats {_}.
Arguments get_cat {_} _.
Notation obj_idx := (_obj_idx env c).
Notation arr_idx := (_arr_idx env c).
Arguments get_obj_cat {_ _} _.
Arguments get_obj {_ _} _.
Arguments get_arr_cat {_ _} _.
Arguments get_arr_dom {_ _} _.
Arguments get_arr_cod {_ _} _.
Arguments get_arr {_ _} _.

(* This describes the morphisms of a magmoid, which forms a quotient category
   under denotation. *)
Inductive Term : Set :=
  | Identity (o : obj_idx)
  | Morph    (a : arr_idx)
  | Compose  (f g : Term).

Fixpoint TermCat (e : Term) : cat_idx :=
  match e with
  | Identity  _ => c
  | Morph _     => c
  | Compose f _ => TermCat f
  end.

Fixpoint TermDom (e : Term) : obj_idx :=
  match e with
  | Identity x  => x
  | Morph x     => get_arr_dom x
  | Compose _ g => TermDom g
  end.

Fixpoint TermCod (e : Term) : obj_idx :=
  match e with
  | Identity x  => x
  | Morph x     => get_arr_cod x
  | Compose f _ => TermCod f
  end.

Definition Arrow := arr_idx.

Definition Arrow_beq (x y : Arrow) : bool := Fin.eqb x y.

Lemma Arrow_beq_eq (x y : Arrow) : Arrow_beq x y = true -> x = y.
Proof. intros; now apply Fin.eqb_eq. Qed.

Lemma Arrow_beq_refl (x : Arrow) : Arrow_beq x x = true.
Proof. intros; now apply Fin.eqb_eq. Qed.

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
      | IdentityOnly cod' => Fin.eqb cod cod'
      | ArrowChain _ _ => false
      end
  | ArrowChain x x0 =>
      match y with
      | IdentityOnly _ => false
      | ArrowChain x1 x2 => Arrow_beq x x1 &&& list_beq Arrow_beq x0 x2
      end
  end.

Definition ArrowList_cat (xs : ArrowList) : cat_idx :=
  match xs with
  | IdentityOnly x => c
  | ArrowChain f _ => c
  end.

Definition ArrowList_cod (xs : ArrowList) : obj_idx :=
  match xs with
  | IdentityOnly x => x
  | ArrowChain f _ => get_arr_cod f
  end.

Definition ArrowList_dom (xs : ArrowList) : obj_idx :=
  match xs with
  | IdentityOnly x => x
  | ArrowChain f xs => get_arr_dom (last xs f)
  end.

Inductive ForallAligned : list Arrow → Prop :=
    Align_nil : ForallAligned []
  | Align_singleton : ∀ (a : Arrow), ForallAligned [a]
  | Align_cons2 : ∀ (a b : Arrow) (l : list Arrow),
      get_arr_dom a = get_arr_cod b ->
      ForallAligned (b :: l) → ForallAligned (a :: b :: l).

Lemma ForallAligned_inv {x xs y} :
  ForallAligned (x :: y :: xs)
    -> get_arr_dom x = get_arr_cod y /\
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
        get_arr_cod y = get_arr_dom (last xs x).
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
    get_arr_cod f = cod /\
    get_arr_dom (last xs f) = dom /\
    (* Ensure that it is a correctly type-aligned list *)
    ForallAligned (f :: xs)
  end.

Ltac equalities :=
  repeat (
    match goal with
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
    | [ H : context[match @Fin.eq_dec ?N ?X ?X with _ => _ end] |- _ ] =>
      rewrite (@Fin_eq_dec_refl N X) in H
    | [ |- context[match @Fin.eq_dec ?N ?X ?X with _ => _ end] ] =>
      rewrite (@Fin_eq_dec_refl N X)
    | [ H : context[match @Fin.eq_dec ?N ?X ?Y with _ => _ end] |- _ ] =>
      destruct (@Fin.eq_dec N X Y); subst
    | [ |- context[match Fin.eq_dec ?N ?X ?Y with _ => _ end] ] =>
      destruct (@Fin.eq_dec N X Y); subst
    | [ |- context[Arrow_beq ?N ?N = true] ] => rewrite Arrow_beq_refl
    | [ H : (_ &&& _) = true |- _ ]          => rewrite <- andb_lazy_alt in H
    | [ H : (_ && _) = true |- _ ]           => apply andb_true_iff in H; destruct H
    | [ H : _ /\ _ |- _ ]                    => destruct H
    | [ H : _ ∧ _ |- _ ]                     => destruct H
    | [ H : Arrow_beq _ _   = true |- _ ]    => apply Arrow_beq_eq in H
    | [ |- Arrow_beq _ _    = true ]         => apply Arrow_beq_eq
    | [ H : list_beq _ _ _   = true |- _ ]   => apply list_beq_eq in H
    | [ |- list_beq _ _ _    = true ]        => apply list_beq_eq
    | [ H : Fin.eqb _ _   = true |- _ ]      => apply Fin.eqb_eq in H
    | [ |- Fin.eqb _ _    = true ]           => apply Fin.eqb_eq
    | [ H : (_ =? _) = true |- _ ]           => apply Pos.eqb_eq in H
    | [ |- (_ =? _) = true ]                 => apply Pos.eqb_eq
    | [ H : (_ =? _) = false |- _ ]          => apply Pos.eqb_neq in H
    | [ |- (_ =? _) = false ]                => apply Pos.eqb_neq
    end;
    subst; simpl; auto;
    simpl TermCat in *;
    simpl TermDom in *;
    simpl TermCod in *;
    try discriminate;
    try tauto;
    try intuition idtac).

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
  destruct y; simpl; split; intros; try discriminate.
  - equalities.
  - inversion_clear H.
    equalities.
  - equalities.
    destruct l; congruence.
  - inversion_clear H.
    now rewrite Arrow_beq_refl.
  - equalities.
    destruct l0; equalities; intuition.
  - inversion_clear H.
    rewrite !Arrow_beq_refl, list_beq_refl; auto; intros.
    apply Arrow_beq_refl.
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
Fixpoint Term_well_typed dom cod (e : Term) : Prop :=
  match e with
  | Identity x => x = dom /\ x = cod
  | Morph f => get_arr_dom f = dom /\ get_arr_cod f = cod
  | Compose f g =>
    TermCod g = TermDom f /\
    Term_well_typed (TermCod g) cod f /\
    Term_well_typed dom (TermCod g) g
  end.

Fixpoint Term_well_typed_bool dom cod (e : Term) : bool :=
  match e with
  | Identity x => (Fin.eqb x dom) &&& (Fin.eqb x cod)
  | Morph f => (Fin.eqb (get_arr_dom f) dom) &&& (Fin.eqb (get_arr_cod f) cod)
  | Compose f g =>
    (Fin.eqb (TermCod g) (TermDom f)) &&&
    Term_well_typed_bool (TermCod g) cod f &&&
    Term_well_typed_bool dom (TermCod g) g
  end.

Lemma Term_well_typed_bool_sound dom cod e :
  Term_well_typed_bool dom cod e = true <-> Term_well_typed dom cod e.
Proof.
  generalize dependent dom.
  generalize dependent cod.
  induction e; simpl;
  intuition; subst; equalities;
  try rewrite !Fin_eqb_refl; auto.
  - apply IHe1; auto.
  - apply IHe2; auto.
  - apply IHe1 in H.
    apply IHe2 in H2.
    rewrite !H0 in *.
    rewrite Fin_eqb_refl, H, H2; reflexivity.
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

Lemma ArrowList_append_cat f g :
  ArrowList_cat f = ArrowList_cat g ->
  ArrowList_cat (ArrowList_append f g) = ArrowList_cat g.
Proof.
  destruct g, f; simpl; intros; auto.
Qed.

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
  try destruct a0; subst; auto.
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
  - rewrite <- (IHl (get_arr_cod x)); clear IHl.
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
  assert (ArrowList_well_typed (get_arr_cod x) cod (ArrowChain a l)). {
    clear IHl.
    simpl in *; equalities.
    - rewrite app_comm_cons in H1.
      now apply ForallAligned_app in H1.
    - rewrite app_comm_cons in H1.
      now apply ForallAligned_app in H1.
  }
  rewrite <- ArrowList_append_chains.
  - specialize (IHl (get_arr_cod x) a H0).
    simpl in *.
    equalities.
    rewrite last_app_cons in H1; simpl in H1.
    rewrite app_comm_cons in H4.
    apply ForallAligned_app in H4.
    equalities.
    clear H0.
    rewrite map_app, fold_left_app.
    simpl.
    rewrite H5.
    intuition; subst.
    + clear -H.
      induction l using rev_ind; simpl; auto.
      rewrite map_app, fold_left_app; simpl.
      now rewrite last_rcons in *.
    + now rewrite H5 in IHl.
  - simpl in *; intuition.
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

Fixpoint denote dom cod (e : Term) :
  option (get_obj dom ~{ vars_cat (get_cat c) }~> get_obj cod).
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
  equalities.
  intros.
  destruct (denote (TermCod f2) cod f1) eqn:?; try discriminate.
  destruct (denote dom (TermCod f2) f2) eqn:?; try discriminate.
  destruct (IHf1 _ eq_refl).
  destruct (IHf2 _ eq_refl).
  intuition.
Qed.

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
  obj := obj_idx;
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

Fixpoint normalize_denote_chain dom cod
         (g : Arrow) (gs : list Arrow) {struct gs} :
  option (get_obj dom ~{ vars_cat (get_cat c) }~> get_obj cod) :=
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

Lemma normalize_denote_chain_cat :
  ∀ (gs : list Arrow) c x y f dom cod f',
    normalize_denote_chain dom cod (Arr c x y f) gs = Some f' ->
    = c.
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
  ∀ (gs : list Arrow) c x y f dom cod f',
    normalize_denote_chain dom cod (Arr c x y f) gs = Some f' ->
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

Theorem normalize_denote_chain_compose {x xs y ys dom cod f} :
  normalize_denote_chain dom cod x (xs ++ y :: ys) = Some f ->
  ∃ mid g h, f ≈ g ∘ h ∧
    get_arr_dom (last xs x) = mid ∧
    get_arr_cod y = mid ∧
    normalize_denote_chain mid cod x xs = Some g ∧
    normalize_denote_chain dom mid y ys = Some h.
Proof.
  generalize dependent f.
  generalize dependent cod.
  generalize dependent y.
  apply ListOfArrows_rect with (x:=x) (l:=xs); simpl; intros;
  destruct x, x0, y; simpl.
  - destruct (arrs _ _ _); try discriminate.
    revert H; equalities.
    destruct (normalize_denote_chain dom o1 (Arr c1 o3 o4 a1) ys) eqn:?;
    try discriminate.
    exists _, h, h0.
    inversion_clear H.
    rewrite Neq_dec_refl; simpl.
    intuition.
    pose proof (normalize_denote_chain_cod _ _ _ _ _ _ _ _ _ Heqo2); auto.
  - destruct (arrs _ _ _) eqn:?; try discriminate.
    revert H; equalities.
    destruct (normalize_denote_chain dom o1 (Arr c1 o3 o4 a1)
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

Lemma normalize_denote_chain_dom_cod :
  ∀ (gs : list Arrow) c x y f dom cod f',
    normalize_denote_chain dom cod (Arr c x y f) gs = Some f' ->
    = c /\
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

Theorem normalize_denote_chain_append_dom_cod : ∀ x xs y ys dom cod f,
  normalize_denote_chain dom cod x (xs ++ y :: ys) = Some f ->
  get_arr_dom (last xs x) = get_arr_cod y.
Proof.
  intros.
  destruct (normalize_denote_chain_compose H).
  firstorder.
  rewrite a0, a1.
  reflexivity.
Qed.

(* The list [f; g; h] maps to [f ∘ g ∘ h]. *)
Definition normalize_denote dom cod (xs : ArrowList) :
  option (objs env dom ~> objs env cod cat) :=
  match xs with
  | IdentityOnly c x =>
    match Pos.eq_dec c cat,
          Pos.eq_dec x dom, Pos.eq_dec x cod with
    | left Hcat, left Hdom, left Hcod =>
      Some (eq_rect x (fun z => objs env dom ~> objs env z cat)
              (eq_rect x (fun z => objs env z ~> objs env x cat)
                 (eq_rect c (fun z => objs env x z ~> objs env x z)
                          (@id (cats env c) (objs env x c)) Hcat)
                 dom Hdom)
              cod Hcod)
    | _, _, _ => None
    end
  | ArrowChain f fs => normalize_denote_chain dom cod f fs
  end.

Theorem normalize_list_cat {p dom cod f} :
  normalize_denote dom cod p = Some f -> ArrowList_cat p = cat.
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

Theorem normalize_list_cod {p dom cod f} :
  normalize_denote dom cod p = Some f -> ArrowList_cod p = cod.
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

Theorem normalize_list_dom {p dom cod f} :
  normalize_denote dom cod p = Some f -> ArrowList_dom p = dom.
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
    destruct (normalize_denote_chain dom o (Arr c0 o1 o2 a0) l) eqn:Heqe;
    try discriminate.
    rewrite <- (IHp _ _ Heqe); clear IHp.
    induction l using rev_ind.
      simpl in *.
      destruct (arrs _ _ _); try discriminate.
      revert H; equalities.
    rewrite !last_rcons.
    destruct l; auto.
Qed.

Theorem normalize_denote_well_typed {p dom cod f} :
  normalize_denote dom cod p = Some f
    -> ∃ p', p = normalize p' ∧ Term_well_typed dom cod p'.
Proof.
  generalize dependent f.
  generalize dependent cod.
  induction p using ArrowList_list_rect; simpl; intros.
  - revert H; equalities.
    exists (Identity cod).
    simpl; intuition.
  - destruct a.
    destruct (arrs _ _ _); try discriminate.
    revert H; equalities.
    exists (Morph dom cod a).
    simpl; intuition.
  - destruct a1, a2.
    destruct (arrs _ _ _); try discriminate.
    revert H; equalities.
    destruct (normalize_denote_chain dom o (Arr c0 o1 o2 a0) l) eqn:?;
    try discriminate.
    destruct (IHp _ _ Heqo0), p.
    exists (Compose (Morph o cod a) x).
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

Theorem normalize_compose {x y dom cod f} :
  ArrowList_cat y = ArrowList_cat x ->
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

Theorem normalize_sound {p dom cod f} :
  Term_well_typed dom cod p ->
  normalize_denote dom cod (normalize p) = Some f ->
  ∃ f', f ≈ f' ∧ denote dom cod p = Some f'.
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
      * pose proof (ArrowList_normalize_dom_cod_sound H2);
        equalities;
        now rewrite a1 in H4.
    + clear IHp1 IHp2.
      equalities.
      pose proof (ArrowList_normalize_dom_cod_sound H2).
      pose proof (ArrowList_normalize_dom_cod_sound H3).
      equalities.
      now rewrite H4.
    + clear IHp1 IHp2.
      equalities.
      pose proof (ArrowList_normalize_dom_cod_sound H2).
      pose proof (ArrowList_normalize_dom_cod_sound H3).
      equalities.
      now rewrite H5, H7.
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
Program Instance Term_ArrowList_Adjunction :
  ArrowList_to_Term ⊣ Term_to_ArrowList := {
  adj := fun x y =>
    {| to   := {| morphism := fun f => (normalize (_ f); _) |}
     ; from := {| morphism := _ |} |}
}.

Print Assumptions Term_ArrowList_Adjunction.
