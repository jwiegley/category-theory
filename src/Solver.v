Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
Require Import Coq.quote.Quote.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.NArith.NArith.

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

Definition obj_idx := N.
Definition arr_idx := N.

Set Universe Polymorphism.

Program Instance option_setoid `{Setoid A} : Setoid (option A) := {
  equiv := fun x y => match x, y with
    | Some x, Some y => x ≈ y
    | None, None => True
    | _, _ => False
    end
}.
Next Obligation. intuition; discriminate. Defined.
Next Obligation. intuition; discriminate. Defined.
Next Obligation.
  equivalence.
  - destruct x; reflexivity.
  - destruct x, y; auto.
    symmetry; auto.
  - destruct x, y, z; auto.
      transitivity a0; auto.
    contradiction.
Defined.

Unset Universe Polymorphism.

Open Scope N_scope.

Inductive Term : Set :=
  | Identity : N -> Term
  | Morph    : N -> N -> N -> Term
  | Compose  : Term -> Term -> Term.

Fixpoint TermDom (e : Term) : obj_idx :=
  match e with
  | Identity x  => x
  | Morph x _ _ => x
  | Compose _ g => TermDom g
  end.

Fixpoint TermCod (e : Term) : obj_idx :=
  match e with
  | Identity x  => x
  | Morph _ x _ => x
  | Compose f _ => TermCod f
  end.

Section Denotation.

Variable C : Category.
Variable objs : obj_idx -> C.
Variable arrs : arr_idx -> ∀ a b : obj_idx, option (objs a ~> objs b).

Fixpoint denote dom cod (e : Term) :
  option (objs dom ~> objs cod) :=
  match e with
  | Identity t =>
    match N.eq_dec t dom, N.eq_dec t cod with
    | left pf_dom, left pf_cod =>
      Some (match pf_dom, pf_cod with
            | eq_refl, eq_refl => @id C (objs t)
            end)
    | _ , _ => None
    end
  | Morph dom' cod' n =>
    match N.eq_dec dom' dom, N.eq_dec cod' cod, arrs n dom' cod' with
    | left pf_dom, left pf_cod, Some arr =>
      Some (match pf_dom, pf_cod with
            | eq_refl, eq_refl => arr
            end)
    | _, _, _ => None
    end
  | Compose g f =>
    match denote dom (TermCod f) f, denote _ cod g with
    | Some farr, Some garr => Some (garr ∘ farr)
    | _ , _ => None
    end
  end.

Inductive Arrow : Set :=
  | Arr : N -> N -> N -> Arrow.

Definition Arrow_dom (f : Arrow) : obj_idx :=
  match f with Arr x _ _ => x end.

Definition Arrow_cod (f : Arrow) : obj_idx :=
  match f with Arr _ y _ => y end.

Definition Arrow_morph (f : Arrow) : arr_idx :=
  match f with Arr _ _ f => f end.

Inductive ArrowList : Set :=
  | Invalid
  | IdentityOnly : N -> ArrowList
  | ArrowChain   : Arrow -> list Arrow -> ArrowList.

Lemma ArrowList_list_rect : ∀ (P : ArrowList → Type),
  P Invalid →
  (∀ (x : N), P (IdentityOnly x)) →
  (∀ (a : Arrow), P (ArrowChain a [])) →
  (∀ (a1 a2 : Arrow) (l : list Arrow), P (ArrowChain a2 l) → P (ArrowChain a1 (a2 :: l))) →
  ∀ l : ArrowList, P l.
Proof.
  intros.
  destruct l; auto.
  generalize dependent a.
  induction l; auto.
Qed.

Lemma ListOfArrows_rect : ∀ (P : Arrow -> list Arrow → Type),
  (∀ (x : Arrow), P x []) →
  (∀ (x y : Arrow) (l : list Arrow), P y l → P x (y :: l)) →
  ∀ (x : Arrow) (l : list Arrow), P x l.
Proof.
  intros.
  generalize dependent x.
  induction l; auto.
Qed.

Definition ArrowList_cod (xs : ArrowList) : option obj_idx :=
  match xs with
  | Invalid => None
  | IdentityOnly x => Some x
  | ArrowChain (Arr x y f) _ => Some y
  end.

Definition ArrowList_dom (xs : ArrowList) : option obj_idx :=
  match xs with
  | Invalid => None
  | IdentityOnly x => Some x
  | ArrowChain f xs =>
    match last xs f with
    | Arr x y m => Some x
    end
  end.

Definition ArrowList_length (xs : ArrowList) : nat :=
  match xs with
  | Invalid => 0
  | IdentityOnly _ => 1
  | ArrowChain _ xs => 1 + length xs
  end.

(* Convert a valid arrow list to a mere list of arrows, stripping out object
   indices. *)
Definition ArrowList_toList (xs : ArrowList) : list N :=
  match xs with
  | Invalid => nil
  | IdentityOnly _ => nil
  | ArrowChain (Arr _ _ f) xs => f :: map Arrow_morph xs
  end.

Definition ArrowList_append (xs ys : ArrowList) : ArrowList :=
  match xs, ys with
  | Invalid, _ => Invalid
  | _, Invalid => Invalid
  | IdentityOnly f, IdentityOnly r =>
    if f =? r
    then IdentityOnly f
    else Invalid
  | IdentityOnly f, ArrowChain (Arr x y g) xs =>
    if f =? y
    then ArrowChain (Arr x y g) xs
    else Invalid
  | ArrowChain f xs, IdentityOnly g =>
    match ArrowList_dom (ArrowChain f xs) with
    | Some dom =>
      if g =? dom
      then ArrowChain f xs
      else Invalid
    | None => Invalid
    end
  | ArrowChain f xs, ArrowChain (Arr z w g) ys =>
    match ArrowList_dom (ArrowChain f xs) with
    | Some dom =>
      if w =? dom
      then ArrowChain f (xs ++ Arr z w g :: ys)
      else Invalid
    | None => Invalid
    end
  end.

Open Scope lazy_bool_scope.

Lemma K_dec_on_type A (x : A) (eq_dec : ∀ y : A, x = y \/ x ≠ y)
      (P : x = x -> Type) :
  P (eq_refl x) -> forall p:x = x, P p.
Proof.
  intros.
  elim (@Eqdep_dec.eq_proofs_unicity_on A _) with x (eq_refl x) p.
    trivial.
  exact eq_dec.
Defined.

Lemma Neq_dec' : ∀ x y : N, x = y \/ x ≠ y.
Proof.
  intros.
  destruct (N.eq_dec x y); auto.
Defined.

Lemma Neq_dec_refl n : N.eq_dec n n = left (@eq_refl N n).
Proof.
  destruct (N.eq_dec n n).
    refine (K_dec_on_type N n (Neq_dec' n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl N n)) _ _).
    reflexivity.
  contradiction.
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

Ltac equalities :=
  repeat (
    match goal with
    | [ H : context[match N.eq_dec ?N ?N with _ => _ end] |- _ ] =>
      rewrite Neq_dec_refl in H
    | [ |- context[match N.eq_dec ?N ?N with _ => _ end] ] =>
      rewrite Neq_dec_refl
    | [ H : context[match N.eq_dec ?N ?M with _ => _ end] |- _ ] =>
      destruct (N.eq_dec N M); subst
    | [ |- context[match N.eq_dec ?N ?M with _ => _ end] ] =>
      destruct (N.eq_dec N M); subst
    | [ |- context[if ?N =? ?N then _ else _] ] =>
      rewrite N.eqb_refl
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
      apply N.eqb_eq in H; subst
    | [ H : (_ =? _) = false |- _ ] =>
      apply N.eqb_neq in H
    end;
    subst; simpl; auto;
    simpl TermDom in *;
    simpl TermCod in *;
    try discriminate;
    try tauto;
    try intuition idtac).

Lemma ArrowList_append_dom f g :
  ArrowList_dom f = ArrowList_cod g ->
  ArrowList_dom (ArrowList_append f g) = ArrowList_dom g.
Proof.
  destruct g, f; simpl; intros; auto.
  - inversion_clear H; equalities.
  - rewrite H; equalities.
  - destruct a; discriminate.
  - destruct a; equalities.
    inversion H; subst.
    contradiction.
  - rewrite H.
    destruct a.
    equalities.
    rewrite last_app_cons.
    rewrite last_cons.
    reflexivity.
Qed.

Lemma ArrowList_append_dom_inv f g x :
  ArrowList_dom (ArrowList_append f g) = Some x ->
  ArrowList_dom f = ArrowList_cod g.
Proof.
  destruct g, f; simpl; intros; auto; try discriminate.
  - revert H; equalities.
  - destruct (last _ _).
    revert H; equalities.
  - destruct a.
    revert H; equalities.
  - destruct a.
    destruct (last l0 a0).
    revert H; equalities.
Qed.

Lemma ArrowList_append_cod f g :
  ArrowList_dom f = ArrowList_cod g ->
  ArrowList_cod (ArrowList_append f g) = ArrowList_cod f.
Proof.
  destruct f, g; simpl; intros; auto.
  - inversion_clear H; equalities.
  - destruct a; equalities.
    inversion H; subst.
    contradiction.
  - destruct (last _ _); discriminate.
  - rewrite H; equalities.
  - destruct a0.
    rewrite H.
    equalities.
Qed.

Lemma ArrowList_append_cod_inv f g x :
  ArrowList_cod (ArrowList_append f g) = Some x ->
  ArrowList_dom f = ArrowList_cod g.
Proof.
  destruct g, f; simpl; intros; auto; try discriminate.
  - revert H; equalities.
  - destruct (last _ _).
    revert H; equalities.
  - destruct a.
    revert H; equalities.
  - destruct a.
    destruct (last l0 a0).
    revert H; equalities.
Qed.

Lemma ArrowList_append_chains a a0 l l0 :
  ArrowList_dom (ArrowChain a l) = ArrowList_cod (ArrowChain a0 l0) ->
  ArrowList_append (ArrowChain a l) (ArrowChain a0 l0) =
  ArrowChain a (l ++ a0 :: l0).
Proof.
  generalize dependent a0.
  generalize dependent l0.
  simpl.
  induction l using rev_ind; simpl; intros.
    destruct a0, a.
    inversion_clear H.
    rewrite N.eqb_refl.
    reflexivity.
  simpl in H.
  destruct a0, a.
  destruct (last (l ++ [x]) (Arr n2 n3 n4)); subst.
  inversion_clear H.
  rewrite N.eqb_refl.
  reflexivity.
Qed.

Lemma ArrowList_id_left x y :
  ArrowList_cod y = Some x ->
  ArrowList_append (IdentityOnly x) y = y.
Proof.
  simpl.
  destruct y.
  - auto.
  - intros.
    inversion_clear H.
    equalities.
  - destruct a.
    simpl; intros.
    inversion_clear H.
    equalities.
Qed.

Lemma ArrowList_id_right x y :
  ArrowList_dom x = Some y ->
  ArrowList_append x (IdentityOnly y) = x.
Proof.
  simpl.
  destruct x.
  - auto.
  - intros.
    inversion_clear H.
    simpl.
    equalities.
  - destruct a.
    simpl; intros.
    destruct (last _ _).
    inversion_clear H.
    equalities.
Qed.

Lemma ArrowList_append_assoc x y z :
  ArrowList_dom y = ArrowList_cod z ->
  ArrowList_dom x = ArrowList_cod y ->
  ArrowList_append (ArrowList_append x y) z =
  ArrowList_append x (ArrowList_append y z).
Proof.
  destruct x, y, z; simpl; auto; intros;
  try destruct a;
  try destruct a0;
  inversion H; subst;
  inversion H0; subst.
  - equalities.
  - equalities.
  - equalities.
  - equalities.
    destruct (last _ _); equalities.
  - equalities.
    destruct (last _ _); equalities.
  - equalities.
    rewrite H0; equalities.
    rewrite H0; equalities.
  - equalities.
    rewrite H0; equalities.
    rewrite H0; equalities.
  - rewrite H0; equalities.
  - rewrite H, H0.
    equalities.
    rewrite last_app_cons.
    rewrite last_cons.
    rewrite H; equalities.
  - destruct a1.
    rewrite H; equalities.
    rewrite H0; equalities.
    rewrite last_app_cons.
    rewrite last_cons.
    rewrite H; equalities.
    rewrite <- app_assoc.
    rewrite app_comm_cons.
    reflexivity.
Qed.

(* We show here that ArrowList morphisms are just one way of representing a
   free category. *)
Program Definition ArrowList_Category : Category := {|
  obj := obj_idx;
  hom := fun x y =>
    ∃ l : ArrowList, ArrowList_dom l = Some x ∧ ArrowList_cod l = Some y;
  homset := fun x y => {| equiv := fun f g => `1 f = `1 g |};
  id := fun x => (IdentityOnly x; _);
  compose := fun _ _ _ f g => (ArrowList_append (`1 f) (`1 g); _);
  id_left := fun _ y f => ArrowList_id_left y (`1 f) _;
  id_right := fun x _ f => ArrowList_id_right (`1 f) x _;
  comp_assoc := fun x y z w f g h =>
    ArrowList_append_assoc (`1 f) (`1 g) (`1 h) _ _
|}.
Next Obligation. equivalence; simpl in *; congruence. Qed.
Next Obligation.
  rewrite ArrowList_append_dom, ArrowList_append_cod;
  intuition; congruence.
Qed.
Next Obligation. proper; simpl in *; subst; reflexivity. Qed.
Next Obligation. congruence. Qed.
Next Obligation. congruence. Qed.
Next Obligation. apply ArrowList_append_assoc; congruence. Qed.
Next Obligation. rewrite ArrowList_append_assoc; auto; congruence. Qed.
Next Obligation. rewrite ArrowList_append_assoc; auto; congruence. Qed.

Fixpoint normalize (p : Term) : ArrowList :=
  match p with
  | Identity x  => IdentityOnly x
  | Morph x y f => ArrowChain (Arr x y f) []
  | Compose f g => ArrowList_append (normalize f) (normalize g)
  end.

Fixpoint normalize_denote_chain dom cod
         (g : Arrow) (gs : list Arrow) {struct gs} :
  option (objs dom ~{ C }~> objs cod) :=
  match g, gs with
  | Arr x y h, nil =>
    match arrs h x y with
    | Some p =>
      match N.eq_dec x dom, N.eq_dec y cod with
      | left Hdom, left Hcod =>
        Some (eq_rect y (fun z => objs dom ~> objs z)
                      (eq_rect x (fun z => objs z ~> objs y)
                               p dom Hdom) cod Hcod)
      | _, _ => None
      end
    | _ => None
    end
  | Arr x y h, Arr z w j :: js =>
    match arrs h x y with
    | Some p =>
      match N.eq_dec y cod with
      | left Hcod =>
        match normalize_denote_chain dom x (Arr z w j) js with
        | Some q =>
          Some (eq_rect y (fun y => objs dom ~> objs y)
                        (p ∘ q) cod Hcod)
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end
  end.

Lemma normalize_denote_chain_cod :
  ∀ (gs : list Arrow) x y f dom cod f',
    normalize_denote_chain dom cod (Arr x y f) gs = Some f' ->
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

Theorem normalize_denote_chain_compose : ∀ x xs y ys dom cod f,
  normalize_denote_chain dom cod x (xs ++ y :: ys) = Some f ->
  ∃ mid g h, f ≈ g ∘ h ∧
    Arrow_dom (last xs x) = mid ∧
    Arrow_cod y = mid ∧
    normalize_denote_chain mid cod x xs = Some g ∧
    normalize_denote_chain dom mid y ys = Some h.
Proof.
  intros ??.
  apply ListOfArrows_rect with (x:=x) (l:=xs); simpl; intros;
  destruct x, x0, y; simpl.
  - destruct (arrs _ _ _); try discriminate.
    revert H; equalities.
    destruct (normalize_denote_chain dom n2 (Arr n5 n6 n7) ys) eqn:?;
    try discriminate.
    exists _, h, h0.
    inversion_clear H.
    rewrite Neq_dec_refl; simpl.
    intuition.
    pose proof (normalize_denote_chain_cod _ _ _ _ _ _ _ Heqo).
    symmetry.
    assumption.
  - destruct (arrs _ _ _) eqn:?; try discriminate.
    revert H; equalities.
    destruct (normalize_denote_chain dom n2 (Arr n5 n6 n7)
                                     (l ++ y0 :: ys)) eqn:?;
    try discriminate.
    destruct (X _ _ _ _ _ Heqo0), s, s.
    equalities.
    subst.
    inversion_clear H.
    exists _, (h ∘ x0), x1.
    split.
      rewrite e.
      rewrite comp_assoc.
      reflexivity.
    rewrite a1, b.
    intuition.
    clear X.
    replace (match l with
             | [] => Arr n5 n6 n7
             | _ :: _ => last l (Arr n2 cod n4)
             end) with (last l (Arr n5 n6 n7)).
      reflexivity.
    clear.
    induction l; auto.
    rewrite !last_cons.
    reflexivity.
Qed.

Lemma normalize_denote_chain_dom_cod :
  ∀ (gs : list Arrow) x y f dom cod f',
    normalize_denote_chain dom cod (Arr x y f) gs = Some f' ->
    cod = y /\ dom = match last gs (Arr x y f) with
                       Arr z _ _ => z
                     end.
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
  revert b; equalities.
  specialize (IHgs _ _ _ _ _ _ a1).
  intuition.
Qed.

Theorem normalize_denote_chain_append_dom_cod : ∀ x xs y ys dom cod f,
  normalize_denote_chain dom cod x (xs ++ y :: ys) = Some f ->
  Arrow_dom (last xs x) = Arrow_cod y.
Proof.
  intros.
  destruct (normalize_denote_chain_compose _ _ _ _ _ _ _ H).
  firstorder.
  rewrite a0, a1.
  reflexivity.
Qed.

(* The list [f; g; h] maps to [f ∘ g ∘ h]. *)
Definition normalize_denote dom cod (xs : ArrowList) :
  option (objs dom ~> objs cod) :=
  match xs with
  | Invalid => None
  | IdentityOnly x =>
    match N.eq_dec x dom, N.eq_dec x cod with
    | left Hdom, left Hcod =>
      Some (eq_rect x (fun z => objs dom ~> objs z)
                    (eq_rect x (fun z => objs z ~> objs x)
                             (@id C (objs x)) dom Hdom) cod Hcod)
    | _, _ => None
    end
  | ArrowChain f fs => normalize_denote_chain dom cod f fs
  end.

Lemma ArrowList_dom_sound dom p :
  ArrowList_dom (normalize p) = Some dom -> TermDom p = dom.
Proof.
  induction p; simpl; intros.
  - inversion_clear H; auto.
  - inversion_clear H; auto.
  - rewrite ArrowList_append_dom in H.
      intuition.
    apply (ArrowList_append_dom_inv _ _ _ H).
Qed.

Lemma ArrowList_cod_sound cod p :
  ArrowList_cod (normalize p) = Some cod -> TermCod p = cod.
Proof.
  induction p; simpl; intros.
  - inversion_clear H; auto.
  - inversion_clear H; auto.
  - rewrite ArrowList_append_cod in H.
      intuition.
    apply (ArrowList_append_cod_inv _ _ _ H).
Qed.

Theorem normalize_list_cod : ∀ p dom cod f,
  normalize_denote dom cod p = Some f -> ArrowList_cod p = Some cod.
Proof.
  intros.
  destruct p.
  - discriminate.
  - simpl in H; equalities.
  - destruct l; intros.
      simpl in *.
      destruct a.
      destruct (arrs n1 n n0); equalities.
      discriminate.
    simpl in *.
    destruct a.
    equalities.
    destruct a0.
    destruct (arrs n1 n n0); discriminate.
Qed.

Theorem normalize_cod : ∀ p dom cod f,
  normalize_denote dom cod (normalize p) = Some f -> TermCod p = cod.
Proof.
  intros.
  apply normalize_list_cod in H.
  now apply ArrowList_cod_sound.
Qed.

Local Obligation Tactic := intros; try solve [program_simpl | equalities].

Theorem normalize_list_dom : ∀ p dom cod f,
  normalize_denote dom cod p = Some f -> ArrowList_dom p = Some dom.
Proof.
  induction p using ArrowList_list_rect; intros.
  - discriminate.
  - simpl in H; equalities.
  - simpl in *.
    destruct a.
    destruct (arrs n1 n n0); equalities.
    discriminate.
  - simpl in *.
    destruct a1, a2.
    destruct (arrs _ _ _); try discriminate.
    revert H; equalities.
    destruct (normalize_denote_chain dom n (Arr n2 n3 n4) l) eqn:Heqe;
    try discriminate.
    rewrite <- (IHp _ _ _ Heqe); clear IHp.
    induction l using rev_ind.
      simpl in *.
      destruct (arrs _ _ _); try discriminate.
      revert H; equalities.
    rewrite !last_rcons.
    destruct l; auto.
Qed.

Theorem normalize_dom : ∀ p dom cod f,
  normalize_denote dom cod (normalize p) = Some f -> TermDom p = dom.
Proof.
  intros.
  apply normalize_list_dom in H.
  now apply ArrowList_dom_sound.
Qed.

Theorem normalize_append_dom_cod : ∀ dom cod x y f,
  normalize_denote dom cod (ArrowList_append x y) = Some f ->
  ∃ m, ArrowList_cod y = Some m /\ ArrowList_dom x = Some m.
Proof.
  induction x using ArrowList_list_rect; intros.
  - discriminate.
  - destruct y; simpl in H.
    + discriminate.
    + revert H; equalities.
      exists n; auto.
    + destruct a.
      revert H; equalities.
      exists n0; auto.
  - simpl in H.
    destruct y.
    + discriminate.
    + destruct a.
      revert H; equalities.
      * exists dom; auto.
      * exists dom; auto.
      * exists n0; auto.
    + destruct a0, a.
      revert H; equalities;
      destruct (arrs _ _ _); try discriminate.
      exists n2; auto.
  - destruct y.
    + discriminate.
    + simpl in H.
      exists n.
      simpl; intuition.
      destruct l.
        destruct a2.
        revert H; equalities.
      rewrite last_cons in *.
      destruct (last l a).
      revert H; equalities.
    + simpl in H.
      destruct a.
      simpl.
      exists n0; intuition.
      destruct l.
        destruct a2.
        revert H; equalities.
      rewrite last_cons in *.
      destruct (last l a).
      revert H; equalities.
Qed.

(* Theorem normalize_denote_cons : ∀ a l dom cod f, *)
(*   normalize_denote dom cod (ArrowChain a l) = Some f -> *)
(*   ∃ mid f', normalize_denote dom cod (ArrowChain a l) = Some f' -> *)

Theorem normalize_compose : ∀ x y dom cod f,
  normalize_denote dom cod (ArrowList_append x y) = Some f ->
  ∃ mid g h, f ≈ g ∘ h ∧
    ArrowList_dom x = Some mid ∧
    ArrowList_cod y = Some mid ∧
    normalize_denote mid cod x = Some g ∧
    normalize_denote dom mid y = Some h.
Proof.
  induction x using ArrowList_list_rect; intros.
  - discriminate.
  - destruct y; simpl in H.
    + discriminate.
    + revert H; equalities.
      exists cod, id, id.
      inversion_clear H.
      split.
        cat.
      intuition;
      rewrite Neq_dec_refl;
      reflexivity.
    + destruct a.
      revert H; equalities.
        exists n0, (@id C (objs n0)), f.
        split.
          cat.
        intuition.
        equalities.
      destruct (normalize_denote_chain_dom_cod _ _ _ _ _ _ _ H); subst.
      contradiction.
  - destruct y; simpl in H.
    + discriminate.
    + destruct a.
      destruct (N.eq_dec n n0); subst.
        rewrite N.eqb_refl in H.
        simpl in H.
        destruct (arrs _ _ _) eqn:Heqe.
          revert H; equalities.
          exists dom, f, (@id C (objs dom)).
          split.
            cat.
          simpl in H.
          rewrite Heqe.
          intuition.
            rewrite Neq_dec_refl.
            assumption.
          equalities.
        discriminate.
      revert H; equalities.
    + destruct a0, a.
      revert H; equalities.
        destruct (arrs _ _ _); simpl in H.
          destruct (normalize_denote_chain dom n2 (Arr n n2 n1) l) eqn:Heqe;
          try discriminate.
          exists n2, h, h0.
          inversion_clear H.
          split.
            cat.
          intuition.
          equalities.
        discriminate.
      destruct (arrs _ _ _); discriminate.
  - destruct y.
    + discriminate.
    + pose proof (normalize_list_dom _ _ _ _ H).
      pose proof (normalize_list_cod _ _ _ _ H).
      destruct (normalize_append_dom_cod _ _ _ _ _ H), a.
      simpl in H0, H1, H2, H3.
      inversion H2; subst.
      exists dom, f, (@id C (objs dom)).
      split.
        cat.
      destruct l.
        simpl in *.
        destruct a2.
        inversion H3; subst.
        rewrite N.eqb_refl in *.
        simpl in H0, H1.
        inversion H0; subst.
        intuition.
        equalities.
      rewrite last_cons in *.
      destruct (last l a).
      inversion H3; subst.
      rewrite N.eqb_refl in *.
      simpl in *.
      rewrite !H0 in *; clear H0.
      destruct (N.eq_dec x dom); subst.
        rewrite N.eqb_refl in *.
        intuition.
      revert H; equalities.
    + specialize (IHx (ArrowChain a l0)).
      pose proof (normalize_list_dom _ _ _ _ H).
      pose proof (normalize_list_cod _ _ _ _ H).
      destruct (normalize_append_dom_cod _ _ _ _ _ H), a0.
      simpl in H0, H1, H2, H3.
      inversion H2; subst.
      rewrite H3 in *.
      destruct a, a1, a2.
      inversion H5; subst; clear H2 H5.
      rewrite N.eqb_refl in *.
      simpl in H0, H1.
      revert H0.
      rewrite last_app_cons.
      rewrite last_cons.
      replace (match l ++ Arr n x n1 :: l0 with
               | [] => Arr n5 n6 n7
               | _ :: _ => last l0 (Arr n x n1)
               end) with (last l0 (Arr n x n1)) by (destruct l; auto).
      destruct (last l0 (Arr n x n1)); intros.
      inversion H0; subst; clear H0.
      inversion H1; subst; clear H1 n8 n9.

      simpl in H.
      rewrite H3 in H.
      rewrite N.eqb_refl in H.
      simpl in H.
      rewrite Neq_dec_refl in H.
      destruct (arrs _ _ _) eqn:?; try discriminate.
      destruct (normalize_denote_chain dom n2 (Arr n5 n6 n7)
                                       (l ++ Arr n x n1 :: l0)) eqn:?;
      try discriminate.
      rewrite ArrowList_append_chains in IHx.
        simpl in IHx.
        destruct (IHx _ _ _ Heqo0), s, s.
        equalities.
        rewrite H3.
        inversion a0; subst.
        exists x0.
        rewrite a1, b, Heqo.
        exists (h ∘ x1), x2.
        split.
          rewrite <- comp_assoc.
          rewrite <- e.
          simpl in H.
          inversion_clear H.
          reflexivity.
        intuition.
      pose proof (normalize_denote_chain_append_dom_cod _ _ _ _ _ _ _ Heqo0).
      simpl in *.
      unfold Arrow_dom in H0.
      destruct (last l (Arr n5 n6 n7)); subst.
      reflexivity.
Qed.

Theorem normalize_sound : ∀ p dom cod f,
  normalize_denote dom cod (normalize p) = Some f ->
  ∃ f', f ≈ f' ∧ denote dom cod p = Some f'.
Proof.
  induction p; intros.
  - simpl in *; exists f; subst.
    split; [reflexivity|].
    equalities.
  - simpl in *; exists f; subst.
    split; [reflexivity|].
    equalities;
    destruct (arrs _ _ _); discriminate.
  - specialize (IHp1 (TermCod p2) cod).
    specialize (IHp2 dom (TermCod p2)).
    apply normalize_compose in H.
    fold @normalize in *.
    destruct H, s, s.
    equalities.
    apply ArrowList_dom_sound in a.
    apply ArrowList_cod_sound in a0.
    subst.
    rewrite a0 in *.
    destruct (IHp1 x0), (IHp2 x1); clear IHp1 IHp2; intuition.
    exists (x ∘ x2).
    split.
      rewrite e, a, a2.
      reflexivity.
    rewrite b1, b0.
    reflexivity.
Qed.

Theorem normalize_apply dom cod : ∀ f g,
  (∃ f', normalize_denote dom cod (normalize f) = Some f') ->
  (∃ g', normalize_denote dom cod (normalize g) = Some g') ->
  normalize f = normalize g ->
  denote dom cod f ≈ denote dom cod g.
Proof.
  intros.
  destruct X.
  destruct (normalize_sound _ dom cod _ e), p.
  destruct X0.
  destruct (normalize_sound _ dom cod _ e2), p.
  inversion H; subst; clear H.
  rewrite e1, e4.
  red.
  rewrite <- e0, <- e3.
  rewrite H1 in e.
  rewrite e in e2.
  inversion e2.
  reflexivity.
Qed.

End Denotation.

Import ListNotations.

Ltac inList x xs :=
  match xs with
  | tt => false
  | (x, _) => true
  | (_, ?xs') => inList x xs'
  end.

Ltac addToList x xs :=
  let b := inList x xs in
  match b with
  | true => xs
  | false => constr:((x, xs))
  end.

Ltac allVars fs xs e :=
  match e with
  | @id _ ?x =>
    let xs := addToList x xs in
    constr:((fs, xs))
  | ?e1 ∘ ?e2 =>
    let res := allVars fs xs e1 in
    match res with
      (?fs, ?xs) => allVars fs xs e2
    end
  | ?f =>
    match type of f with
    | ?x ~> ?y =>
      let xs := addToList x xs in
      let xs := addToList y xs in
      let fs := addToList f fs in
      constr:((fs, xs))
    end
  end.

Ltac lookup x xs :=
  match xs with
  | (x, _) => constr:(0)
  | (_, ?xs') =>
    let n := lookup x xs' in
    constr:(N.succ n)
  end.

Ltac reifyTerm fs xs t :=
  match t with
  | @id _ ?X =>
    let x := lookup X xs in
    constr:(Identity x)
  | ?X1 ∘ ?X2 =>
    let r1 := reifyTerm fs xs X1 in
    let r2 := reifyTerm fs xs X2 in
    constr:(Compose r1 r2)
  | ?F =>
    let n := lookup F fs in
    match type of F with
    | ?X ~> ?Y =>
      let x := lookup X xs in
      let y := lookup Y xs in
      constr:(Morph x y n)
    end
  end.

Ltac objects_function xs :=
  let rec loop n xs' :=
    match xs' with
    | (?x, tt) => constr:(fun _ : N => x)
    | (?x, ?xs'') =>
      let f := loop (N.succ n) xs'' in
      constr:(fun m : N => if m =? n then x else f m)
    end in
  loop 0 xs.

Ltac observe n f xs objs k :=
  match type of f with
  | ?X ~> ?Y =>
    let xn := lookup X xs in
    let yn := lookup Y xs in
    constr:(fun i x y : N =>
      if i =? n
      then (match N.eq_dec xn x, N.eq_dec yn y with
            | left Hx, left Hy =>
              @Some (objs x ~> objs y)
                    (eq_rect yn (fun y => objs x ~> objs y)
                       (eq_rect xn (fun x => objs x ~> objs yn) f x Hx) y Hy)
            | _, _ => @None (objs x ~> objs y)
            end)
      else k i x y)
  end.

Ltac arrows_function fs xs objs :=
  let rec loop n fs' :=
    match fs' with
    | tt =>
      constr:(fun _ x y : N => @None (objs x ~> objs y))
    | (?f, tt) =>
      observe n f xs objs (fun _ x y : N => @None (objs x ~> objs y))
    | (?f, ?fs'') =>
      let k := loop (N.succ n) fs'' in
      observe n f xs objs k
    end in
  loop 0 fs.

Ltac categorical :=
  match goal with
  | [ |- ?S ≈ ?T ] =>
    let env := allVars tt tt S in
    match env with
      (?fs, ?xs) =>
      let env := allVars fs xs T in
      match env with
        (?fs, ?xs) =>
        pose xs;
        pose fs;
        let objs := objects_function xs in
        let arrs := arrows_function fs xs objs in
        pose objs;
        pose arrs;
        let r1  := reifyTerm fs xs S in
        let r2  := reifyTerm fs xs T in
        pose r1;
        pose r2;
        change (denote _ objs arrs (TermDom r1) (TermCod r1) r1 ≈
                denote _ objs arrs (TermDom r2) (TermCod r2) r2);

        let r1' := eval simpl in (denote _ objs arrs (TermDom r1)
                                         (TermCod r1) r1) in
        pose r1';
        match r1' with
        | Some ?r1'' =>
          let r2' := eval simpl in (denote _ objs arrs (TermDom r2)
                                           (TermCod r2) r2) in
          pose r2';
          match r2' with
          | Some ?r2'' =>
            apply (normalize_apply _ objs arrs (TermDom r1) (TermCod r1) r1 r2);
            vm_compute; auto;
            eexists; reflexivity
          | None => idtac
          end
        | None => idtac
        end
      end
    end
  end.

Example sample_1 :
  ∀ (C : Category) (x y z w : C) (f : z ~> w) (g : y ~> z) (h : x ~> y),
    f ∘ (id ∘ g ∘ h) ≈ (f ∘ g) ∘ h.
Proof.
  intros.
  Time categorical.
Qed.
