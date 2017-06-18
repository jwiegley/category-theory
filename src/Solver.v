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

Inductive Term : Set :=
  | Identity : positive -> Term
  | Morph    : positive -> positive -> positive -> Term
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

Inductive Arrow : Set :=
  | Arr : positive -> positive -> positive -> Arrow.

Definition Arrow_dom (f : Arrow) : obj_idx :=
  match f with Arr x _ _ => x end.

Definition Arrow_cod (f : Arrow) : obj_idx :=
  match f with Arr _ y _ => y end.

Inductive ArrowList : Set :=
  | IdentityOnly : positive -> ArrowList
  | ArrowChain   : Arrow -> list Arrow -> ArrowList.

Definition ArrowList_cod (xs : ArrowList) : obj_idx :=
  match xs with
  | IdentityOnly x => x
  | ArrowChain (Arr x y f) _ => y
  end.

Definition ArrowList_dom (xs : ArrowList) : obj_idx :=
  match xs with
  | IdentityOnly x => x
  | ArrowChain f xs =>
    match last xs f with
    | Arr x y m => x
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

Definition ArrowList_well_typed dom cod (xs : ArrowList) : Prop :=
  match xs with
  | IdentityOnly x => x = dom /\ x = cod
  | ArrowChain (Arr x y f) xs =>
    y = cod /\
    match last xs (Arr x y f) with
      Arr a b g => a = dom
    end /\
    (* Ensure that it is a correctly type-aligned list *)
    ForallAligned (Arr x y f :: xs)
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

Corollary ArrowList_well_typed_dom {f dom cod } :
  ArrowList_well_typed dom cod f -> ArrowList_dom f = dom.
Proof.
  induction f; simpl; intros; intuition.
  destruct a; equalities.
  destruct (last l (Arr p cod p1)); auto.
Qed.

Corollary ArrowList_well_typed_cod {f dom cod} :
  ArrowList_well_typed dom cod f -> ArrowList_cod f = cod.
Proof.
  induction f; simpl; intros; intuition.
  destruct a; equalities.
Qed.

Definition ArrowList_list_rect : ∀ (P : ArrowList → Type),
  (∀ (x : positive), P (IdentityOnly x)) →
  (∀ (a : Arrow), P (ArrowChain a [])) →
  (∀ (a1 a2 : Arrow) (l : list Arrow), P (ArrowChain a2 l) → P (ArrowChain a1 (a2 :: l))) →
  ∀ l : ArrowList, P l.
Proof.
  intros.
  destruct l; auto.
  generalize dependent a.
  induction l; auto.
Defined.

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
  | IdentityOnly f, IdentityOnly r =>
    IdentityOnly r
  | IdentityOnly f, ArrowChain (Arr x y g) xs =>
    ArrowChain (Arr x y g) xs
  | ArrowChain f xs, IdentityOnly g =>
    ArrowChain f xs
  | ArrowChain f xs, ArrowChain (Arr z w g) ys =>
    ArrowChain f (xs ++ Arr z w g :: ys)
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
      destruct a; auto.
    destruct a1, a2; auto.
  - destruct a.
    simpl in *.
    equalities; subst.
    destruct f2.
      simpl in *; subst; intuition.
    destruct a.
    induction l using rev_ind.
      simpl in *; equalities.
      repeat (constructor; auto).
    destruct x.
    simpl in *.
    rewrite !last_app_cons in *; simpl in *.
    intuition.
      replace (match l ++ [Arr p3 p4 p5] with
               | [] => Arr p p0 p2
               | _ :: _ => Arr p3 p4 p5
               end) with (Arr p3 p4 p5) by (destruct l; auto).
      assumption.
    constructor; auto.
  - destruct a1, a2.
    equalities; subst.
    destruct f2.
      constructor; simpl in H1; intuition.
      simpl in *; subst.
      intuition.
      rewrite <- H.
      destruct l; auto.
    rewrite ArrowList_append_chains by congruence.
    simpl.
    constructor.
      simpl in H1; intuition.
    rewrite last_app_cons, last_cons.
    replace (match l ++ a :: l0 with
             | [] => Arr p2 p3 p4
             | _ :: _ => last l0 a
             end) with (last l0 a) by (destruct l; auto).
    pose proof (ArrowList_well_typed_dom H2).
    split.
      simpl in H.
      destruct (last l0 a); auto.
    clear -H1 H2.
    inversion H1.
    simpl in H2.
    rewrite app_comm_cons.
    rewrite app_comm_cons.
    apply ForallAligned_app.
    destruct a; intuition; subst.
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
Fixpoint Term_well_typed dom cod (e : Term) : Prop :=
  match e with
  | Identity x  => x = dom /\ x = cod
  | Morph x y f => x = dom /\ y = cod
  | Compose f g =>
    TermDom g = dom /\
    TermCod f = cod /\
    TermCod g = TermDom f /\
    Term_well_typed (TermCod g) cod f /\
    Term_well_typed dom (TermCod g) g
  end.

Fixpoint Term_well_typed_bool dom cod (e : Term) : bool :=
  match e with
  | Identity x  => (x =? dom) &&& (x =? cod)
  | Morph x y f => (x =? dom) &&& (y =? cod)
  | Compose f g =>
    (TermDom g =? dom) &&&
    (TermCod f =? cod) &&&
    (TermCod g =? TermDom f) &&&
    Term_well_typed_bool (TermCod g) cod f &&&
    Term_well_typed_bool dom (TermCod g) g
  end.

Lemma Term_well_typed_bool_sound dom cod e :
  Term_well_typed_bool dom cod e = true -> Term_well_typed dom cod e.
Proof.
  generalize dependent dom.
  generalize dependent cod.
  induction e; simpl; intuition; equalities.
Qed.

Corollary Term_well_typed_dom {f dom cod } :
  Term_well_typed dom cod f -> TermDom f = dom.
Proof. induction f; simpl; intros; intuition. Qed.

Corollary Term_well_typed_cod {f dom cod} :
  Term_well_typed dom cod f -> TermCod f = cod.
Proof. induction f; simpl; intros; intuition. Qed.

Fixpoint normalize (p : Term) : ArrowList :=
  match p with
  | Identity x  => IdentityOnly x
  | Morph x y f => ArrowChain (Arr x y f) []
  | Compose f g => ArrowList_append (normalize f) (normalize g)
  end.

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

Lemma ArrowList_specific_sound p :
  Term_well_typed (TermDom p) (TermCod p) p ->
  ArrowList_dom (normalize p) = TermDom p /\
  ArrowList_cod (normalize p) = TermCod p.
Proof.
  induction p; simpl; intros; intuition; subst;
  rewrite H1 in H2;
  specialize (IHp1 H2).
    rewrite ArrowList_append_dom; auto; intuition.
    congruence.
  rewrite ArrowList_append_cod; auto; intuition.
  congruence.
Qed.

Lemma ArrowList_normalize_dom_cod_sound {p dom cod} :
  Term_well_typed dom cod p ->
  ArrowList_dom (normalize p) = dom /\
  ArrowList_cod (normalize p) = cod.
Proof.
  generalize dependent dom.
  generalize dependent cod.
  induction p; simpl; intros; intuition; subst;
  rewrite H1 in H2;
  rewrite ArrowList_append_dom ||
  rewrite ArrowList_append_cod; auto;
  try apply ArrowList_specific_sound; auto;
  rewrite (proj1 (IHp1 _ _ H2));
  rewrite <- H1;
  symmetry;
  apply ArrowList_specific_sound; auto.
Qed.

Lemma ArrowList_id_left x y :
  ArrowList_append (IdentityOnly x) y = y.
Proof.
  simpl.
  destruct y; simpl; intros; subst; auto.
  destruct a; reflexivity.
Qed.

Lemma ArrowList_id_right x y :
  ArrowList_dom x = y ->
  ArrowList_append x (IdentityOnly y) = x.
Proof.
  destruct x; simpl; intros; subst; auto.
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
   composition was associated, so really it's a normalized free category.

   jww (2017-06-16): Show that Term ⊣ ArrowList (meaning, the functors that
   map between them). *)
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
Next Obligation. apply ArrowList_well_typed_dom in X; auto. Qed.
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
  destruct f, g; simpl in *; intuition idtac; subst; auto;
  rewrite H3; assumption.
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
  Term_well_typed dom cod f -> ArrowList_well_typed dom cod (normalize f).
Proof.
  generalize dependent dom.
  generalize dependent cod.
  induction f; simpl; intros.
  - intuition.
  - intuition.
    constructor; constructor.
  - equalities.
    specialize (IHf1 _ _ H1).
    specialize (IHf2 _ _ H3).
    intros.
    pose proof (ArrowList_well_typed_dom IHf1).
    pose proof (ArrowList_well_typed_cod IHf2).
    apply (ArrowList_append_well_typed H2 H4 IHf1 IHf2).
Qed.

Set Transparent Obligations.

Program Instance Term_to_ArrowList : Term_Category ⟶ ArrowList_Category := {
  fobj := fun x => x;
  fmap := fun x y f => (normalize _; _)
}.
Next Obligation. apply ArrowList_well_typed_sound; auto. Qed.

Fixpoint denormalize (f : ArrowList) : Term :=
  match f with
  | IdentityOnly x  => Identity x
  | ArrowChain (Arr x y f) xs =>
    (fold_left (fun acc x => (fun y => Compose y x) \o acc)
               (map (fun x => match x with
                                Arr x y f => Morph x y f
                              end) xs)
               Datatypes.id) (Morph x y f)
  end.

Lemma normalize_denormalize dom cod f :
  ArrowList_well_typed dom cod f
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
    destruct H, H0.
    apply ForallAligned_app in H1.
    destruct H1, H2.
    intuition.
    destruct (last l (Arr p p0 p1)).
    simpl in H3.
    congruence.
  destruct a; simpl in *.
  destruct H, H0.
  apply ForallAligned_app in H1.
  destruct H1, H2.
  intuition.
Qed.

Theorem denormalize_well_typed dom cod f :
  ArrowList_well_typed dom cod f
    -> Term_well_typed dom cod (denormalize f).
Proof.
  destruct f; auto.
  generalize dependent a.
  generalize dependent dom.
  induction l using rev_ind; intros.
    destruct a; simpl in *; intuition.
  rewrite <- ArrowList_append_chains.
    assert (ArrowList_well_typed (Arrow_cod x) cod (ArrowChain a l)).
      clear IHl.
      destruct a; simpl in *.
      destruct H, H0.
      apply ForallAligned_app in H1.
      destruct H1, H2.
      subst.
      rewrite last_app_cons in H0; simpl in H0.
      destruct x; subst.
      intuition.
      simpl in *.
      destruct (last l (Arr p cod p1)); auto.
    specialize (IHl (Arrow_cod x) a H0).
    simpl in H, H0.
    destruct x, a; simpl.
    rewrite last_app_cons in H; simpl in H.
    destruct H, H1.
    destruct H0, H3.
    subst.
    apply ForallAligned_app in H2.
    destruct H2, H1.
    clear H0.
    rewrite map_app.
    rewrite fold_left_app.
    simpl.
    intuition.
      clear.
      induction l using rev_ind; simpl; auto.
      rewrite map_app.
      rewrite fold_left_app.
      simpl; assumption.
    clear -H2.
    induction l using rev_ind; simpl; auto.
    destruct x.
    rewrite map_app.
    rewrite fold_left_app.
    simpl in *.
    rewrite last_app_cons in H2; simpl in H2.
    assumption.
  destruct a; simpl in *.
  destruct H, H0.
  apply ForallAligned_app in H1.
  destruct H1, H2.
  intuition.
Qed.

Program Instance ArrowList_to_Term : ArrowList_Category ⟶ Term_Category := {
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

Variable C : Category.
Variable objs : obj_idx -> C.
Variable arrs : arr_idx -> ∀ a b : obj_idx, option (objs a ~> objs b).

Fixpoint denote dom cod (e : Term) :
  option (objs dom ~> objs cod) :=
  match e with
  | Identity t =>
    match Pos.eq_dec t dom, Pos.eq_dec t cod with
    | left pf_dom, left pf_cod =>
      Some (match pf_dom, pf_cod with
            | eq_refl, eq_refl => @id C (objs t)
            end)
    | _ , _ => None
    end
  | Morph dom' cod' n =>
    match Pos.eq_dec dom' dom, Pos.eq_dec cod' cod, arrs n dom' cod' with
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

Fixpoint normalize_denote_chain dom cod
         (g : Arrow) (gs : list Arrow) {struct gs} :
  option (objs dom ~{ C }~> objs cod) :=
  match g, gs with
  | Arr x y h, nil =>
    match arrs h x y with
    | Some p =>
      match Pos.eq_dec x dom, Pos.eq_dec y cod with
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
      match Pos.eq_dec y cod with
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

Theorem normalize_denote_chain_compose {x xs y ys dom cod f} :
  normalize_denote_chain dom cod x (xs ++ y :: ys) = Some f ->
  ∃ mid g h, f ≈ g ∘ h ∧
    Arrow_dom (last xs x) = mid ∧
    Arrow_cod y = mid ∧
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
    destruct (normalize_denote_chain dom p2 (Arr p5 p6 p7) ys) eqn:?;
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
    destruct (normalize_denote_chain dom p2 (Arr p5 p6 p7)
                                     (l ++ y0 :: ys)) eqn:?;
    try discriminate.
    destruct (X _ _ _ Heqo0), s, s.
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
             | [] => Arr p5 p6 p7
             | _ :: _ => last l (Arr p2 cod p4)
             end) with (last l (Arr p5 p6 p7)).
      reflexivity.
    clear.
    induction l; auto.
    rewrite !last_cons.
    reflexivity.
Qed.

Theorem normalize_denote_chain_append_dom_cod : ∀ x xs y ys dom cod f,
  normalize_denote_chain dom cod x (xs ++ y :: ys) = Some f ->
  Arrow_dom (last xs x) = Arrow_cod y.
Proof.
  intros.
  destruct (normalize_denote_chain_compose H).
  firstorder.
  rewrite a0, a1.
  reflexivity.
Qed.

(* The list [f; g; h] maps to [f ∘ g ∘ h]. *)
Definition normalize_denote dom cod (xs : ArrowList) :
  option (objs dom ~> objs cod) :=
  match xs with
  | IdentityOnly x =>
    match Pos.eq_dec x dom, Pos.eq_dec x cod with
    | left Hdom, left Hcod =>
      Some (eq_rect x (fun z => objs dom ~> objs z)
                    (eq_rect x (fun z => objs z ~> objs x)
                             (@id C (objs x)) dom Hdom) cod Hcod)
    | _, _ => None
    end
  | ArrowChain f fs => normalize_denote_chain dom cod f fs
  end.

Theorem normalize_list_cod {p dom cod f} :
  normalize_denote dom cod p = Some f -> ArrowList_cod p = cod.
Proof.
  intros.
  destruct p.
  - simpl in H; equalities.
  - destruct l; intros.
      simpl in *.
      destruct a.
      destruct (arrs p1 p p0); equalities.
      discriminate.
    simpl in *.
    destruct a.
    equalities.
    destruct a0.
    destruct (arrs p1 p p0); discriminate.
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
    destruct (arrs p1 p p0); equalities.
    discriminate.
  - simpl in *.
    destruct a1, a2.
    destruct (arrs _ _ _); try discriminate.
    revert H; equalities.
    destruct (normalize_denote_chain dom p (Arr p2 p3 p4) l) eqn:Heqe;
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
    exists (Morph dom cod p1).
    simpl; intuition.
  - destruct a1, a2.
    destruct (arrs _ _ _); try discriminate.
    revert H; equalities.
    destruct (normalize_denote_chain dom p (Arr p2 p3 p4) l) eqn:?;
    try discriminate.
    destruct (IHp _ _ Heqo), p0.
    exists (Compose (Morph p cod p1) x).
    simpl.
    inversion_clear H.
    intuition.
    + rewrite <- e.
      reflexivity.
    + eapply Term_well_typed_dom; eauto.
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
  - rewrite <- H.
    exists cod, id, f.
    rewrite ArrowList_id_left in H0.
    simpl in H.
    rewrite (normalize_list_cod H0) in *; subst.
    split; cat.
    simpl; equalities.
  - destruct y using ArrowList_list_rect; simpl in H.
    + destruct a.
      exists dom, f, id.
      rewrite ArrowList_id_right in H0 by auto.
      rewrite (normalize_list_dom H0); subst.
      rewrite H0.
      pose proof (normalize_list_dom H0).
      simpl in H; subst.
      split; cat.
      simpl; equalities.
    + rewrite ArrowList_append_chains in H0 by auto.
      apply (normalize_denote_chain_compose H0).
    + rewrite ArrowList_append_chains in H0 by auto.
      apply (normalize_denote_chain_compose H0).
  - destruct y using ArrowList_list_rect; simpl in H.
    + destruct a1, a2.
      exists dom, f, id.
      rewrite ArrowList_id_right in H0 by auto.
      rewrite (normalize_list_dom H0); subst.
      rewrite H0.
      pose proof (normalize_list_dom H0).
      simpl in H; subst.
      split; cat.
      simpl; equalities.
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
  induction p; intros.
  - simpl in *; exists f; subst.
    split; [reflexivity|].
    equalities.
  - simpl in *; exists f; subst.
    split; [reflexivity|].
    equalities;
    destruct (arrs _ _ _); discriminate.
  - simpl in H.
    apply normalize_compose in H0.
      fold @normalize in *.
      destruct H0, s, s.
      equalities.
      destruct (Pos.eq_dec x (TermCod p2)).
        rewrite <- e in *.
        destruct (IHp1 _ _ _ H1 a2), (IHp2 _ _ _ H3 b0), p, p0.
        rewrite e3.
        rewrite e1.
        exists (x2 ∘ x3).
        split.
          rewrite <- e0, <- e2.
          assumption.
        reflexivity.
      pose proof (ArrowList_specific_sound _ H3).
      equalities.
      rewrite a1 in H4.
      contradiction.
    fold @normalize in *.
    equalities.
    clear IHp1 IHp2.
    pose proof (ArrowList_normalize_dom_cod_sound H2).
    pose proof (ArrowList_normalize_dom_cod_sound H4).
    equalities.
    rewrite H6, H.
    reflexivity.
Qed.

Theorem normalize_apply dom cod : ∀ f g,
  Term_well_typed_bool dom cod f = true ->
  Term_well_typed_bool dom cod g = true ->
  normalize f = normalize g ->
  normalize_denote dom cod (normalize f) ||| false = true ->
  denote dom cod f ≈ denote dom cod g.
Proof.
  intros.
  apply Term_well_typed_bool_sound in H.
  apply Term_well_typed_bool_sound in H0.
  pose proof (ArrowList_well_typed_sound H).
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
  | (x, _) => constr:(1)
  | (_, ?xs') =>
    let n := lookup x xs' in
    constr:(Pos.succ n)
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
    | (?x, tt) => constr:(fun _ : positive => x)
    | (?x, ?xs'') =>
      let f := loop (Pos.succ n) xs'' in
      constr:(fun m : positive => if m =? n then x else f m)
    end in
  loop 1 xs.

Ltac observe n f xs objs k :=
  match type of f with
  | ?X ~> ?Y =>
    let xn := lookup X xs in
    let yn := lookup Y xs in
    constr:(fun i x y : positive =>
      (* It's unfortunate that we have to carry this structure in the type; if
         we moved to a typed representation of arrows (where they return
         appropriate object types), we won't need to do this here. *)
      if i =? n
      then (match Pos.eq_dec xn x, Pos.eq_dec yn y with
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
      constr:(fun _ x y : positive => @None (objs x ~> objs y))
    | (?f, tt) =>
      observe n f xs objs (fun _ x y : positive => @None (objs x ~> objs y))
    | (?f, ?fs'') =>
      let k := loop (Pos.succ n) fs'' in
      observe n f xs objs k
    end in
  loop 1 fs.

Ltac categorical :=
  match goal with
  | [ |- ?S ≈ ?T ] =>
    let env := allVars tt tt S in
    match env with
      (?fs, ?xs) =>
      let env := allVars fs xs T in
      match env with
        (?fs, ?xs) =>
        (* pose xs; *)
        (* pose fs; *)
        let objs := objects_function xs in
        let arrs := arrows_function fs xs objs in
        (* pose objs; *)
        (* pose arrs; *)
        let r1  := reifyTerm fs xs S in
        let r2  := reifyTerm fs xs T in
        (* pose r1; *)
        (* pose r2; *)
        change (denote _ objs arrs (TermDom r1) (TermCod r1) r1 ≈
                denote _ objs arrs (TermDom r2) (TermCod r2) r2);
        apply (normalize_apply _ objs arrs (TermDom r1) (TermCod r1)
                               r1 r2 eq_refl eq_refl);
        vm_compute; auto;
        eexists; reflexivity
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

Print Assumptions sample_1.

Require Import Category.Theory.Adjunction.

Local Obligation Tactic :=
  cat_simpl; proper; simpl in *;
  try erewrite !normalize_denormalize; eauto;
  try (eapply ArrowList_append_well_typed;
       [ eapply ArrowList_well_typed_dom; eauto
       | eapply ArrowList_well_typed_cod; eauto
       | eauto
       | eauto ]).

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
