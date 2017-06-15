Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Classes.Morphisms.
(* Require Import Coq.Relations.Relations. *)
(* Require Import Coq.Classes.RelationClasses. *)
Require Import Coq.quote.Quote.
Require Import Coq.Wellfounded.Lexicographic_Product.
(* Require Import Coq.Vectors.Vector. *)
Require Import Coq.NArith.NArith.

Generalizable All Variables.

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

Program Definition index_eq_dec (n m : index) : {n = m} + {n ≠ m} :=
  match index_eq n m with
  | true  => left (index_eq_prop n m _)
  | false => right _
  end.
Next Obligation.
  intro; subst.
  induction m; simpl in Heq_anonymous; auto.
  discriminate.
Defined.

Lemma K_dec_on_type A (x : A) (eq_dec : ∀ y : A, x = y \/ x ≠ y)
      (P : x = x -> Type) :
  P (eq_refl x) -> ∀ p:x = x, P p.
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
Defined.

Corollary index_eq_dec' : ∀ x y : index, x = y \/ x ≠ y.
Proof. intros; destruct (index_eq_dec x y); auto. Defined.

Lemma index_eq_dec_refl n : index_eq_dec n n = left (@eq_refl _ n).
Proof.
  destruct (index_eq_dec n n).
    refine (K_dec_on_type index n (index_eq_dec' n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl index n)) _ _).
    reflexivity.
  contradiction.
Defined.

Unset Universe Polymorphism.

Open Scope N_scope.

Set Decidable Equality Schemes.

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

Lemma Term_eq_dec' : ∀ x y : Term, x = y \/ x ≠ y.
Proof.
  intros.
  destruct (Term_eq_dec x y); auto.
Defined.

Lemma Term_eq_dec_refl n : Term_eq_dec n n = left (@eq_refl _ n).
Proof.
  destruct (Term_eq_dec n n).
    refine (K_dec_on_type Term n (Term_eq_dec' n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl _ n)) _ _).
    reflexivity.
  contradiction.
Defined.

Inductive Subterm : Term -> Term -> Prop :=
  | Compose1 : ∀ t1 t2, Subterm t1 (Compose t1 t2)
  | Compose2 : ∀ t1 t2, Subterm t2 (Compose t1 t2).

Definition Subterm_inv_t : ∀ x y, Subterm x y -> Prop.
Proof.
  intros [] [] f;
  match goal with
  | [ H : Subterm ?X (Compose ?Y _ ?Z) |- Prop ] =>
    destruct (Term_eq_dec X Y); subst;
    [ destruct (Term_eq_dec X Z); subst;
      [ exact (f = Compose1 _ _ \/ f = Compose2 _ _)
      | exact (f = Compose1 _ _) ]
    | destruct (Term_eq_dec X Z); subst;
      [ exact (f = Compose2 _ _)
      | exact False ] ]
  | [ H : Subterm ?X (Compose ?Y _ ?Z) |- Prop ] =>
    destruct (Term_eq_dec X Y); subst;
    [ destruct (Term_eq_dec X Z); subst;
      [ exact (f = Compose1 _ _ \/ f = Compose2 _ _)
      | exact (f = Compose1 _ _) ]
    | destruct (Term_eq_dec X Z); subst;
      [ exact (f = Compose2 _ _)
      | exact False ] ]
  | _ => exact False
  end.
Defined.

(*
Corollary Subterm_inv x y f : Subterm_inv_t x y f.
Proof.
  pose proof Term_eq_dec.
  destruct f, t1, t2; simpl; intuition;
  rewrite Term_eq_dec_refl;
  unfold eq_rec_r, eq_rec, eq_rect, eq_sym; intuition;
  destruct (Term_eq_dec _ _);
  try (rewrite e || rewrite <- e);
  try (rewrite e0 || rewrite <- e0);
  try congruence; intuition.
Defined.
*)

Lemma Subterm_wf : well_founded Subterm.
Proof.
  constructor; intros.
  inversion H; subst; simpl in *;
  induction y;
  induction t1 || induction t2;
  simpl in *;
  constructor; intros;
  inversion H0; subst; clear H0;
  try (apply IHy1; constructor);
  try (apply IHy2; constructor).
Defined.

Section Symmetric_Product2.

  Variable A : Type.
  Variable leA : A -> A -> Prop.

  Inductive symprod2 : A * A -> A * A -> Prop :=
    | left_sym2 :
      ∀ x x':A, leA x x' -> ∀ y:A, symprod2 (x, y) (x', y)
    | right_sym2 :
      ∀ y y':A, leA y y' -> ∀ x:A, symprod2 (x, y) (x, y')
    | both_sym2 :
      ∀ (x x':A) (y y':A),
        leA x x' ->
        leA y y' ->
        symprod2 (x, y) (x', y').

  Lemma Acc_symprod2 :
    ∀ x:A, Acc leA x -> ∀ y:A, Acc leA y -> Acc symprod2 (x, y).
  Proof.
    induction 1 as [x _ IHAcc]; intros y H2.
    induction H2 as [x1 H3 IHAcc1].
    apply Acc_intro; intros y H5.
    inversion_clear H5; auto with sets.
    apply IHAcc; auto.
    apply Acc_intro; trivial.
  Defined.

  Lemma wf_symprod2 :
    well_founded leA -> well_founded symprod2.
  Proof.
    red.
    destruct a.
    apply Acc_symprod2; auto with sets.
  Defined.

End Symmetric_Product2.

Program Fixpoint eval (C : Category) (dom cod : obj_idx) (e : Term)
        (objs : obj_idx -> C)
        (arrs : arr_idx -> ∀ x y : obj_idx, option (objs x ~> objs y))
        {struct e} :
  TermDom e = dom ->
  TermCod e = cod ->
  option (objs dom ~> objs cod) := fun Hdom Hcod =>
    match e with
    | Identity x  => Some (@id C (objs x))
    | Morph x y n => _ (arrs n x y)
    | Compose f g =>
      match N.eq_dec (TermDom f) (TermCod g) with
      | left _ =>
        match eval C (TermCod g) cod f objs arrs _ Hcod,
              eval C dom (TermCod g) g objs arrs Hdom _ with
        | Some f', Some g' => Some (f' ∘ g')
        | _, _ => None
        end
      | right _ => None
      end
    end.

Definition R := symprod2 Term Subterm.
Arguments R /.

Open Scope lazy_bool_scope.

Set Transparent Obligations.

Local Obligation Tactic := intros; try discriminate.

Section denote.

Variable (C : Category).
Variable (objs : obj_idx -> C).
Variable (arrs : arr_idx -> ∀ a b : obj_idx, option (objs a ~> objs b)).

Fixpoint denote_infer dom (e : Term) :
  option { cod : _ & objs dom ~> objs cod } :=
  match e with
  | Identity t =>
    match N.eq_dec t dom with
    | left pf_dom =>
      Some (t; match pf_dom with
               | eq_refl => @id C (objs t)
               end)
    | _ => None
    end
  | Morph dom' cod' n =>
    match N.eq_dec dom' dom, arrs n dom' cod' with
    | left pf_dom, Some arr =>
      Some (cod'; match pf_dom with
                  | eq_refl => arr
                  end)
    | _ , _ => None
    end
  | Compose g f =>
    match denote_infer dom f with
    | Some (t'; farr) =>
      match denote_infer t' g with
      | Some (t''; garr) =>
        Some (t''; (garr ∘ farr))
      | _ => None
      end
    | _ => None
    end
  end.

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

(* Define what it means for a Term to be valid within a given context. *)
Fixpoint Valid dom cod (e : Term) : Type :=
  TermDom e = dom ∧
  TermCod e = cod ∧
  match e with
  | Identity x  => dom = cod ∧ dom = x
  | Morph x y f => dom = x ∧ cod = y ∧ ∃ f', arrs f x y = Some f'
  | Compose f g => Valid (TermCod g) cod f ∧ Valid dom (TermCod g) g
  end.

Ltac equalities :=
  repeat match goal with
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
      apply N.eqb_eq in H
    end;
  simpl TermDom in *;
  simpl TermCod in *;
  subst.

Ltac forward_reason :=
  repeat match goal with
  | |- context[match ?X with left _ => _ | right _ => None end = Some _] =>
    destruct X; [| solve [ inversion 1 | inversion 2 ] ]
  | |- context[match ?X with Some _ => _ | None => None end = Some _] =>
    destruct X; [| solve [ inversion 1 | inversion 2 ] ]
  | |- context[match ?X with left _ => _ | right _ => None end = Some _] =>
    destruct X; [| solve [ inversion 1 | inversion 2 ] ]
  end.

Lemma denote_dom_cod_eq : ∀ f dom cod f',
  denote dom cod f = Some f' ->
  TermDom f = dom /\ TermCod f = cod.
Proof.
  induction f; intros dom cod; simpl;
  try solve [ forward_reason; auto ].
  specialize (IHf2 dom (TermCod f2)).
  specialize (IHf1 (TermCod f2) cod).
  forward_reason.
  destruct (IHf1 _ eq_refl).
  destruct (IHf2 _ eq_refl).
  tauto.
Qed.

Lemma denote_dom_cod : ∀ f dom cod f',
  denote dom cod f ≈ Some f' ->
  TermDom f = dom /\ TermCod f = cod.
Proof.
  induction f; intros dom cod; simpl.
  - destruct (N.eq_dec n dom);
    destruct (N.eq_dec n cod);
    subst; intuition.
  - destruct (N.eq_dec n dom);
    destruct (N.eq_dec n0 cod);
    subst; intuition.
  - specialize (IHf2 dom (TermCod f2)).
    specialize (IHf1 (TermCod f2) cod).
    destruct (denote dom (TermCod f2) f2); [|tauto].
    destruct (IHf2 h); [reflexivity|]; subst.
    destruct (denote (TermCod f2) cod f1); [|tauto].
    destruct (IHf1 h0); [reflexivity|]; subst.
    intros; intuition.
Defined.

Definition denote_valid dom cod e :
  Valid dom cod e ↔ (∃ f, denote dom cod e = Some f).
Proof.
  split; intros;
  generalize dependent dom;
  generalize dependent cod.
  - induction e; intros; simpl in X; equalities.
    + exists id.
      simpl.
      rewrite Neq_dec_refl.
      reflexivity.
    + destruct s.
      exists x.
      simpl.
      rewrite !Neq_dec_refl.
      destruct (arrs n1 dom cod); auto.
    + destruct (IHe1 _ _ v).
      destruct (IHe2 _ _ v0).
      exists (x ∘ x0).
      simpl.
      rewrite e, e0.
      reflexivity.
  - induction e; intros; simpl in *;
    destruct X.
    + destruct (N.eq_dec n dom); subst.
        destruct (N.eq_dec dom cod); subst.
          intuition.
        discriminate.
     discriminate.
    + destruct (N.eq_dec n dom); subst.
        destruct (N.eq_dec n0 cod); subst.
          destruct (arrs n1 dom cod).
            inversion e; subst.
            intuition.
            exists x.
            reflexivity.
          discriminate.
        discriminate.
     discriminate.
   + destruct (denote dom (TermCod e2) e2) eqn:Heqe2;
     destruct (denote (TermCod e2) cod e1) eqn:Heqe1; try discriminate.
     pose proof (denote_dom_cod_eq _ _ _ _ Heqe2).
     pose proof (denote_dom_cod_eq _ _ _ _ Heqe1).
     equalities; intuition.
     inversion e; subst.
       exact (IHe1 _ _ (h0; Heqe1)).
     exact (IHe2 _ _ (h; Heqe2)).
Qed.

(* Valid terms are easily denoted. *)
Definition valid_denote dom cod :
  (∃ e : Term, Valid dom cod e) -> objs dom ~> objs cod.
Proof.
  intros.
  destruct X.
  generalize dependent dom.
  generalize dependent cod.
  induction x; simpl; intros.
  - destruct v; subst.
    equalities.
    exact id.
  - equalities.
    destruct s.
    exact x.
  - equalities.
    exact (IHx1 _ _ v ∘ IHx2 _ _ v0).
Defined.

Program Fixpoint mkComposeValid x y z (a b : Term) :
  Valid y z a -> Valid x y b -> ∃ t : Term, Valid x z t := fun Ha Hb =>
  match a with
  | Identity _ => (b; Hb)
  | _ => match b with
        | Identity _  => (a; Ha)
        | Compose g h => (Compose (Compose a g) h; _)
        | _ => (Compose a b; (_, (_, (Ha, Hb))))
        end
  end.
Next Obligation.
  subst; simpl in *.
  now equalities.
Defined.
Next Obligation.
  subst; simpl in *.
  now equalities.
Defined.
Next Obligation.
  subst; simpl in *.
  equalities; intuition.
  - destruct a; simpl in *; now equalities.
  - destruct g; simpl in *; now equalities.
  - destruct a; simpl in *; now equalities.
Defined.
Next Obligation.
  subst; simpl in *.
  destruct b; simpl in *; now equalities.
Defined.
Next Obligation.
  subst; simpl in *.
  destruct a; simpl in *; now equalities.
Defined.
Next Obligation.
  subst; simpl in *.
  destruct b; simpl in *; now equalities.
Defined.
Next Obligation.
  subst; simpl in *.
  destruct b; simpl in *; now equalities.
Defined.
Next Obligation.
  subst; simpl in *.
  destruct b; simpl in *; now equalities.
Defined.

Definition normalizeValid dom cod (p : Term) :
  Valid dom cod p -> ∃ t : Term, Valid dom cod t.
Proof.
  intros.
  generalize dependent dom.
  generalize dependent cod.
  induction p; intros; simpl in X.
  - exact (Identity n; X).
  - exact (Morph n n0 n1; X).
  - equalities.
    destruct (IHp1 _ _ v)  as [f Hf].
    destruct (IHp2 _ _ v0) as [g Hg].
    exact (mkComposeValid _ (TermCod p2) _ f g Hf Hg).
Defined.

Theorem normalizeValid_sound_eq
: ∀ p dom cod (H : Valid dom cod p) pV,
    valid_denote dom cod (p; H) = pV ->
    ∃ pV', pV ≈ pV' ∧ valid_denote dom cod (normalizeValid dom cod p H) = pV'.
Proof.
  induction p; intros.
  - exists pV.
    split; [reflexivity|].
    simpl normalizeValid.
    assumption.
  - exists pV.
    split; [reflexivity|].
    simpl normalizeValid.
    assumption.
  - simpl in H.
    equalities.
    specialize (IHp1 (TermCod p2) _ v).
    specialize (IHp2 _ (TermCod p2) v0).
    destruct (IHp1 _ eq_refl).
    destruct (IHp2 _ eq_refl).
    equalities.
Admitted.

Theorem normalizeValid_apply dom cod : ∀ f g,
  `1 (normalizeValid dom cod (`1 f) (`2 f)) =
  `1 (normalizeValid dom cod (`1 g) (`2 g)) ->
  valid_denote dom cod f ≈ valid_denote dom cod g.
Proof.
  generalize dependent dom.
  generalize dependent cod.
  intros.
  destruct f, g; simpl in H.
  generalize dependent dom.
  generalize dependent cod.
  generalize dependent x0.
  induction x; intros.
Admitted.

End denote.

Section Reduction.

Context {C : Category}.

Variable (objs : obj_idx -> C).
Variable (arrs : arr_idx -> ∀ x y : obj_idx, option (objs x ~> objs y)).

Ltac equalities :=
  repeat match goal with
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
      apply N.eqb_eq in H
    end;
  simpl TermDom in *;
  simpl TermCod in *;
  subst.

Corollary Identity_dom_cod {dom cod x f'} :
  denote C objs arrs dom cod (Identity x) ≈ Some f'
    -> dom = cod ∧ dom = x.
Proof.
  intros.
  pose proof (denote_dom_cod C objs arrs _ _ _ _ X).
  simpl in H.
  equalities; auto.
Defined.

Corollary Identity_dom_cod_eq {dom cod x f'} :
  denote C objs arrs dom cod (Identity x) = Some f'
    -> dom = cod ∧ dom = x.
Proof.
  intros.
  pose proof (denote_dom_cod_eq C objs arrs _ _ _ _ H).
  simpl in H.
  equalities; auto.
Defined.

Lemma Identity_denote x f' :
  denote C objs arrs x x (Identity x) ≈ Some f' ->
  f' ≈ @id C (objs x).
Proof.
  simpl.
  rewrite Neq_dec_refl.
  intros.
  rewrite <- X.
  reflexivity.
Defined.

Corollary Morph_dom_cod {dom cod x y f f'} :
  denote C objs arrs dom cod (Morph x y f) ≈ Some f'
    -> dom = x ∧ cod = y.
Proof.
  intros.
  pose proof (denote_dom_cod C objs arrs _ _ _ _ X).
  simpl in H.
  equalities; auto.
Defined.

Corollary Morph_dom_cod_eq {dom cod x y f f'} :
  denote C objs arrs dom cod (Morph x y f) = Some f'
    -> dom = x ∧ cod = y.
Proof.
  intros.
  pose proof (denote_dom_cod_eq C objs arrs _ _ _ _ H).
  simpl in H.
  equalities; auto.
Defined.

Lemma Compose_denote_eq x y z f g f' g' :
  y = TermCod g ->
  denote C objs arrs y z f = Some f' ->
  denote C objs arrs x y g = Some g' ->
  denote C objs arrs x z (Compose f g) = Some (f' ∘ g').
Proof.
  intros.
  induction f.
  - destruct (Identity_dom_cod_eq H0); subst.
    simpl in H0.
    rewrite Neq_dec_refl in H0.
    inversion_clear H0.
    simpl.
    rewrite H1.
    rewrite Neq_dec_refl.
    reflexivity.
  - destruct (Morph_dom_cod_eq H0); subst.
    simpl in H0.
    rewrite !Neq_dec_refl in H0.
    simpl.
    rewrite H1.
    rewrite !Neq_dec_refl.
    destruct (arrs n1 (TermCod g) n0); try discriminate.
    inversion_clear H0.
    reflexivity.
  - subst.
    simpl in *.
    rewrite H1.
    destruct (denote C objs arrs (TermCod g) (TermCod f2) f2);
    destruct (denote C objs arrs (TermCod f2) z f1); try discriminate.
    inversion_clear H0.
    reflexivity.
Qed.

Definition mkCompose (a b : Term) : Term :=
  match a with
  | Identity _ => b
  | _ => match b with
        | Identity _ => a
        | Compose g h => Compose (Compose a g) h
        | _ => Compose a b
        end
  end.

Ltac forward_reason :=
  repeat match goal with
  | |- context[match ?X with left _ => _ | right _ => None end = Some _] =>
    destruct X; [| solve [ inversion 1 | inversion 2 ] ]
  | |- context[match ?X with Some _ => _ | None => None end = Some _] =>
    destruct X; [| solve [ inversion 1 | inversion 2 ] ]
  | |- context[match ?X with left _ => _ | right _ => None end = Some _] =>
    destruct X; [| solve [ inversion 1 | inversion 2 ] ]
  end.

Lemma Compose_dom_cod {dom mid cod f g f' g' fg'} :
  denote C objs arrs mid cod f ≈ Some f' ->
  denote C objs arrs dom mid g ≈ Some g' ->
  denote C objs arrs dom cod (Compose f g) ≈ Some fg'
    -> dom = TermDom g ∧ cod = TermCod f.
Proof.
  intros.
  pose proof (denote_dom_cod C objs arrs _ _ _ _ X).
  pose proof (denote_dom_cod C objs arrs _ _ _ _ X0).
  pose proof (denote_dom_cod C objs arrs _ _ _ _ X1).
  simpl in H, H0, H1.
  equalities; auto.
Qed.

Lemma mkCompose_sound_lem_eq :
  ∀ (τ τ' τ'' : obj_idx) (f : Term) (fV : objs τ ~{ C }~> objs τ') (t : Term)
    (gV : objs τ' ~{ C }~> objs τ''),
    denote C objs arrs τ τ' f = Some fV
    → denote C objs arrs τ' τ'' t = Some gV
    → ∃ fgV : objs τ ~{ C }~> objs τ'',
        {_ : equiv (gV ∘ fV) fgV |
         denote C objs arrs τ τ''
                match f with
                | Identity _ => t
                | Morph _ _ _ => Compose t f
                | Compose _ _ => Compose t f
                end = Some fgV}.
Proof.
  intros τ τ' τ'' f fV.
  destruct f.
  { simpl.
    forward_reason.
    inversion 1; subst.
    intros.
    eexists.
    esplit; [ | eassumption ].
    apply id_right. }
  { generalize dependent (Morph n n0 n1).
    simpl. intros.
    destruct (denote_dom_cod_eq _ _ _ _ H).
    destruct (denote_dom_cod_eq _ _ _ _ H0).
    subst. rewrite H0. rewrite H.
    eexists; eexists; auto. reflexivity. }
  { generalize dependent (Compose f1 f2).
    simpl. intros.
    destruct (denote_dom_cod_eq _ _ _ _ H).
    destruct (denote_dom_cod_eq _ _ _ _ H0).
    subst. rewrite H0. rewrite H.
    eexists; eexists; auto. reflexivity. }
Defined.

Lemma mkCompose_sound_lem :
  ∀ (x y z : obj_idx)
    (f : Term) (f' : objs y ~> objs z)
    (g : Term) (g' : objs x ~> objs y),
    denote C objs arrs y z f ≈ Some f' ->
    denote C objs arrs x y g ≈ Some g' ->
    ∃ fg' : objs x ~{ C }~> objs z,
      equiv (f' ∘ g') fg' ∧
      denote C objs arrs x z (match g with
                              | Identity _ => f
                              | Morph _ _ _ => Compose f g
                              | Compose _ _ => Compose f g
                              end) ≈ Some fg'.
Proof.
  intros ?????.
  destruct g.
  - destruct (denote _ _ _ _ _ _) eqn:Heqe; [|inversion 1].
    eexists.
    destruct (Identity_dom_cod X0); subst.
    rewrite Heqe.
    esplit.
      reflexivity.
    rewrite X.
    unfold equiv; simpl.
    apply Identity_denote in X0.
    rewrite X0.
    rewrite id_right.
    reflexivity.
  - generalize dependent (Morph n n0 n1).
    simpl; intros.
    subst.
    eexists; eexists.
      reflexivity.
    destruct (denote_dom_cod _ _ _ _ X).
    destruct (denote_dom_cod _ _ _ _ X0).
    subst.
    rewrite H2; clear H2.
    destruct (denote C objs arrs (TermDom t) (TermDom f) t); [|tauto].
    destruct (denote C objs arrs (TermDom f) (TermCod f) f); [|tauto].
    rewrite X, X0; reflexivity.
  - generalize dependent (Compose g1 g2).
    simpl; intros.
    subst.
    eexists; eexists.
      reflexivity.
    destruct (denote_dom_cod _ _ _ _ X).
    destruct (denote_dom_cod _ _ _ _ X0).
    subst.
    rewrite H2; clear H2.
    destruct (denote C objs arrs (TermDom t) (TermDom f) t); [|tauto].
    destruct (denote C objs arrs (TermDom f) (TermCod f) f); [|tauto].
    rewrite X, X0; reflexivity.
Defined.

Theorem denote_comp_assoc x y f g h :
  denote C objs arrs x y (Compose f (Compose g h)) ≈
  denote C objs arrs x y (Compose (Compose f g) h).
Proof.
  simpl.
  destruct (denote C objs arrs x (TermCod h) h);
  destruct (denote C objs arrs (TermCod h) (TermCod g) g);
  destruct (denote C objs arrs (TermCod g) y f); auto.
  apply comp_assoc.
Defined.

Theorem mkCompose_sound_eq
: ∀ τ τ' τ'' f fV g gV,
    @denote C objs arrs τ τ' f = Some fV ->
    @denote C objs arrs τ' τ'' g = Some gV ->
    { fgV : _ & { pf : gV ∘ fV ≈ fgV | @denote C objs arrs τ τ'' (mkCompose g f) = Some fgV } }.
Proof.
  destruct g.
  - simpl.
    forward_reason.
    inversion 2; subst. exists fV.
    exists (@id_left _ _ _ _). assumption.
  - intros.
    pose proof (mkCompose_sound_lem_eq τ τ' τ'' f fV (Morph n n0 n1) gV H H0).
    destruct X as [fg' [Heqv X]].
    eexists fg'.
    eexists; eauto.
    destruct f; try eassumption.
    simpl.
    destruct (Morph_dom_cod_eq H0); subst.
    simpl in *.
    destruct (denote C objs arrs τ (TermCod f2) f2); auto.
    destruct (denote C objs arrs (TermCod f2) (TermCod f1) f1); auto.
    destruct (N.eq_dec n (TermCod f1)); auto.
    rewrite Neq_dec_refl in *.
    subst.
    destruct (arrs n1 (TermCod f1) n0); auto.
    rewrite Neq_dec_refl in *.
Admitted.

Theorem mkCompose_no_exists_sound_eq : ∀ x y z f g,
  denote C objs arrs y z f = None ->
  denote C objs arrs x y g = None ->
  denote C objs arrs x z (mkCompose f g) = None.
Proof.
  intros.
  destruct f, g; simpl mkCompose.
Abort.

Theorem mkCompose_sound : ∀ x y z f f' g g',
  @denote C objs arrs y z f ≈ Some f' ->
  @denote C objs arrs x y g ≈ Some g' ->
  ∃ fg', f' ∘ g' ≈ fg' ∧ denote C objs arrs x z (mkCompose f g) ≈ Some fg'.
Proof.
  destruct f.
  - intros.
    pose proof (mkCompose_sound_lem x y z (Identity n) f' g g' X X0).
    destruct X1 as [fg' [Heqv X1]].
    eexists fg'.
    eexists; eauto.
    simpl mkCompose.
    destruct (Identity_dom_cod X); subst.
    apply Identity_denote in X.
    rewrite X, id_left in Heqv.
    rewrite X0.
    unfold equiv; simpl.
    assumption.
  - intros.
    pose proof (mkCompose_sound_lem x y z (Morph n n0 n1) f' g g' X X0).
    destruct X1 as [fg' [Heqv X1]].
    eexists fg'.
    eexists; eauto.
    destruct g; try eassumption.
    rewrite <- (denote_comp_assoc x z (Morph n n0 n1) g1 g2).
    assumption.
  - intros.
    pose proof (mkCompose_sound_lem x y z (Compose f1 f2) f' g g' X X0).
    destruct X1 as [fg' [Heqv X1]].
    eexists fg'.
    eexists; eauto.
    destruct g; try eassumption.
    simpl mkCompose.
    rewrite <- (denote_comp_assoc x z _ g1 g2).
    assumption.
Defined.

(** I don't think this type is really what you want. The soundness of this
 ** gallina program should be something like:
 **
 ** ∀ dom cod val,
 **   eval' dom cod p = Some val ->
 **   exists val', eval' dom cod t = Some val'
 **           /\  val ≈ val'
 **
 ** This phrasing captures the fact that the function can assume the
 ** input `Term` is well-typed, and must ensure that the output `Term`
 ** is also well-typed. Without this, you end up needing to do a lot of
 ** type-checking within your automation which is slow and gets in the
 ** way. This is also the reason why you want to specify the denotation
 ** function by passing in `dom` and `cod` rather than computing them.
 **)

Inductive Arrow : Set :=
  | Arr : N -> N -> N -> Arrow.

Program Fixpoint normalize_arrows (p : Term) : list Arrow :=
  match p with
  | Identity x  => []
  | Morph x y f => [Arr x y f]
  | Compose f g => normalize_arrows f ++ normalize_arrows g
  end.

(* The list [f; g; h] maps to [f ∘ g ∘ h]. *)
Fixpoint normalize_denote dom cod (xs : list Arrow) {struct xs} :
  option (objs dom ~> objs cod) :=
  match xs with
  | nil =>
    match N.eq_dec dom cod with
    | left H  => Some (eq_rect dom (fun x => objs dom ~> objs x)
                               (@id C (objs dom)) cod H)
    | right _ => None
    end
  | cons (Arr x y f) nil =>
    match N.eq_dec x dom, N.eq_dec y cod with
    | left Hx, left Hy =>
      eq_rect y (fun y => option (objs dom ~> objs y))
              (eq_rect x (fun x => option (objs x ~> objs y))
                       (arrs f x y) dom Hx) cod Hy
    | _, _ => None
    end
  | cons (Arr x y f) gs =>
    match N.eq_dec y cod with
    | left H =>
      match arrs f x y with
      | Some f =>
        match normalize_denote dom x gs with
        | Some g => Some (eq_rect y (fun y => objs dom ~> objs y)
                                  (f ∘ g) cod H)
        | _ => None
        end
      | None => None
      end
    | right _ => None
    end
  end.

Goal ∀ x, normalize_denote x x [] = Some id.
  intros; simpl.
  rewrite Neq_dec_refl.
  reflexivity.
Qed.

Goal ∀ x y f, normalize_denote x y [Arr x y f] = arrs f x y.
  intros; simpl.
  rewrite !Neq_dec_refl.
  reflexivity.
Qed.

Goal ∀ x y z f g, normalize_denote x z [Arr y z f; Arr x y g] =
                  match arrs f y z, arrs g x y with
                  | Some f, Some g => Some (f ∘ g)
                  | _, _ => None
                  end.
  intros; simpl.
  rewrite !Neq_dec_refl.
  destruct (arrs f y z); reflexivity.
Qed.

Theorem normalize_arrows_sound_eq
: ∀ p dom cod pV,
    denote C objs arrs dom cod p = Some pV ->
    ∃ pV', pV ≈ pV' ∧ normalize_denote dom cod (normalize_arrows p) = Some pV'.
Proof.
  induction p; simpl; intros.
  - exists pV.
    split; [reflexivity|].
    destruct (N.eq_dec _ _); subst;
    destruct (N.eq_dec _ _); subst; auto.
    discriminate.
  - exists pV.
    split; [reflexivity|].
    repeat destruct (N.eq_dec _ _); subst; auto.
    destruct (arrs n1 dom cod); auto.
  - specialize (IHp1 (TermCod p2) cod).
    specialize (IHp2 dom (TermCod p2)).
    destruct (denote C objs arrs dom (TermCod p2) p2) eqn:Heqe1;
    destruct (denote C objs arrs (TermCod p2) cod p1) eqn:Heqe2;
    try discriminate.
    destruct (IHp1 _ eq_refl); clear IHp1.
    destruct (IHp2 _ eq_refl); clear IHp2.
    destruct p, p0.
    inversion_clear H.
    exists (x ∘ x0); eexists; auto.
      rewrite e, e1; reflexivity.
    clear e e1.
    simpl.
Admitted.

Theorem no_normalize dom cod : ∀ f,
  denote C objs arrs dom cod f = None ->
  normalize_denote dom cod (normalize_arrows f) = None.
Proof.
  generalize dependent dom.
  generalize dependent cod.
  induction f; intros; subst;
  simpl normalize_arrows;
  simpl normalize_denote;
  simpl in H.
Admitted.

Theorem normalize_arrows_id dom : ∀ g,
  TermDom g = dom ->
  normalize_arrows g = [] ->
  denote C objs arrs dom dom g ≈ Some (@id C (objs dom)).
Proof.
  generalize dependent dom.
  induction g; simpl; intros.
  - destruct (N.eq_dec n dom); subst.
      destruct e.
      reflexivity.
    contradiction.
  - destruct (N.eq_dec n dom); subst; subst;
    destruct (N.eq_dec n0 dom); subst; subst; auto;
    destruct (arrs n1 dom dom); simpl; discriminate.
  - simpl in *.
    apply app_eq_nil in H0.
    destruct H0.
    subst.
    intuition.

Theorem normalize_arrows_apply dom cod : ∀ f g,
  TermDom f = TermDom g ->
  normalize_arrows f = normalize_arrows g ->
  denote C objs arrs dom cod f ≈ denote C objs arrs dom cod g.
Proof.
  generalize dependent dom.
  generalize dependent cod.
  induction f; intros; simpl in H, H0; subst.
  - admit.
  - admit.
  - 
  pose proof (normalize_arrows_sound_eq).
  destruct (denote C objs arrs dom cod f) eqn:Heqe.
    destruct (normalize_arrows_sound_eq _ _ _ _ Heqe), p.
    destruct (denote C objs arrs dom cod g) eqn:Heqe2.
      destruct (normalize_arrows_sound_eq _ _ _ _ Heqe2), p.
      rewrite H1 in e0.
      rewrite e0 in e2.
      inversion e2.
      subst.
      red.
      rewrite e, e1.
      reflexivity.
    rewrite H1 in e0; clear H1 Heqe e.
    apply no_normalize in Heqe2.
    rewrite e0 in Heqe2.
    discriminate.
  destruct (denote C objs arrs dom cod g) eqn:Heqe2.
    destruct (normalize_arrows_sound_eq _ _ _ _ Heqe2), p.
    rewrite <- H1 in e0; clear H1 Heqe2 e.
    apply no_normalize in Heqe.
    rewrite e0 in Heqe.
    discriminate.
  reflexivity.
Qed.

Fixpoint normalize (p : Term) : Term :=
  match p with
  | Compose g f => mkCompose (normalize g) (normalize f)
  | _ => p
  end.

Theorem normalize_sound_no_exist_eq
: ∀ p dom cod,
    @denote C objs arrs dom cod p = None ->
    @denote C objs arrs dom cod (normalize p) = None.
Proof.
  induction p; intros; auto.
  specialize (IHp1 (TermCod p2) cod).
  specialize (IHp2 dom (TermCod p2)).
  simpl in H.
  destruct (denote C objs arrs dom (TermCod p2) p2);
  destruct (denote C objs arrs (TermCod p2) cod p1);
  try discriminate; intuition idtac.
Abort.

Theorem normalize_sound : ∀ f dom cod f',
  denote C objs arrs dom cod f ≈ Some f' ->
  ∃ g', f' ≈ g' ∧ denote C objs arrs dom cod (normalize f) ≈ Some g'.
Proof.
  induction f; intros.
  - eexists; eexists.
      reflexivity.
    simpl normalize; subst.
    assumption.
  - eexists; eexists.
      reflexivity.
    simpl normalize; subst.
    assumption.
  - specialize (IHf1 (TermCod f2) cod).
    specialize (IHf2 dom (TermCod f2)).
    revert X.
    subst.
Admitted.

(*
    simpl.
    destruct (denote C objs arrs dom (TermCod f2) f2).
    destruct (IHf2 h); [reflexivity|]; subst.
    destruct (denote C objs arrs (TermCod f2) cod f1); [|tauto].
    destruct (IHf1 h0); [reflexivity|]; subst.
    destruct (IHf1 _ eq_refl) as [ ? [ ? ? ] ]; clear IHf1.
    specialize (IHf2 _ eq_refl) as [ ? [ ? ? ] ].
    destruct (mkCompose_sound _ _ _ _ _ _ _ e0 e2) as [ ? [ ? ? ] ].
    intros.
    eexists.
    inversion_clear H.
    split.
      rewrite e, e1, e3.
      reflexivity.
    assumption.
Defined.
*)

Eval vm_compute in normalize (Compose (Morph 0 0 0) (Identity 0)).
Eval vm_compute in normalize (Compose (Morph 0 0 0) (Compose (Morph 0 0 0) (Identity 0))).
Eval vm_compute in normalize (Compose (Morph 0 0 0) (Compose (Morph 0 0 0) (Morph 0 0 0))).

End Reduction.

Theorem normalize_apply_identity_eq C objs arrs : ∀ f x,
  normalize f = Identity x ->
  denote C objs arrs x x f ≈ Some (@id C (objs x)).
Proof.
  intros.
  induction f; simpl normalize in H; try discriminate.
  - rewrite H; simpl.
    rewrite Neq_dec_refl.
    reflexivity.
Admitted.

Theorem normalize_apply_eq C objs arrs dom cod : ∀ f f' g g',
  normalize f = f' ->
  normalize g = g' ->
  f' = g' ->
  denote C objs arrs dom cod f ≈ denote C objs arrs dom cod g.
Proof.
  intros; subst.
  induction f; simpl normalize in H1.
Abort.

Theorem normalize_apply C objs arrs dom cod : ∀ f f' g g',
  normalize f = f' ->
  normalize g = g' ->
  denote C objs arrs dom cod f' ≈ denote C objs arrs dom cod g' ->
  denote C objs arrs dom cod f  ≈ denote C objs arrs dom cod g.
Proof.
  intros.
  subst.
  destruct f, g; try solve [simpl normalize in X; auto].
  - simpl normalize at 1 in X.
    rewrite X; clear X.
    pose proof (normalize_sound objs arrs (Compose g1 g2) dom cod).
    destruct (denote C objs arrs dom cod (Compose g1 g2)) eqn:Heqe.
      destruct (X h).
        reflexivity.
      destruct p.
      rewrite e0.
      red.
      symmetry.
      assumption.
    rewrite <- Heqe.
    clear.
    induction (Compose g1 g2); try reflexivity.
Admitted.

Definition Equiv C objs arrs dom cod (a b : Term) : Type :=
  denote C objs arrs dom cod a ≈ denote C objs arrs dom cod b.
Arguments Equiv _ _ _ _ _ _ _ /.

Corollary Compose'_Identity_Left x g : mkCompose (Identity x) g = g.
Proof. reflexivity. Qed.

Lemma Compose'_Identity_Right f x :
  TermDom f = x -> mkCompose f (Identity x) = f.
Proof. destruct f; simpl; intros; subst; auto. Qed.

Program Fixpoint check_equiv (p : Term * Term) dom cod {wf (R) p} : bool :=
  match p with (s, t) =>
    N.eqb (TermDom s) dom &&& N.eqb (TermDom t) dom &&&
    N.eqb (TermCod s) cod &&& N.eqb (TermCod t) cod &&&
    match s with
    | Identity x =>
      match t with
      | Identity y  => N.eqb x y
      | Morph x y g => false
      | Compose h k => false
      end
    | Morph x y f =>
      match t with
      | Identity _  => false
      | Morph z w g => N.eqb f g
      | Compose h k => false
      end
    | Compose f g =>
      match t with
      | Identity _  => false
      | Morph _ _ g => false
      | Compose h k =>
        N.eqb (TermDom f) (TermCod g) &&&
        N.eqb (TermDom f) (TermDom h) &&&
        N.eqb (TermCod g) (TermCod k) &&&
        check_equiv (f, h) (TermDom f) (TermCod f) &&&
        check_equiv (g, k) (TermDom g) (TermCod g)
      end
    end
  end.
Next Obligation.
  subst; simpl in *; clear.
  constructor; constructor.
Defined.
Next Obligation.
  subst; simpl in *; clear.
  constructor; constructor.
Defined.
Next Obligation.
  apply measure_wf.
  apply wf_symprod2.
  apply Subterm_wf.
Defined.

Lemma check_equiv_dom_cod dom cod s t :
  check_equiv (s, t) dom cod = true ->
  TermDom s = dom ∧ TermDom t = dom ∧
  TermCod s = cod ∧ TermCod t = cod.
Proof.
  Local Opaque N.eqb.
  intros.
  destruct s, t; simpl in *;
  compute in H;
  equalities;
  intuition.
Qed.

Lemma check_equiv_compose dom cod s1 s2 t1 t2 :
  check_equiv (Compose s1 s2, Compose t1 t2) dom cod = true ->
  TermDom s1 = TermCod s2 ∧
  TermDom t1 = TermCod t2 ∧
  check_equiv (s1, t1) (TermDom s1) cod = true ∧
  check_equiv (s2, t2) dom (TermCod s2) = true.
Proof.
  intros.
  pose proof (check_equiv_dom_cod _ _ _ _ H).
  Local Opaque TermDom.
  Local Opaque TermCod.
  compute in H.
  Local Transparent TermDom.
  Local Transparent TermCod.
  equalities.
  intuition idtac.
  - congruence.
Admitted.

Local Opaque N.eqb.

Theorem check_equiv_sound C objs arrs dom cod (s t : Term) :
  check_equiv (s, t) dom cod = true
    -> Equiv C objs arrs dom cod s t.
Proof.
  unfold Equiv.
  Local Opaque N.eqb.
  Local Opaque TermDom.
  Local Opaque TermCod.
  generalize dependent t.
  generalize dependent dom.
  generalize dependent cod.
  induction s; intros.
  - destruct t; compute in H;
    equalities; try discriminate.
    Local Transparent TermDom.
    Local Transparent TermCod.
    reflexivity.
  - destruct t; compute in H;
    equalities; try discriminate.
    Local Transparent TermDom.
    Local Transparent TermCod.
    reflexivity.
  - destruct t.
    + compute in H; equalities; discriminate.
    + compute in H; equalities; discriminate.
    + assert (∀ mid,
              TermDom s1 = mid ->
              TermDom t1 = mid ->
              TermCod s2 = mid ->
              TermCod t2 = mid ->
              equiv (denote C objs arrs mid cod s1)
                    (denote C objs arrs mid cod t1) ->
              equiv (denote C objs arrs dom mid s2)
                    (denote C objs arrs dom mid t2) ->
              equiv (denote C objs arrs dom cod (Compose s1 s2))
                    (denote C objs arrs dom cod (Compose t1 t2))).
        clear; intros.
        subst.
        simpl in *.
        rewrite !H2, !H1.
        destruct (denote C objs arrs dom (TermDom s1) s2);
        destruct (denote C objs arrs (TermDom s1) cod s1);
        destruct (denote C objs arrs dom (TermDom s1) t2);
        destruct (denote C objs arrs (TermDom s1) cod t1); auto.
        rewrite X, X0; reflexivity.
      pose proof (check_equiv_dom_cod _ _ _ _ H).
      pose proof (check_equiv_compose _ _ _ _ _ _ H).
      Local Opaque TermDom.
      Local Opaque TermCod.
      compute in H.
      Local Transparent TermDom.
      Local Transparent TermCod.
      equalities.
      eapply X.
        apply e.
        congruence.
        congruence.
        congruence.
        apply IHs1.
        rewrite <- e.
        assumption.
      apply IHs2; assumption.
Qed.

Print Assumptions check_equiv_sound.

Example speed_test :
  check_equiv
    (normalize (Compose (Morph 2 3 0) (Compose (Morph 1 2 1) (Morph 0 1 2))),
     normalize (Compose (Compose (Morph 2 3 0) (Morph 1 2 1)) (Morph 0 1 2))) 0 3 = true.
Proof. reflexivity. Qed.

Definition decision_correct C objs arrs dom cod {t u : Term}
           (Heq : check_equiv (t, u) dom cod = true) :
  Equiv C objs arrs dom cod t u :=
  check_equiv_sound C objs arrs dom cod t u Heq.

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

Ltac reifyValidTerm fs xs t objs arrs :=
  match t with
  | @id _ ?X =>
    let x := lookup X xs in
    constr:(existT (Valid _ objs arrs x x)
                   (Identity x) (eq_refl, (eq_refl, (eq_refl, eq_refl))))
  | ?X1 ∘ ?X2 =>
    let r1 := reifyValidTerm fs xs X1 objs arrs in
    match r1 with
      (?r1_1; ?r1_2) =>
      let r2 := reifyValidTerm fs xs X2 objs arrs in
      match r2 with
        (?r2_1; ?r2_2) =>
        constr:(existT (Valid _ objs arrs (TermDom r2_1) (TermCod r1_1))
                       (Compose r1_1 r2_1)
                       (eq_refl, (eq_refl, (r1_2, r2_2))))
      end
    end
  | ?F =>
    let n := lookup F fs in
    match type of F with
    | ?X ~> ?Y =>
      let x := lookup X xs in
      let y := lookup Y xs in
      constr:(existT (Valid _ objs arrs x y) (Morph x y n)
                     (eq_refl, (eq_refl, (eq_refl, (eq_refl, (F; eq_refl))))))
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
        (* let r1'  := reifyValidTerm fs xs S objs arrs in *)
        (* let r2'  := reifyValidTerm fs xs T objs arrs in *)
        (* pose r1'; *)
        (* pose r2'; *)
        change (denote _ objs arrs (TermDom r1) (TermCod r1) r1 ≈
                denote _ objs arrs (TermDom r2) (TermCod r2) r2);
        apply (normalize_arrows_apply
                 objs arrs (TermDom r1) (TermCod r1)
                 r1 r2 eq_refl eq_refl eq_refl)
        (* apply (normalizeValid_apply *)
        (*          _ objs arrs (TermDom (`1 r1')) (TermCod (`1 r1')) *)
        (*          r1' r2')(* ; *) *)
        (* change (denote _ objs arrs (TermDom r1) (TermCod r1) r1 ≈ *)
        (*         denote _ objs arrs (TermDom r2) (TermCod r2) r2); *)
        (* (* apply (normalize_apply_eq _ objs arrs (TermDom r1) (TermCod r1) *) *)
        (* (*                        r1 (normalize r1) r2 (normalize r2) *) *)
        (* (*                        eq_refl eq_refl); *) *)
        (* apply (normalize_apply _ objs arrs (TermDom r1) (TermCod r1) *)
        (*                        r1 (normalize r1) r2 (normalize r2) *)
        (*                        eq_refl eq_refl); *)
        (* simpl N.succ; *)
        (* simpl normalize; *)
        (* apply (@decision_correct _ objs arrs); *)
        (* vm_compute; *)
        (* auto *)
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
