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

Lemma K_dec_on_type A (x : A) (eq_dec : ∀ y : A, x = y \/ x ≠ y)
      (P : x = x -> Type) :
  P (eq_refl x) -> ∀ p:x = x, P p.
Proof.
  intros.
  elim (@Eqdep_dec.eq_proofs_unicity_on A _) with x (eq_refl x) p.
    trivial.
  exact eq_dec.
Defined.

Corollary Neq_dec' : ∀ x y : N, x = y \/ x ≠ y.
Proof. intros; destruct (N.eq_dec x y); auto. Defined.

Lemma Neq_dec_refl n : N.eq_dec n n = left (@eq_refl N n).
Proof.
  destruct (N.eq_dec n n).
    refine (K_dec_on_type N n (Neq_dec' n)
              (fun x => @left _ _ x = @left _ _ (@eq_refl N n)) _ _).
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

Inductive Subterm : Term -> Term -> Prop :=
  | Compose1 : ∀ t1 t2, Subterm t1 (Compose t1 t2)
  | Compose2 : ∀ t1 t2, Subterm t2 (Compose t1 t2).

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

Definition R := symprod2 Term Subterm.
Arguments R /.

Open Scope lazy_bool_scope.

Set Transparent Obligations.

Local Obligation Tactic := intros; try discriminate.

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

Lemma denote_dom_cod : ∀ f dom cod f',
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

Inductive Arrow : Set :=
  | Arr : N -> N -> N -> Arrow.

Program Fixpoint normalize (p : Term) : list Arrow :=
  match p with
  | Identity x  => []
  | Morph x y f => [Arr x y f]
  | Compose f g => normalize f ++ normalize g
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

Theorem normalize_sound : ∀ p dom cod pV,
  denote dom cod p = Some pV ->
  ∃ pV', pV ≈ pV' ∧ normalize_denote dom cod (normalize p) = Some pV'.
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
    destruct (denote dom (TermCod p2) p2) eqn:Heqe1;
    destruct (denote (TermCod p2) cod p1) eqn:Heqe2;
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

Theorem normalize_apply dom cod : ∀ f g,
  TermDom f = TermDom g ->
  normalize f = normalize g ->
  denote dom cod f ≈ denote dom cod g.
Proof.
  intros.
  destruct (denote dom cod f) eqn:Heqe.
    destruct (normalize_sound _ _ _ _ Heqe), p.
    destruct (denote dom cod g) eqn:Heqe2.
      destruct (normalize_sound _ _ _ _ Heqe2), p.
      rewrite H0 in e0.
      rewrite e0 in e2.
      inversion e2.
      subst.
      red.
      rewrite e, e1.
      reflexivity.
    rewrite H0 in e0.
    admit.
  destruct (denote dom cod g) eqn:Heqe2.
    destruct (normalize_sound _ _ _ _ Heqe2), p.
    rewrite <- H0 in e0.
    admit.
  reflexivity.
Admitted.

Definition Equiv dom cod (a b : Term) : Type :=
  denote dom cod a ≈ denote dom cod b.
Arguments Equiv _ _ _ _ /.

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

Theorem check_equiv_sound dom cod (s t : Term) :
  check_equiv (s, t) dom cod = true
    -> Equiv dom cod s t.
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
              equiv (denote mid cod s1)
                    (denote mid cod t1) ->
              equiv (denote dom mid s2)
                    (denote dom mid t2) ->
              equiv (denote dom cod (Compose s1 s2))
                    (denote dom cod (Compose t1 t2))).
        clear; intros.
        subst.
        simpl in *.
        rewrite !H2, !H1.
        destruct (denote dom (TermDom s1) s2);
        destruct (denote (TermDom s1) cod s1);
        destruct (denote dom (TermDom s1) t2);
        destruct (denote (TermDom s1) cod t1); auto.
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

Definition decision_correct dom cod {t u : Term}
           (Heq : check_equiv (t, u) dom cod = true) :
  Equiv dom cod t u :=
  check_equiv_sound dom cod t u Heq.

End denote.

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
        apply (normalize_apply _ objs arrs (TermDom r1) (TermCod r1)
                 r1 r2 eq_refl eq_refl);
        vm_compute;
        auto
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
