Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Solver.ilist.

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Relations.Relations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.quote.Quote.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Coq.Vectors.Vector.
Require Import Coq.NArith.NArith.

Generalizable All Variables.
Set Primitive Projections.
Unset Transparent Obligations.
Set Universe Polymorphism.

Program Instance option_Setoid `{Setoid A} : Setoid (option A) := {
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

Section Solver.

Context {C : Category}.

Set Decidable Equality Schemes.

Open Scope N_scope.

Definition obj_idx := N.
Definition arr_idx := N.

Inductive Term : Type :=
  | Identity : ∀ x : obj_idx, Term
  | Morph    : ∀ x y : obj_idx, arr_idx -> Term
  | Compose  : Term -> Term -> Term.

Fixpoint TermDom (e : Term) : obj_idx :=
  match e with
  | Identity x => x
  | Morph x _ _ => x
  | Compose _ g => TermDom g
  end.

Fixpoint TermCod (e : Term) : obj_idx :=
  match e with
  | Identity x => x
  | Morph _ x _ => x
  | Compose f _ => TermCod f
  end.

Inductive Subterm : Term -> Term -> Prop :=.

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

Import EqNotations.

Program Fixpoint eval (e : Term)
         (objs : obj_idx -> C)
         (arrs : arr_idx -> ∀ a b : obj_idx, option (objs a ~> objs b)) :
  option (objs (TermDom e) ~> objs (TermCod e)) :=
  match e with
  | Morph x y n => arrs n x y
  | Identity x  => Some (@id C (objs x))
  | Compose f g =>
    match N.eq_dec (TermCod g) (TermDom f) with
    | left Heq =>
      let f' := eval f objs arrs in
      let g' := eval g objs arrs in
      match f', g' with
      | Some f', Some g' => Some (f' ∘ g')
      | _, _ => None
      end
    | right _ => None
    end
  end.
Next Obligation.
  rewrite Heq; reflexivity.
Defined.

Definition Equiv (f g : Term)
           (Heq_dom : TermDom g = TermDom f)
           (Heq_cod : TermCod g = TermCod f) : Type.
Proof.
  refine (∀ objs arrs, _).
  pose (eval f objs arrs) as Hf.
  pose (eval g objs arrs) as Hg.
  rewrite Heq_dom, Heq_cod in Hg.
  exact (Hf ≈ Hg).
Defined.
Arguments Equiv _ _ _ _ /.

Definition R := symprod Term Term Subterm Subterm.
Arguments R /.

Open Scope lazy_bool_scope.

Set Transparent Obligations.

(*
Definition decision (p : Term * Term)
           (Heq_dom : TermDom (snd p) = TermDom (fst p))
           (Heq_cod : TermCod (snd p) = TermCod (fst p)) :
  { b : bool & b = true -> Equiv (fst p) (snd p) Heq_dom Heq_cod }.
Proof.
  pose (wf_symprod _ _ _ _ Subterm_wf Subterm_wf) as wf.
  refine (Fix wf (fun (p : ((Term * Term) * _) * _) =>
                    { b : bool & b = true -> Equiv (fst p) (snd p) Heq_dom Heq_cod })
              (fun p rec => _) (p, Heq_dom, Heq_cod)).
  destruct p as [s t].
  destruct s as [x1|x1 y1 n1|x1 y1 z1 f1 g1].
  - exists false.
    intros; discriminate.
  - destruct t as [x2|x2 y2 n2|x2 y2 z2 f2 g2].
    + exists false.
      intros; discriminate.
    + exists (N.eqb n1 n2); simpl; intros.
      apply N.eqb_eq in H; subst.
      destruct (arrs n2 x2 y2); reflexivity.
    + exists false.
      intros; discriminate.
  - destruct t as [x2|x2 y2 n2|x2 y2 z2 f2 g2].
    + exists false.
      intros; discriminate.
    + exists false.
      intros; discriminate.
    + destruct (N.eq_dec y1 y2); subst.
        destruct (rec (f1, f2)).
        destruct (decision _ _ (g1, g2)).
        exists (x0 &&& x1); simpl; intros.
        destruct x0, x1; try discriminate.
        simpl in e, e0.
        specialize (e eq_refl objs arrs).
        specialize (e0 eq_refl objs arrs).
        destruct (eval s1 objs arrs), (eval s2 objs arrs),
                 (eval t1 objs arrs), (eval t2 objs arrs); auto.
        apply compose_respects; auto.
      exists false.
      intros; discriminate.
Qed.
*)

Local Obligation Tactic := intros; try discriminate.

Program Fixpoint decision (p : Term * Term)
        (Heq_dom : TermDom (snd p) = TermDom (fst p))
        (Heq_cod : TermCod (snd p) = TermCod (fst p))
        {wf (R) p} :
  { b : bool & b = true -> Equiv (fst p) (snd p) Heq_dom Heq_cod } :=
  match p with
  | (s, t) =>
    match s with
    | Identity _ => existT _ false _
    | Morph _ _ f =>
      match t with
      | Identity _  => existT _ false _
      | Morph _ _ g   => existT _ (N.eqb f g) _
      | Compose h k => existT _ false _
      end
    | Compose f g =>
      match t with
      | Identity _  => existT _ false _
      | Morph _ _ g   => existT _ false _
      | Compose h k =>
        match N.eq_dec (TermDom f) (TermDom h) with
        | left Heq_dom_f =>
          match N.eq_dec (TermCod f) (TermCod h) with
          | left Heq_cod_f =>
            match N.eq_dec (TermDom g) (TermDom k) with
            | left Heq_dom_g =>
              match N.eq_dec (TermCod g) (TermCod k) with
              | left Heq_cod_g =>
                existT _ (`1 (decision (f, h) Heq_dom_f Heq_cod_f) &&&
                          `1 (decision (g, k) Heq_dom_g Heq_cod_g)) _
              | right _ => existT _ false _
              end
            | right _ => existT _ false _
            end
          | right _ => existT _ false _
          end
        | right _ => existT _ false _
        end
      end
    end
  end.
Next Obligation.
  subst; simpl; intros.
  apply N.eqb_eq in H; subst.
  unfold eq_rect; simpl in *; subst.
  destruct (arrs g _ _); simpl; reflexivity.
Defined.
Next Obligation. subst; simpl in *; congruence. Defined.
Next Obligation. subst; simpl in *; congruence. Defined.
Next Obligation. subst; simpl in *; congruence. Defined.
Next Obligation. subst; simpl in *; congruence. Defined.
Next Obligation.
  subst; simpl in *.
Admitted.
Next Obligation. subst; simpl in *; congruence. Defined.
Next Obligation. subst; simpl in *; congruence. Defined.
Next Obligation. subst; simpl in *; congruence. Defined.
Next Obligation. subst; simpl in *; congruence. Defined.
Next Obligation.
  subst; simpl in *.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
  simpl; unfold MR.
  apply wf_symprod.
Admitted.
Next Obligation. simpl; intros; discriminate. Defined.
Next Obligation. simpl; intros; discriminate. Qed.
Next Obligation. simpl; intros; discriminate. Qed.
Next Obligation.
  simpl; intros; discriminate.
Next Obligation. intros; discriminate. Qed.
Next Obligation.
  intros; discriminate.
Qed.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
  destruct x; simpl in *.
  unfold eq_rect in *; simpl in *.
Admitted.
(* Next Obligation. *)
(*   apply wf_symprod; *)
(*   apply Subterm_wf. *)
(* Defined. *)

Example speed_test :
  ` (leq (Meet (Var 0) (Var 1), Join (Var 0) (Var 1))) = true.
Proof. reflexivity. Qed.

Notation "s ≲ t" := (leq (s, t)) (at level 30).

Definition leq_correct {t u : Term} (Heq : ` (t ≲ u) = true) :
  forall env, 〚t〛env ≤ 〚u〛env := proj2_sig (leq (t, u)) Heq.

End Lattice.

Notation "〚 t 〛 env" := (@eval _ _ t env) (at level 9).
Notation "s ≲ t" := (@leq _ _ _ _ (s, t)) (at level 30).

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

Ltac allVars xs e :=
  match e with
  | ?e1 ⊓ ?e2 =>
    let xs := allVars xs e1 in
    allVars xs e2
  | ?e1 ⊔ ?e2 =>
    let xs := allVars xs e1 in
    allVars xs e2
  | _ => addToList e xs
  end.

Ltac lookup x xs :=
  match xs with
  | (x, _) => O
  | (_, ?xs') =>
    let n := lookup x xs' in
    constr:(S n)
  end.

Ltac reifyTerm env t :=
  match t with
  | ?X1 ⊓ ?X2 =>
    let r1 := reifyTerm env X1 in
    let r2 := reifyTerm env X2 in
    constr:(Meet r1 r2)
  | ?X1 ⊔ ?X2 =>
    let r1 := reifyTerm env X1 in
    let r2 := reifyTerm env X2 in
    constr:(Join r1 r2)
  | ?X =>
    let n := lookup X env in
    constr:(Var n)
  end.

Ltac functionalize xs :=
  let rec loop n xs' :=
    match xs' with
    | (?x, tt) => constr:(fun _ : nat => x)
    | (?x, ?xs'') =>
      let f := loop (S n) xs'' in
      constr:(fun m : nat => if m =? n then x else f m)
    end in
  loop 0 xs.

Ltac reify :=
  match goal with
  | [ |- ?S ≤ ?T ] =>
    let xs  := allVars tt S in
    let xs' := allVars xs T in
    let r1  := reifyTerm xs' S in
    let r2  := reifyTerm xs' T in
    let env := functionalize xs' in
    (* pose xs'; *)
    (* pose env; *)
    (* pose r1; *)
    (* pose r2; *)
    change (〚r1〛env ≤ 〚r2〛env)
  end.

Ltac lattice := reify; apply leq_correct; vm_compute; auto.

Example sample_1 `{LOSet A} : forall a b : A,
  a ≤ a ⊔ b.
Proof. intros; lattice. Qed.

Lemma running_example `{LOSet A} : forall a b : A,
  a ⊓ b ≤ a ⊔ b.
Proof.
  intros a b.
  rewrite meet_consistent.
  rewrite meet_associative.
  rewrite join_commutative.
  rewrite meet_absorptive.
  reflexivity.
Qed.

Lemma running_example' `{LOSet A} : forall a b : A,
  a ⊓ b ≤ a ⊔ b.
Proof. intros; lattice. Qed.

Lemma median_inequality `{LOSet A} : forall x y z : A,
  (x ⊓ y) ⊔ (y ⊓ z) ⊔ (z ⊓ x) ≤ (x ⊔ y) ⊓ (y ⊔ z) ⊓ (z ⊔ x).
Proof. intros; lattice. Qed.

End Solver.
