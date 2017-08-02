Set Warnings "-notation-overridden".

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Recdef.

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Solver.Lib.
Require Import Solver.Expr.

Generalizable All Variables.

Section Normal.

Import EqNotations.

(* Notation Term    := (Term arrs). *)
(* Notation TermDom := (TermDom arrs). *)
(* Notation TermCod := (TermCod arrs). *)

(* This describes the morphisms of a path, or free, category over a quiver of
   Arrows, while our environment describes a quiver (where vertices are all
   object indices, and edges are all arrow indices associated pairs of object
   indices). The denotation of an ArrowList to some category C is a forgetful
   functor from the path category over this quiver to C. Note that this
   functor is only total if the denotation of the quiver itself is total. *)
Inductive ArrowList : Set :=
  | IdentityOnly (o : obj_idx) : ArrowList
  | ArrowChain   (a : arr_idx) : ArrowList -> ArrowList.

Function ArrowList_beq (f g : ArrowList) : bool :=
  match f with
  | IdentityOnly o =>
    match g with
    | IdentityOnly o' => Eq_eqb o o'
    | ArrowChain _ _ => false
    end
  | ArrowChain f fs =>
    match g with
    | IdentityOnly _ => false
    | ArrowChain g gs => Eq_eqb f g &&& ArrowList_beq fs gs
    end
  end.

Fixpoint ArrowList_length (x : ArrowList) : nat :=
  match x with
  | IdentityOnly x  => 0
  | ArrowChain x xs => 1 + ArrowList_length xs
  end.

Lemma ArrowList_beq_eq (f g : ArrowList) : ArrowList_beq f g = true -> f = g.
Proof.
  apply well_founded_induction_type_2
    with (R:=symprod2 _ (ltof _ ArrowList_length)) (a:=f) (b:=g).
    apply wf_symprod2;
    apply well_founded_ltof.
  intros; destruct x, x'; simpl in H0.
  - equalities.
  - discriminate.
  - discriminate.
  - equalities.
    f_equal.
    apply H; auto.
    constructor; unfold ltof; simpl; abstract omega.
Defined.

Function ArrowList_dom (xs : ArrowList) : obj_idx :=
  match xs with
  | IdentityOnly o => o
  | ArrowChain _ x => ArrowList_dom x
  end.

Variable arrs : arr_idx -> (obj_idx * obj_idx).

Definition arr_dom (f : arr_idx) : obj_idx := fst (arrs f).
Definition arr_cod (f : arr_idx) : obj_idx := snd (arrs f).

Definition ArrowList_cod (xs : ArrowList) : obj_idx :=
  match xs with
  | IdentityOnly o => o
  | ArrowChain a _ => arr_cod a
  end.

(*
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
*)

Function ArrowList_append (xs ys : ArrowList) : ArrowList :=
  match xs with
  | IdentityOnly _  => ys
  | ArrowChain f fs => ArrowChain f (ArrowList_append fs ys)
  end.

Fixpoint normalize `(p : Term a b) : ArrowList :=
  match p with
  | Identity x   => IdentityOnly x
  | @Morph x _ f => ArrowChain f (IdentityOnly x)
  | Compose f g  => ArrowList_append (normalize f) (normalize g)
  end.

Function denormalize (f : ArrowList) : ∃ a b, Term a b :=
  match f with
  | IdentityOnly o => (o; (o; Identity o))
  | ArrowChain f fs =>
    let z := arr_cod f in
    let '(x; (y; g)) := denormalize fs in
    (x; (z; match g return Term x z with
            | Identity _ => @Morph x z f
            | _ => @Compose x y z (@Morph y z f) g
            end))
  end.

Lemma normalize_denormalize {f} : normalize (`2 `2 (denormalize f)) = f.
Proof.
  induction f; simpl; auto.
  destruct (denormalize f), s, t; simpl in *;
  now rewrite IHf.
Qed.

(*
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
*)

(*
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
*)

(*
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

Fixpoint ArrowList_from_list (xs : obj_idx * list Arrow) : ArrowList :=
  match xs with
  | (x, nil) => IdentityOnly x
  | (_, x :: xs) => ArrowChain x xs
  end.

Lemma ArrowList_to_from_list xs :
  ArrowList_to_list (ArrowList_from_list xs) = xs.
Proof.
  destruct xs.
  induction l; simpl; auto.
  simpl in IHl.
  f_equal.
  destruct l; simpl in *.
    admit.
  inversion_clear IHl.
  destruct l; auto.
  f_equal.
  f_equal.
Abort.

Definition ArrowList_length (x : ArrowList) : nat :=
  match x with
  | IdentityOnly x => 0
  | ArrowChain x xs => 1 + length xs
  end.

Function ArrowList_beqn (n : nat) (x y : ArrowList) : bool :=
  match n with
  | O => true
  | S n' =>
    match x, y with
    | IdentityOnly cod1, IdentityOnly cod2 => Eq_eqb cod1 cod2
    | ArrowChain x1 nil, ArrowChain x2 (_ :: _) =>
      match n' with
      | O => Eq_eqb x1 x2
      | S x => false
      end
    | ArrowChain x1 (_ :: _), ArrowChain x2 nil =>
      match n' with
      | O => Eq_eqb x1 x2
      | S x => false
      end
    | ArrowChain x1 (y1 :: ys1), ArrowChain x2 (y2 :: ys2) =>
      Eq_eqb x1 x2 &&&
      ArrowList_beqn n' (ArrowChain y1 ys1) (ArrowChain y2 ys2)
    | _, _ => false
    end
  end.

Function ArrowList_drop (n : nat) (xs : ArrowList) : ArrowList :=
  match n with
  | O => xs
  | S n' =>
    match xs with
    | IdentityOnly o => IdentityOnly o
    | ArrowChain f nil => IdentityOnly (arr_cod f)
    | ArrowChain f (x :: xs) => ArrowList_drop n' (ArrowChain x xs)
    end
  end.
*)

End Normal.
