Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Category.

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
(* Require Import Coq.Relations.Relations. *)
(* Require Import Coq.Classes.RelationClasses. *)
(* Require Import Coq.quote.Quote. *)
Require Import Coq.Wellfounded.Lexicographic_Product.
(* Require Import Coq.Vectors.Vector. *)
Require Import Coq.NArith.NArith.

Generalizable All Variables.

(*
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
*)

Open Scope N_scope.

Definition obj_idx := N.
Definition arr_idx := N.

Set Decidable Equality Schemes.

Inductive Term : Set :=
| Identity : ∀ x : obj_idx, Term
| Morph    : ∀ x y : obj_idx, arr_idx -> Term
| Compose  : Term -> Term -> Term. (** It might be useful to store the (middle) obj_idx on Compose, it makes type checking easier. *)

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

Section denote.
  Variable (C : Category).
  Variables (objs : obj_idx -> C)
            (arrs : arr_idx -> ∀ a b : obj_idx, option (objs a ~> objs b)).

  Fixpoint denote_infer dom (e : Term)
  : option { codom : _ & objs dom ~> objs codom } :=
    match e with
    | Identity t =>
      match N.eq_dec t dom with
      | left pf_dom => Some (existT (fun codom => objs dom ~> objs codom)
                                   t match pf_dom with
                                       | eq_refl => @id C (objs t)
                                       end)
      | _ => None
      end
    | Morph dom' codom' n =>
      match N.eq_dec dom' dom
          , arrs n dom' codom'
      with
      | left pf_dom , Some arr =>
        Some (existT (fun codom => objs dom ~> objs codom) codom' match pf_dom with
                              | eq_refl => arr
                              end)
      | _ , _ => None
      end
    | Compose g f =>
      match denote_infer dom f with
      | Some (existT _ t' farr) =>
        match denote_infer t' g with
        | Some (existT _ t'' garr) =>
          Some (existT (fun codom => objs dom ~> objs codom) t''
                       (garr ∘ farr))
        | _ => None
        end
      | _ => None
      end
    end.

  Fixpoint denote dom codom (e : Term)
  : option (objs dom ~> objs codom) :=
    match e with
    | Identity t =>
      match N.eq_dec t dom
          , N.eq_dec t codom
      with
      | left pf_dom , left pf_codom => Some (match pf_dom , pf_codom with
                                            | eq_refl , eq_refl => (@id C (objs t))
                                            end)
      | _ , _ => None
      end
    | Morph dom' codom' n =>
      match N.eq_dec dom' dom
          , N.eq_dec codom' codom
          , arrs n dom' codom'
      with
      | left pf_dom , left pf_codom , Some arr =>
        Some (match pf_dom , pf_codom with
              | eq_refl , eq_refl => arr
              end)
      | _ , _ , _ => None
      end
    | Compose g f =>
      match denote dom (TermCod f) f
          , denote _ codom g with
      | Some farr , Some garr =>
        Some (garr ∘ farr)
      | _ , _ => None
      end
      (** This is a nicer formulation, but it requires proving an
       ** additional fact
      match denote_infer dom f with
      | Some (existT _ z farr) =>
        match denote z codom g with
        | Some garr =>
          Some (garr ∘ farr)
        | _ => None
        end
      | _ => None
      end
      **)
    end.
End denote.

(** A simple definition of `Equiv`. Again, it might be convenient to
 ** pass in `dom` and `codom` to this definition.
 **)
Definition Equiv dom codom (a b : Term) : Type :=
  forall C objs arrs,
    match @denote C objs arrs dom codom a
        , @denote C objs arrs dom codom b with
    | Some aV , Some bV => aV ≈ bV
    | _ , _ => False
    end.

Fixpoint Term_eq_dec (x y : Term) : {x = y} + {x ≠ y}.
Proof.
  destruct x, y; try (right; unfold not; intros; discriminate).
  - destruct (N.eq_dec x x0); subst;
    solve [ left; reflexivity | right; congruence ].
  - destruct (N.eq_dec x x0); subst;
    destruct (N.eq_dec y y0); subst;
    destruct (N.eq_dec a a0); subst;
    solve [ left; reflexivity | right; congruence ].
  - destruct (Term_eq_dec x1 y1); subst;
    destruct (Term_eq_dec x2 y2); subst;
    solve [ left; reflexivity | right; congruence ].
Defined.

(** While useful, none of your definitions require this. *)
Inductive Subterm : Term -> Term -> Prop :=
  | Compose1 : forall t1 t2, Subterm t1 (Compose t1 t2)
  | Compose2 : forall t1 t2, Subterm t2 (Compose t1 t2).

(** gmm: What is this? *)
Definition Subterm_inv_t : forall x y, Subterm x y -> Prop.
Proof.
  intros [] [] f;
  match goal with
  | [ H : Subterm ?X (Compose ?Y ?Z) |- Prop ] =>
    destruct (Term_eq_dec X Y); subst;
    [ destruct (Term_eq_dec X Z); subst;
      [ exact (f = Compose1 _ _ \/ f = Compose2 _ _)
      | exact (f = Compose1 _ _) ]
    | destruct (Term_eq_dec X Z); subst;
      [ exact (f = Compose2 _ _)
      | exact False ] ]
  | [ H : Subterm ?X (Compose ?Y ?Z) |- Prop ] =>
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

Lemma K_dec_on_type A (x : A) (eq_dec : ∀ y : A, x = y \/ x ≠ y)
      (P : x = x -> Type) :
  P (eq_refl x) -> forall p:x = x, P p.
Proof.
  intros.
  elim (@Eqdep_dec.eq_proofs_unicity_on A _) with x (eq_refl x) p.
    trivial.
  exact eq_dec.
Defined.

Lemma Term_eq_dec' : ∀ x y : Term, x = y \/ x ≠ y.
Proof.
  intros.
  destruct (Term_eq_dec x y); auto.
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

(*
Corollary Subterm_inv x y f : Subterm_inv_t x y f.
Proof.
  pose proof Term_eq_dec.
  destruct f, t1, t2; simpl;
  repeat destruct (Term_eq_dec _ _); subst;
  unfold eq_rec_r, eq_rec, eq_rect, eq_sym;
  repeat rewrite Neq_dec_refl; simpl;
  try (rewrite e || rewrite <- e);
  try (rewrite e0 || rewrite <- e0);
  try congruence;
  try rewrite <- Eqdep_dec.eq_rect_eq_dec; eauto; simpl; intuition;
  try rewrite <- Eqdep_dec.eq_rect_eq_dec; eauto; simpl; intuition; simpl;
  repeat destruct (N.eq_dec _ _); subst; simpl; intuition;
  try dependent destruction e;
  try dependent destruction e0;
  try dependent destruction e1;
  try dependent destruction e2;
  intuition.
Abort.                          (* nasty axiomses; we hates them forever! *)
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
      forall x x':A, leA x x' -> forall y:A, symprod2 (x, y) (x', y)
    | right_sym2 :
      forall y y':A, leA y y' -> forall x:A, symprod2 (x, y) (x, y')
    | both_sym2 :
      forall (x x':A) (y y':A),
        leA x x' ->
        leA y y' ->
        symprod2 (x, y) (x', y').

  Lemma Acc_symprod2 :
    forall x:A, Acc leA x -> forall y:A, Acc leA y -> Acc symprod2 (x, y).
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


(*
Definition Equiv (C : Category) (p : Term * Term) : Type.
Proof.
  refine (∀ objs arrs, _).
  destruct (N.eq_dec (TermDom (snd p)) (TermDom (fst p))).
    destruct (N.eq_dec (TermCod (snd p)) (TermCod (fst p))).
      destruct (eval C (fst p) objs arrs).
        destruct (eval C (snd p) objs arrs).
          rewrite e, e0 in h0.
          exact (h ≈ h0).
        exact False.
      exact True.
    exact False.
  exact False.
Defined.

Arguments Equiv _ _ /.
*)

Definition R := symprod2 Term Subterm.
Arguments R /.

Open Scope lazy_bool_scope.

Set Transparent Obligations.

Local Obligation Tactic := intros; try discriminate.


Definition mkCompose (a b : Term) : Term :=
  match a with
  | Identity _ => b
  | _ => match b with
        | Identity _ => a
        | _ => Compose a b
        end
  end.

Section with_category.
  Variable (C : Category).
  Variables (objs : obj_idx -> C)
            (arrs : arr_idx -> ∀ a b : obj_idx, option (objs a ~> objs b)).

Ltac forward_reason :=
  repeat match goal with
         | |- context [ match ?X with left _ => _ | right _ => None end = Some _ ] =>
           destruct X; [ | solve [ inversion 1 | inversion 2 ] ]
         | |- context [ match ?X with Some _ => _ | None => None end = Some _ ] =>
           destruct X; [ | solve [ inversion 1 | inversion 2 ] ]
         end.

Lemma denote_Dom_CoDom : forall f dom codom fV,
    @denote C objs arrs dom codom f = Some fV ->
    TermDom f = dom /\ TermCod f = codom.
Proof.
  induction f; intros dom codom; simpl; try solve [ forward_reason; auto ].
  { specialize (IHf2 dom (TermCod f2)).
    specialize (IHf1 (TermCod f2) codom).
    forward_reason.
    destruct (IHf1 _ eq_refl).
    destruct (IHf2 _ eq_refl).
    tauto. }
Defined.

Lemma mkCompose_sound_lem:
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
  { generalize dependent (Morph x y a).
    simpl. intros.
    destruct (denote_Dom_CoDom _ _ _ _ H).
    destruct (denote_Dom_CoDom _ _ _ _ H0).
    subst. rewrite H0. rewrite H.
    eexists. exists (reflexivity _). reflexivity. }
  { generalize dependent (Compose f1 f2).
    simpl. intros.
    destruct (denote_Dom_CoDom _ _ _ _ H).
    destruct (denote_Dom_CoDom _ _ _ _ H0).
    subst. rewrite H0. rewrite H.
    eexists. exists (reflexivity _). reflexivity. }
Defined.

Theorem mkCompose_sound
: forall τ τ' τ'' f fV g gV,
    @denote C objs arrs τ τ' f = Some fV ->
    @denote C objs arrs τ' τ'' g = Some gV ->
    { fgV : _ & { pf : gV ∘ fV ≈ fgV | @denote C objs arrs τ τ'' (mkCompose g f) = Some fgV } }.
Proof.
  destruct g.
  { simpl.
    forward_reason.
    inversion 2; subst. exists fV.
    exists (@id_left _ _ _ _). assumption. }
  { apply mkCompose_sound_lem. }
  { apply mkCompose_sound_lem. }
Defined.

(** I don't think this type is really what you want. The soundness of this
 ** gallina program should be something like:
 **
 ** forall dom codom val,
 **   eval' dom codom p = Some val ->
 **   exists val', eval' dom codom t = Some val'
 **           /\  val ≈ val'
 **
 ** This phrasing captures the fact that the function can assume the
 ** input `Term` is well-typed, and must ensure that the output `Term`
 ** is also well-typed. Without this, you end up needing to do a lot of
 ** type-checking within your automation which is slow and gets in the
 ** way. This is also the reason why you want to specify the denotation
 ** function by passing in `dom` and `codom` rather than computing them.
 **)
Fixpoint normalize (p : Term)
: Term :=
  match p with
  | Compose g f => mkCompose (normalize g) (normalize f)
  | _ => p
  end.

Theorem normalize_sound
: forall p dom codom pV,
    @denote C objs arrs dom codom p = Some pV ->
    { pV' : _ & { pf : pV ≈ pV' | @denote C objs arrs dom codom (normalize p) = Some pV' } }.
Proof.
  induction p; simpl; intros.
  { eexists. exists (reflexivity _). assumption. }
  { eexists. exists (reflexivity _). assumption. }
  { specialize (IHp1 (TermCod p2) codom).
    specialize (IHp2 dom (TermCod p2)).
    revert H. forward_reason.
    destruct (IHp1 _ eq_refl) as [ ? [ ? ? ] ]; clear IHp1.
    specialize (IHp2 _ eq_refl) as [ ? [ ? ? ] ].
    destruct (mkCompose_sound _ _ _ _ _ _ _ e0 e) as [ ? [ ? ? ] ].
    intros.
    eexists.
    split; [ | eassumption ].
    inversion H. subst.
    clear - x4 x2 x0.
    etransitivity; [ | eassumption ].
    eapply compose_respects; assumption. }
Defined.

Eval vm_compute in (normalize (Compose (Morph 0 0 0) (Identity 0))).

End with_category.

Program Fixpoint decision (p : Term * Term) {wf (R) p} :
  { b : bool & b = true -> ∀ C, Equiv C p } :=
  match p with
  | (s, t) =>
    match N.eq_dec (TermDom t) (TermDom s) with
    | right _ => existT _ false _
    | left Heq_dom_s =>
      match N.eq_dec (TermCod t) (TermCod s) with
      | right _ => existT _ false _
      | left Heq_dom_t =>

        match s with
        | Identity _ =>
          match t with
          | Identity _  => existT _ true _
          | Morph _ _ g => existT _ false _
          | Compose h k => existT _ false _
          end
        | Morph _ _ f =>
          match t with
          | Identity _  => existT _ false _
          | Morph _ _ g => existT _ (N.eqb f g) _
          | Compose h k => existT _ false _
          end
        | Compose f g =>
          match t with
          | Identity _  => existT _ false _
          | Morph _ _ g => existT _ false _
          | Compose h k => existT _ (`1 (decision (f, h)) &&&
                                     `1 (decision (g, k))) _
          end
        end

      end
    end
  end.
Next Obligation.
  simpl; intros; subst.
  repeat destruct (N.eq_dec _ _); simpl; auto.
  unfold eq_rect; simpl.
  destruct e.
  reflexivity.
Defined.
Next Obligation.
  simpl; intros; subst.
  apply N.eqb_eq in H; subst.
  repeat destruct (N.eq_dec _ _); simpl; auto.
  unfold eq_rect; simpl; subst.
  destruct (arrs g _ _); reflexivity.
Defined.
Next Obligation.
  subst; simpl in *; clear.
  constructor; constructor.
Defined.
Next Obligation.
  subst; simpl in *; clear.
  constructor; constructor.
Defined.
Next Obligation.
  simpl; intros; subst.
  repeat destruct (decision _ _); simpl in *;
  destruct x, x0; try discriminate;
  specialize (e eq_refl C objs arrs);
  specialize (e0 eq_refl C objs arrs);
  repeat destruct (N.eq_dec _ _); simpl; auto;
  unfold eval_obligation_1 in *; simpl in *;
  clear decision;
  destruct (eval C f objs arrs),
           (eval C g objs arrs),
           (eval C k objs arrs),
           (eval C h objs arrs);
  unfold eq_ind_r, eq_ind, eq_sym, eq_rect in *; simpl in *;
  auto; try tauto.
    destruct e5, e2, e1, e6, e3.
    rewrite e.
    apply compose_respects.
      reflexivity.
    rewrite e0; clear.
    (* Avoid the use of JMeq_eq, since otherwise [dependent destruction e4]
       would solve this goal. *)
    assert (K_dec_on_type :
              forall (x:N) (P:x = x -> Type),
                P (eq_refl x) -> forall p:x = x, P p).
      intros.
      elim (@Eqdep_dec.eq_proofs_unicity_on N _) with x (eq_refl x) p.
        trivial.
      intros.
      destruct (N.eq_dec x y); auto.
    exact (
      K_dec_on_type
        (TermCod k)
        (fun x =>
           Setoid.equiv
             match x in (_ = y) return (objs (TermDom k) ~{ C }~> objs y)
             with eq_refl => h2
             end h2)
        (Setoid.setoid_refl _ _) e4).
  clear -e3 e4 e5 n.
  congruence.
Admitted.
Next Obligation.
  apply measure_wf.
  apply wf_symprod2.
  apply Subterm_wf.
Defined.

Example speed_test (C : Category) :
  `1 (decision
      (`1 (normalize (Compose (Morph 2 3 0) (Compose (Morph 1 2 1) (Morph 0 1 2)))),
       `1 (normalize (Compose (Compose (Morph 2 3 0) (Morph 1 2 1)) (Morph 0 1 2))))) = true.
Proof. reflexivity. Qed.

Definition decision_correct {t u : Term}
        (Heq : `1 (decision (`1 (normalize t), `1 (normalize u))) = true) :
  ∀ C, Equiv C (`1 (normalize t), `1 (normalize u)) :=
  `2 (decision (`1 (normalize t), `1 (normalize u))) Heq.

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
  (* jww (2017-06-12): TODO *)
  | ?e1 ∘ ?e2 =>
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
  (* jww (2017-06-12): TODO *)
  | ?X1 ∘ ?X2 =>
    let r1 := reifyTerm env X1 in
    let r2 := reifyTerm env X2 in
    constr:(Compose r1 r2)
  | ?X =>
    let n := lookup X env in
    constr:(Morph n)
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
  | [ |- ?S ≈ ?T ] =>
    let xs  := allVars tt S in
    let xs' := allVars xs T in
    let r1  := reifyTerm xs' S in
    let r2  := reifyTerm xs' T in
    let objs := functionalize xs' in
    let arrs := functionalize xs' in
    (* pose xs'; *)
    (* pose env; *)
    (* pose r1; *)
    (* pose r2; *)
    (* jww (2017-06-12): TODO *)
    change (eval r1 objs arrs ≈ eval r2 objs arrs)
  end.

Ltac categorical := reify; apply decision_correct; vm_compute; auto.

Example sample_1 {C : Category} :
  ∀ (x y z w : C) (f : z ~> w) (g : y ~> z) (h : x ~> y),
    f ∘ (g ∘ h) ≈ (f ∘ g) ∘ h.
Proof. Fail intros; categorical. Abort.
