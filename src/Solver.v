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

Inductive ArrowList : Set :=
  | Invalid
  | IdentityOnly : N -> ArrowList
  | ArrowChain   : Arrow -> list Arrow -> ArrowList.

Fixpoint ArrowList_length (xs : ArrowList) : nat :=
  match xs with
  | Invalid => 0
  | IdentityOnly _ => 1
  | ArrowChain _ xs => 1 + length xs
  end.

Definition ArrowList_append (xs ys : ArrowList) : ArrowList :=
  match xs, ys with
  | Invalid, _ => Invalid
  | _, Invalid => Invalid
  | IdentityOnly f, IdentityOnly r =>
    if f =? r then IdentityOnly f else Invalid
  | IdentityOnly f, ArrowChain (Arr x y g) xs =>
    if f =? y then ArrowChain (Arr x y g) xs else Invalid
  | ArrowChain f xs, IdentityOnly g =>
    match last xs f with
    | Arr x y m =>
      if g =? x
      then ArrowChain f xs
      else Invalid
    end
  | ArrowChain f xs, ArrowChain (Arr z w g) ys =>
    match last xs f with
    | Arr x y m =>
      if w =? x
      then ArrowChain f (xs ++ Arr z w g :: ys)
      else Invalid
    end
  end.

Lemma ArrowList_append_chains a a0 l l0 :
  match last l a, a0 with
  | Arr x y f, Arr z w g => w = x
  end ->
  ArrowList_append (ArrowChain a l) (ArrowChain a0 l0) =
  ArrowChain a (l ++ a0 :: l0).
Proof.
  generalize dependent a0.
  generalize dependent l0.
  induction l using rev_ind; simpl; intros.
    destruct a0, a.
    subst.
    rewrite N.eqb_refl.
    reflexivity.
  simpl in H.
  destruct a0, a.
  destruct (last (l ++ [x]) (Arr n2 n3 n4)); subst.
  rewrite N.eqb_refl.
  reflexivity.
Qed.

Fixpoint normalize (p : Term) : ArrowList :=
  match p with
  | Identity x  => IdentityOnly x
  | Morph x y f => ArrowChain (Arr x y f) []
  | Compose f g => ArrowList_append (normalize f) (normalize g)
  end.

(* The list [f; g; h] maps to [f ∘ g ∘ h]. *)
Fixpoint normalize_denote dom cod (xs : ArrowList) {struct xs} :
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
  | ArrowChain f fs =>
    let fix go cod' g gs :=
        match g, gs with
        | Arr x y h, nil =>
          match arrs h x y with
          | Some p =>
            match N.eq_dec x dom, N.eq_dec y cod' with
            | left Hdom, left Hcod =>
              Some (eq_rect y (fun z => objs dom ~> objs z)
                            (eq_rect x (fun z => objs z ~> objs y)
                                     p dom Hdom) cod' Hcod)
            | _, _ => None
            end
          | _ => None
          end
        | Arr x y h, Arr z w j :: js =>
          match arrs h x y with
          | Some p =>
            match N.eq_dec y cod' with
            | left Hcod =>
              match go x (Arr z w j) js with
              | Some q =>
                Some (eq_rect y (fun y => objs dom ~> objs y)
                              (p ∘ q) cod' Hcod)
              | _ => None
              end
            | _ => None
            end
          | _ => None
          end
        end
    in go cod f fs
  end.

Theorem normalize_compose : ∀ p1 p2 dom cod f,
  normalize_denote dom cod (normalize (Compose p1 p2)) = Some f ->
  ∃ g h, f ≈ g ∘ h ∧
    normalize_denote (TermCod p2) cod (normalize p1) = Some g ∧
    normalize_denote dom (TermCod p2) (normalize p2) = Some h.
Proof.
Admitted.

Theorem normalize_sound : ∀ p dom cod f,
  normalize_denote dom cod (normalize p) = Some f ->
  ∃ f', f ≈ f' ∧ denote dom cod p = Some f'.
Proof.
  induction p; intros.
  - simpl in *; exists f; subst.
    split; [reflexivity|].
    destruct (N.eq_dec n dom); subst;
    destruct (N.eq_dec dom cod); subst; auto.
  - simpl in *; exists f; subst.
    split; [reflexivity|].
    destruct (N.eq_dec n dom); subst;
    destruct (N.eq_dec n0 cod); subst; auto.
    + destruct (arrs n1 dom n0); auto.
    + destruct (arrs n1 n cod); auto.
    + destruct (arrs n1 n n0); auto.
  - specialize (IHp1 (TermCod p2) cod).
    specialize (IHp2 dom (TermCod p2)).
    apply normalize_compose in H.
    destruct H, s, p, p.
    destruct (IHp1 _ e0), (IHp2 _ e1); clear IHp1 IHp2.
    exists (x1 ∘ x2).
    intuition.
    simpl.
      rewrite a, a0 in e.
      apply e.
    simpl.
    rewrite b0, b.
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

Print Assumptions sample_1.
