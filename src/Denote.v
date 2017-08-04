Set Warnings "-notation-overridden".

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Recdef.

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Solver.Lib.
Require Import Solver.Expr.
Require Import Solver.Normal.

Generalizable All Variables.

Section Denote.

Import EqNotations.

Context {C : Category}.

Variable objs : obj_idx -> C.
Variable arrs : ∀ f : arr_idx, option (∃ x y, objs x ~{C}~> objs y).

Fixpoint termD dom cod (e : Term) : option (objs dom ~{C}~> objs cod) :=
  match e with
  | Identity _ =>
      match Eq_eq_dec cod dom with
      | left edom =>
        Some (rew [fun x => objs x ~{ C }~> objs cod] edom in @id _ (objs cod))
      | right _ => None
      end
  (* jww (2017-08-02): Why does morph need [obj_idx] arguments? *)
  | Morph _ _ a =>
    match arrs a with
    | Some (x'; (y'; f)) =>
      match Eq_eq_dec x' dom, Eq_eq_dec y' cod with
      | left edom, left ecod =>
        Some (rew [fun x => objs x  ~{ C }~> objs cod] edom in
              rew [fun y => objs x' ~{ C }~> objs y] ecod in f)
      | _, _ => None
      end
    | _ => None
    end
  | Compose mid f g =>
    match termD mid cod f, termD dom mid g with
    | Some f, Some g => Some (f ∘ g)
    | _, _ => None
    end
  end.

Fixpoint arrowsD dom cod `(fs : list (Arrow t)) :
  option (objs dom ~{C}~> objs cod) :=
  match fs with
  | nil =>
    match Eq_eq_dec cod dom with
    | left edom =>
      Some (rew [fun x => objs x ~{ C }~> objs cod] edom in @id _ (objs cod))
    | right _ => None
    end
  | cons f nil =>
    match arrs (snd (get_arrow f)) with
    | Some (x'; (y'; f)) =>
      match Eq_eq_dec x' dom, Eq_eq_dec y' cod with
      | left edom, left ecod =>
        Some (rew [fun x => objs x  ~{ C }~> objs cod] edom in
              rew [fun y => objs x' ~{ C }~> objs y] ecod in f)
      | _, _ => None
      end
    | _ => None
    end
  | cons f fs =>
    let '(x, a) := get_arrow f in
    match arrowsD dom x fs with
    | Some g =>
      match arrs a with
      | Some (x'; (y'; f)) =>
        match Eq_eq_dec x' x, Eq_eq_dec y' cod with
        | left edom, left ecod =>
          Some (rew [fun x => objs x  ~{ C }~> objs cod] edom in
                rew [fun y => objs x' ~{ C }~> objs y] ecod in f ∘ g)
        | _, _ => None
        end
      | _ => None
      end
    | _ => None
    end
  end.

(*
Lemma arrowsD_app x y m f1 f2 f g :
  arrowsD m y (arrows f1) = Some f ->
  arrowsD x m (arrows f2) = Some g ->
  arrowsD x y (arrows (Compose m f1 f2)) ≈ Some (f ∘ g).
Proof.
  intros.
  generalize dependent f2.
  generalize dependent f.
  generalize dependent g.
  generalize dependent m.
  generalize dependent y.
  generalize dependent x.
  induction f1; simpl; intros; equalities.
  - inversion_clear H.
    admit.
  - destruct (arrs _); [|discriminate].
    destruct s, s; repeat equalities.
Admitted.

Lemma arrowsD_termD_some x y f r :
  arrowsD x y (arrows f) = Some r -> termD x y f ≈ Some r.
Proof.
  generalize dependent r.
  generalize dependent y.
  generalize dependent x.
  induction f; simpl; intros; repeat equalities; simpl_eq.
  - inversion_clear H; cat.
  - destruct (arrs _); [|discriminate].
    destruct s, s; equalities.
    equalities'; auto.
    equalities'; auto.
    equalities; [|discriminate].
    inversion_clear H.
    reflexivity.
  - rewrite arrowsD_app in H.
    equalities.
    specialize (IHf1 _ _ _ a).
    specialize (IHf2 _ _ _ a0).
    destruct (termD m y f1) eqn:?, (termD x m f2) eqn:?; try tauto.
    red in IHf1.
    red in IHf2.
    rewrite IHf1, IHf2, b0.
    reflexivity.
Qed.

Lemma termD_arrowsD_some x y f r :
  termD x y f = Some r -> arrowsD x y (arrows f) ≈ Some r.
Proof.
  generalize dependent r.
  generalize dependent y.
  generalize dependent x.
  induction f; simpl; intros; repeat equalities; simpl_eq.
  - inversion_clear H; cat.
  - destruct (arrs _); [|discriminate].
    destruct s, s; equalities.
    equalities'; auto.
    equalities'; auto.
    equalities; [|discriminate].
    inversion_clear H.
    reflexivity.
  - destruct (termD m y f1) eqn:?, (termD x m f2) eqn:?; try discriminate.
    specialize (IHf1 _ _ _ Heqo).
    specialize (IHf2 _ _ _ Heqo0).
    inversion_clear H.
    red in IHf1.
    red in IHf2.
    destruct (arrowsD m y (arrows f1)) eqn:?; [|contradiction].
    destruct (arrowsD x m (arrows f2)) eqn:?; [|contradiction].
    destruct (arrowsD x y (map (Left m f1 f2) (arrows f1) ++
                           map (Right m f1 f2) (arrows f2))) eqn:?.
      apply arrowsD_app in Heqo3.
      equalities.
      rewrite <- IHf1, <- IHf2, b0.
      rewrite a in Heqo1.
      rewrite a0 in Heqo2.
      inversion_clear Heqo1.
      inversion_clear Heqo2.
      reflexivity.
    admit.
Admitted.

Lemma termD_arrowsD_none x y f :
  termD x y f = None ↔ arrowsD x y (arrows f) = None.
Proof.
  generalize dependent y.
  generalize dependent x.
  induction f.
  - destruct (arrs _); auto.
  - destruct (arrs _); auto.
  - destruct (termD m y f1) eqn:?.
      destruct (termD x m f2) eqn:?.
        discriminate.
  admit.
Admitted.
*)

Fixpoint exprD (e : Expr) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv x y f g => termD x y f ≈ termD x y g
  (* | Not p         => exprD p -> False *)
  | And p q       => exprD p ∧ exprD q
  | Or p q        => exprD p + exprD q
  | Impl p q      => exprD p -> exprD q
  end.

Fixpoint exprAD (e : Expr) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv x y f g => arrowsD x y (arrows f) ≈ arrowsD x y (arrows g)
  (* | Not p         => exprD p -> False *)
  | And p q       => exprD p ∧ exprD q
  | Or p q        => exprD p + exprD q
  | Impl p q      => exprD p -> exprD q
  end.

Theorem arrowsD_sound {p dom cod f} :
  arrowsD dom cod (arrows p) = Some f ->
  ∃ f', f ≈ f' ∧ termD dom cod p = Some f'.
Proof.
Admitted.

Lemma arrowsD_apply dom cod (f g : Term) :
  arrows_bequiv (arrows f) (arrows g) = true ->
  arrowsD dom cod (arrows f) ||| false = true ->
  arrowsD dom cod (arrows f) = arrowsD dom cod (arrows g) ->
  termD dom cod f ≈ termD dom cod g.
Proof.
  intros.
  destruct (arrowsD dom cod (arrows f)) eqn:?; [|discriminate].
  destruct (arrowsD_sound Heqo), p.
  rewrite e0; clear e0.
  rewrite H1 in Heqo; clear H1.
  destruct (arrowsD_sound Heqo), p.
  rewrite e1; clear e1.
  red.
  rewrite <- e, <- e0.
  reflexivity.

  induction f; simpl in *; repeat equalities.
  - destruct g; simpl in *; repeat equalities.
    + destruct (arrs a); [|contradiction].
      destruct s, s; equalities; contradiction.
    + destruct (arrowsD x x (map (Left m g1 g2) (arrows g1) ++
                             map (Right m g1 g2) (arrows g2))) eqn:?;
      [|contradiction].
      admit.
  - destruct g; simpl in *; repeat equalities.
    + destruct (arrs a); auto.
    + destruct (arrowsD _ _ _) eqn:?; [contradiction|].
        admit.
  - admit.
Admitted.

Lemma exprAD_sound (e : Expr) : exprAD e -> exprD e.
Proof.
  destruct e; auto; intros.
  red in X; red.
  apply arrowsD_sound; auto.
Qed.

End Denote.

(*
Context {C : Category}.
Variable x : C.
Variables f g h : x ~> x.

Definition objs := (fun _ : obj_idx => x).

Eval simpl in @exprD C objs
  (fun i => if Pos.eqb i 1 then Some (1; (1; f)) else
            if Pos.eqb i 2 then Some (1; (1; g)) else Some (1; (1; h)))%positive
  (Equiv 1 1 (@Compose 1 (@Morph 1) (@Compose 1 (@Morph 2) (@Morph 3)))
             (@Compose 1 (@Compose 1 (@Morph 1) (@Morph 2)) (@Morph 3)))%positive.
*)
