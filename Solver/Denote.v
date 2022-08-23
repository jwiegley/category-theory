Set Warnings "-notation-overridden".

Require Import Coq.Vectors.Vector.
Require Import Coq.PArith.PArith.

From Equations Require Import Equations.
Require Import Equations.Type.EqDec.
Set Equations With UIP.

Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.
Require Import Category.Solver.Expr.

Generalizable All Variables.

Section Denote.

Context `{Env}.

Import VectorNotations.

Corollary helper {f} :
  (let '(dom, cod) := tys[@f] in objs[@dom] ~> objs[@cod])
    -> objs[@(fst (tys[@f]))] ~> objs[@(snd (tys[@f]))].
Proof. destruct (tys[@f]); auto. Defined.

Import EqNotations.

Definition Pos_to_fin {n} (p : positive) : option (Fin.t n).
Proof.
  generalize dependent n.
  induction p using Pos.peano_rect; intros.
    destruct n.
      exact None.
    exact (Some Fin.F1).
  destruct n.
    exact None.
  destruct (IHp n).
    exact (Some (Fin.FS t)).
  exact None.
Defined.

Fixpoint stermD_work dom (e : STerm) :
  option (∃ cod, objs[@dom] ~> objs[@cod]) :=
  match e with
  | SIdent => Some (dom; @id _ (objs[@dom]))
  | SMorph a =>
    match Pos_to_fin a with
    | Some f =>
      match eq_dec (fst (tys[@f])) dom with
      | left H =>
        Some (snd (tys[@f]);
              rew [fun x => objs[@x] ~> _] H in helper (ith arrs f))
      | _ => None
      end
    | _ => None
    end
  | SComp f g =>
    match stermD_work dom g with
    | Some (mid; g) =>
      match stermD_work mid f with
      | Some (y; f) => Some (y; f ∘ g)
      | _ => None
      end
    | _ => None
    end
  end.

Definition stermD dom cod (e : STerm) : option (objs[@dom] ~> objs[@cod]) :=
  match stermD_work dom e with
  | Some (y; f) =>
    match eq_dec y cod with
    | left ecod =>
      Some (rew [fun y => objs[@dom] ~> objs[@y]] ecod in f)
    | _ => None
    end
  | _ => None
  end.

Theorem stermD_SIdent {x} :
  stermD x x SIdent ≈ Some id[objs[@x]].
Proof.
  unfold stermD; simpl.
  rewrite EqDec.peq_dec_refl.
  reflexivity.
Qed.

Theorem stermD_not_SIdent {d c} :
  d ≠ c → stermD d c SIdent ≈ None.
Proof.
  unfold stermD; simpl; intros.
  destruct (eq_dec d c); subst; auto.
Qed.

Definition option_comp {a b c : cat}
  (f : option (b ~> c)) (g : option (a ~> b)) : option (a ~> c).
Proof.
  destruct f, g.
    exact (Some (h ∘ h0)).
  all:exact None.
Defined.

#[export] Program Instance option_comp_respects {a b c : cat} :
  Proper (equiv ==> equiv ==> equiv) (@option_comp a b c).
Next Obligation.
  repeat intro.
  destruct x, y, x0, y0; simpl in *; auto.
  now rewrite X, X0.
Qed.

Theorem stermD_SComp {d c} f g :
  ∃ m, stermD d c (SComp f g) ≈ option_comp (stermD m c f) (stermD d m g).
Proof.
  unfold stermD; simpl.
  destruct (stermD_work d g) eqn:Heqg.
  - destruct s.
    destruct (stermD_work x f) eqn:Heqf.
    + destruct s.
      exists x.
      rewrite Heqf.
      rewrite !EqDec.peq_dec_refl; simpl.
      destruct (eq_dec _ c); subst; simpl; auto.
      reflexivity.
    + exists x.
      rewrite Heqf; simpl.
      rewrite !EqDec.peq_dec_refl; simpl; auto.
  - exists d.
    destruct (stermD_work d f) eqn:Heqf.
    + destruct s.
      destruct (eq_dec x c); subst; simpl; auto.
    + simpl; auto.
Qed.

Program Fixpoint sexprD (e : SExpr) : Type :=
  match e with
  | STop           => True
  | SBottom        => False
  | SEquiv x y f g =>
    match Pos_to_fin x, Pos_to_fin y with
    | Some d, Some c =>
      match stermD d c f, stermD d c g with
      | Some f, Some g => f ≈ g
      | _, _ => False
      end
    | _, _ => False
    end
  | SAnd p q       => sexprD p ∧ sexprD q
  | SOr p q        => sexprD p + sexprD q
  | SImpl p q      => sexprD p → sexprD q
  end.

End Denote.
