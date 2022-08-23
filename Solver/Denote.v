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

Program Instance Opt : Category := {|
  obj     := cat;
  hom     := fun A B => option (A ~> B);
  homset  := fun _ _ => {| equiv := fun f g =>
    match f, g with
    | Some f', Some g' => f' ≈ g'
    | None, None => True
    | _, _ => False
    end
  |};
  id      := λ _, Some id;
  compose := fun x y z f g =>
    match f, g with
    | Some f', Some g' => Some (f' ∘ g')
    | _, _ => None
    end
|}.
Next Obligation.
  split; intros;
  destruct H3; discriminate.
Qed.
Next Obligation.
  split; intros;
  destruct H3; discriminate.
Qed.
Next Obligation.
  equivalence.
  - now destruct x.
  - destruct x, y; try tauto; auto.
    now symmetry.
  - destruct x, y, z; try tauto; auto.
    now rewrite X, X0.
Qed.
Next Obligation.
  proper.
  destruct x0, x1, y0, y1; auto.
  now rewrite X, X0.
Qed.
Next Obligation.
  destruct f; cat.
Qed.
Next Obligation.
  destruct f; cat.
Qed.
Next Obligation.
  destruct f, g, h; auto; cat.
Qed.
Next Obligation.
  destruct f, g, h; auto; cat.
Qed.

Theorem stermD_SIdent {x} :
  stermD x x SIdent ≈ id.
Proof.
  unfold stermD; simpl.
  rewrite EqDec.peq_dec_refl.
  reflexivity.
Qed.

Theorem stermD_SIdent_None {d c} :
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
  match stermD d c (SComp f g) with
  | Some fg => ∃! m, stermD m c f ∘ stermD d m g = Some fg
  | None    => ∀  m, stermD m c f ∘ stermD d m g = None
  end.
Proof.
  unfold stermD; simpl.
  destruct (stermD_work d g) eqn:Heqg.
  - destruct s.
    intros.
    destruct (stermD_work x f) eqn:Heqf.
    + destruct s.
      destruct (eq_dec _ c); subst; simpl; auto.
      * exists x.
        ** rewrite Heqf.
           rewrite !EqDec.peq_dec_refl; simpl; auto.
        ** intros.
           destruct (stermD_work v f) eqn:Heqf'.
           *** destruct s.
               destruct (eq_dec _ c); subst; simpl; auto.
               **** destruct (eq_dec _ v); subst; simpl; auto; discriminate.
               **** discriminate.
           *** discriminate.
      * intros.
        destruct (stermD_work m f) eqn:Heqf'.
        ** destruct s.
           destruct (eq_dec _ c); subst; simpl; auto.
           *** destruct (eq_dec _ m); subst; simpl; auto.
               rewrite Heqf in Heqf'.
               inv Heqf'.
               contradiction.
        ** auto.
    + intros.
      destruct (stermD_work m f) eqn:Heqf'.
      ** destruct s.
         destruct (eq_dec _ c); subst; simpl; auto.
         *** destruct (eq_dec _ m); subst; simpl; auto.
             rewrite Heqf in Heqf'.
             discriminate.
      ** auto.
  - intros.
    destruct (stermD_work m f) eqn:Heqf'.
    + destruct s.
      destruct (eq_dec _ c); subst; simpl; auto.
    + reflexivity.
Qed.

Theorem stermD_SComp_Some {d c} f g fg :
  stermD d c (SComp f g) = Some fg →
  ∃! m f' g',
     stermD m c f ≈ Some f' ∧
     stermD d m g ≈ Some g' ∧
     fg ≈ f' ∘ g'.
Proof.
  unfold stermD; simpl.
  destruct (stermD_work d g) eqn:Heqg.
  - destruct s.
    intros.
    exists x.
    + revert H0.
      destruct (stermD_work x f) eqn:Heqf; [|discriminate].
      destruct s.
      destruct (eq_dec _ c); subst; simpl; auto; [|discriminate].
      rewrite !EqDec.peq_dec_refl; simpl; auto.
      intros.
      inv H0.
      exists h0.
      * exists h; cat.
        intros.
        intuition.
      * intros.
        destruct X.
        intuition.
    + intros.
      destruct X, unique_property.
      destruct (stermD_work v f) eqn:Heqf; [|tauto].
      destruct s.
      destruct (eq_dec _ c); subst; [|tauto].
      destruct (eq_dec x v); subst; [|tauto].
      rewrite Heqf in H0.
      reflexivity.
  - discriminate.
Qed.

Lemma stermD_SIdent_left dom cod (e : STerm) :
  stermD dom cod (SComp SIdent e) ≈ stermD dom cod e.
Proof.
  unfold stermD.
  induction e; simpl.
  destruct (eq_dec dom cod); subst; simpl; auto.
  - cat.
  - destruct (Pos_to_fin a); auto.
    destruct (eq_dec (fst tys[@t]) dom); subst; auto.
    destruct (eq_dec _ cod); subst; simpl; cat.
  - simpl in *.
    destruct (stermD_work dom e2) eqn:Heqe2; auto.
    destruct s.
    destruct (stermD_work x e1) eqn:Heqe1; auto.
    destruct s.
    destruct (eq_dec x0 cod); subst; auto.
    simpl; cat.
Qed.

Lemma stermD_SIdent_right dom cod (e : STerm) :
  stermD dom cod (SComp e SIdent) ≈ stermD dom cod e.
Proof.
  unfold stermD.
  induction e; simpl.
  destruct (eq_dec dom cod); subst; simpl; auto.
  - cat.
  - destruct (Pos_to_fin a); auto.
    destruct (eq_dec (fst tys[@t]) dom); subst; auto.
    destruct (eq_dec _ cod); subst; simpl; cat.
  - simpl in *.
    destruct (stermD_work dom e2) eqn:Heqe2; auto.
    destruct s.
    destruct (stermD_work x e1) eqn:Heqe1; auto.
    destruct s.
    destruct (eq_dec x0 cod); subst; auto.
    simpl; cat.
Qed.

Lemma stermD_SComp_respects_left dom cod (f g g' : STerm) :
  (∀ mid, stermD dom mid g ≈ stermD dom mid g') →
  stermD dom cod (SComp f g) ≈ stermD dom cod (SComp f g').
Proof.
  unfold stermD; simpl; intros.
  destruct (stermD_work dom g) eqn:Heqg.
  - destruct s.
    specialize (X x).
    rewrite EqDec.peq_dec_refl in X.
    destruct (stermD_work x f) eqn:Heqf.
    + destruct s.
      destruct (eq_dec _ cod); subst; simpl; auto.
      * destruct (stermD_work dom g') eqn:Heqg'; [|contradiction].
        destruct s.
        destruct (stermD_work x0 f) eqn:Heqf'.
        ** destruct s.
           destruct (eq_dec _ cod); subst; simpl; auto.
           *** destruct (eq_dec x0 x); subst; simpl in X; [|contradiction].
               rewrite Heqf in Heqf'.
               inv Heqf'.
               apply inj_pair2 in H1; subst.
               now rewrite X.
           *** destruct (eq_dec x0 x); subst; simpl in X; [|contradiction].
               rewrite Heqf in Heqf'.
               inv Heqf'.
               contradiction.
        ** destruct (eq_dec x0 x); subst; simpl in X; [|contradiction].
           rewrite Heqf in Heqf'.
           discriminate.
      * destruct (stermD_work dom g') eqn:Heqg'; [|contradiction].
        destruct s.
        destruct (stermD_work x1 f) eqn:Heqf'.
        ** destruct s.
           destruct (eq_dec _ cod); subst; simpl; auto.
           *** destruct (eq_dec x1 x); subst; simpl in X; [|contradiction].
               rewrite Heqf in Heqf'.
               inv Heqf'.
               apply inj_pair2 in H2; subst.
               contradiction.
        ** destruct (eq_dec x1 x); subst; simpl in X; [|contradiction].
           rewrite Heqf in Heqf'.
           discriminate.
    + destruct (stermD_work dom g') eqn:Heqg'; [|contradiction].
      destruct s.
      destruct (stermD_work x0 f) eqn:Heqf'.
      * destruct s.
        destruct (eq_dec _ cod); subst; simpl; auto.
        ** destruct (eq_dec x0 x); subst; simpl in X; [|contradiction].
           rewrite Heqf in Heqf'.
           discriminate.
      * destruct (eq_dec x0 x); subst; simpl in X; auto.
  - destruct (stermD_work dom g') eqn:Heqg'; auto.
    destruct s.
    specialize (X x).
    rewrite EqDec.peq_dec_refl in X.
    destruct (stermD_work x f) eqn:Heqf'; [|contradiction].
    destruct s.
    destruct (eq_dec _ cod); subst; simpl; auto.
Qed.

Lemma stermD_SComp_respects_right dom cod (f f' g : STerm) :
  (∀ mid, stermD mid cod f ≈ stermD mid cod f') →
  stermD dom cod (SComp f g) ≈ stermD dom cod (SComp f' g).
Proof.
  unfold stermD; simpl; intros.
  destruct (stermD_work dom g) eqn:Heqg; auto.
  destruct s.
  specialize (X x).
  destruct (stermD_work x f) eqn:Heqf.
  - destruct s.
    destruct (eq_dec _ cod); subst; simpl; auto.
    + destruct (stermD_work x f') eqn:Heqf'.
      * destruct s.
        destruct (eq_dec _ cod); subst; simpl; auto.
        simpl in X.
        now rewrite X.
      * contradiction.
    + destruct (stermD_work x f') eqn:Heqf'; auto.
      destruct s.
      destruct (eq_dec _ cod); subst; simpl; auto.
  - destruct (stermD_work x f') eqn:Heqf'; auto.
    destruct s.
    destruct (eq_dec _ cod); subst; simpl; auto.
Qed.

Lemma stermD_SComp_respects dom cod (f f' g g' : STerm) :
  (∀ mid, stermD mid cod f ≈ stermD mid cod f') →
  (∀ mid, stermD dom mid g ≈ stermD dom mid g') →
  stermD dom cod (SComp f g) ≈ stermD dom cod (SComp f' g').
Proof.
  intros.
  rewrite stermD_SComp_respects_left; eauto.
  apply stermD_SComp_respects_right; intuition.
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
