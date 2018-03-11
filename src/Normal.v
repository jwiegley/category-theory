Set Warnings "-notation-overridden".

Require Export Solver.Denote.

Unset Equations WithK.

Generalizable All Variables.

Section Normal.

Context `{Env}.

Import ListNotations.
Import EqNotations.

Fixpoint arrowsD_work dom (fs : list arr_idx) :
  option (∃ cod, objs dom ~> objs cod) :=
  match fs with
  | nil => Some (dom; @id _ (objs dom))
  | a :: fs =>
    match arrs a with
    | Some (x; (y; f)) =>
      match fs with
      | nil =>
        match Eq_eq_dec x dom with
        | Specif.left edom =>
          Some (y; rew [fun x => objs x ~> objs y] edom in f)
        | _ => None
        end
      | _ =>
        match arrowsD_work dom fs with
        | Some (mid; g) =>
          match Eq_eq_dec mid x with
          | Specif.left emid =>
            (* jww (2017-08-06): This associates the wrong way, which doesn't
               technically matter, but does make the normalized results look
               funny. At some point, the correct orientation should be
               done. *)
            Some (y; f ∘ rew [fun y => objs dom ~> objs y] emid in g)
          | _ => None
          end
        | _ => None
        end
      end
    | _ => None
    end
  end.

Definition arrowsD dom cod (fs : list arr_idx) :
  option (objs dom ~> objs cod) :=
  match arrowsD_work dom fs with
  | Some (y; f) =>
    match Eq_eq_dec y cod with
    | Specif.left ecod => Some (rew [fun y => objs dom ~> objs y] ecod in f)
    | _ => None
    end
  | _ => None
  end.

(** Template for using this:

  pattern f, dom, cod, f'.
  apply arrowsD_rect. *)

Lemma arrowsD_rect
      (P : ∀ (f : list arr_idx) dom cod (f' : objs dom ~> objs cod), Type) :
     Proper (eq ==>
             forall_relation (fun dom =>
             forall_relation (fun cod =>
               @equiv _ (@homset cat (objs dom) (objs cod))
                 ==> arrow)%signature)) P
  -> (∀ dom (H : arrowsD dom dom [] = Some id), P [] dom dom id)
  -> (∀ f mid cod f', arrs f = Some (mid; (cod; f'))
        -> ∀ g dom g' (H : arrowsD dom mid g = Some g'),
           P g dom mid g'
        -> ∀ fg' (Hfg : arrowsD dom cod (f :: g) = Some fg'),
           P (f :: g) dom cod fg')
  -> ∀ f dom cod f' (H : arrowsD dom cod f = Some f'),
       P f dom cod f'.
Proof.
  unfold arrowsD.
  induction f; simpl; intros.
  - destruct (Pos.eq_dec dom cod); [|discriminate]; subst; auto.
    inversion H0; subst.
    apply X0; simpl.
    now rewrite Pos_eq_dec_refl.
  - destruct (arrs a) eqn:?; [|discriminate].
    destruct s, s.
    destruct f.
      destruct (Pos.eq_dec x dom); [|discriminate].
      destruct (Pos.eq_dec x0 cod); [|discriminate].
      inversion H0; subst.
      simpl.
      specialize (X1 a dom cod h Heqo [] dom id).
      simpl in X1.
      rewrite Pos_eq_dec_refl in X1.
      simpl in X0.
      specialize (X0 dom).
      rewrite Pos_eq_dec_refl in X0.
      specialize (X1 eq_refl (X0 eq_refl)).
      rewrite Heqo in X1.
      rewrite Pos_eq_dec_refl in X1.
      rewrite Pos_eq_dec_refl in X1.
      simpl in X1.
      eapply X; eauto; cat.
    destruct (arrowsD_work dom (a0 :: f)) eqn:?; [|discriminate].
    destruct s.
    destruct (Pos.eq_dec x1 x); [|discriminate].
    destruct (Pos.eq_dec x0 cod); [|discriminate].
    subst.
    specialize (IHf dom x h0).
    rewrite Heqo0, Eq_eq_dec_refl in IHf.
    specialize (IHf eq_refl).
    specialize (X1 a x cod h Heqo (a0 :: f) dom h0).
    rewrite Heqo0, Eq_eq_dec_refl in X1.
    specialize (X1 eq_refl IHf).
    inversion H0; subst.
    apply X1; clear X1 X0 IHf.
    simpl in *.
    rewrite Heqo; clear Heqo.
    destruct (arrs a0) eqn:?; [|discriminate].
    destruct s, s.
    destruct f.
      destruct (Pos.eq_dec x0 dom); [|discriminate].
      subst.
      inversion Heqo0; subst; clear Heqo0.
      rewrite Pos_eq_dec_refl.
      eapply Eqdep_dec.inj_pair2_eq_dec in H3; [ | apply Eq_eq_dec ].
      subst.
      rewrite Pos_eq_dec_refl.
      reflexivity.
    destruct (arrowsD_work dom (a1 :: f)); [|discriminate].
    destruct s.
    destruct (Pos.eq_dec x2 x0); [|discriminate].
    subst.
    inversion Heqo0; subst; clear Heqo0.
    rewrite Pos_eq_dec_refl.
    eapply Eqdep_dec.inj_pair2_eq_dec in H3; [ | apply Eq_eq_dec ].
    subst.
    rewrite Pos_eq_dec_refl.
    reflexivity.
Defined.

Fixpoint exprAD (e : Expr arr_idx) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv x y f g => arrowsD x y (arrows f) ≈ arrowsD x y (arrows g)
  | And p q       => exprAD p ∧ exprAD q
  | Or p q        => exprAD p + exprAD q
  | Impl p q      => exprAD p -> exprAD q
  end.

End Normal.
