Set Warnings "-notation-overridden".

Require Export Equations.Equations.
Require Export Equations.EqDec.
Unset Equations WithK.

Require Export Solver.Normal.

Generalizable All Variables.

Section Rewrite.

Context `{Env}.

Import EqNotations.

Notation "x ::: xs" := (Arr x _ _ xs) (at level 62, right associativity).

Equations Arrows_find
          {j k} (xs : Arrows tys j k)
          {i l} (ys : Arrows tys i l) :
  option (Arrows tys k l * Arrows tys i j) :=
  Arrows_find (Nil j) (Nil i) <= Pos.eq_dec j i => {
    | left H =>
      Some (rew [fun x => Arrows tys _ x] H in Nil,
            rew [fun x => Arrows tys x _] H in Nil);
    | _ => None
  };
  Arrows_find (Nil j) (Arr i o l y H1 H2 ys) <= Pos.eq_dec j l => {
    | left H =>
      Some (rew <- [fun x => Arrows tys x _] H in Nil, y ::: ys);
    | _ <= Arrows_find Nil ys => {
      | None => None;
      | Some (pair ys zs) => Some (y ::: ys, zs)
    }
  };
  Arrows_find _ Nil := None;
  Arrows_find (Arr _ m k x _ _ xs) (Arr _ o l y Hy1 Hy2 ys)
    <= (Pos.eq_dec k l, Pos.eq_dec m o) => {
      | pair (left H1) (left H2)
        <= Fin.eq_dec x y => {
          | left _ <= Arrows_find xs ys => {
              | Some (pair bs cs)
                <= Arrows_eq_dec bs
                     (rew [fun a => Arrows tys _ a] H2 in Nil) => {
                  | left _ =>
                    Some (rew [fun a => Arrows tys _ a] H1 in Nil, cs);
                  | _ <= Arrows_find (x ::: xs) ys => {
                    | None => None;
                    | Some (pair ys zs) => Some (y ::: ys, zs)
                  }
                };
              | None <= Arrows_find (x ::: xs) ys => {
                  | None => None;
                  | Some (pair ys zs) => Some (y ::: ys, zs)
                }
            };
          | _ <= Arrows_find (x ::: xs) ys => {
              | None => None;
              | Some (pair ys zs) => Some (Arr y Hy1 Hy2 ys, zs)
            }
        };
      | _  <= Arrows_find (x ::: xs) ys => {
          | None => None;
          | Some (pair ys zs) => Some (y ::: ys, zs)
        }
      }.

Infix "+++" := Arrows_app (at level 62, right associativity).

Import VectorNotations.

Lemma termD_unarrows_cons {i}
      (f : arr_idx (vec_size tys))
      (H1 : fst tys[@f] = fst tys[@f])
      (H2 : snd tys[@f] = snd tys[@f])
      (fs : Arrows tys i (fst tys[@f])) :
  helper (ith arrs f) ∘ termD (unarrows fs)
    ≈ termD (unarrows (@Arr _ tys i (fst tys[@f]) (snd tys[@f]) f H1 H2 fs)).
Proof.
  simpl.
  simpl_eq.
  unfold Normal.unarrows_obligation_2.
  unfold EqdepFacts.internal_eq_rew_r_dep;
  unfold EqdepFacts.internal_eq_sym_involutive.
  dependent elimination H2; simpl;
  dependent elimination H1; simpl;
  reflexivity.
Defined.

Lemma Arrows_app_comm_cons {i j k l}
      (x : arr_idx (vec_size tys))
      (H1 : k = fst tys[@x])
      (H2 : l = snd tys[@x])
      (xs : Arrows tys j k) (ys : Arrows tys i j) :
  @Arr _ tys i k l x H1 H2 (xs +++ ys) = (@Arr _ tys j k l x H1 H2 xs) +++ ys.
Proof.
  destruct xs, ys; simpl;
  unfold Normal.Arrows_app_obligation_4;
  simpl_eq;
  unfold EqdepFacts.internal_eq_rew_r_dep;
  unfold EqdepFacts.internal_eq_sym_involutive;
  dependent elimination H2; simpl;
  dependent elimination H1; simpl;
  reflexivity.
Defined.

Ltac cleanup f1 g f0 H0 IHf :=
  destruct (Arrows_find (f1 ::: g) f0) as [[? ?]|] eqn:?;
    [|discriminate];
  inv H0;
  rewrite Arrows_app_comm_cons;
  rewrite IHf; eauto;
  rewrite <- !Arrows_app_comm_cons;
  rewrite termD_unarrows_cons;
  repeat f_equiv;
  apply eq_proofs_unicity.

Lemma Arrows_find_app
      {j k} (g : Arrows tys j k)
      {i l} (f : Arrows tys i l) {pre post} :
  Arrows_find g f = Some (pre, post)
    -> termD (unarrows f) ≈ termD (unarrows (pre +++ g +++ post)).
Proof.
  intros.
  generalize dependent k.
  generalize dependent j.
  induction f; intros; simpl in *.
  - destruct g.
      rewrite Arrows_find_equation_1 in H0.
      unfold Arrows_find_obligation_1 in H0.
      destruct (Pos.eq_dec dom0 dom); [|discriminate].
      inversion H0; now subst.
    discriminate.
  - destruct g.
      rewrite Arrows_find_equation_2 in H0.
      unfold Arrows_find_obligation_7 in H0.
      destruct (Pos.eq_dec dom0 cod); subst.
        inversion H0; now subst.
      unfold Arrows_find_obligation_6 in H0.
      destruct (Arrows_find _ _) eqn:?; [|discriminate].
      destruct p.
      inversion H0; subst.
      simpl_eq; simpl.
      comp_left.
      rewrite IHf; eauto.
      reflexivity.
    rewrite Arrows_find_equation_4 in H0.
    unfold Arrows_find_obligation_34 in H0.
    destruct (Pos.eq_dec cod0 cod); subst. {
      simpl.
      destruct (Pos.eq_dec _ _); subst. {
        unfold Arrows_find_obligation_25 in H0.
        destruct (Fin.eq_dec _ _). {
          unfold Arrows_find_obligation_23 in H0.
          destruct (Arrows_find _ _) eqn:?. {
            destruct p.
            unfold Arrows_find_obligation_19 in H0.
            destruct (Arrows_eq_dec _ _). {
              rewrite Arrows_app_comm_cons.
              inv H0.
              rewrite IHf; eauto.
              simpl; simpl_eq.
              dependent elimination e; simpl.
              dependent elimination e3; simpl.
              reflexivity.
            }
            unfold Arrows_find_obligation_13 in H0.
            now cleanup f1 g f0 H0 IHf.
          }
          unfold Arrows_find_obligation_19 in H0.
          unfold Arrows_find_obligation_18 in H0.
          now cleanup f1 g f0 H0 IHf.
        }
        unfold Arrows_find_obligation_23 in H0.
        unfold Arrows_find_obligation_22 in H0.
        now cleanup f1 g f0 H0 IHf.
      }
      unfold Arrows_find_obligation_30 in H0.
      now cleanup f1 g f0 H0 IHf.
    }
    unfold Arrows_find_obligation_33 in H0.
    destruct (Arrows_find (f1 ::: g) f0) eqn:?; [|discriminate].
    destruct p.
    inv H0; simpl.
    now rewrite Arrows_app_comm_cons, IHf; eauto.
Defined.

Corollary termD_Comp `{Env} d m c (x : Term tys m c) (y : Term tys d m) :
  termD (Comp x y) ≈ termD x ∘ termD y.
Proof. reflexivity. Defined.

Lemma Term_find_app
      {j k} (g h : Term tys j k)
      {i l} (f : Term tys i l) {pre post} :
  Arrows_find (arrows g) (arrows f) = Some (pre, post)
    -> termD g ≈ termD h
    -> termD f ≈ termD (unarrows ((pre +++ arrows h) +++ post)).
Proof.
  intros.
  rewrite <- unarrows_arrows.
  erewrite Arrows_find_app; eauto.
  rewrite !unarrows_app.
  rewrite !termD_Comp.
  rewrite !unarrows_app.
  rewrite !termD_Comp.
  rewrite !unarrows_arrows.
  rewrite comp_assoc.
  now rewrite X.
Defined.

End Rewrite.
