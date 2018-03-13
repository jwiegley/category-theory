Set Warnings "-notation-overridden".

Require Export Equations.Equations.
Require Export Equations.EqDec.
Unset Equations WithK.

Require Export Solver.Denote.

Generalizable All Variables.

Section Normal.

Context `{Env}.

Import VectorNotations.

Inductive Arrows {a} (tys : Vector.t (obj_idx * obj_idx) a) :
  obj_idx -> obj_idx -> Type :=
  | Nil : ∀ dom, Arrows tys dom dom
  | Arr dom mid cod (f : arr_idx a) :
      mid = fst (tys[@f]) -> cod = snd (tys[@f]) ->
      (* We can't use the results of function calls directly as constructor
         arguments, because it breaks dependent elimination. *)
      Arrows tys dom mid -> Arrows tys dom cod.

Arguments Nil {a tys dom}.
Arguments Arr {a tys dom mid cod} _ _.

Import EqNotations.

Instance positive_EqDec : EqDec.EqDec positive := {
  eq_dec := Eq_eq_dec
}.

Lemma Arrows_eq_dec {d c} (f g : Arrows tys d c) : {f = g} + {f ≠ g}.
Proof.
  induction f; dependent elimination g; auto;
  try (right; intro; discriminate).
  destruct (Fin_eq_dec f1 f); subst.
    destruct (IHf y); subst.
      left; f_equal.
      now dependent elimination e.
    right.
    intro.
    apply n.
    inv H0.
    apply Eqdep_dec.inj_pair2_eq_dec in H2; [|apply Pos.eq_dec].
    now apply Eqdep_dec.inj_pair2_eq_dec in H2; [|apply Pos.eq_dec].
  right.
  intro.
  apply n.
  now inv H0.
Defined.

Program Fixpoint Arrows_app {d m c} (f : Arrows tys m c) (g : Arrows tys d m) :
  Arrows tys d c :=
  match f with
  | Nil => g
  | Arr x _ _ xs => Arr x _ _ (Arrows_app xs g)
  end.

Program Fixpoint arrows `(t : Term tys d c) : Arrows tys d c :=
  match t with
  | Ident    => Nil
  | Morph a  => Arr a _ _ Nil
  | Comp f g => Arrows_app (arrows f) (arrows g)
  end.

Program Fixpoint unarrows `(t : Arrows tys d c) : Term tys d c :=
  match t with
  | Nil => Ident
  | Arr x _ _ xs => Comp (Morph x) (unarrows xs)
  end.

Theorem arrows_unarrows d c (xs : Arrows tys d c) : arrows (unarrows xs) = xs.
Proof.
  induction xs; simpl; auto.
  unfold unarrows_obligation_1.
  unfold unarrows_obligation_2.
  simpl_eq.
  unfold EqdepFacts.internal_eq_rew_r_dep.
  unfold EqdepFacts.internal_eq_sym_involutive.
  dependent elimination e0; simpl.
  dependent elimination e; simpl.
  rewrite IHxs.
  reflexivity.
Qed.

Theorem unarrows_app d m c (t1 : Arrows tys m c) (t2 : Arrows tys d m) :
  termD (unarrows (Arrows_app t1 t2)) ≈ termD (Comp (unarrows t1) (unarrows t2)).
Proof.
  induction t1; simpl; cat.
  unfold unarrows_obligation_2.
  simpl_eq.
  unfold EqdepFacts.internal_eq_rew_r_dep.
  unfold EqdepFacts.internal_eq_sym_involutive.
  unfold Arrows_app_obligation_3.
  unfold EqdepFacts.internal_eq_rew_r_dep.
  unfold EqdepFacts.internal_eq_sym_involutive.
  dependent elimination e0; simpl.
  simpl_eq.
  dependent elimination e; simpl.
  comp_left.
  apply IHt1.
Defined.

Theorem unarrows_arrows d c (t : Term tys d c) :
  termD (unarrows (arrows t)) ≈ termD t.
Proof.
  induction t; simpl; cat.
  rewrite unarrows_app; simpl.
  now rewrite IHt1, IHt2.
Defined.

Fixpoint exprAD (e : Expr) : Type :=
  match e with
  | Top           => True
  | Bottom        => False
  | Equiv _ _ f g => termD (unarrows (arrows f)) ≈ termD (unarrows (arrows g))
  | And p q       => exprD p ∧ exprD q
  | Or p q        => exprD p + exprD q
  | Impl p q      => exprD p -> exprD q
  end.

Theorem exprAD_sound (e : Expr) : exprAD e -> exprD e.
Proof.
  induction e; intuition; simpl in *.
  now rewrite !unarrows_arrows in X.
Defined.

Notation "x ::: xs" := (Arr x _ _ xs) (at level 62, right associativity).

Equations Arrows_find
          {j k} (xs : Arrows tys j k)
          {i l} (ys : Arrows tys i l) : option (Arrows tys k l * Arrows tys i j) :=
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

Lemma termD_unarrows_cons {i j k}
      (f : arr_idx (vec_size tys))
      (H1 : j = fst tys[@f])
      (H2 : k = snd tys[@f])
      (fs : Arrows tys i j) :
  termD (unarrows (@Arr _ tys i j k f H1 H2 fs))
    ≈ (rew <- [fun x => objs x ~> _] H1 in
       rew <- [fun x => _ ~> objs x] H2 in helper (ith arrs f))
        ∘ termD (unarrows fs).
Proof.
  simpl_eq.
  unfold unarrows_obligation_2.
  unfold EqdepFacts.internal_eq_rew_r_dep;
  unfold EqdepFacts.internal_eq_sym_involutive;
  dependent elimination H2; simpl;
  dependent elimination H1; simpl;
  reflexivity.
Defined.

Lemma termD_unarrows_cons2 {i}
      (f : arr_idx (vec_size tys))
      (H1 : fst tys[@f] = fst tys[@f])
      (H2 : snd tys[@f] = snd tys[@f])
      (fs : Arrows tys i (fst tys[@f])) :
  helper (ith arrs f) ∘ termD (unarrows fs)
    ≈ termD (unarrows (@Arr _ tys i (fst tys[@f]) (snd tys[@f]) f H1 H2 fs)).
Proof.
  simpl.
  simpl_eq.
  unfold unarrows_obligation_2.
  unfold EqdepFacts.internal_eq_rew_r_dep;
  unfold EqdepFacts.internal_eq_sym_involutive;
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
  unfold Arrows_app_obligation_4;
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
  rewrite termD_unarrows_cons2;
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

End Normal.
