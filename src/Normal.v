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
Qed.

Theorem unarrows_arrows d c (t : Term tys d c) :
  termD (unarrows (arrows t)) ≈ termD t.
Proof.
  induction t; simpl; cat.
  rewrite unarrows_app; simpl.
  now rewrite IHt1, IHt2.
Qed.

End Normal.
