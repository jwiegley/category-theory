Require Import
  Coq.FSets.FMapFacts
  Coq.Structures.DecidableTypeEx.

Module FMapExt (E : DecidableType) (M : WSfun E).

Module P := WProperties_fun E M.
Module F := P.F.

Ltac normalize :=
  repeat match goal with
  | [ H : M.find ?ADDR ?Z = Some ?CBLK |- _ ] => apply F.find_mapsto_iff in H
  | [ |-  M.find ?ADDR ?Z = Some ?CBLK ]      => apply F.find_mapsto_iff
  end.

Ltac simplify_maps :=
  normalize;
  match goal with
  | [ H : M.MapsTo (elt:=?T) ?A ?B (M.add ?K ?E ?M) |- _ ] =>
    apply F.add_mapsto_iff in H;
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    destruct H as [[H1 H2]|[H3 H4]]; [subst|]
  | [ H : M.MapsTo (elt:=?T) ?A ?B (M.remove ?KE ?M) |- _ ] =>
    apply F.remove_mapsto_iff in H;
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    destruct H as [H1 H2]
  | [ H : M.MapsTo (elt:=?T) ?A ?B (M.map ?F ?M) |- _ ] =>
    apply F.map_mapsto_iff in H;
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let cblk := fresh "cblk" in
    destruct H as [cblk [H1 H2]]
  | [ H : M.MapsTo (elt:=?T) ?A ?B (P.filter ?F ?M) |- _ ] =>
    apply P.filter_iff in H;
    [let H1 := fresh "H1" in
     let H2 := fresh "H2" in
     destruct H as [H1 H2]|]
  | [ H : M.MapsTo (elt:=?T) ?A ?B (P.update ?M1 ?M2) |- _ ] =>
    apply P.update_mapsto_iff in H;
    [let H1 := fresh "H1" in
     let H2 := fresh "H2" in
     destruct H as [H1|[H1 H2]]]
  | [ H : M.MapsTo (elt:=?T) ?A ?B (M.mapi ?F ?M) |- _ ] =>
    apply F.find_mapsto_iff in H;
    rewrite F.mapi_o, <- F.map_o in H;
    apply F.find_mapsto_iff in H
  | [ H : M.MapsTo (elt:=?T) ?A ?B (M.empty ?U) |- _ ] =>
    apply F.empty_mapsto_iff in H; contradiction
  | [ H1 : M.MapsTo (elt:=?T) ?A ?B ?M,
      H2 : M.Empty (elt:=?T) ?M |- _ ] =>
    apply F.find_mapsto_iff in H1;
    apply P.elements_Empty in H2;
    rewrite F.elements_o in H1;
    rewrite H2 in H1;
    inversion H1

  | [ |- M.MapsTo (elt:=?T) ?A ?B (M.add ?K ?E ?M) ] =>
    apply F.add_mapsto_iff
  | [ |- M.MapsTo (elt:=?T) ?A ?B (M.remove ?KE ?M) ] =>
    apply F.remove_mapsto_iff
  | [ |- M.MapsTo (elt:=?T) ?A ?B (M.map ?F ?M) ] =>
    apply F.map_mapsto_iff
  | [ |- M.MapsTo (elt:=?T) ?A ?B (P.filter ?F ?M) ] =>
    apply P.filter_iff
  | [ |- M.MapsTo (elt:=?T) ?A ?B (P.update ?M1 ?M2) ] =>
    apply P.update_mapsto_iff
  | [ |- M.MapsTo (elt:=?T) ?A ?B (M.mapi ?F ?M) ] =>
    rewrite F.mapi_o, <- F.map_o;
    apply F.map_mapsto_iff

  | [ |- ~ M.In ?d (M.remove ?d ?r) ] =>
    let H := fresh "H" in
    unfold not; intro H; destruct H; simplify_maps
  end; simpl; auto.

Hint Extern 5 =>
  match goal with
    [ H : M.MapsTo _ _ (M.empty _) |- _ ] =>
      apply F.empty_mapsto_iff in H; contradiction
  end.

Global Program Instance MapsTo_Proper {elt} :
  Proper (E.eq ==> eq ==> M.Equal ==> iff) (@M.MapsTo elt) :=
  (@F.MapsTo_m_Proper elt).

Ltac relational :=
  repeat match goal with
  | [ |- Proper _ _ ] => intros ???
  | [ |- respectful _ _ _ _ ] => intros ???
  | [ |- iff _ _ ] => split; intro
  end; subst; auto.

Global Program Instance find_Proper {elt} :
  Proper (E.eq ==> eq ==> M.Equal ==> iff)
         (fun k e m => @M.find elt k m = Some e).
Obligation 1.
  relational.
    rewrite <- H, <- H1; assumption.
  rewrite H, H1; assumption.
Qed.

Global Program Instance fold_Proper {elt A} : forall f (eqA : relation A),
  Equivalence eqA
    -> Proper (E.eq ==> eq ==> eqA ==> eqA) f
    -> P.transpose_neqkey eqA f
    -> Proper (M.Equal (elt:=elt) ==> eqA ==> eqA) (@M.fold elt A f).
Obligation 1. relational; eapply P.fold_Equal2; eauto. Qed.

Lemma add_equal_iff : forall elt k (e : elt) m1 m2,
  P.Add k e m1 m2 <-> M.Equal (M.add k e m1) m2.
Proof.
  split; intros; intro addr;
  specialize (H addr);
  congruence.
Qed.

Global Program Instance filter_Proper {elt} : forall P,
  Proper (E.eq ==> eq ==> eq) P
    -> Proper (M.Equal (elt:=elt) ==> M.Equal) (@P.filter elt P).
Obligation 1.
  relational.
  unfold P.filter at 1.
  generalize dependent y.
  apply P.fold_rec; intros.
    apply F.Equal_mapsto_iff.
    split; intros.
      simplify_maps.
    simplify_maps.
    rewrite <- H1 in H3.
    apply P.elements_Empty in H0.
    apply F.find_mapsto_iff in H3.
    rewrite F.elements_o in H3.
    rewrite H0 in H3.
    inversion H3.
  specialize (H3 m' (F.Equal_refl _)).
  apply add_equal_iff in H2.
  rewrite <- H2 in H4; clear H2 m'' H0.
  destruct (P k e) eqn:Heqe; rewrite H3; clear H3.
    apply F.Equal_mapsto_iff.
    split; intros.
      simplify_maps.
        rewrite <- H2.
        simplify_maps.
        intuition.
        rewrite <- H4.
        simplify_maps.
      simplify_maps.
      simplify_maps.
      intuition.
      rewrite <- H4.
      simplify_maps.
    simplify_maps.
    rewrite <- H4 in H2.
    repeat simplify_maps.
    right.
    intuition.
    simplify_maps.
  apply F.Equal_mapsto_iff.
  split; intros;
  simplify_maps;
  simplify_maps;
  intuition.
    rewrite <- H4; clear H4.
    apply F.add_neq_mapsto_iff; auto.
    unfold not; intros.
    rewrite <- H0 in H2.
    apply F.not_find_in_iff in H1.
    apply F.find_mapsto_iff in H2.
    congruence.
  rewrite <- H4 in H2; clear H4.
  simplify_maps.
  rewrite H0 in Heqe.
  congruence.
Qed.

Lemma filter_Empty : forall elt (m : M.t elt) P,
  M.Empty (elt:=elt) m -> M.Empty (elt:=elt) (P.filter P m).
Proof.
  intros.
  unfold P.filter.
  revert H.
  apply P.fold_rec; intros.
    apply M.empty_1.
  specialize (H1 k).
  unfold P.Add in H1.
  rewrite F.elements_o in H1.
  apply P.elements_Empty in H3.
  rewrite H3 in H1; simpl in H1.
  rewrite F.add_eq_o in H1; [| apply E.eq_refl].
  discriminate.
Qed.

Lemma filter_empty : forall elt f m,
  Proper (E.eq ==> eq ==> eq) f
    -> M.Empty (elt:=elt) m
    -> M.Equal (P.filter f m) m.
Proof.
  intros.
  apply F.Equal_mapsto_iff; split; intros.
    simplify_maps.
  simplify_maps.
Qed.

Lemma filter_idempotent : forall elt (m : M.t elt) P,
  Proper (E.eq ==> eq ==> eq) P
    -> M.Equal (P.filter P (P.filter P m)) (P.filter P m).
Proof.
  intros.
  unfold P.filter.
  apply P.fold_rec; intros.
    intro k.
    apply P.elements_Empty in H0.
    symmetry; rewrite F.elements_o, H0.
    symmetry; rewrite F.elements_o, P.elements_empty.
    reflexivity.
  pose proof (P.filter_iff H).
  apply H4 in H0; clear H4.
  rewrite (proj2 H0).
  rewrite H3.
  unfold P.Add in H2.
  symmetry.
  exact H2.
Qed.

Lemma filter_add_true : forall elt k (e : elt) m m' P,
  Proper (E.eq ==> eq ==> eq) P
    -> ~ M.In (elt:=elt) k m
    -> M.Equal (P.filter P (M.add k e m)) m'
    -> P k e = true
    -> M.Equal (M.add k e (P.filter P m)) m'.
Proof.
  intros.
  rewrite <- H1; clear H1.
  apply F.Equal_mapsto_iff; split; intros.
    simplify_maps.
      rewrite <- H3.
      simplify_maps; intuition.
      simplify_maps.
    simplify_maps; intuition.
  simplify_maps.
  simplify_maps.
    rewrite H1.
    simplify_maps.
  simplify_maps.
  right; intuition.
  simplify_maps.
Qed.

Lemma filter_add_true_r : forall elt k (e : elt) m m' P,
  Proper (E.eq ==> eq ==> eq) P
    -> ~ M.In (elt:=elt) k m
    -> M.Equal (M.add k e (P.filter P m)) m'
    -> P k e = true
    -> M.Equal (P.filter P (M.add k e m)) m'.
Proof.
  intros.
  rewrite <- H1; clear H1.
  apply F.Equal_mapsto_iff; split; intros.
    simplify_maps.
    simplify_maps.
      simplify_maps.
    simplify_maps.
    right; intuition.
    simplify_maps.
  simplify_maps.
    simplify_maps.
    intuition.
    rewrite <- H3.
    assumption.
  simplify_maps.
  simplify_maps.
  intuition.
Qed.

Lemma in_mapsto_iff : forall elt k (m : M.t elt),
  M.In (elt:=elt) k m <-> exists e, M.MapsTo (elt:=elt) k e m.
Proof.
  split; intros.
    apply F.mem_in_iff in H.
    rewrite F.mem_find_b in H.
    destruct (M.find (elt:=elt) k m) eqn:Heqe.
      exists e.
      apply F.find_mapsto_iff.
      assumption.
    discriminate.
  apply F.mem_in_iff.
  rewrite F.mem_find_b.
  destruct H.
  apply F.find_mapsto_iff in H.
  rewrite H.
  reflexivity.
Qed.

Lemma not_in_mapsto_iff : forall elt k (m : M.t elt),
  ~ M.In (elt:=elt) k m <-> forall e, ~ M.MapsTo (elt:=elt) k e m.
Proof.
  split; intros; unfold not; intros.
    apply H.
    apply in_mapsto_iff.
    exists e; assumption.
  apply (proj1 (in_mapsto_iff _ _ _)) in H0.
  destruct H0.
  apply (H x); assumption.
Qed.

Lemma filter_add_false : forall elt k (e : elt) m m' P,
  Proper (E.eq ==> eq ==> eq) P
    -> ~ M.In (elt:=elt) k m
    -> M.Equal (P.filter P (M.add k e m)) m'
    -> P k e = false
    -> M.Equal (P.filter P m) m'.
Proof.
  intros.
  rewrite <- H1; clear H1.
  apply F.Equal_mapsto_iff; split; intros.
    simplify_maps.
    simplify_maps; intuition.
    simplify_maps.
    right; intuition.
    rewrite <- H1 in H3.
    contradiction H0.
    apply in_mapsto_iff.
    exists e0; assumption.
  simplify_maps.
  simplify_maps.
    rewrite H1 in H2.
    congruence.
  simplify_maps.
Qed.

Lemma filter_add_false_r : forall elt k (e : elt) m m' P,
  Proper (E.eq ==> eq ==> eq) P
    -> ~ M.In (elt:=elt) k m
    -> M.Equal (P.filter P m) m'
    -> P k e = false
    -> M.Equal (P.filter P (M.add k e m)) m'.
Proof.
  intros.
  rewrite <- H1; clear H1.
  apply F.Equal_mapsto_iff; split; intros.
    simplify_maps.
    simplify_maps.
      simplify_maps.
      intuition.
      rewrite H1 in H2.
      congruence.
    simplify_maps.
  simplify_maps.
  simplify_maps.
  intuition.
  simplify_maps.
  right; intuition.
  rewrite <- H1 in H3.
  contradiction H0.
  apply in_mapsto_iff.
  exists e0.
  assumption.
Qed.

Lemma filter_not_in : forall elt k (m : M.t elt) P,
  ~ M.In (elt:=elt) k m -> ~ M.In (elt:=elt) k (P.filter P m).
Proof.
  intros.
  unfold P.filter.
  apply P.fold_rec_nodep; intros.
    unfold not; intros.
    apply F.empty_in_iff in H0.
    contradiction.
  destruct (P k0 e); auto.
  unfold not; intros.
  apply F.add_in_iff in H2; intuition.
  rewrite H3 in *; clear H3.
  apply H.
  apply in_mapsto_iff.
  exists e.
  assumption.
Qed.

Global Instance add_Proper {elt} :
  Proper (E.eq ==> eq ==> M.Equal ==> M.Equal) (M.add (elt:=elt)) :=
  (@F.add_m_Proper elt).

(* Adding to an FMap overwrites the previous entry. *)
Lemma remove_add : forall elt k (e : elt) m,
  M.Equal (M.add k e (M.remove k m)) (M.add k e m).
Proof.
  intros.
  induction m using P.map_induction_bis.
  - rewrite <- H; assumption.
  - apply F.Equal_mapsto_iff; split; intros;
    repeat simplify_maps.
  - apply F.Equal_mapsto_iff; split; intros;
    repeat simplify_maps;
    right; intuition; simplify_maps.
Qed.

Lemma add_associative {elt}
      (k : M.key) (e : elt)
      (k0 : M.key) (e0 : elt)
      (z : M.t elt) :
  (E.eq k k0 -> e = e0)
    -> M.Equal (M.add k e (M.add k0 e0 z)) (M.add k0 e0 (M.add k e z)).
Proof.
  intros H addr.
  rewrite !F.add_o.
  destruct (E.eq_dec k addr);
  destruct (E.eq_dec k0 addr); eauto.
  apply E.eq_sym in e2.
  pose proof (E.eq_trans e1 e2).
  rewrite (H H0).
  reflexivity.
Qed.

Section for_all.

Variable elt : Type.
Variable P : M.key -> elt -> bool.
Variable P_Proper : Proper (E.eq ==> eq ==> eq) P.

Global Program Instance for_all_Proper :
  Proper (M.Equal ==> eq) (@P.for_all elt P).
Obligation 1.
  relational.
  revert H.
  unfold P.for_all.
  revert y.
  apply P.fold_rec; intros.
    rewrite P.fold_Empty; eauto.
    rewrite <- H0; assumption.
  apply add_equal_iff in H1.
  rewrite H3 in H1.
  apply add_equal_iff in H1.
  rewrite P.fold_Add; eauto.
  - destruct (P k e); auto.
    apply H2.
    reflexivity.
  - relational.
    rewrite H4; reflexivity.
  - intros ??????.
    destruct (P k0 e0), (P k' e'); auto.
Qed.

Lemma for_all_empty : P.for_all P (M.empty elt) = true.
Proof.
  intros.
  apply P.for_all_iff; trivial; intros.
  apply F.empty_mapsto_iff in H.
  contradiction.
Qed.

Lemma for_all_add_true : forall (m : M.t elt) k e,
  ~ M.In k m
    -> (P.for_all P (M.add k e m) = true
          <-> P.for_all P m = true /\ P k e = true).
Proof.
  unfold P.for_all.
  remember (fun _ _ _ => _) as f.
  assert (Proper (E.eq ==> eq ==> eq ==> eq) f).
    relational.
    rewrite H; reflexivity.
  assert (P.transpose_neqkey eq f).
    rewrite Heqf; intros ??????.
    destruct (P k e), (P k' e'); auto.
  assert (Proper (E.eq ==> eq ==> eq --> flip eq) f).
    unfold flip; relational.
    rewrite H1; reflexivity.
  assert (P.transpose_neqkey (flip eq) f).
    unfold flip; rewrite Heqf; intros ??????.
    destruct (P k e), (P k' e'); auto.
  split; intros.
    rewrite P.fold_Add with (k:=k) (e:=e) (m1:=m) in H4; eauto.
      rewrite Heqf in *.
      destruct (P k e); firstorder.
    constructor.
  rewrite P.fold_Add with (k:=k) (e:=e) (m1:=m); eauto.
    rewrite Heqf in *.
    destruct (P k e); firstorder.
  constructor.
Qed.

Lemma for_all_remove : forall (m : M.t elt) (k : M.key),
  P.for_all P m = true
    -> P.for_all P (M.remove k m) = true.
Proof.
  intros.
  apply P.for_all_iff; trivial; intros.
  apply F.remove_mapsto_iff in H0.
  eapply P.for_all_iff in H.
  - exact H.
  - exact P_Proper.
  - tauto.
Qed.

Lemma for_all_remove_inv : forall (m : M.t elt) (k : M.key),
  P.for_all P (M.remove k m) = true
    -> ~ M.In k m -> P.for_all P m = true.
Proof.
  intros.
  apply P.for_all_iff; trivial; intros.
  eapply P.for_all_iff in H.
  - exact H.
  - exact P_Proper.
  - simplify_maps.
    split; trivial.
    unfold not; intros.
    rewrite <- H3 in H1.
    contradiction H0.
    apply in_mapsto_iff.
    exists e.
    assumption.
Qed.

Lemma for_all_remove_inv_2 : forall (m : M.t elt) (k : M.key),
  P.for_all P (M.remove k m) = true
    -> forall k' e, M.MapsTo k' e m -> ~ E.eq k' k -> P k' e = true.
Proof.
  intros.
  eapply P.for_all_iff; eauto.
  simplify_maps.
Qed.

Lemma for_all_impl : forall (P' : M.key -> elt -> bool) m,
  P.for_all P m = true
    -> Proper (E.eq ==> eq ==> eq) P'
    -> (forall k e, P k e = true -> P' k e = true)
    -> P.for_all P' m = true.
Proof.
  intros.
  apply P.for_all_iff; trivial; intros.
  eapply P.for_all_iff in H; eauto.
Qed.

End for_all.

Import ListNotations.

Definition take_first {elt} (f : M.key -> elt -> bool) (k : M.key) (e : elt)
           (x0 : option (M.key * elt)) :=
  match x0 with
  | Some _ => x0
  | None => if f k e then Some (k, e) else None
  end.

Definition optionP {A} (P : relation A) : relation (option A) :=
  fun x y => match x, y with
             | Some x', Some y' => P x' y'
             | None, None => True
             | _, _ => False
             end.

Program Instance optionP_Equivalence {A} (P : relation A) :
  Equivalence P -> Equivalence (optionP P).
Obligation 1.
  intro x.
  destruct x; simpl; trivial.
  reflexivity.
Qed.
Obligation 2.
  intros x y Heq.
  destruct x, y; simpl in *; trivial.
  intuition.
Qed.
Obligation 3.
  intros x y z Heq1 Heq2.
  destruct x, y, z; simpl in *; auto;
  firstorder.
Qed.

Definition pairP {A B} (P : relation A) (Q : relation B) : relation (A * B) :=
  fun p p' => match p, p' with
              | (x, y), (x', y') => P x x' /\ Q y y'
              end.

Program Instance pairP_Equivalence {A B} (P : relation A) (Q : relation B) :
  Equivalence P -> Equivalence Q -> Equivalence (pairP P Q).
Obligation 1.
  intro x.
  destruct x; simpl.
  intuition.
Qed.
Obligation 2.
  intros x y Heq.
  destruct x, y; simpl in *.
  intuition.
Qed.
Obligation 3.
  intros x y z Heq1 Heq2.
  destruct x, y, z; simpl in *.
  firstorder.
Qed.

Program Instance take_first_Proper {elt} :
  Proper ((E.eq ==> eq ==> eq)
            ==> E.eq
            ==> eq
            ==> optionP (pairP E.eq eq)
            ==> optionP (pairP E.eq eq)) (take_first (elt:=elt)).
Obligation 1.
  relational.
  destruct x2, y2.
  - destruct p, p0; simpl in *.
    assumption.
  - contradiction.
  - contradiction.
  - unfold take_first.
    rewrite (H _ _ H0 y1 y1 eq_refl).
    destruct (y y0 y1); auto.
    unfold optionP, pairP; auto.
Qed.

Corollary take_first_None
          {elt} (f : M.key -> elt -> bool) (k : M.key) (e : elt) x :
  take_first f k e (Some x) = Some x.
Proof. reflexivity. Qed.

Definition singleton {elt} (k : M.key) (e : elt) : M.t elt :=
  M.add k e (M.empty _).
Arguments singleton {elt} k e /.

Corollary MapsTo_singleton : forall k elt (e : elt),
  M.MapsTo k e (singleton k e).
Proof. unfold singleton; intros; simplify_maps. Qed.

Lemma Oeq_neq_sym : forall x y, ~ E.eq x y -> ~ E.eq y x.
Proof.
  intros.
  unfold not; intros.
  apply E.eq_sym in H0.
  contradiction.
Qed.

Hint Resolve Oeq_neq_sym.

Lemma Proper_Oeq_negb : forall B f,
  Proper (E.eq ==> eq ==> eq) f ->
  Proper (E.eq ==> eq ==> eq) (fun (k : M.key) (e : B) => negb (f k e)).
Proof. intros ?????????; f_equal; subst; rewrite H0; reflexivity. Qed.

Hint Resolve Proper_Oeq_negb.

Ltac apply_for_all :=
  try match goal with
  | [ H1 : is_true (P.for_all ?P ?m),
      H2 : M.MapsTo ?k ?e ?m |- _ ] => unfold is_true in H1
  end;
  match goal with
  | [ H1 : P.for_all ?P ?m = true,
      H2 : M.MapsTo ?k ?e ?m |- _ ] =>
    cut (Proper (eq ==> eq ==> eq) P);
    [ let HP := fresh "HP" in
      intro HP;
      let H := fresh "H" in
      pose proof (proj1 (@P.for_all_iff _ P HP m) H1 k e H2) as H;
      simpl in H | ]
  end.

Definition keep_keys {elt} (P : M.key -> bool) : M.t elt -> M.t elt :=
  P.filter (fun k _ => P k).

Global Program Instance update_Proper {elt} :
  Proper (M.Equal (elt:=elt) ==> M.Equal (elt:=elt) ==> M.Equal)
         (@P.update elt).
Obligation 1.
  relational.
  apply F.Equal_mapsto_iff; split; intros.
    simplify_maps.
      simplify_maps.
        left.
        rewrite <- H0.
        assumption.
      simplify_maps.
      right; intuition.
      rewrite <- H.
      assumption.
    apply H3.
    rewrite H0.
    assumption.
  simplify_maps.
    simplify_maps.
      left.
      rewrite H0.
      assumption.
    simplify_maps.
    right; intuition.
    rewrite H.
    assumption.
  apply H3.
  rewrite <- H0.
  assumption.
Qed.

Lemma update_empty_l : forall elt (m : M.t elt),
  M.Equal (P.update (M.empty _) m) m.
Proof. intros; apply F.Equal_mapsto_iff; split; intros; simplify_maps. Qed.

Lemma update_empty_r : forall elt (m : M.t elt),
  M.Equal (P.update m (M.empty _)) m.
Proof.
  intros.
  apply F.Equal_mapsto_iff; split; intros.
    simplify_maps.
  simplify_maps.
  right; intuition.
  apply F.empty_in_iff in H0.
  assumption.
Qed.

Lemma update_find_l : forall k elt (m1 m2 : M.t elt),
  ~ M.In k m2 -> M.find k (P.update m1 m2) = M.find k m1.
Proof.
  intros.
  unfold P.update.
  apply P.fold_rec_bis; intros; auto.
  destruct (E.eq_dec k0 k).
    rewrite e0 in H0.
    contradiction H.
    exists e.
    assumption.
  rewrite !F.add_neq_o; trivial.
Qed.

Lemma update_find_r : forall k elt (m1 m2 : M.t elt),
  ~ M.In k m1 -> M.find k (P.update m1 m2) = M.find k m2.
Proof.
  intros.
  unfold P.update.
  apply P.fold_rec_bis; intros.
  - rewrite <- H0; assumption.
  - rewrite F.empty_o.
    apply F.not_find_in_iff; assumption.
  - destruct (E.eq_dec k0 k).
      rewrite !F.add_eq_o; trivial.
    rewrite !F.add_neq_o; trivial.
Qed.

Lemma update_add : forall k elt e (m1 m2 : M.t elt),
  M.Equal (P.update m1 (M.add k e m2)) (M.add k e (P.update m1 m2)).
Proof.
  intros.
  apply F.Equal_mapsto_iff; split; intros.
    apply P.update_mapsto_iff in H.
    destruct H.
      simplify_maps.
        simplify_maps.
      simplify_maps.
      right; intuition.
      apply P.update_mapsto_iff.
      left; assumption.
    destruct H.
    simplify_maps.
    destruct (E.eq_dec k k0) eqn:Heqe.
      left; intuition; subst.
      contradiction H0.
      apply F.in_find_iff.
      rewrite F.add_eq_o; trivial.
      unfold not; intros.
      discriminate.
    right; intuition.
    apply P.update_mapsto_iff.
    right; intuition.
    apply H0.
    apply F.in_find_iff.
    rewrite F.add_neq_o; trivial.
    apply F.in_find_iff; trivial.
  simplify_maps;
  apply P.update_mapsto_iff.
    left.
    simplify_maps.
  apply P.update_mapsto_iff in H4.
  destruct H4.
    left.
    simplify_maps.
  destruct H.
  right; intuition.
  destruct (proj1 (in_mapsto_iff _ _ _) H1).
  simplify_maps.
  apply H0.
  apply in_mapsto_iff.
  exists x.
  assumption.
Qed.

End FMapExt.
