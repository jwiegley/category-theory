Set Warnings "-notation-overridden".

Require Import Coq.Vectors.Fin.
Require Import Coq.FSets.FMaps.
Require Import Coq.omega.Omega.

Require Import Category.Lib.
Require Import Category.Lib.FMapExt.
Require Import Category.Theory.Functor.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Module PO := PairOrderedType Nat_as_OT Nat_as_OT.
Module M := FMapList.Make(PO).
Module FMapExt := FMapExt PO M.

(* An arrows-only meta-category defines identity arrows as those which, when
   composed to the left or right of another arrow, result in that same arrow.
   This definition requires that all such composition be present. *)

Record Metacategory := {
  num_arrows : nat;
  arrow := Fin.t num_arrows;

  pairs : M.t arrow;

  composite (f g h : arrow) := M.MapsTo (` (to_nat f), ` (to_nat g)) h pairs;
  defined (f g : arrow) := ∃ h, composite f g h;

  composite_defined {f g h : arrow} (H : composite f g h) :
    defined f g := (h; H);

  (*a ∀ edges (X, Y) and (Y, Z), ∃ an edge (X, Z) which is equal to the
     composition of those edges. *)
  composite_correct {k g f kg gf : arrow} :
    composite k g kg ->
    composite g f gf -> ∃ kgf, composite kg f kgf;

  composition_law {k g f kg gf : arrow} :
    composite k g kg ->
    composite g f gf ->
    ∀ kgf, composite kg f kgf ↔ composite k gf kgf;

  is_identity (u : arrow) :=
    (∀ f, defined f u -> composite f u f) ∧
    (∀ g, defined u g -> composite u g g);

  identity_law (g : arrow) :
    ∃ u u', is_identity u -> is_identity u' ->
      composite g u g ∧ composite u' g g
}.

Corollary identity_law' (M : Metacategory) (g : arrow M) :
  ∃ u u', is_identity M u -> is_identity M u' ->
    composite M g u g ∧ composite M u' g g.
Proof. intros; apply identity_law. Defined.

Lemma MapsTo_dec (M : Metacategory) : ∀ elt k e (m : M.t elt),
  (∀ x y : elt, {x = y} + {x ≠ y}) ->
  { M.MapsTo k e m } + { ~ M.MapsTo k e m }.
Proof.
  intros.
  destruct (M.find k m) eqn:?.
    apply FMapExt.F.find_mapsto_iff in Heqo.
    destruct (X e e0); subst.
      left; assumption.
    right; unfold not; intros.
    pose proof (FMapExt.F.MapsTo_fun H Heqo).
    contradiction.
  apply FMapExt.F.not_find_in_iff in Heqo.
  right.
  apply FMapExt.not_in_mapsto_iff.
  assumption.
Qed.

Lemma identity_dec (M : Metacategory) : ∀ u,
  { identity M u } + { ~ identity M u }.
Proof.
Abort.

(* Lemma arrows_ind (M : Metacategory) : *)
(*   ∀ (P : arrow M → Prop), *)
(*   (∀ (i : arrow M) (H : identity M i), P i) → *)
(*   (∀ (i : arrow M) (H : ~ identity M i), P i) → *)
(*   ∀ n : arrow M, P n. *)
(* Proof. *)
(* Abort. *)

(* Every meta-category, defined wholly in terms of the axioms of category
   theory, gives rise to a category interpreted in the context of set
   theory. *)

Local Obligation Tactic := intros.

Lemma identity (M : Metacategory) :
  ∀ i : arrow M, defined M i i ∧ is_identity M i -> composite M i i i.
Proof.
  intros.
  apply H.
  intuition.
Defined.

Lemma identity_composition_left (M : Metacategory) : ∀ f g fg u,
  is_identity M u ->
  composite M f g fg ->
  defined M u f ->
  defined M u fg.
Proof.
  intros.
  destruct H.
  specialize (c0 _ H1); clear H1.
  destruct (composite_correct M c0 H0).
  spose (fst (composition_law M c0 H0 _) m) as X.
  eapply composite_defined.
  apply X.
Qed.

Lemma identity_composition_right (M : Metacategory) : ∀ f g fg u,
  is_identity M u ->
  composite M f g fg ->
  defined M g u ->
  defined M fg u.
Proof.
  intros.
  destruct H.
  specialize (c _ H1); clear H1.
  destruct (composite_correct M H0 c).
  eapply composite_defined.
  apply m.
Qed.

Program Definition Category_from_Metacategory (M : Metacategory) :
  Category := {|
  obj     := ∃ i : arrow M, defined M i i ∧ is_identity M i;
  hom     := fun x y =>
    ∃ f : arrow M, defined M f (`1 x) ∧ defined M (`1 y) f;
  homset  := fun _ _ => {| Setoid.equiv := fun f g => `1 f = `1 g |};

  id      := fun x => (`1 x; (fst (`2 x), fst (`2 x)));

  compose := fun x y z f g =>
    let fg := composite_correct
                M (fst (snd (`2 y)) (`1 f) (fst (`2 f)))
                  (snd (snd (`2 y)) (`1 g) (snd (`2 g))) in
    (`1 fg;
       (identity_composition_right M _ _ _ _ (snd (`2 x)) (`2 fg) (fst (`2 g)),
        identity_composition_left  M _ _ _ _ (snd (`2 z)) (`2 fg) (snd (`2 f))))
|}.
Next Obligation. equivalence; simpl in *; congruence. Qed.
Next Obligation. proper; simpl in *; subst; auto. Admitted.
Next Obligation.
  simpl in *.
  destruct f; simpl in *.
  destruct (composite_correct M _ _); simpl.
  eapply FMapExt.F.MapsTo_fun; eauto.
Qed.
Next Obligation.
  destruct X0; simpl in *.
  destruct (composite_correct M _ _ _ _ _ _ _); simpl.
  eapply FMapExt.F.MapsTo_fun; eauto.
Qed.
Next Obligation.
  destruct X1, X0; simpl in *.
  repeat destruct (composite_correct M _ _ _ _ _ _ _); simpl.
  spose (fst (composition_law M _ _ _ _ _ m1 m x3) m2) as X1.
  eapply FMapExt.F.MapsTo_fun; eauto.
Qed.
Next Obligation.
  symmetry.
  destruct X1, X0; simpl in *.
  repeat destruct (composite_correct M _ _ _ _ _ _ _); simpl.
  spose (fst (composition_law M _ _ _ _ _ m1 m x3) m2) as X1.
  eapply FMapExt.F.MapsTo_fun; eauto.
Qed.

Notation "[map ]" := (M.empty _) (at level 9, only parsing).
Notation "x +=> y" := (M.add x y) (at level 9, y at level 100, only parsing).
Notation "[map  a ; .. ; b ]" := (a .. (b [map]) ..) (only parsing).

Ltac cleanup :=
  try FMapExt.simplify_maps;
  repeat (right; intuition; try discriminate; FMapExt.simplify_maps).

Program Definition Two : Metacategory := {|
  num_arrows := 3;
  pairs := [map (0, 0) +=> 0
           ;    (1, 1) +=> 1
           ;    (1, 2) +=> 2
           ;    (2, 0) +=> 2 ]%nat
|}.
Next Obligation.
  destruct f, g, h; simpl in *;
  repeat (
    FMapExt.simplify_maps; simplify;
    try omega;
    simpl in *;
    try discriminate;
    try omega).
Qed.
Next Obligation.
  unfold arrow in *.
  repeat (match goal with
  | [ H : M.MapsTo _ _ (M.add _ _ _) |- _ ] =>
    apply FMapExt.add_mapsto_iffT in H
  | [ H : _ + _ |- _ ] => destruct H
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ H : _ ∧ _ |- _ ] => destruct H
  | [ H : ¬ (_ /\ _) |- _ ] =>
    pose proof (proj1 (not_and_implication _ _) H eq_refl);
    contradiction
  | [ |- ∃ _, M.MapsTo (?X, ?Y) _ _ ] =>
    match goal with
      [ |- context[M.add (X, Y) ?F _ ] ] =>
        exists F
    end
  end; subst; simpl in *);
  try discriminate;
  try congruence; cleanup.
Qed.
Next Obligation.
  split; intros;
  repeat FMapExt.simplify_maps;
  simpl in *;
  destruct H0, H1, H2; subst;
  intuition idtac;
  try discriminate;
  try omega; cleanup.
Qed.

(*
Require Import Category.Instance.Two.

Lemma composite_0_x_0 : forall x, composite Two 0%nat x 0%nat -> 0%nat = x.
Proof.
  intros.
  unfold composite in H; simpl in H.
  repeat match goal with
    [ H : M.MapsTo _ _ (M.add _ _ _) |- _ ] =>
    apply FMapExt.add_mapsto_iffT in H; destruct H; simplify; simpl in *; subst
  end; auto.
Defined.

Lemma composite_x_0_0 : forall x, composite Two x 0%nat 0%nat -> 0%nat = x.
Proof.
  intros.
  unfold composite in H; simpl in H.
  repeat match goal with
    [ H : M.MapsTo _ _ (M.add _ _ _) |- _ ] =>
    apply FMapExt.add_mapsto_iffT in H; destruct H; simplify; simpl in *; subst
  end; auto.
  discriminate.
Defined.

Lemma composite_1_x_1 : forall x, composite Two 1%nat x 1%nat -> 1%nat = x.
Proof.
  intros.
  unfold composite in H; simpl in H.
  repeat match goal with
    [ H : M.MapsTo _ _ (M.add _ _ _) |- _ ] =>
    apply FMapExt.add_mapsto_iffT in H; destruct H; simplify; simpl in *; subst
  end; auto.
Defined.

Lemma composite_x_1_1 : forall x, composite Two x 1%nat 1%nat -> 1%nat = x.
Proof.
  intros.
  unfold composite in H; simpl in H.
  repeat match goal with
    [ H : M.MapsTo _ _ (M.add _ _ _) |- _ ] =>
    apply FMapExt.add_mapsto_iffT in H; destruct H; simplify; simpl in *; subst
  end; auto.
Defined.

Lemma composite_2_x_2 : forall x, composite Two 2%nat x 2%nat -> 0%nat = x.
Proof.
  intros.
  unfold composite in H; simpl in H.
  repeat match goal with
    [ H : M.MapsTo _ _ (M.add _ _ _) |- _ ] =>
    apply FMapExt.add_mapsto_iffT in H; destruct H; simplify; simpl in *; subst
  end; auto.
  discriminate.
Defined.

Lemma composite_x_2_2 : forall x, composite Two x 2%nat 2%nat -> 1%nat = x.
Proof.
  intros.
  unfold composite in H; simpl in H.
  repeat match goal with
    [ H : M.MapsTo _ _ (M.add _ _ _) |- _ ] =>
    apply FMapExt.add_mapsto_iffT in H; destruct H; simplify; simpl in *; subst
  end; auto.
  discriminate.
  discriminate.
Defined.

Local Obligation Tactic := program_simpl; simpl in *.

Lemma not_identity : ∀ x, (2 <= x)%nat -> identity Two x -> False.
Proof.
Admitted.

Program Definition Two_to_Two : Category_from_Metacategory Two ⟶ _2 := {|
  fobj := fun x => match `1 x with
    | 0%nat => TwoX
    | 1%nat => TwoY
    | _     => False_rect _ (not_identity (`1 x) _ (`2 x))
    end;
  fmap := fun x y f => match `1 x, `1 y, `1 f with
    | 0%nat, 0%nat, 0%nat => TwoIdX
    | 1%nat, 1%nat, 1%nat => TwoIdY
    | 0%nat, 1%nat, 2%nat => TwoXY
    | _, _, _ => !
    end
|}.
Next Obligation.
  destruct x. contradiction.
  destruct x. contradiction.
  omega.
Qed.
Next Obligation. subst; auto. Defined.
Next Obligation. subst; auto. Defined.
Next Obligation. subst; auto. Defined.
Next Obligation. subst; auto. Defined.
Next Obligation. subst; auto. Defined.
Next Obligation. subst; auto. Defined.
Next Obligation.
  repeat match goal with
  | [ H : Some _ = Some _ |- _ ] =>
    inversion H; subst; clear H
  | [ H : PO.eq _ _ |- _ ] =>
    destruct H; simpl in *; subst
  | [ H : ~ PO.eq _ _ |- _ ] =>
    unfold PO.eq in H; simpl in H;
    apply Decidable.not_and in H
  | [ H : M.find _ (M.add _ _ _) = Some _ |- _ ] =>
    rewrite FMapExt.F.add_o in H;
    destruct (PO.eq_dec _ _)
  | [ H : M.find _ (M.empty _) = Some _ |- _ ] =>
    inversion H
  | [ |- Decidable.decidable (?X = ?Y) ] =>
    destruct (Nat.eq_dec X Y); [left|right]; assumption
  end.
  - omega.
  - omega.
  - eapply not_identity; eauto.
  - eapply not_identity; eauto.
Defined.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
*)
