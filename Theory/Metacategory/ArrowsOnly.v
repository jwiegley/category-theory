Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Coq.FSets.FMaps.
Require Import Category.Lib.FMapExt.
Require Import Coq.Vectors.Vector.

Lemma comparison_eq_dec : ∀ x y : comparison, x = y ∨ x ≠ y.
Proof.
  intros.
  destruct x, y; intuition idtac;
  right; intros; discriminate.
Qed.

Module Type NatValue.
  Parameter n : nat.
End NatValue.

Module Fin_as_OT (Import N : NatValue) <: OrderedType.
  Definition t := Fin.t n.

  Definition eq (x y : Fin.t n) : Prop := x = y.
  Definition lt (x y : Fin.t n) : Prop :=
    (` (Fin.to_nat x) < ` (Fin.to_nat y))%nat.

  Lemma eq_refl : ∀ x : t, eq x x.
  Proof. reflexivity. Qed.

  Lemma eq_sym : ∀ x y : t, eq x y → eq y x.
  Proof. symmetry; assumption. Qed.

  Lemma eq_trans : ∀ x y z : t, eq x y → eq y z → eq x z.
  Proof. intros; transitivity y; assumption. Qed.

  Lemma lt_trans : ∀ x y z : t, lt x y → lt y z → lt x z.
  Proof.
    unfold lt; intros.
    transitivity (` (Fin.to_nat y)); assumption.
  Qed.

  Lemma lt_not_eq : ∀ x y : t, lt x y → ¬ eq x y.
  Proof.
    unfold lt, eq, not; intros; subst.
    contradiction (PeanoNat.Nat.lt_irrefl (` (Fin.to_nat y))).
  Qed.

  Definition compare (x y : t) : Compare lt eq x y.
  Proof.
    destruct (Nat_as_OT.compare (` (Fin.to_nat x)) (` (Fin.to_nat y))).
    - apply LT, l.
    - apply Fin.to_nat_inj in e.
      apply (EQ e).
    - apply GT, l.
  Defined.

  Definition eq_dec (x y : t) : eq x y ∨ ¬ eq x y :=
    Fin.eq_dec x y.
End Fin_as_OT.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Module Graph (Import N : NatValue).

Module FO := Fin_as_OT N.
Module PO := PairOrderedType FO FO.

Module M := FMapList.Make(PO).

Module Import FMapExt := FMapExt PO M.
Module P := FMapExt.P.
Module F := P.F.

(* An arrows-only metagraph consists only of arrows, which are merely
   distinguished, there is no other structure. *)

Set Warnings "-non-primitive-record".
Record Metagraph := {
  arrow := Fin.t N.n
}.

(* An arrows-only meta-semigroupoid defines all the composable pairs of
   arrows, plus the axioms for such pairs. *)

Record Metasemigroupoid := {
  is_metagraph :> Metagraph;

  pairs : M.t (arrow is_metagraph);

  composite (f g h : arrow is_metagraph) := M.MapsTo (f, g) h pairs;

  (* ∀ edges (X, Y) and (Y, Z), ∃ an edge (X, Z) which is equal to the
     composition of those edges. *)
  composite_correct (k g f kg gf : arrow is_metagraph) :
    composite k g kg ->
    composite g f gf -> ∃ kgf, composite kg f kgf;

  composition_law (k g f kg gf : arrow is_metagraph) :
    composite k g kg ->
    composite g f gf ->
    ∀ kgf, composite kg f kgf ↔ composite k gf kgf
}.

(* An arrows-only meta-category defines identity arrows as those which, when
   composed to the left or right of another arrow, result in that same arrow.
   This definition requires that all such composition be present. *)

Record Metacategory := {
  is_metasemigroupoid :> Metasemigroupoid;

  identity (u : arrow is_metasemigroupoid) :=
    (∀ f, composite is_metasemigroupoid f u f) ∧
    (∀ g, composite is_metasemigroupoid u g g)
}.

(* Every meta-category, defined wholly in terms of the axioms of category
   theory, gives rise to a category interpreted in the context of set
   theory. *)

Global Program Definition Category_from_Metacategory (M : Metacategory) :
  Category := {|
  obj     := ∃ i : arrow M, identity M i;
  hom     := fun x y =>
    ∃ f : arrow M, composite M f (`1 x) f ∧ composite M (`1 y) f f;
  homset  := fun _ _ => {| Setoid.equiv := fun f g => `1 f = `1 g |};
  id      := fun x =>
    let f := `1 x in
    (f; (fst (`2 x) f, snd (`2 x) f));
  compose := fun x y z f g =>
    let fg := `1 (composite_correct
                    M (`1 f) (`1 y) (`1 g) (`1 f) (`1 g)
                    (fst (`2 y) (`1 f)) (snd (`2 y) (`1 g))) in
    (fg; (fst (`2 x) fg, snd (`2 z) fg))
|}.
Next Obligation. equivalence; simpl in *; congruence. Qed.
Next Obligation. proper; simpl in *; subst; auto. Qed.
Next Obligation.
  simpl.
  destruct X; simpl in *.
  destruct (composite_correct M y y f y f (c1 y) (c2 f)); simpl.
  apply (FMapExt.F.MapsTo_fun m c0).
Qed.
Next Obligation.
  simpl.
  destruct X0; simpl in *.
  destruct (composite_correct M f x x f x (c1 f) (c2 x)); simpl.
  apply (FMapExt.F.MapsTo_fun m c).
Qed.
Next Obligation.
  simpl.
  destruct X1, X0; simpl in *.
  repeat destruct (composite_correct M _ _ _ _ _ _ _); simpl in *.
  spose (fst (composition_law M _ _ _ _ _ m1 m x3) m2) as X1.
  apply (FMapExt.F.MapsTo_fun m0 X1).
Qed.
Next Obligation.
  symmetry; apply Category_from_Metacategory_obligation_5.
Qed.

End Graph.

Module Two.

Module NatFour <: NatValue.
  Monomorphic Definition n := 4%nat.
End NatFour.

(* A graph with four arrows. *)
Module Import G4 := Graph NatFour.

Import VectorNotations.
Import Fin.

Program Definition TwoG : Metagraph := Build_Metagraph.

Notation "[map ]" := (M.empty _) (at level 9, only parsing).
Notation "x +=> y" := (M.add x y) (at level 9, y at level 100, only parsing).
Notation "[map  a ; .. ; b ]" := (a .. (b [map]) ..) (only parsing).

Ltac cleanup :=
  G4.FMapExt.simplify_maps;
  repeat (right; intuition; try discriminate; G4.FMapExt.simplify_maps).

Program Definition TwoMS : Metasemigroupoid := {|
  is_metagraph := TwoG;
  pairs := [map (F1,         F1        ) +=> F1
           ;    (FS F1,      FS F1     ) +=> FS F1
           ;    (FS F1,      FS (FS F1)) +=> FS (FS F1)
           ;    (FS (FS F1), F1        ) +=> FS (FS F1) ]
|}.
Next Obligation.
  unfold arrow in *.
  repeat (match goal with
  | [ H : M.MapsTo _ _ (M.add _ _ _) |- _ ] =>
    apply G4.FMapExt.add_mapsto_iffT in H
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
  try discriminate; cleanup.
Qed.
Next Obligation.
  split; intros;
  repeat G4.FMapExt.simplify_maps;
  simpl in *;
  destruct H0, H1, H2; subst;
  intuition idtac; try discriminate; cleanup.
Qed.

Program Definition TwoC : Metacategory := {|
  is_metasemigroupoid := TwoMS
|}.

End Two.
