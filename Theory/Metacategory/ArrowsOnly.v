Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Coq.FSets.FMaps.
Require Import Category.Lib.FMapExt.
Require Import Coq.Vectors.Vector.
Require Import Coq.omega.Omega.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Module PO := PairOrderedType Nat_as_OT Nat_as_OT.

Module M := FMapList.Make(PO).

Module Import FMapExt := FMapExt PO M.
Module P := FMapExt.P.
Module F := P.F.

(* An arrows-only metagraph consists only of arrows, which are merely
   distinguished, there is no other structure. *)

Set Warnings "-non-primitive-record".
Record Metagraph := {
  num_arrows : nat;
  arrow := Fin.t num_arrows
}.

(* An arrows-only meta-semigroupoid defines all the composable pairs of
   arrows, plus the axioms for such pairs. *)

Record Metasemigroupoid := {
  is_metagraph :> Metagraph;

  pairs : M.t (arrow is_metagraph);

  pairs_correct : ∀ k, M.In k pairs ->
    (fst k < num_arrows is_metagraph ∧ snd k < num_arrows is_metagraph)%nat;

  composite (f g h : arrow is_metagraph) :=
    M.MapsTo (` (Fin.to_nat f), ` (Fin.to_nat g)) h pairs;

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
  simpl.
  symmetry.
  destruct X1, X0; simpl in *.
  repeat destruct (composite_correct M _ _ _ _ _ _ _); simpl in *.
  spose (fst (composition_law M _ _ _ _ _ m1 m x3) m2) as X1.
  apply (FMapExt.F.MapsTo_fun m0 X1).
Qed.

Import VectorNotations.
Import Fin.

Program Definition TwoG : Metagraph := {|
  num_arrows := 3
|}.

Notation "[map ]" := (M.empty _) (at level 9, only parsing).
Notation "x +=> y" := (M.add x y) (at level 9, y at level 100, only parsing).
Notation "[map  a ; .. ; b ]" := (a .. (b [map]) ..) (only parsing).

Ltac cleanup :=
  FMapExt.simplify_maps;
  repeat (right; intuition; try discriminate; FMapExt.simplify_maps).

Program Definition TwoMS : Metasemigroupoid := {|
  is_metagraph := TwoG;
  pairs := [map (0, 0) +=> F1
           ;    (1, 1) +=> FS F1
           ;    (1, 2) +=> FS (FS F1)
           ;    (2, 0) +=> FS (FS F1) ]%nat
|}.
Next Obligation.
  destruct k; simpl in *.
  destruct n, n0; simpl in *.
  - destruct (fst (in_mapsto_iffT _ _ _) H); clear H.
    cleanup.
  - destruct (fst (in_mapsto_iffT _ _ _) H); clear H.
    cleanup.
      destruct H1; discriminate.
    cleanup.
      destruct H1; discriminate.
    cleanup.
      destruct H1; discriminate.
    cleanup.
    destruct H1; discriminate.
  - destruct (fst (in_mapsto_iffT _ _ _) H); clear H.
    cleanup.
      destruct H1; discriminate.
    cleanup.
      destruct H1; discriminate.
    cleanup.
      destruct H1; discriminate.
    cleanup.
    destruct H1.
    inversion_clear H.
    inversion_clear H1.
    split; omega.
  - destruct (fst (in_mapsto_iffT _ _ _) H); clear H.
    cleanup.
      destruct H1; discriminate.
    cleanup.
      destruct H1.
      simpl in *.
      rewrite <- H, <- H0.
      split; omega.
    cleanup.
      destruct H1.
      simpl in *.
      rewrite <- H, <- H1.
      split; omega.
    cleanup.
    destruct H1.
    inversion_clear H.
    inversion_clear H1.
Qed.
Next Obligation.
  unfold arrow in *.
  repeat (match goal with
  | [ H : M.MapsTo _ _ (M.add _ _ _) |- _ ] =>
    apply FMapExt.add_mapsto_iffT in H
  | [ H : _ + _ |- _ ] => destruct H
  | [ H : _ /\ _ |- _ ] => destruct H
  | [ H : _ ∧ _ |- _ ] => destruct H
  | [ H : _ = _ |- _ ] => rewrite <- H
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
  intuition idtac; try discriminate; cleanup.
Qed.

Program Definition TwoC : Metacategory := {|
  is_metasemigroupoid := TwoMS
|}.
