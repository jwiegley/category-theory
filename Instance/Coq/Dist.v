Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Coq.Reals.Reals.
Require Import Coq.Sets.Ensembles.

Require Import Category.Lib.
Require Import Category.Lib.Same_set.
Require Export Category.Theory.Functor.
Require Import Category.Instance.Coq.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Ensemble_map {A B : Type} (f : A -> B) (x : Ensemble A) :
  Ensemble B := fun b => (exists a : A, x a /\ f a = b)%type.

Program Instance Ensemble_map_Proper {A B} :
  Proper ((eq ==> eq) ==> Same_set A ==> Same_set B) Ensemble_map.
Next Obligation.
  unfold Ensemble_map.
  repeat intro.
  destruct H.
  split; repeat intro;
  inversion_clear H1;
  destruct H2; subst;
  exists x2;
  split; auto.
  - now apply H.
  - erewrite X; eauto.
  - now apply H0.
Qed.

(** Same as Singleton *)
Definition Ensemble_pure {A : Type} (x : A) : Ensemble A := fun a => x = a.

Definition Ensemble_ap {A B : Type} (mf : Ensemble (A -> B)) (mx : Ensemble A) :
  Ensemble B := fun b => (exists f x, mf f /\ mx x /\ f x = b)%type.

(** Same as Empty_set *)
Definition Ensemble_empty {A : Type} : Ensemble A := fun _ => False.

(** Same as Union *)
Definition Ensemble_choose {A : Type} (x y : Ensemble A) :=
  fun a => x a \/ y a.

Definition Ensemble_join {A : Type} (m : Ensemble (Ensemble A)) : Ensemble A :=
  fun a => (exists t : Ensemble A, m t /\ t a)%type.

Program Instance Ensemble_join_Proper {A : Type} :
  Proper (Same_set _ ==> Same_set A) Ensemble_join.
Next Obligation.
  unfold Ensemble_join.
  repeat intro.
  destruct H.
  split; repeat intro;
  inversion_clear H1;
  destruct H2; subst;
  exists x1;
  split; auto.
    now apply H.
  now apply H0.
Qed.

Definition Ensemble_bind {A B : Type} (f : A -> Ensemble B) (x : Ensemble A) :
  Ensemble B := fun b => (exists a : A, x a /\ In _ (f a) b)%type.

Program Instance Ensemble_bind_Proper {A B : Type} :
  Proper ((eq ==> Same_set B) ==> Same_set A ==> Same_set B) Ensemble_bind.
Next Obligation.
  unfold Ensemble_bind.
  repeat intro.
  destruct H.
  split; repeat intro;
  inversion_clear H1;
  destruct H2; subst;
  exists x2;
  split; auto.
  - now apply H.
  - specialize (X x2 x2 eq_refl).
    now apply X, H2.
  - now apply H0.
  - specialize (X x2 x2 eq_refl).
    now apply X, H2.
Qed.

Definition Ensemble_distr `(s : Ensemble (A * B)) : A -> Ensemble B :=
  fun a b => s (a, b).

Program Instance Ensemble_distr_Proper {A B : Type} :
  Proper (Same_set (A * B) ==> eq ==> Same_set B) Ensemble_distr.
Next Obligation.
  unfold Ensemble_distr.
  repeat intro.
  subst.
  destruct H.
  split; repeat intro.
    now apply H.
  now apply H0.
Qed.

Definition Ensemble_unionWith `(f : B -> B -> B) (z : B)
           `(xs : Ensemble (A * B)) : Ensemble (A * B) :=
  fun '(a, b) => (exists l : list B,
    (forall x : B, (In _ xs (a, x) <-> List.In x l))
      /\ b = List.fold_left f l z)%type.

Program Instance Ensemble_unionWith_Proper `(f : B -> B -> B) (z : B) {A : Type} :
  Proper (Same_set _ ==> Same_set (A * B)) (Ensemble_unionWith f z).
Next Obligation.
  unfold Ensemble_unionWith.
  repeat intro.
  split; repeat intro;
  unfold In in *;
  destruct x0, H0, H0; subst;
  exists x0; intros;
  split; auto;
  intuition.
  - now apply H0, H, H1.
  - now apply H, H0, H1.
  - now apply H0, H, H1.
  - now apply H, H0, H1.
Qed.

Definition Ensemble_Dist_bind {A B : Type}
           `(xs : Ensemble (A * R)) `(f : A -> Ensemble (B * R)) :
  Ensemble (B * R) :=
  Ensemble_bind (fun '(a, pa) =>
                   Ensemble_map (fun '(b, pb) => (b, pa * pb)%R) (f a)) xs.

Program Instance Ensemble_Dist_bind_Proper {A B : Type} :
  Proper (Same_set _ ==> (eq ==> Same_set _) ==> Same_set _)
         (@Ensemble_Dist_bind A B).
Next Obligation.
  repeat intro.
  unfold Ensemble_Dist_bind.
  apply Ensemble_bind_Proper; auto.
  repeat intro.
  destruct x1, y1.
  apply Ensemble_map_Proper.
    repeat intro.
    destruct x1, y1.
    inversion H0; subst; clear H0.
    inversion H1; subst; clear H1.
    reflexivity.
  inversion H0; subst; clear H0.
  now apply X.
Qed.

Definition Ensemble_sum_at_key `(xs : Ensemble (A * R)) : Ensemble (A * R) :=
  Ensemble_unionWith Rplus 0%R xs.

Program Instance Ensemble_sum_at_key_Proper A :
  Proper (Same_set (A * R) ==> Same_set (A * R)) Ensemble_sum_at_key.
Next Obligation.
  repeat intro.
  unfold Ensemble_sum_at_key.
  apply Ensemble_unionWith_Proper; auto.
Qed.

Program Instance real_setoid : Setoid R.

(** The category of partial maps, built on the category of setoids. *)

(* jww (2021-07-28): This is a work in progress. *)
(*
Program Definition Dist : Category := {|
  obj := Coq;

  hom    := fun x y => x -> Ensemble (y ∧ R);
  homset := fun _ _ => {| equiv := fun f g => ∀ x, Same_set _ (f x) (g x) |};

  id := fun _ v => Singleton _ (v, 1%R);

  compose := fun _ _ _ f g v =>
    Ensemble_sum_at_key (Ensemble_Dist_bind (g v) f)
|}.
Next Obligation.
  pose proof (@Same_set_Equivalence (H0 ∧ R)).
  equivalence.
  - now apply X.
  - specialize (H1 x0).
    specialize (H2 x0).
    pose proof (@Equivalence_Transitive _ _ X).
    eapply X0; eauto.
Qed.
Next Obligation.
  proper.
  apply Ensemble_sum_at_key_Proper.
  apply Ensemble_Dist_bind_Proper.
    now apply H0.
  repeat intro; subst.
  now apply H.
Qed.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
Next Obligation.
Admitted.
*)

(*
Require Import Category.Structure.Cartesian.

Program Instance Dist_Cartesian : @Cartesian Dist := {
  product_obj := fun x y => _
}.
*)
