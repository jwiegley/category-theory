Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Category.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section Morphisms.

Context `{C : Category}.

Open Scope type_scope.

Class Idempotent `(f : X ~> X) := {
  idem : f ∘ f ≈ f
}.

Class Involutive `(f : X ~> X) := {
  invol : f ∘ f ≈ id
}.

Lemma flip_invol {X Y} (f h : X ~> Y) (g : Y ~> Y) `{@Involutive _ g} :
  f ≈ g ∘ h <--> g ∘ f ≈ h.
Proof.
  split; intros.
  rewrite X0, comp_assoc, invol; cat.
  rewrite <- X0, comp_assoc, invol; cat.
Qed.

Class Section `(f : X ~> Y) := {
  section : Y ~> X;
  section_comp : section ∘ f ≈ id
}.

Class Retraction `(f : X ~> Y) := {
  retract : Y ~> X;
  retract_comp : f ∘ retract ≈ id
}.

Class SplitIdempotent {X Y : C} := {
  split_idem_retract := Y;

  split_idem       : X ~> X;
  split_idem_r     : X ~> split_idem_retract;
  split_idem_s     : split_idem_retract ~> X;
  split_idem_law_1 : split_idem_s ∘ split_idem_r ≈ split_idem;
  split_idem_law_2 : split_idem_r ∘ split_idem_s ≈ id
}.

Class Epic {X Y} (f : X ~> Y) := {
  epic : ∀ Z (g1 g2 : Y ~> Z), g1 ∘ f ≈ g2 ∘ f → g1 ≈ g2
}.

Class Monic {X Y} (f : X ~> Y) := {
  monic : ∀ Z (g1 g2 : Z ~> X), f ∘ g1 ≈ f ∘ g2 → g1 ≈ g2
}.

Definition Bimorphic `(f : X ~> Y) := (Epic f * Monic f)%type.
Definition SplitEpi  `(f : X ~> Y) := Retraction f.
Definition SplitMono `(f : X ~> Y) := Section f.

Corollary id_idempotent : ∀ X, Idempotent (id (A := X)).
Proof. intros; constructor; cat. Qed.

Corollary id_involutive : ∀ X, Involutive (id (A := X)).
Proof. intros; constructor; cat. Qed.

Corollary id_monic : ∀ X, Monic (id (A := X)).
Proof.
  intros; constructor; intros.
  rewrite !id_left in X0.
  assumption.
Qed.

Corollary id_epic : ∀ X, Epic (id (A := X)).
Proof.
  intros; constructor; intros.
  rewrite !id_right in X0.
  assumption.
Qed.

Hint Unfold Bimorphic.
Hint Unfold SplitEpi.
Hint Unfold SplitMono.

Section Lemmas.

Variables X Y : C.
Variable f : X ~> Y.

Ltac reassociate_left  := repeat (rewrite <- comp_assoc); try f_equiv; cat.
Ltac reassociate_right := repeat (rewrite comp_assoc); try f_equiv; cat.

Lemma retractions_are_epic : Retraction f → Epic f.
Proof.
  autounfold.
  intros.
  destruct X0.
  constructor; intros.
  rewrite <- id_right.
  symmetry.
  rewrite <- id_right.
  rewrite <- retract_comp0.
  reassociate_right.
Qed.

Lemma sections_are_monic : Section f → Monic f.
Proof.
  autounfold.
  intros.
  destruct X0.
  constructor; intros.
  rewrite <- id_left.
  symmetry.
  rewrite <- id_left.
  rewrite <- section_comp0.
  reassociate_left.
Qed.

End Lemmas.

Ltac reassociate_left  := repeat (rewrite <- comp_assoc); cat.
Ltac reassociate_right := repeat (rewrite comp_assoc); cat.

Definition epi_compose {X Y Z : C}
           `(ef : @Epic Y Z f) `(eg : @Epic X Y g) : Epic (f ∘ g).
Proof.
  autounfold; intros.
  destruct ef, eg.
  constructor; intros.
  apply epic0, epic1.
  reassociate_left.
Qed.

Definition monic_compose {X Y Z : C}
           `(ef : @Monic Y Z f) `(eg : @Monic X Y g) : Monic (f ∘ g).
Proof.
  autounfold; intros.
  destruct ef, eg.
  constructor; intros.
  apply monic1, monic0.
  reassociate_right.
Qed.

End Morphisms.

Hint Unfold Bimorphic.
Hint Unfold SplitEpi.
Hint Unfold SplitMono.

Definition flip_Section `{C : Category} `(f : X ~> Y)
           (s : @Section C X Y f) : @Retraction C Y X section.
Proof.
  autounfold.
  destruct s.
  exists f.
  assumption.
Qed.

Definition flip_Retraction `{C : Category} `(f : X ~> Y)
           (s : @Retraction C X Y f) : @Section C Y X retract.
Proof.
  autounfold.
  destruct s.
  exists f.
  assumption.
Qed.
