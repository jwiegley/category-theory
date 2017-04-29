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

Definition Idempotent `(f : X ~> X) := f ∘ f ≈ f.
Definition Involutive `(f : X ~> X) := f ∘ f ≈ id.

Definition Section    `(f : X ~> Y) := { g : Y ~> X & g ∘ f ≈ id }.
Definition Retraction `(f : X ~> Y) := { g : Y ~> X & f ∘ g ≈ id }.

Class SplitIdempotent {X Y : C} := {
  split_idem_retract := Y;
  split_idem         : X ~> X;
  split_idem_r       : X ~> split_idem_retract;
  split_idem_s       : split_idem_retract ~> X;
  split_idem_law_1   : split_idem_s ∘ split_idem_r ≈ split_idem;
  split_idem_law_2   : split_idem_r ∘ split_idem_s ≈ id
}.

Definition Epic  `(f : X ~> Y) := ∀ Z (g1 g2 : Y ~> Z), g1 ∘ f ≈ g2 ∘ f → g1 ≈ g2.
Definition Monic `(f : X ~> Y) := ∀ Z (g1 g2 : Z ~> X), f ∘ g1 ≈ f ∘ g2 → g1 ≈ g2.

Definition Bimorphic `(f : X ~> Y) := (Epic f * Monic f)%type.
Definition SplitEpi  `(f : X ~> Y) := Retraction f.
Definition SplitMono `(f : X ~> Y) := Section f.

Corollary id_idempotent : ∀ X, Idempotent (id (A := X)).
Proof. intros; unfold Idempotent; cat. Qed.

Corollary id_involutive : ∀ X, Involutive (id (A := X)).
Proof. intros; unfold Involutive; cat. Qed.

Hint Unfold Idempotent.
Hint Unfold Involutive.
Hint Unfold Section.
Hint Unfold Retraction.
Hint Unfold Epic.
Hint Unfold Monic.
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
  rewrite <- id_right.
  symmetry.
  rewrite <- id_right.
  rewrite <- c.
  reassociate_right.
Qed.

Lemma sections_are_monic : Section f → Monic f.
Proof.
  autounfold.
  intros.
  destruct X0.
  rewrite <- id_left.
  symmetry.
  rewrite <- id_left.
  rewrite <- c.
  reassociate_left.
Qed.

End Lemmas.

Ltac reassociate_left  := repeat (rewrite <- comp_assoc); cat.
Ltac reassociate_right := repeat (rewrite comp_assoc); cat.

Definition epi_compose {X Y Z : C}
           `(ef : @Epic Y Z f) `(eg : @Epic X Y g) : Epic (f ∘ g).
Proof.
  autounfold; intros.
  apply ef, eg.
  reassociate_left.
Qed.

Definition monic_compose {X Y Z : C}
           `(ef : @Monic Y Z f) `(eg : @Monic X Y g) : Monic (f ∘ g).
Proof.
  autounfold; intros.
  apply eg, ef.
  reassociate_right.
Qed.

End Morphisms.

Hint Unfold Idempotent.
Hint Unfold Involutive.
Hint Unfold Section.
Hint Unfold Retraction.
Hint Unfold Epic.
Hint Unfold Monic.
Hint Unfold Bimorphic.
Hint Unfold SplitEpi.
Hint Unfold SplitMono.

Require Export Category.Theory.Isomorphism.

Program Instance Monic_Retraction_Iso
        `{C : Category} {X Y : C} `(r : Retraction f) `(m : Monic f) :
  X ≅ Y := {
  to := f;
  from := projT1 r
}.
Next Obligation. destruct r; auto. Qed.
Next Obligation.
  destruct r; simpl.
  apply m.
  rewrite comp_assoc.
  rewrite c; cat.
Qed.

Program Instance Epic_Section_Iso
        `{C : Category} {X Y : C} `(s : Section f) `(e : Epic f) :
  X ≅ Y := {
  to := f;
  from := projT1 s
}.
Next Obligation.
  destruct s; auto.
  simpl.
  specialize (e Y (f ∘ x) id).
  apply e.
  rewrite <- comp_assoc.
  rewrite c; cat.
Qed.
Next Obligation. destruct s; auto. Qed.

Definition flip_Section `{C : Category} `(f : X ~> Y)
           (s : @Section C X Y f) : @Retraction C Y X (projT1 s).
Proof.
  autounfold.
  destruct s.
  exists f.
  assumption.
Qed.

Definition flip_Retraction `{C : Category} `(f : X ~> Y)
           (s : @Retraction C X Y f) : @Section C Y X (projT1 s).
Proof.
  autounfold.
  destruct s.
  exists f.
  assumption.
Qed.
