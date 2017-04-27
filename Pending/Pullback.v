Set Warnings "-notation-overridden".

(* jww (2017-04-13): TODO
Record Pullback `{Category C} {X Y : C} (Z : C) (f : X ~> Z) (g : Y ~> Z) := {
  pullback_obj : C;
  pullback_fst : pullback_obj ~> X;
  pullback_snd : pullback_obj ~> Y;
  pullback_ump_1 : f ∘ pullback_fst ≈ g ∘ pullback_snd;
  pullback_ump_2 : ∀ Q (q1 : Q ~> X) (q2 : Q ~> Y),
    { u : Q ~> pullback_obj
    & pullback_snd ∘ u ≈ q2 ∧ pullback_fst ∘ u ≈ q1
      ∧ ∀ (v : Q ~> pullback_obj),
          pullback_snd ∘ v ≈ q2 ∧ pullback_fst ∘ v ≈ q1 → v ≈ u }%type
}.

Definition Product `{Terminal C} {X Y : C} := @Pullback C _ X Y.
Arguments Product {C _ X Y _ _ _} /.

(*
Program Instance Product_Terminal `{Terminal C} {X Y : C} :
  Category (@Product C _ X Y).
Next Obligation.
  reflexivity.
Qed.
Next Obligation.
  reflexivity.
Qed.
Next Obligation.
  econstructor.
  constructor; apply proof_irrelevance.
Admitted.

Program Instance Product_Terminal `{Terminal C} {X Y : C} :
  Terminal (@Product C _ X Y).
Obligation 1.
  constructor.

Program Instance Product_Cartesian `{Terminal C} {X Y : C} :
  Cartesian (@Product C _ X Y).
Obligation 1.
  constructor.
*)

Lemma uniqueness_of_products `{T : Terminal C} :
  ∀ {X Y} (p q : @Product C T X Y One one one),
    let ump1 := pullback_ump_2 q _ (pullback_fst p) (pullback_snd p) in
    let ump2 := pullback_ump_2 p _ (pullback_fst q) (pullback_snd q) in
    projT1 ump1 ∘ projT1 ump2 ≈ id ∧
    projT1 ump2 ∘ projT1 ump1 ≈ id.
Proof.
  intros.
  split.
    destruct ump1, ump2; simpl.
    destruct a, a0.
    destruct H0 as [? ?].
    destruct H2 as [? ?].
    rewrite <- H in H1.
    rewrite <- comp_assoc in H1.
Abort.
*)