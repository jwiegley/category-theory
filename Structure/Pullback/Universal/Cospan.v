Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Pullback.
Require Export Category.Structure.Pullback.Universal.
Require Export Category.Structure.Limit.
Require Export Category.Structure.Span.
Require Export Category.Instance.Roof.

Program Definition Pullback_to_Universal {C : Category}
        (F : Cospan C) (P : Pullback F) :
  Pullback_Universal (unop (fmap[F] ZeroNeg)) (unop (fmap[F] ZeroPos)) := {|
  pullback_obj := @Lim _ _ _ P;
  pullback_fst := vertex_map;
  pullback_snd := vertex_map
|}.
Next Obligation.
  destruct P.
  pose proof (@ump_cones _ _ _ Lim).
  unfold unop.
  rewrite !X.
  reflexivity.
Qed.
Next Obligation.
  given (cone : Cone F). {
    unshelve (refine {| vertex := Q |}); intros.
      destruct X0; auto.
      exact (unop (fmap[F] ZeroPos) ∘ q2).
    abstract (
      simpl;
      destruct X0, Y; auto with roof_laws; simpl in f;
      [ pattern f;
        apply caseRoofNegNeg; cat
      | unfold unop;
        pattern f;
        apply caseRoofZeroNeg; clear f;
        apply X
      | pattern f;
        apply caseRoofZeroZero; cat
      | unfold unop;
        pattern f;
        apply caseRoofZeroPos; clear f;
        reflexivity
      | pattern f;
        apply caseRoofPosPos; cat ]).
  }
  destruct P, Lim; simpl in *.
  exists (limit_terminal cone). {
    split;
    [ pose proof (ump_limits cone RNeg)
    | pose proof (ump_limits cone RPos) ];
    unfold cone in *; simpl in *; clear cone;
    rewrite X0; clear X0; reflexivity.
  }
  intros.
  pose proof (limit_unique cone).
  pose proof (ump_limits cone).
  unfold cone in *; simpl in *; clear cone.
  split.
    split;
    rewrite <- X0;
    apply X1.
  symmetry.
  apply X0.
Qed.

Program Definition Pullback_from_Universal {C : Category}
        {X Y Z : C} (f : X ~> Z) (g : Y ~> Z) (P : Pullback_Universal f g) :
  Limit (@ASpan (C^op) Z X Y f g)^op := {|
  Lim := {| vertex := pullback_obj _ _ P |}
|}.
Next Obligation.
  destruct X0;
  destruct P; simpl in *; auto.
  exact (f ∘ pullback_fst).
Defined.
Next Obligation.
  destruct X0, Y0;
  destruct P; simpl in *; auto with roof_laws; cat.
Qed.
Next Obligation.
  destruct P, N; simpl in *.
  given (eqv : f ∘ vertex_map RNeg ≈ g ∘ vertex_map RPos).
    rewrite (ump_cones RNeg RZero ZeroNeg).
    rewrite (ump_cones RPos RZero ZeroPos).
    reflexivity.
  exact (``(sigT_of_sigT2 (pullback_ump vertex (vertex_map RNeg)
                                        (vertex_map RPos) eqv))).
Defined.
Next Obligation.
  destruct P, N; simpl in *.
  destruct pullback_ump.
  specialize (p0 f0); intuition.
Qed.
Next Obligation.
  destruct P, N; simpl in *.
  destruct X0; simpl.
  - destruct pullback_ump; intuition.
  - destruct pullback_ump.
    destruct p.
    rewrite <- comp_assoc.
    rewrite e.
    apply (ump_cones RNeg RZero ZeroNeg).
  - destruct pullback_ump; intuition.
Qed.

(*
Require Import Category.Structure.Terminal.

Definition Product' {C : Category} `{@Terminal C} {X Y : C} :=
  @Pullback_Morphisms C X Y.
Arguments Product {C _ X Y _ _ _} /.

Program Instance Product_Terminal {Terminal C} {X Y : C} :
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

Program Instance Product_Terminal {Terminal C} {X Y : C} :
  Terminal (@Product C _ X Y).
Obligation 1.
  constructor.

Program Instance Product_Cartesian {Terminal C} {X Y : C} :
  Cartesian (@Product C _ X Y).
Obligation 1.
  constructor.

Lemma uniqueness_of_products {T : Terminal C} :
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
