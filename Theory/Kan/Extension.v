Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Adjunction.
Require Export Category.Instance.Nat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section KanExtension.

Context `{A : Category}.
Context `{B : Category}.
Context `{F : A ⟶ B}.
Context `{C : Category}.

Program Definition Induced : ([B, C]) ⟶ ([A, C]) := {|
  fobj := fun G => G ○ F;
  fmap := fun _ _ f => {| transform := fun Z => transform[f] (F Z) |}
|}.
Next Obligation. apply naturality. Qed.

Class HasRan := {
  Ran : ([A, C]) ⟶ ([B, C]);

  ran_adjoint : Induced ⊣ Ran
}.

End KanExtension.

Arguments Ran {_ _} F {_ _}.
Arguments HasRan {_ _} F {_}.

Require Export Category.Functor.Constant.
Require Export Category.Functor.Diagonal.
Require Export Category.Structure.Terminal.
Require Export Category.Theory.Cone.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Instance.Cat.
Require Export Category.Instance.One.

(* A natural transformation Δd ⟹ F (where Δd is the Constant functor on d) is
   the same as a cone over F (whose vertex is d). *)

Theorem Cone_Transform `{J : Category} `{C : Category} (F : J ⟶ C) (d : C) :
  Constant J d ⟹ F <--> { c : Cone F | vertex = d }.
Proof.
  split; intros.
  - unshelve eexists.
    + unshelve econstructor; intros.
      * exact d.
      * apply X.
      * simpl.
        rewrite (naturality[X]); cat.
    + reflexivity.
  - transform; simpl; intros;
    destruct X; subst.
    + apply x.
    + cat; apply ump_cones.
Qed.

Require Import Category.Theory.Limit.

Theorem Kan_Limit `{J : Category} `{C : Category} (F : J ⟶ C)
        `{@HasLimit J C F} `{@HasRan J 1%object one[J] C} :
  Limit F ≅[Nat] Ran (one[J]) F.
Proof.
  given (nat : Unique Lim ○ To_1 J ⟹ F).
    transform; simpl; intros.
      apply vertex_map.
    cat; apply ump_cones.

  pose (to (@adj_iso _ _ _ _ (@ran_adjoint _ _ _ _ H0)
                     (Unique Lim) F) nat) as adj_to;
  simpl in adj_to.

  pose (from (@adj_iso _ _ _ _ (@ran_adjoint _ _ _ _ H0)
                       (Ran (To_1 J) F) F)
             nat_identity) as adj_from;
  simpl in adj_from.

  given (cone : Cone F).
    unshelve (refine {| vertex := Ran (To_1 J) F tt |}).
      apply adj_from.
    intros.
    rewrite (naturality[adj_from]); simpl; cat.

  given (from_ran : Ran (To_1 J) F ⟹ Unique Lim).
    transform; simpl; intros.
      destruct X.
      apply (@limit J C F H cone).
    cat.

  constructive; simpl.
  - apply adj_to.
  - apply (naturality[adj_to]).
  - destruct X.
    apply (@limit J C F H cone).
  - destruct X, Y, f; simpl; cat.
    unfold Limit.Limit_obligation_1.
    unfold reflexivity; simpl; cat.
  - destruct A; simpl.
    pose proof (@ump_limits J C F H cone).
    unfold cone in *; clear cone; simpl in *.
    pose proof (iso_to_from
                  (@adj_iso _ _ _ _ (@ran_adjoint _ _ _ _ H0)
                            (Ran (To_1 J) F) F) nat_identity tt).
    simpl in X0; rewrite <- X0.
    simpl.
    unfold adj_to; simpl.
    unfold adj_from in X.
    pose proof (@adj_left_nat_l' _ _ _ _ (@ran_adjoint _ _ _ _ H0)
                                 (Ran (To_1 J) F) (Unique Lim)
                                 F nat from_ran tt).
    simpl in X1; rewrite <- X1; clear X1.
    unfold nat_compose; simpl.
    (* jww (2017-05-19): Make this into a lemma called "functional". *)
    assert (∀ f g, f ≈ g
              -> to (@adj_iso ([J, C]) ([1, C])
                              (@Induced J 1 (To_1 J) C)
                              (@Ran J 1 (To_1 J) C H0)
                              (@ran_adjoint J 1 (To_1 J) C H0)
                              ((@Ran J 1 (To_1 J) C H0) F) F) f
                    ≈ to (@adj_iso ([J, C]) ([1, C])
                                   (@Induced J 1 (To_1 J) C)
                                   (@Ran J 1 (To_1 J) C H0)
                                   (@ran_adjoint J 1 (To_1 J) C H0)
                                   ((@Ran J 1 (To_1 J) C H0) F) F) g).
      intros; rewrite X1; reflexivity.
    simpl in X1; apply X1; clear X1.
    intros; simpl.
    apply X.
  - destruct A; simpl; cat.
    apply limit_unique.
Qed.
