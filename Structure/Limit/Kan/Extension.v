Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Theorem Kan_Limit `(F : J ⟶ C) `{@Limit _ _ F} `{@RightKan _ _ (Erase J) C} :
  Lim F ≅ Ran (Erase J) F ().
Proof.
  given (cone : Cone F).
    pose (from ((@adj _ _ _ _ ran_adjoint
                      (Ran (Erase J) F) F)) nat_identity) as adj_from;
    simpl in adj_from.

    unshelve (refine {| vertex := Ran (Erase J) F tt |}).
      apply adj_from.
    abstract (intros; rewrite (naturality[adj_from]); simpl; cat).

  given (nat : Const (Lim F) ○ Erase J ⟹ F). {
    transform; simpl; intros.
    + apply vertex_map.
    + abstract (cat; apply ump_cones).
    + abstract (cat; symmetry; apply ump_cones).
  }

  pose (to (@adj _ _ _ _ ran_adjoint (Const (Lim F)) F) nat)
    as adj_to; simpl in adj_to.

  isomorphism; simpl.
  - apply adj_to.
  - apply (unique_morphism (ump_limits cone)).
  - simpl.
    pose proof (iso_to_from
                  ((@adj _ _ _ _ ran_adjoint
                         (Ran (Erase J) F) F)) nat_identity tt) as X;
    simpl in X.
    rewrite fmap_id in X.
    rewrite <- X.
    unfold adj_to; simpl.

    given (from_ran : Ran (Erase J) F ⟹ Const (Lim F)). {
      transform; simpl; intros.
      + destruct X0.
        apply (unique_morphism (ump_limits cone)).
      + abstract cat.
      + abstract cat.
    }

    pose proof (@to_adj_nat_l _ _ _ _ ran_adjoint
                              (Ran (Erase J) F) (Const (Lim F))
                              F nat from_ran tt) as X0;
    simpl in X0; rewrite <- X0; clear X0.

    assert (∀ f g, f ≈ g
              -> to (@adj _ _ _ _ ran_adjoint (Ran (Erase J) F) F) f
               ≈ to (@adj _ _ _ _ ran_adjoint (Ran (Erase J) F) F) g).
      intros; rewrite X0; reflexivity.
    simpl in X0; apply X0; clear X0.

    intros; simpl.
    apply (unique_property (ump_limits cone)).

  - unfold adj_to; simpl in *; clear adj_to.
    evar (j : @ob J).
    pose proof (unique_property (ump_limits cone) j) as X; simpl in X.
    rewrite (@adj_unit _ _ _ _ ran_adjoint _ _ nat tt).
    pose proof (@counit_fmap_unit _ _ Induced (Ran (Erase J))
                                  ran_adjoint (Const (Lim F))) as X0;
    simpl in X0; simpl.
    rewrite comp_assoc.
    rewrite <- (X0 j); clear X0.
    comp_right.
    unfold counit; simpl.
    pose proof (@ump_cones _ _ _ cone); simpl in X0.
    pose proof nat as X1.
    pose proof (naturality[nat]) as X2.
    pose proof (transform[nat]) as X3.
    pose proof (uniqueness (ump_limits cone)) as X4.
    pose proof (iso_from_to ((@adj _ _ _ _ ran_adjoint
                                   (Const (Lim F)) F)) nat) as X5.
    simpl in *.
    destruct H0.
    destruct ran_adjoint.
    simpl in *.
Admitted.
