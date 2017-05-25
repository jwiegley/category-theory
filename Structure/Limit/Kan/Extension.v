Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Instance.One.
Require Import Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Theorem Kan_Limit {J : Category} {C : Category} (F : J ⟶ C)
        `{@Limit J C F} `{@RightKan J 1%object (Erase J) C} :
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
  - apply (@limit_terminal J C F H cone).
  - simpl.
    pose proof (@ump_limits J C F H cone).
    pose proof (iso_to_from
                  ((@adj _ _ _ _ ran_adjoint
                         (Ran (Erase J) F) F)) nat_identity tt).
    simpl in X0.
    rewrite fmap_id in X0.
    rewrite <- X0.
    unfold adj_to; simpl.

    given (from_ran : Ran (Erase J) F ⟹ Const (Lim F)). {
      transform; simpl; intros.
      + destruct X1.
        apply (@limit_terminal _ _ _ H cone).
      + abstract cat.
      + abstract cat.
    }

    pose proof (@to_adj_nat_l _ _ _ _ ran_adjoint
                              (Ran (Erase J) F) (Const (Lim F))
                              F nat from_ran tt).
    simpl in X1; rewrite <- X1; clear X1.
    assert (∀ f g, f ≈ g
              -> to (@adj _ _ _ _ ran_adjoint (Ran (Erase J) F) F) f
               ≈ to (@adj _ _ _ _ ran_adjoint (Ran (Erase J) F) F) g).
      intros; rewrite X1; reflexivity.
    simpl in X1; apply X1; clear X1.
    intros; simpl.
    abstract apply X.
  - rewrite <- limit_unique.
    apply limit_unique.
Qed.
