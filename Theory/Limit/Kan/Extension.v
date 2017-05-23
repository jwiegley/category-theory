Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Cone.
Require Import Category.Theory.Limit.
Require Import Category.Theory.Kan.Extension.
Require Import Category.Instance.One.
Require Import Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Theorem Kan_Limit {J : Category} {C : Category} (F : J ⟶ C)
        `{@HasLimit J C F} `{@HasRan J 1%object (Erase J) C} :
  Limit F ≅ Ran (Erase J) F ().
Proof.
  given (cone : Cone F).
    pose (from ((@adj_iso _ _ _ _ ran_adjoint
                          (Ran (Erase J) F) F)) nat_identity) as adj_from;
    simpl in adj_from.

    unshelve (refine {| vertex := Ran (Erase J) F tt |}).
      apply adj_from.
    abstract (intros; rewrite (naturality[adj_from]); simpl; cat).

  given (nat : Const (Limit F) ○ Erase J ⟹ F).
    transform; simpl; intros.
      apply vertex_map.
    abstract (cat; apply ump_cones).

  pose (to (@adj_iso _ _ _ _ ran_adjoint (Const (Limit F)) F) nat)
    as adj_to; simpl in adj_to.

  isomorphism; simpl.
  - apply adj_to.
  - apply (@limit_terminal J C F H cone).
  - simpl.
    pose proof (@ump_limits J C F H cone).
    pose proof (iso_to_from
                  ((@adj_iso _ _ _ _ ran_adjoint
                             (Ran (Erase J) F) F)) nat_identity tt).
    simpl in X0.
    rewrite fmap_id in X0.
    rewrite <- X0.
    unfold adj_to; simpl.

    given (from_ran : Ran (Erase J) F ⟹ Const (Limit F)).
      transform; simpl; intros.
        destruct X1.
        apply (@limit_terminal _ _ _ H cone).
      abstract cat.

    pose proof (@adj_left_nat_l' _ _ _ _ ran_adjoint
                                 (Ran (Erase J) F) (Const (Limit F))
                                 F nat from_ran tt).
    simpl in X1; rewrite <- X1; clear X1.
    assert (∀ f g, f ≈ g
              -> to (@adj_iso _ _ _ _ ran_adjoint (Ran (Erase J) F) F) f
               ≈ to (@adj_iso _ _ _ _ ran_adjoint (Ran (Erase J) F) F) g).
      intros; rewrite X1; reflexivity.
    simpl in X1; apply X1; clear X1.
    intros; simpl.
    abstract apply X.
  - abstract apply limit_unique.
Qed.
