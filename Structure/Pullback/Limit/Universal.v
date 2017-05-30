Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Structure.Pullback.Limit.
Require Export Category.Structure.Pullback.
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
      rewrite (RoofHom_inv _ _ f); cat).
  }
  destruct P, Lim; simpl in *.
  exists (unique_morphism (ump_limits cone)). {
    split;
    [ pose proof (unique_property (ump_limits cone) RNeg)
    | pose proof (unique_property (ump_limits cone) RPos) ];
    unfold cone in *; simpl in *; clear cone;
    rewrite X0; clear X0; reflexivity.
  }
  intros.
  apply (uniqueness (ump_limits cone)); intros.
  simpl in *.
  destruct X0, X1; simpl; auto.
  rewrite <- e0.
  rewrite comp_assoc.
  unfold unop.
  rewrite ump_cones.
  reflexivity.
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
  assert (eqv : f ∘ vertex_map RNeg ≈ g ∘ vertex_map RPos).
    rewrite (ump_cones RNeg RZero ZeroNeg).
    rewrite (ump_cones RPos RZero ZeroPos).
    reflexivity.
  unfold Pullback_from_Universal_obligation_1; simpl.
  destruct (ump_pullbacks vertex (vertex_map RNeg) (vertex_map RPos) eqv).
  construct; simplify; auto.
    destruct X0; auto.
    rewrite <- comp_assoc.
    rewrite x.
    apply (ump_cones RNeg RZero ZeroNeg).
  apply uniqueness.
  split.
    apply (X0 RNeg).
  apply (X0 RPos).
Defined.
