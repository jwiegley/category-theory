Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Structure.Limit.
Require Export Category.Structure.Span.
Require Export Category.Structure.Pullback.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Definition Pullback_Limit {C : Category} (F : Cospan C) := Limit F.
Arguments Pullback_Limit {_%category} F%functor /.

Definition Pushout_Limit {C : Category} (F : Span C) := Colimit F.
Arguments Pushout_Limit {_%category} F%functor /.

Program Definition Pullback_to_Universal {C : Category}
        (F : Cospan C) (P : Pullback_Limit F) :
  Pullback (unop (fmap[F] ZeroNeg)) (unop (fmap[F] ZeroPos)) := {|
  Pull := P;
  pullback_fst := vertex_map;
  pullback_snd := vertex_map
|}.
Next Obligation.
  pose proof (@ump_cones _ _ _ P).
  unfold unop.
  rewrite !X.
  reflexivity.
Qed.
Next Obligation.
  given (cone : Cone F). {
    unshelve (refine {| vertex_obj := Q |}); intros.
      destruct x; auto.
      exact (unop (fmap[F] ZeroPos) ∘ q2).
    simpl;
    destruct x, y; auto with roof_laws; simpl in f;
    rewrite (RoofHom_inv _ _ f); cat.
  }
  destruct P, limit_cone; simpl in *.
  exists (unique_morphism (ump_limits cone)). {
    split;
    [ pose proof (unique_property (ump_limits cone) RNeg)
    | pose proof (unique_property (ump_limits cone) RPos) ];
    unfold cone in *; simpl in *; clear cone;
    rewrites; reflexivity.
  }
  intros.
  apply (uniqueness (ump_limits cone)); intros.
  simpl in *.
  destruct x, X0; simpl; auto.
  rewrites.
  rewrite comp_assoc.
  unfold unop.
  rewrite ump_cones.
  reflexivity.
Qed.

Program Definition Pullback_from_Universal {C : Category}
        {x y z : C} (f : x ~> z) (g : y ~> z) (P : Pullback f g) :
  Pullback_Limit (@ASpan (C^op) _ _ _ f g)^op := {|
  limit_cone := {| vertex_obj := P |}
|}.
Next Obligation.
  destruct x0;
  destruct P; simpl in *; auto.
  exact (f ∘ pullback_fst).
Defined.
Next Obligation.
  destruct x0, y0;
  destruct P; simpl in *; auto with roof_laws; cat.
Qed.
Next Obligation.
  destruct P, N; simpl in *.
  assert (eqv : f ∘ vertex_map RNeg ≈ g ∘ vertex_map RPos).
    rewrite (ump_cones RNeg RZero ZeroNeg).
    rewrite (ump_cones RPos RZero ZeroPos).
    reflexivity.
  unfold Pullback_from_Universal_obligation_1; simpl.
  destruct (ump_pullbacks vertex_obj (vertex_map RNeg) (vertex_map RPos) eqv).
  construct; simplify; auto.
    destruct x0; auto.
    rewrite <- comp_assoc.
    rewrite unique_property.
    apply (ump_cones RNeg RZero ZeroNeg).
  apply uniqueness.
  split.
    apply (X RNeg).
  apply (X RPos).
Defined.
