Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Span.
Require Import Category.Structure.Pullback.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Roof.

Generalizable All Variables.

Definition Pullback_Limit {C : Category} (F : Cospan C) := Limit F.
Arguments Pullback_Limit {_%category} F%functor /.

Definition Pushout_Limit {C : Category} (F : Span C) := Colimit F.
Arguments Pushout_Limit {_%category} F%functor /.

Program Definition Pullback_to_Universal {C : Category}
        (F : Cospan C) (P : Pullback_Limit F) :
  Pullback (unop (fmap[F] ZeroNeg)) (unop (fmap[F] ZeroPos)) := {|
  Pull := P;
  pullback_fst := (vertex_map _);
  pullback_snd := (vertex_map _)
|}.
Next Obligation.
  pose proof (@cone_coherence _ (@vertex_obj  _ _ _ (limit_cone)) _ F (coneFrom)).
  unfold unop.
  rewrite !X.
  reflexivity.
Qed.
Next Obligation.
  given (cone : Cone F). {
    unshelve (refine {| vertex_obj := Q |}); unshelve econstructor; intros.
    - destruct x; auto.
      exact (unop (fmap[F] ZeroPos) ∘ q2).
    - simpl;
      destruct x, y; auto with roof_laws; simpl in f;
      rewrite (RoofHom_inv _ _ f); cat.
  }
  destruct P, limit_cone; simpl in *.
  exists (unique_obj (ump_limits cone)). {
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
  rewrite cone_coherence.
  reflexivity.
Qed.

Program Definition Pullback_from_Universal {C : Category}
        {x y z : C} (f : x ~> z) (g : y ~> z) (P : Pullback f g) :
  Pullback_Limit (@ASpan (C^op) _ _ _ f g)^op := {|
  limit_cone := {| vertex_obj := P ; coneFrom := {| vertex_map := _; cone_coherence := _ |} |}
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
  destruct P, N, coneFrom; simpl in *.
  assert (eqv : f ∘ (vertex_map RNeg) ≈
                  g ∘ (vertex_map RPos)). {
    rewrite (cone_coherence RNeg RZero ZeroNeg).
    rewrite (cone_coherence RPos RZero ZeroPos).
    reflexivity.
  }
  unfold Pullback_from_Universal_obligation_1; simpl.
  destruct (ump_pullbacks vertex_obj (vertex_map RNeg) (vertex_map RPos) eqv).
  construct; simplify; auto.
  - destruct x0; auto.
    rewrite <- comp_assoc.
    rewrite unique_property.
    apply (cone_coherence RNeg RZero ZeroNeg).
  - apply uniqueness.
    split.
    + apply (X RNeg).
    + apply (X RPos).
Defined.
