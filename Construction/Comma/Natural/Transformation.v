Set Warnings "-notation-overridden".
Set Warnings "-deprecated-hint-without-locality".

Require Import Category.Lib.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Construction.Comma.
Require Export Category.Instance.Cat.
Require Export Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* Wikipedia: "If the domains of S, T are equal, then the diagram which
   defines morphisms in S↓T with α=β, α′=β′, g=h is identical to the diagram
   which defines a natural transformation S ⟹ T. The difference between the
   two notions is that a natural transformation is a particular collection of
   morphisms of type of the form S(α) → T(α), while objects of the comma
   category contains all morphisms of type of such form. A functor to the
   comma category selects that particular collection of morphisms. This is
   described succinctly by an observation by Huq that a natural transformation
   η : S → T, with S, T : A → C, corresponds to a functor A → (S↓T) which maps
   each object α to (α, α, η α) and maps each morphism g to (g, g). This is a
   bijective correspondence between natural transformations S ⟹ T and functors
   A ⟶ (S↓T) which are sections of both forgetful functors from S↓T."

   This is also given in Mac Lane, page 47, exercise 4. *)

Program Definition Comma_Functor {C D : Category} {S T : D ⟶ C}
        (F : S ⟹ T) : D ⟶ (S ↓ T) := {|
  fobj := fun X : D => ((X, X); F X);
  fmap := fun _ _ f => ((f, f); _)
|}.
Next Obligation. apply naturality_sym. Qed.

Local Obligation Tactic := simpl; intros.

Program Definition Comma_Transform {C D : Category} {S T : D ⟶ C}
        (F : D ⟶ (S ↓ T))
        (proj1 : comma_proj1 ◯ F ≈[Cat] Id)
        (proj2 : comma_proj2 ◯ F ≈[Cat] Id) : S ⟹ T := {|
  transform := fun X =>
    fmap (to (`1 proj2 X)) ∘ `2 (F X) ∘ fmap (from (`1 proj1 X))
|}.
Next Obligation.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- !comp_assoc.
  rewrite <- fmap_comp.

  spose (`2 proj1 _ _ f) as X0.
  spose (`2 proj2 _ _ f) as X1.

  rewrite <- (id_left f) at 1.
  rewrite <- (iso_to_from (`1 proj2 y)).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ f).
  rewrites.
  rewrite fmap_comp.
  comp_left.

  symmetry.
  rewrite <- (id_right f) at 1.
  rewrite <- (iso_to_from (`1 proj1 x)).
  rewrite !comp_assoc.
  rewrites.
  rewrite fmap_comp.
  comp_right.

  exact (`2 (fmap[F] f)).
Qed.
Next Obligation.
  symmetry.
  apply Comma_Transform_obligation_1.
Qed.
