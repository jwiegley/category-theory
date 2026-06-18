Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Comma.
Require Import Category.Instance.Cat.

Generalizable All Variables.

(** Huq's correspondence: natural transformations as sections of the comma
    projections. *)

(* nLab: https://ncatlab.org/nlab/show/comma+category
   Wikipedia: https://en.wikipedia.org/wiki/Comma_category

   Wikipedia: "If the domains of S, T are equal, then the diagram which
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

   This is also given in Mac Lane, page 47, exercise 4.

   The two definitions below realize the two directions of Huq's bijection for
   functors S T : D ⟶ C sharing the domain D (the "domains equal" case above).
   Comma_Functor sends a natural transformation F : S ⟹ T to the functor
   D ⟶ (S ↓ T) of the observation, X ↦ (X, X; F X) and f ↦ (f, f); it is a
   common section of comma_proj1 and comma_proj2 by construction. Comma_Transform
   is the inverse: from a functor F : D ⟶ (S ↓ T) together with witnesses that
   it is a section of both projections (comma_proj1 ◯ F ≈ Id and
   comma_proj2 ◯ F ≈ Id), it recovers a natural transformation S ⟹ T. *)

(* natural transformation S ⟹ T  ↦  section functor D ⟶ (S ↓ T) *)
Program Definition Comma_Functor {C D : Category} {S T : D ⟶ C}
        (F : S ⟹ T) : D ⟶ (S ↓ T) := {|
  fobj := fun X : D => ((X, X); F X);
  fmap := fun _ _ f => ((f, f); _)
|}.
Next Obligation. apply naturality_sym. Qed.

#[local] Obligation Tactic := simpl; intros.

(* section functor D ⟶ (S ↓ T) of both projections  ↦  natural transformation
   S ⟹ T (the inverse direction of Huq's bijection) *)
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
