Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Natural.Transformation.
Require Export Category.Construction.Comma.
Require Export Category.Instance.Cat.
Require Export Category.Instance.Fun.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

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

Program Definition Comma_Functor {C : Category} {D : Category}
        {S : D ⟶ C} {T : D ⟶ C} (F : S ⟹ T) : D ⟶ (S ↓ T) := {|
  fobj := fun X : D => ((X, X); F X);
  fmap := fun _ _ f => (f, f)
|}.

Local Obligation Tactic := simpl; intros.

Program Definition Comma_Transform {C : Category} {D : Category}
        {S : D ⟶ C} {T : D ⟶ C} (F : D ⟶ (S ↓ T))
        (proj1_commutes : comma_proj1 ○ F ≈[Cat] Id)
        (proj2_commutes : comma_proj2 ○ F ≈[Cat] Id)
        (functoriality : ∀ X Y (g : X ~> Y),
           fmap[T] g ∘ fmap (to proj2_commutes X)
                     ∘ projT2 (F X)
                     ∘ fmap (from proj1_commutes X)
             ≈ fmap (to proj2_commutes Y)
                     ∘ projT2 (F Y)
                     ∘ fmap (from proj1_commutes Y)
                     ∘ fmap[S] g) :
  S ⟹ T := {|
  transform := fun X => _
|}.
Next Obligation.
  exact (fmap (to proj2_commutes X)
           ∘ projT2 (F X) ∘ fmap (from proj1_commutes X)).
Defined.
Next Obligation.
  unfold Comma_Transform_obligation_1.
  pose proof (functoriality X Y f).
  rewrite !comp_assoc.
  apply X0.
Qed.
