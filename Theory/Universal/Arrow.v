Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Initial.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Comma.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.

Generalizable All Variables.

Section UniversalArrow.

Context `{C : Category}.
Context `{D : Category}.

(* A universal arrow is an initial object in the comma category (=(c) ↓ F). *)
Class UniversalArrow (c : C) (F : D ⟶ C) := {
  arrow_initial : @Initial (=(c) ↓ F);

  arrow_obj := snd (`1 (@initial_obj _ arrow_initial));
  arrow : c ~> F arrow_obj := `2 (@initial_obj _ arrow_initial)
}.

Notation "c ⟿ F" := (UniversalArrow c F) (at level 20) : category_theory_scope.

(* The following UMP follows directly from the nature of initial objects in a
   comma category. *)
Corollary ump_universal_arrows `(c ⟿ F) `(h : c ~> F d) :
  ∃! g : arrow_obj ~> d, h ≈ fmap[F] g ∘ arrow.
Proof.
  unfold arrow_obj, arrow; simpl.
  destruct (@zero _ arrow_initial ((ttt, d); h)), x.
  simpl in *.
  rewrite id_right in e.
  exists h1.
  - assumption.
  - intros.
    rewrite <- id_right in e.
    rewrite <- id_right in X.
    exact (snd (@zero_unique _ arrow_initial ((ttt, d); h)
                             ((ttt, h1); e) ((ttt, v); X))).
Qed.



Class AUniversalArrow (c : C) (F : D ⟶ C) (a : D) := {
    universal_arrow : c ~> fobj[F] a ;
    universal_arrow_universal {d} {f : c ~> (fobj[F] d)} :
    Unique (fun g : hom a d => fmap[F] g ∘ universal_arrow ≈ f)
  }.

#[export] Program Instance AUniversalArrowEquiv (c : C) (F : D ⟶ C) (a : D) :
  Setoid (AUniversalArrow c F a) :=
  {| equiv := fun X Y => (@universal_arrow _ _ _ X) ≈ (@universal_arrow _ _ _ Y) |}.

End UniversalArrow.
