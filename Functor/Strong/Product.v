Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Bifunctor.
Require Export Category.Functor.Product.
Require Export Category.Functor.Strong.
Require Export Category.Structure.Cartesian.
Require Export Category.Structure.Monoidal.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section ProductStrong.

Context `{C : Category}.
Context `{@Monoidal C}.
Context `{@SymmetricMonoidal C _}.
Context `{@CartesianMonoidal C _}.
Context `{F : C ⟶ C}.
Context `{G : C ⟶ C}.

Local Obligation Tactic := idtac.

Lemma Product_Strong_strength_nat :
  StrongFunctor F -> StrongFunctor G
    -> (⨂) ○ (Id[C]) ∏⟶ (F :*: G) ⟹ F :*: G ○ (⨂).
Proof.
  simpl; intros O P.
  natural.
  - intros [x y]; simpl.
    enough (x ⨂ F y ⨂ G y ~> (x ⨂ F y) ⨂ (x ⨂ G y)).
      exact (bimap (transform[@strength_nat _ _ _ O] (x, y))
                   (transform[@strength_nat _ _ _ P] (x, y)) ∘ X).
    exact
      ((from tensor_assoc
          : x ⨂ (F y ⨂ (x ⨂ G y)) ~> (x ⨂ F y) ⨂ (x ⨂ G y)) ∘
       (bimap id (to tensor_assoc)
          : x ⨂ ((F y ⨂ x) ⨂ G y) ~> x ⨂ (F y ⨂ (x ⨂ G y))) ∘
       (bimap id (bimap (to sym_swap) id)
          : x ⨂ ((x ⨂ F y) ⨂ G y) ~> x ⨂ ((F y ⨂ x) ⨂ G y)) ∘
       (bimap (id[x]) (from tensor_assoc)
          : x ⨂ (x ⨂ (F y ⨂ G y)) ~> x ⨂ ((x ⨂ F y) ⨂ G y)) ∘
       (to tensor_assoc
          : (x ⨂ x) ⨂ (F y ⨂ G y) ~> x ⨂ (x ⨂ (F y ⨂ G y))) ∘
       (bimap diagonal (id[F y ⨂ G y])
          : x ⨂ (F y ⨂ G y) ~> (x ⨂ x) ⨂ (F y ⨂ G y))).
  - destruct X, Y, f; simpl in *.
    rewrite comp_assoc.
    rewrite <- bimap_comp.
    rewrite !bimap_fmap.
    rewrite <- !comp_assoc.
    rewrite (comp_assoc (bimap _ _)).
    rewrite (comp_assoc (bimap _ _)).
    rewrite <- !bimap_comp.
    rewrite (comp_assoc (bimap _ _)).
    rewrite <- !bimap_comp.
    symmetry.
    rewrite (comp_assoc (bimap _ _)).
    rewrite (comp_assoc (bimap _ _)).
    rewrite <- !bimap_comp.
    rewrite (comp_assoc (bimap _ _)).
    rewrite <- !bimap_comp.
    symmetry.
    rewrite !comp_assoc.
    rewrite !id_left.
    pose proof (naturality[@strength_nat _ _ _ O] (o, o0) (o1, o2) (h, h0));
    simpl in X; rewrite !X; clear X.
    pose proof (naturality[@strength_nat _ _ _ P] (o, o0) (o1, o2) (h, h0));
    simpl in X; rewrite !X; clear X.
    rewrite bimap_comp.
    rewrite <- !comp_assoc.
    apply compose_respects; [reflexivity|].
    rewrite !bimap_fmap.
    symmetry.
    rewrite !comp_assoc.
    pose proof (@pentagon_identity _ _ o o0 o1 o2).
Admitted.

Program Definition Product_Strong :
  StrongFunctor F -> StrongFunctor G -> StrongFunctor (F :*: G) := fun O P => {|
  strength_nat := Product_Strong_strength_nat O P;
  strength_id_left := _;
  strength_assoc := _
|}.
Next Obligation.
Admitted.
Next Obligation.
Admitted.

End ProductStrong.
