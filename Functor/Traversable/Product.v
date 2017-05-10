Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Product.
Require Export Category.Functor.Strong.
Require Export Category.Functor.Strong.Product.
Require Export Category.Functor.Monoidal.
Require Export Category.Functor.Monoidal.Product.
Require Export Category.Structure.Monoidal.
Require Export Category.Functor.Traversable.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section ProductTraversable.

Context `{C : Category}.
Context `{@Monoidal C}.
Context `{F : C ⟶ C}.
Context `{G : C ⟶ C}.

Local Obligation Tactic := program_simpl.

Lemma ProductFunctor_Traversable_ap_functor_nat :
  Traversable F → Traversable G
    → ∀ H : (C ∏ C) ⟶ C ∏ C,
      StrongFunctor H → LaxMonoidalFunctor H → F ∏⟶ G ○ H ⟹ H ○ F ∏⟶ G.
Proof.
  intros O P ???.

  natural.
    intros [x y]; split.
      pose (transform[@sequence _ _ _ O
                        (ProductFunctor_fst H0)
                        (ProductFunctor_fst_Strong H0 X)
                        (ProductFunctor_fst_LaxMonoidal H0 X0)] x).
      simpl in *.
      (* sequence wants [I ~> I], but we need to plumb [y ~> G y] there. *)
Abort.
(*
    exact (transform[ap_functor_nat] (z, w)).

  all:(try destruct X as [[x1 x2] [y1 y2]],
                    Y as [[z1 z2] [w1 w2]],
                    f as [[f1a f1b] [f2a f2b]];
       try destruct A as [[x z] [y w]]; simpl).

  split.
    abstract apply (naturality ap_functor_nat (x1, y1)).
  abstract apply (naturality ap_functor_nat (x2, y2)).
Defined.
*)

(*
Program Definition ProductFunctor_Traversable :
  Traversable F -> Traversable G
    -> Traversable (F ∏⟶ G) := fun _ _ => {|
  sequence := _; (* ProductFunctor_Traversable_ap_functor_nat _ _; *)
  sequence_id  := _;
  sequence_comp  := _
|}.

Lemma ProductFunctor_Traversable_proj1_ap_functor_nat :
  Traversable F ∏⟶ G
    → (⨂) ○ F ∏⟶ F ⟹ F ○ (⨂).

Program Definition ProductFunctor_Traversable_proj1 :
  Traversable (F ∏⟶ G) -> Traversable F := fun P => {|
  lax_pure := _;
  ap_functor_nat := ProductFunctor_Traversable_proj1_ap_functor_nat P;
  pure_left  := _;
  pure_right := _;
  ap_assoc := _;
  lax_monoidal_unit_left := _;
  lax_monoidal_unit_right := _;
  lax_monoidal_assoc := _
|}.

Lemma ProductFunctor_Traversable_proj2_ap_functor_nat :
  Traversable F ∏⟶ G
    → (⨂) ○ G ∏⟶ G ⟹ G ○ (⨂).

Program Definition ProductFunctor_Traversable_proj2 :
  Traversable (F ∏⟶ G) -> Traversable G := fun P => {|
  lax_pure := _;
  ap_functor_nat := ProductFunctor_Traversable_proj2_ap_functor_nat P;
  pure_left  := _;
  pure_right := _;
  ap_assoc := _;
  lax_monoidal_unit_left := _;
  lax_monoidal_unit_right := _;
  lax_monoidal_assoc := _
|}.
*)

End ProductTraversable.

Section ProductTraversableProj.

Context `{C : Category}.
Context `{@Monoidal C}.
Context `{F : C ⟶ C}.
Context `{G : C ⟶ C}.

(*
Lemma ProductFunctor_fst_Traversable_ap_functor_nat :
  Traversable P
    → (⨂) ○ (ProductFunctor_fst P) ∏⟶ (ProductFunctor_fst P)
          ⟹ ProductFunctor_fst P ○ (⨂).

Local Obligation Tactic := program_simpl.

Program Definition ProductFunctor_fst_Traversable :
  Traversable P
    -> Traversable (ProductFunctor_fst P) := fun L => {|
  lax_pure := _;
  ap_functor_nat := ProductFunctor_fst_Traversable_ap_functor_nat L;
  pure_left  := _;
  pure_right := _;
  ap_assoc := _;
  lax_monoidal_unit_left := _;
  lax_monoidal_unit_right := _;
  lax_monoidal_assoc := _
|}.

Lemma ProductFunctor_snd_Traversable_ap_functor_nat :
  Traversable P
    → (⨂) ○ (ProductFunctor_snd P) ∏⟶ (ProductFunctor_snd P)
          ⟹ ProductFunctor_snd P ○ (⨂).

Program Definition ProductFunctor_snd_Traversable :
  Traversable P
    -> Traversable (ProductFunctor_snd P) := fun L => {|
  lax_pure := _;
  ap_functor_nat := ProductFunctor_snd_Traversable_ap_functor_nat L;
  pure_left  := _;
  pure_right := _;
  ap_assoc := _;
  lax_monoidal_unit_left := _;
  lax_monoidal_unit_right := _;
  lax_monoidal_assoc := _
|}.

Corollary ProductFunctor_proj_Traversable :
  Traversable P
    -> Traversable ((ProductFunctor_fst P) ∏⟶ (ProductFunctor_snd P)).
*)

End ProductTraversableProj.
