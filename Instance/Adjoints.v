Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** The category of adjunctions. *)

(* nLab: https://ncatlab.org/nlab/show/adjoint+functor
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors#Composition

   Adjunctions can be composed: the identity functor is self-adjoint
   (Id ⊣ Id, [adj_id]), and given F ⊣ U and F' ⊣ U' the composites are again
   adjoint, with the left adjoints composing covariantly and the right adjoints
   contravariantly,

       F ⊣ U  →  F' ⊣ U'  →  F ◯ F' ⊣ U' ◯ U     ([adj_comp]).

   (Recall F ◯ G applies G then F, so F ◯ F' is the left adjoint and U' ◯ U the
   right adjoint of the composite.) This is exactly what is needed to organize
   categories and adjunctions into a category [Adjoints]:

       objects        Categories
       arrows         Adjunctions F ⊣ U between categories
       identity       Id ⊣ Id
       composition    F ⊣ U → F' ⊣ U' → F ◯ F' ⊣ U' ◯ U

   Two adjunctions are identified when their left and right adjoints are
   correspondingly naturally isomorphic ([adj_morphism_setoid]). Choosing the
   left adjoint as the "forward" direction is an arbitrary but harmless
   convention; see the closing note on InvAdj for the involutive refinement that
   removes the choice. *)

(* The identity functor is its own left and right adjoint: the transpose iso
   F x ~> y ≅ x ~> U y is the identity on hom-sets when F = U = Id. *)
#[export]
Program Instance adj_id {C : Category} : Id ⊣ Id := {
  adj := fun _ _ =>
    {| to   := {| morphism := _ |}
     ; from := {| morphism := _ |} |}
}.

(* Composite of two adjunctions. The transpose iso for F ◯ F' ⊣ U' ◯ U is the
   composite of the two component transposes,

       F (F' a) ~> b  ≅[X]  F' a ~> U b  ≅[Y]  a ~> U' (U b),

   so ⌊-⌋ of the composite is ⌊-⌋ ∘ ⌊-⌋ and its inverse runs the two ⌈-⌉ in the
   opposite order. *)
Program Definition adj_comp
        {C : Category} {D : Category} {E : Category}
        (F : D ⟶ C) (U : C ⟶ D) (F' : E ⟶ D) (U' : D ⟶ E)
        (X : F ⊣ U) (Y : F' ⊣ U') :
  F ◯ F' ⊣ U' ◯ U := {|
  adj := fun a b =>
    {| to   := {| morphism := fun (f : F (F' a) ~> b) => to adj (to adj f) |}
     ; from := {| morphism := fun (f : a ~> U' (U b)) => adj⁻¹ (adj⁻¹ f) |} |}
|}.
Next Obligation. proper. rewrites; reflexivity. Qed.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation.
  srewrite (@iso_to_from _ _ _ (@adj C D F U X (F' a) b)).
  sapply (@iso_to_from _ _ _ (@adj D E F' U' Y a (U b))).
Qed.
Next Obligation.
  srewrite (@iso_from_to _ _ _ (@adj D E F' U' Y a (U b))).
  sapply (@iso_from_to _ _ _ (@adj C D F U X (F' a) b)).
Qed.
Next Obligation. rewrite <- !to_adj_nat_l; reflexivity. Qed.
Next Obligation. rewrite <- !to_adj_nat_r; reflexivity. Qed.
Next Obligation. rewrite <- !from_adj_nat_l; reflexivity. Qed.
Next Obligation. rewrite <- !from_adj_nat_r; reflexivity. Qed.

Notation "F ⊚ G" := (@adj_comp _ _ _ _ _ _ _ F G)
  (at level 30, right associativity) : category_scope.

(* An arrow C ⇸ D in [Adjoints]: a left/right adjoint pair, the left adjoint
   ("free") taken as the forward direction. *)
Record adj_morphism {C : Category} {D : Category} := {
  free_functor : D ⟶ C;                       (* the left adjoint  *)
  forgetful_functor : C ⟶ D;                  (* the right adjoint *)
  adjunction : free_functor ⊣ forgetful_functor
}.

Local Set Warnings "-intuition-auto-with-star".

(* Two adjunctions are equal when their left adjoints are naturally isomorphic
   and their right adjoints are naturally isomorphic (in the functor category
   [Fun]); the conjugate-pair correspondence then makes the choice coherent. *)
#[export]
Program Instance adj_morphism_setoid {C : Category} {D : Category} :
  Setoid (@adj_morphism C D) := {
  equiv := fun f g =>
              (free_functor f ≅[Fun] free_functor g) *
              (forgetful_functor f ≅[Fun] forgetful_functor g)
}.
(* The relation is a pair of natural isomorphisms, so it is an equivalence
   componentwise, straight from [iso_equivalence] in [Theory.Isomorphism].
   Spelled out rather than left to [equivalence]: this obligation was proved
   by that tactic plus two transitivity bullets, and its reflexivity and
   symmetry components were being closed only because [equivalence] reached
   [solve_crelation], a pattern-less [Hint Extern] in the standard library's
   [crelations] database, through a wide [auto with *].  Which pattern-less
   hints a wide [auto] reaches, and in which order, is a property of the hint
   database rather than anything this library states; on Rocq master the
   reflexivity and symmetry components stopped being discharged, the first
   bullet landed on a symmetry goal instead of the transitivity one it was
   written for, and [assumption] had nothing to close
   [free_functor y ≅ free_functor y] with -- issue #213.  Proving the three
   laws directly removes the dependency.  See [Test/Issue213.v]. *)
Next Obligation.
  constructor.
  - intros f.
    split; reflexivity.
  - intros f g [Hfree Hforget].
    split; symmetry; assumption.
  - intros f g h [Hfree Hforget] [Hfree' Hforget'].
    split; etransitivity; eassumption.
Qed.

(* The category of Adjoints:

    objects                Categories
    arrows                 Adjunctions between categories
    identity               Id ⊣ Id
    composition            F ⊣ U → F' ⊣ U' → F ◯ F' ⊣ U' ◯ U *)

Program Definition Adjoints : Category := {|
  obj     := Category;
  hom     := @adj_morphism;
  homset  := @adj_morphism_setoid;
  id      := fun X => {| free_functor      := Id[X]
                  ; forgetful_functor := Id[X] |};
  compose := fun A B C f g =>
    {| adjunction :=
         @adj_comp A B C (free_functor g) (forgetful_functor g)
                   (free_functor f) (forgetful_functor f)
                   (adjunction g) (adjunction f) |}
|}.
Next Obligation.
  proper; simpl.
  - isomorphism; simpl.
    + transform; simpl; intros.
      * exact (fmap (transform[to X] _) ∘ transform[to X0] _).
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
    + transform; simpl; intros.
      * exact (fmap (transform[from X] _) ∘ transform[from X0] _).
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
    + simpl.
      rewrite naturality.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap (transform[to X] _))).
      rewrite <- fmap_comp.
      rewrite naturality.
      rewrite comp_assoc.
      destruct X; simpl in *.
      rewrite iso_to_from; cat.
      destruct X0; simpl in *.
      rewrite iso_to_from0; cat.
    + simpl.
      rewrite naturality.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap (transform[from X] _))).
      rewrite <- fmap_comp.
      rewrite naturality.
      rewrite comp_assoc.
      destruct X; simpl in *.
      rewrite iso_from_to; cat.
      destruct X0; simpl in *.
      rewrite iso_from_to0; cat.
  - isomorphism; simpl.
    + transform; simpl; intros.
      * exact (fmap (transform[to H] _) ∘ transform[to H0] _).
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
    + transform; simpl; intros.
      * exact (fmap (transform[from H] _) ∘ transform[from H0] _).
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
      * rewrite comp_assoc.
        rewrite <- fmap_comp.
        rewrite !naturality.
        rewrite <- comp_assoc.
        rewrite <- fmap_comp.
        reflexivity.
    + simpl.
      rewrite naturality.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap (transform[to H] _))).
      rewrite <- fmap_comp.
      rewrite naturality.
      rewrite comp_assoc.
      destruct H; simpl in *.
      rewrite iso_to_from; cat.
      destruct H0; simpl in *.
      rewrite iso_to_from0; cat.
    + simpl.
      rewrite naturality.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap (transform[from H] _))).
      rewrite <- fmap_comp.
      rewrite naturality.
      rewrite comp_assoc.
      destruct H; simpl in *.
      rewrite iso_from_to; cat.
      destruct H0; simpl in *.
      rewrite iso_from_to0; cat.
Qed.
Next Obligation.
  split; isomorphism;
  try (transform; simpl; intros; try exact id; cat); cat.
Qed.
Next Obligation.
  split; isomorphism;
  try (transform; simpl; intros; try exact id; cat); cat.
Qed.
Next Obligation.
  split; isomorphism;
  try (transform; simpl; intros; try exact id; cat); cat.
Qed.
Next Obligation.
  split; isomorphism;
  try (transform; simpl; intros; try exact id; cat); cat.
Qed.

(* The closing quote (Chris Heunen, on MathOverflow) describes InvAdj, the
   involutive refinement of [Adjoints] that removes the arbitrary forward/
   backward choice; it is defined in §3.1.8 of his thesis "Categorical Quantum
   Models and Logics":
   https://homepages.inf.ed.ac.uk/cheunen/publications/2009/thesis/thesis.pdf
   This library implements only the plain [Adjoints] above, not InvAdj. *)

(* mathoverflow: "You will have to make an arbitrary choice for the direction
   of morphisms: is the left adjoint "forward" or "backward"? To prevent that,
   you can add involutions. The resulting category [InvAdj] of involutive
   categories and adjunctions has a lot of interesting structure. It is a
   dagger category, and in fact the `mother of all dagger categories', as it
   universally embeds any dagger category. In particular, the full subcategory
   of (ortho)posets and Galois connections has dagger kernels, dagger
   biproducts, an an opclassifier. See these two papers. Now for the
   definition (from 3.1.8 of my thesis):

   A functor ∗ : C^op → C is called involutive when ∗ ∘ ∗ = Id. Define a
   category [InvAdj] as follows. Objects are pairs (C,∗) of a category with an
   involution. A morphism (C,∗) → (D,∗) is functor F : C^op → D that has a
   left adjoint, where two such functors are identified when they are
   naturally isomorphic. The identity morphism on (C,∗) is the functor ∗ :
   C^op → C ; its left adjoint is ∗^op : C → C^op. The composition of F : C^op
   → D and G : D^op → E is defined by G ∘ ∗^op ∘ F : C^op → E; its left
   adjoint is F′ ∘ ∗ ∘ G′, where F′ ⊣ F and G′ ⊣ G.

   (It is not arbitrary to require a left adjoint instead of a right one. A
   contravariant functor from C to D can be written both as a (covariant)
   functor F : C^op → D or as a (covariant) functor F^op : C → D^op. The
   latter version has a right adjoint precisely when the former version has a
   left adjoint.)" *)
