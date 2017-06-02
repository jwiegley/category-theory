Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Adjunction.Natural.Transformation.
Require Export Category.Adjunction.Natural.Transformation.Universal.
Require Export Category.Construction.Comma.
Require Export Category.Construction.Comma.Adjunction.Lib.
Require Export Category.Construction.Product.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section AdjunctionComma.

(* Wikipedia: "Lawvere showed that the functors F : C → D and G : D → C are
   adjoint if and only if the comma categories (F ↓ Id[D]) and (Id[C] ↓ G) are
   isomorphic, and equivalent elements in the comma category can be projected
   onto the same element of C × D. This allows adjunctions to be described
   without involving sets, and was in fact the original motivation for
   introducing comma categories."

   From ncatlab: "To give an adjunction i ⊣ r it suffices to give, for each k
   : x → pe in B ↓ p, an object rk in E such that prk = x and an arrow irk =
   1x → k in B ↓ p that is universal from i to k."

   Lawvere's own statement of the theorem, from his thesis (page 40):

   "For each functor f : A ⟶ B, there exists a functor g : B ⟶ A such that g
   is adjoint to f iff for every object B ∈ |B| there exists an object A ∈ |A|
   and a map φ : B ~> Af in B such that for every object A′ ∈ |A| and every
   map x : B ~> A′f in B, there exists a unique map y : A ~> A′ in A such that
   x = φ(yf) in B."

   Repeating this using the names and syntax of this module:

   "∀ (G : C ⟶ D) (F : D ⟶ C), F ⊣ G <-->
      ∀ d : D, ∃ (c : C) (phi : d ~{D}~> G c),
        ∀ (c′ : C) (psi : d ~{D}~> G c′), ∃! y : c ~{C}~> c′,
          psi ≈ fmap[G] y ∘ phi" *)

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {G : C ⟶ D}.

Definition fiber_eqv_unit (E : @fibered_equivalence _ _ F G) {a} :
  a ~{ D }~> G (F a) :=
  fmap (snd (``(projF E) (Left_Functor a))⁻¹)
    ∘ projT2 (to (fiber_iso E) (Left_Functor a))
    ∘ fst (to (``(projF E) (Left_Functor a))).

Definition fiber_eqv_counit (E : @fibered_equivalence _ _ F G) {a} :
  F (G a) ~{ C }~> a :=
  snd (``(projG E) (Right_Functor a))⁻¹
    ∘ projT2 ((fiber_iso E)⁻¹ (Right_Functor a))
    ∘ fmap (fst (to (``(projG E) (Right_Functor a)))).

Set Transparent Obligations.

Program Definition fiber_eqv_unit_transform (E : @fibered_equivalence _ _ F G) :
  Id ⟹ G ○ F := {|
  transform := _ fiber_eqv_unit;
  naturality := fun X Y f =>
    Left_Functoriality E X Y (f, fmap[F] f);
  naturality_sym := fun X Y f =>
    symmetry (Left_Functoriality E X Y (f, fmap[F] f))
|}.

Program Definition fiber_eqv_counit_transform (E : @fibered_equivalence _ _ F G) :
  F ○ G ⟹ Id := {|
  transform := _ fiber_eqv_counit;
  naturality := fun X Y f =>
    Right_Functoriality E X Y (fmap[G] f, f);
  naturality_sym := fun X Y f =>
    symmetry (Right_Functoriality E X Y (fmap[G] f, f))
|}.

Program Instance comma_projG_iso (E : @fibered_equivalence _ _ F G) f :
  `1 f ≅ `1 (from (fiber_iso E) f) := (`1 (projG E) f).

Definition comma_from (E : @fibered_equivalence _ _ F G)
           a b (f : a ~> G b) : F a ~> b :=
  snd (comma_projG_iso E ((a, b); f))⁻¹
    ∘ `2 (from (fiber_iso E) ((a, b); f))
    ∘ fmap[F] (fst (to (comma_projG_iso E ((a, b); f)))).

Lemma fiber_eqv_counit_fmap_unit (E : @fibered_equivalence _ _ F G) {a} :
  fiber_eqv_counit E ∘ fmap[F] (fiber_eqv_unit E) ≈ id[F a].
Proof.
  simpl; intros.
  pose proof (naturality[fiber_eqv_counit_transform E]); simpl in X.
  unfold fiber_eqv_counit_transform_obligation_1 in X.
  unfold fiber_eqv_unit.
  do 2 rewrite fmap_comp.
  do 2 rewrite comp_assoc.
  rewrite <- X.
  rewrite <- !comp_assoc.
  remember (_ ∘ (fiber_eqv_counit E ∘ _)) as p.
  pose proof (@monic _ _ _ _ (iso_monic (`1 (projF E) (Left_Functor a)))
                     (a, F a) (id, p) (id, id)).
  simpl in X0.
  refine (snd (X0 _)).
  split.
    reflexivity.
  clear X0.
  rewrite Heqp; clear Heqp p.
  rewrite !comp_assoc.
  rewrite (snd (iso_to_from (`1 (projF E) (Left_Functor a)))).
  rewrite id_left, id_right.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
Admitted.                       (* DEFERRED *)

Lemma fiber_eqv_fmap_counit_unit (E : @fibered_equivalence _ _ F G) {a} :
  fmap[G] (fiber_eqv_counit E) ∘ fiber_eqv_unit E ≈ id[G a].
Proof.
  simpl; intros.
  pose proof (naturality[fiber_eqv_unit_transform E]); simpl in X.
  unfold fiber_eqv_unit_transform_obligation_1 in X.
  unfold fiber_eqv_counit.
  do 2 rewrite fmap_comp.
  do 2 rewrite <- comp_assoc.
  rewrite X.
  rewrite !comp_assoc.
  remember ((_ ∘ fiber_eqv_unit E) ∘ _) as p.
  pose proof (@epic _ _ _ _ (iso_from_epic (`1 (projG E) (Right_Functor a)))
                     (G a, a) (p, id) (id, id)).
  simpl in X0.
  refine (fst (X0 _)).
  split; [|reflexivity].
  clear X0.
  rewrite Heqp; clear Heqp p.
  rewrite <- !comp_assoc.
Admitted.                       (* DEFERRED *)

Theorem Adjunction_Comma : F ⊣ G  <-->  @fibered_equivalence _ _ F G.
Proof.
  split; intros H. {
    refine {| fiber_iso := Comma_F_Id_Id_G_Iso H |}.
    - abstract (
        simpl; unshelve eexists; intros; split;
        destruct f; simpl; cat).
    - abstract (
        simpl; unshelve eexists; intros; split;
        destruct f; simpl; cat).
  }

  apply Adjunction_from_Transform.

  exact (Build_Adjunction_Transform
           (fiber_eqv_unit_transform H)
           (fiber_eqv_counit_transform H)
           (@fiber_eqv_counit_fmap_unit H)
           (@fiber_eqv_fmap_counit_unit H)).
Qed.

End AdjunctionComma.
