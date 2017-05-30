Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Adjunction.Natural.Transformation.
Require Export Category.Adjunction.Natural.Transformation.Isomorphism.
Require Export Category.Construction.Comma.
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
Context {G : C ⟶ D}.
Context {F : D ⟶ C}.

Record fibered_equivalence := {
  fiber_iso : (F ↓ Id[C]) ≅[Cat] (Id[D] ↓ G);

  projG : comma_proj ≈[Cat] comma_proj ○ from fiber_iso;
  projF : comma_proj ≈[Cat] comma_proj ○ to fiber_iso
}.

Program Definition Left_Functor : D ⟶ (F ↓ Id[C]) := {|
  fobj := fun X : D => ((X, F X); id[F X]);
  fmap := fun _ _ f => ((f, fmap[F] f); _)
|}.
Next Obligation.
  proper.
  rewrite X0; reflexivity.
Qed.
Next Obligation.
  split.
    reflexivity.
  apply fmap_comp.
Qed.

Program Definition Right_Functor : C ⟶ (Id[D] ↓ G) := {|
  fobj := fun X : C => ((G X, X); id[G X]);
  fmap := fun _ _ f => ((fmap[G] f, f); _)
|}.
Next Obligation.
  proper.
  rewrite X0; reflexivity.
Qed.
Next Obligation.
  split.
    apply fmap_comp.
  reflexivity.
Qed.

Lemma Left_Functoriality (eqv : fibered_equivalence) X Y
      (f : comma_proj (Left_Functor X) ~> comma_proj (Left_Functor Y)) :
  fmap[G] (fmap[F] (fst f))
    ∘ (fmap[G] (snd (`1 (projF eqv) (Left_Functor X))⁻¹)
         ∘ `2 (to (fiber_iso eqv) (Left_Functor X))
         ∘ fst (to (`1 (projF eqv) (Left_Functor X))))
    ≈ fmap[G] (snd (`1 (projF eqv) (Left_Functor Y))⁻¹)
        ∘ `2 (to (fiber_iso eqv) (Left_Functor Y))
        ∘ fst (to (`1 (projF eqv) (Left_Functor Y)))
        ∘ fst f.
Proof.
  Opaque Left_Functor.
  given (ff :
    { f : (fst `1 (Left_Functor X) ~{ D }~> fst `1 (Left_Functor Y)) *
          (snd `1 (Left_Functor X) ~{ C }~> snd `1 (Left_Functor Y))
    & `2 (Left_Functor Y) ∘ fmap[F] (fst f) ≈ snd f ∘ `2 (Left_Functor X) }).
    exists (fst f, fmap[F] (fst f)).
    abstract (simpl; rewrite id_left, id_right; reflexivity).
  destruct (`2 (projF eqv) (Left_Functor X) (Left_Functor Y) ff).
  simpl in *.
  rewrite e0.
  do 2 rewrite fmap_comp.
  comp_left.
  rewrite (comp_assoc (fmap[G] (snd (to (`1 (projF eqv) (Left_Functor X)))))).
  rewrite <- fmap_comp.
  rewrite (snd (iso_to_from (`1 (projF eqv) (Left_Functor X)))).
  simpl snd.
  rewrite fmap_id.
  rewrite id_left.
  symmetry.
  pose proof (`2 (fmap[to (fiber_iso eqv)] ff)).
  simpl in X0.
  rewrite !comp_assoc.
  rewrite <- X0.
  comp_left.
  rewrite e at 1.
  comp_right.
  rewrite (fst (iso_to_from (`1 (projF eqv) (Left_Functor Y)))).
  rewrite id_left.
  reflexivity.
Qed.

Lemma Right_Functoriality (eqv : fibered_equivalence) X Y
      (f : comma_proj (Right_Functor X) ~> comma_proj (Right_Functor Y)) :
  snd f ∘ (snd (`1 (projG eqv) (Right_Functor X))⁻¹
        ∘ `2 ((fiber_iso eqv)⁻¹ (Right_Functor X))
        ∘ fmap[F] (fst (to (`1 (projG eqv) (Right_Functor X)))))
  ≈ snd (`1 (projG eqv) (Right_Functor Y))⁻¹
      ∘ `2 ((fiber_iso eqv)⁻¹ (Right_Functor Y))
      ∘ fmap[F] (fst (to (`1 (projG eqv) (Right_Functor Y))))
      ∘ fmap[F] (fmap[G] (snd f)).
Proof.
  Opaque Right_Functor.
  given (ff :
    { f : (fst `1 (Right_Functor X) ~{ D }~> fst `1 (Right_Functor Y)) *
          (snd `1 (Right_Functor X) ~{ C }~> snd `1 (Right_Functor Y))
    & `2 (Right_Functor Y) ∘ fst f ≈ fmap[G] (snd f) ∘ `2 (Right_Functor X) }).
    exists (fmap[G] (snd f), snd f).
    abstract (simpl; rewrite id_left, id_right; reflexivity).
  destruct (`2 (projG eqv) (Right_Functor X) (Right_Functor Y) ff).
  simpl in *.
  symmetry.
  rewrite e.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite !comp_assoc.
  rewrite (fst (iso_to_from (`1 (projG eqv) (Right_Functor Y)))).
  rewrite id_left.
  symmetry.
  rewrite e0 at 1.
  comp_left.
  rewrite (comp_assoc (snd (to (`1 (projG eqv) (Right_Functor X))))).
  rewrite (snd (iso_to_from (`1 (projG eqv) (Right_Functor X)))).
  rewrite id_left.
  rewrite fmap_comp.
  comp_right.
  symmetry.
  apply (`2 (fmap[from (fiber_iso eqv)] ff)).
Qed.

Program Definition Comma_Functor_F_Id_Id_G (H : F ⊣ G) :
  (F ↓ Id[C]) ⟶ (Id[D] ↓ G) := {|
  fobj := fun x => (``x; to adj (`2 x));
  fmap := fun _ _ f => (``f; _)
|}.
Next Obligation.
  rewrite <- to_adj_nat_r;
  rewrite <- X;
  rewrite <- to_adj_nat_l;
  reflexivity.
Qed.

Program Definition Comma_Functor_Id_G_F_Id (H : F ⊣ G) :
  (Id[D] ↓ G) ⟶ (F ↓ Id[C]) := {|
  fobj := fun x => (``x; from adj (`2 x));
  fmap := fun _ _ f => (``f; _)
|}.
Next Obligation.
  rewrite <- from_adj_nat_r;
  rewrite <- X;
  rewrite <- from_adj_nat_l;
  reflexivity.
Qed.

Program Instance Comma_F_Id_Id_G_Iso (H : F ⊣ G) :
  (F ↓ Id[C]) ≅[Cat] (Id[D] ↓ G) := {
  to   := Comma_Functor_F_Id_Id_G H;
  from := Comma_Functor_Id_G_F_Id H
}.
Next Obligation.
  constructive; simpl.
  - exists (id, id); cat.
    srewrite (iso_to_from (@adj _ _ _ _ H x y)); reflexivity.
  - exists (id, id); cat.
    srewrite (iso_to_from (@adj _ _ _ _ H x y)); reflexivity.
  - clear; simpl; split; cat.
  - clear; simpl; split; cat.
  - clear; simpl; split; cat.
Qed.
Next Obligation.
  constructive; simpl.
  - exists (id, id); cat.
    srewrite (iso_from_to (@adj _ _ _ _ H x y)); reflexivity.
  - exists (id, id); cat.
    srewrite (iso_from_to (@adj _ _ _ _ H x y)); reflexivity.
  - clear; simpl; split; cat.
  - clear; simpl; split; cat.
  - clear; simpl; split; cat.
Qed.

Definition fiber_eqv_unit (eqv : fibered_equivalence) {a} : a ~{ D }~> G (F a) :=
  fmap (snd (``(projF eqv) (Left_Functor a))⁻¹)
    ∘ projT2 (to (fiber_iso eqv) (Left_Functor a))
    ∘ fst (to (``(projF eqv) (Left_Functor a))).

Definition fiber_eqv_counit (eqv : fibered_equivalence) {a} : F (G a) ~{ C }~> a :=
  snd (``(projG eqv) (Right_Functor a))⁻¹
    ∘ projT2 ((fiber_iso eqv)⁻¹ (Right_Functor a))
    ∘ fmap (fst (to (``(projG eqv) (Right_Functor a)))).

Set Transparent Obligations.

Program Definition fiber_eqv_unit_transform (eqv : fibered_equivalence) :
  Id ⟹ G ○ F := {|
  transform := _ fiber_eqv_unit;
  naturality := fun X Y f =>
    Left_Functoriality eqv X Y (f, fmap[F] f);
  naturality_sym := fun X Y f =>
    symmetry (Left_Functoriality eqv X Y (f, fmap[F] f))
|}.

Program Definition fiber_eqv_counit_transform (eqv : fibered_equivalence) :
  F ○ G ⟹ Id := {|
  transform := _ fiber_eqv_counit;
  naturality := fun X Y f =>
    Right_Functoriality eqv X Y (fmap[G] f, f);
  naturality_sym := fun X Y f =>
    symmetry (Right_Functoriality eqv X Y (fmap[G] f, f))
|}.

Lemma fiber_eqv_counit_fmap_unit (eqv : fibered_equivalence) {a} :
  fiber_eqv_counit eqv ∘ fmap[F] (fiber_eqv_unit eqv) ≈ id[F a].
Proof.
  simpl; intros.
  pose proof (naturality[fiber_eqv_counit_transform eqv]); simpl in X.
  unfold fiber_eqv_counit_transform_obligation_1 in X.
  unfold fiber_eqv_unit.
  do 2 rewrite fmap_comp.
  do 2 rewrite comp_assoc.
  rewrite <- X.
  rewrite <- !comp_assoc.
  remember (_ ∘ (fiber_eqv_counit eqv ∘ _)) as p.
  pose proof (@monic _ _ _ _ (iso_monic (`1 (projF eqv) (Left_Functor a)))
                     (a, F a) (id, p) (id, id)).
  simpl in X0.
  refine (snd (X0 _)).
  split.
    reflexivity.
  clear X0.
  rewrite Heqp; clear Heqp p.
  rewrite !comp_assoc.
  rewrite (snd (iso_to_from (`1 (projF eqv) (Left_Functor a)))).
  rewrite id_left, id_right.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  destruct eqv.
  destruct fiber_iso0.
  destruct to.
  simpl in *.
  pose proof (to (`1 (projF0) (Left_Functor a))) as f.
  simpl in f.
  Transparent Left_Functor.
  unfold Left_Functor in f.
  simpl in f.
  (* f : (a ~{ D }~> fst `1 (fobj ((a, F a); id[F a]))) *
         (F a ~{ C }~> snd `1 (fobj ((a, F a); id[F a]))) *)
  pose proof (fmap ((a, F a); id[F a]));
  simpl in X0.
Admitted.

Lemma fiber_eqv_fmap_counit_unit (eqv : fibered_equivalence) {a} :
  fmap[G] (fiber_eqv_counit eqv) ∘ fiber_eqv_unit eqv ≈ id[G a].
Proof.
Admitted.

Theorem Adjunction_Comma : F ⊣ G  <-->  fibered_equivalence.
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
