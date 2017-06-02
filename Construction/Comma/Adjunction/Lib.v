Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Adjunction.Natural.Transformation.
Require Export Category.Adjunction.Natural.Transformation.Universal.
Require Export Category.Construction.Comma.
Require Export Category.Construction.Product.
Require Export Category.Instance.Cat.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

Section AdjunctionComma.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {G : C ⟶ D}.

Record fibered_equivalence := {
  fiber_iso : (F ↓ Id[C]) ≅[Cat] (Id[D] ↓ G);

  projG : comma_proj ≈[Cat] comma_proj ○ from fiber_iso;
  projF : comma_proj ≈[Cat] comma_proj ○ to fiber_iso
}.

Program Definition Left_Functor : D ⟶ (F ↓ Id[C]) := {|
  fobj := fun x : D => ((x, F x); id[F x]);
  fmap := fun _ _ f => ((f, fmap[F] f); _)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation.
  split.
    reflexivity.
  apply fmap_comp.
Qed.

Program Definition Right_Functor : C ⟶ (Id[D] ↓ G) := {|
  fobj := fun x : C => ((G x, x); id[G x]);
  fmap := fun _ _ f => ((fmap[G] f, f); _)
|}.
Next Obligation. proper; rewrites; reflexivity. Qed.
Next Obligation.
  split.
    apply fmap_comp.
  reflexivity.
Qed.

Lemma Left_Functoriality (eqv : fibered_equivalence) x y
      (f : comma_proj (Left_Functor x) ~> comma_proj (Left_Functor y)) :
  fmap[G] (fmap[F] (fst f))
    ∘ (fmap[G] (snd (`1 (projF eqv) (Left_Functor x))⁻¹)
         ∘ `2 (to (fiber_iso eqv) (Left_Functor x))
         ∘ fst (to (`1 (projF eqv) (Left_Functor x))))
    ≈ fmap[G] (snd (`1 (projF eqv) (Left_Functor y))⁻¹)
        ∘ `2 (to (fiber_iso eqv) (Left_Functor y))
        ∘ fst (to (`1 (projF eqv) (Left_Functor y)))
        ∘ fst f.
Proof.
  Opaque Left_Functor.
  given (ff :
    { f : (fst `1 (Left_Functor x) ~{ D }~> fst `1 (Left_Functor y)) *
          (snd `1 (Left_Functor x) ~{ C }~> snd `1 (Left_Functor y))
    & `2 (Left_Functor y) ∘ fmap[F] (fst f) ≈ snd f ∘ `2 (Left_Functor x) }).
    exists (fst f, fmap[F] (fst f)).
    abstract (simpl; rewrite id_left, id_right; reflexivity).
  destruct (`2 (projF eqv) (Left_Functor x) (Left_Functor y) ff).
  simpl in *.
  rewrite e0.
  do 2 rewrite fmap_comp.
  comp_left.
  rewrite (comp_assoc (fmap[G] (snd (to (`1 (projF eqv) (Left_Functor x)))))).
  rewrite <- fmap_comp.
  rewrite (snd (iso_to_from (`1 (projF eqv) (Left_Functor x)))).
  simpl snd.
  rewrite fmap_id.
  rewrite id_left.
  symmetry.
  spose (`2 (fmap[to (fiber_iso eqv)] ff)) as X.
  rewrite !comp_assoc.
  rewrite <- X.
  comp_left.
  rewrite e at 1.
  comp_right.
  rewrite (fst (iso_to_from (`1 (projF eqv) (Left_Functor y)))).
  rewrite id_left.
  reflexivity.
Qed.

Lemma Right_Functoriality (eqv : fibered_equivalence) x y
      (f : comma_proj (Right_Functor x) ~> comma_proj (Right_Functor y)) :
  snd f ∘ (snd (`1 (projG eqv) (Right_Functor x))⁻¹
        ∘ `2 ((fiber_iso eqv)⁻¹ (Right_Functor x))
        ∘ fmap[F] (fst (to (`1 (projG eqv) (Right_Functor x)))))
  ≈ snd (`1 (projG eqv) (Right_Functor y))⁻¹
      ∘ `2 ((fiber_iso eqv)⁻¹ (Right_Functor y))
      ∘ fmap[F] (fst (to (`1 (projG eqv) (Right_Functor y))))
      ∘ fmap[F] (fmap[G] (snd f)).
Proof.
  Opaque Right_Functor.
  given (ff :
    { f : (fst `1 (Right_Functor x) ~{ D }~> fst `1 (Right_Functor y)) *
          (snd `1 (Right_Functor x) ~{ C }~> snd `1 (Right_Functor y))
    & `2 (Right_Functor y) ∘ fst f ≈ fmap[G] (snd f) ∘ `2 (Right_Functor x) }).
    exists (fmap[G] (snd f), snd f).
    abstract (simpl; rewrite id_left, id_right; reflexivity).
  destruct (`2 (projG eqv) (Right_Functor x) (Right_Functor y) ff).
  simpl in *.
  symmetry.
  rewrite e.
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite !comp_assoc.
  rewrite (fst (iso_to_from (`1 (projG eqv) (Right_Functor y)))).
  rewrite id_left.
  symmetry.
  rewrite e0 at 1.
  comp_left.
  rewrite (comp_assoc (snd (to (`1 (projG eqv) (Right_Functor x))))).
  rewrite (snd (iso_to_from (`1 (projG eqv) (Right_Functor x)))).
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
  - exists (id, id).
    destruct x as [[x y] f]; cat.
    srewrite (iso_to_from (@adj _ _ _ _ H x y)); reflexivity.
  - exists (id, id).
    destruct x as [[x y] f]; cat.
    srewrite (iso_to_from (@adj _ _ _ _ H x y)); reflexivity.
  - clear; simpl; split; cat.
  - clear; simpl; split; cat.
  - clear; simpl; split; cat.
Qed.
Next Obligation.
  constructive; simpl.
  - exists (id, id).
    destruct x as [[x y] f]; cat.
    srewrite (iso_from_to (@adj _ _ _ _ H x y)); reflexivity.
  - exists (id, id).
    destruct x as [[x y] f]; cat.
    srewrite (iso_from_to (@adj _ _ _ _ H x y)); reflexivity.
  - clear; simpl; split; cat.
  - clear; simpl; split; cat.
  - clear; simpl; split; cat.
Qed.

End AdjunctionComma.
