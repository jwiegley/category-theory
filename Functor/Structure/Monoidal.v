Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.Product.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(** Monoidal functors. *)

(* nLab: https://ncatlab.org/nlab/show/monoidal+functor
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_functor

   A monoidal functor between monoidal categories C and D is a functor
   F : C ⟶ D equipped with comparison maps relating F to the tensor and the
   unit, subject to coherence with the associator and unitors.

   In the lax form (here [LaxMonoidalFunctor]) the comparisons point from the
   tensor of images to the image of the tensor and from the unit into the
   image of the unit,

       lax_ap   : F x ⨂ F y ~> F (x ⨂ y)   (the tensor comparison),
       lax_pure : I ~> F I                  (the unit comparison),

   following nLab and Wikipedia (μ_{x,y} : F x ⊗ F y → F (x ⊗ y) and
   η : I → F I). A strong monoidal functor (here [MonoidalFunctor]) is the
   same data with both comparisons invertible, so they are stated directly as
   isomorphisms [ap_iso] and [pure_iso] oriented in the lax direction; a
   strict monoidal functor would take them to be identities. The oplax (a.k.a.
   opmonoidal, colax, comonoidal) variant reverses both comparisons,
   F (x ⨂ y) ~> F x ⨂ F y and F I ~> I, and is not formalized here.

   Three coherence conditions are imposed in each form:

       unit_left   left  unitality, λ vs. the tensor and unit comparisons,
       unit_right  right unitality, ρ vs. the tensor and unit comparisons,
       assoc       associativity,  the associator α vs. two tensor comparisons.

   The [pure_iso_left], [pure_iso_right] and [ap_iso_assoc] fields (and their
   lax counterparts) record the derived isomorphisms used to phrase those
   coherence squares; they are consequences of the comparisons, not extra
   structure. *)

Section MonoidalFunctor.

Context {C : Category}.
Context {D : Category}.
Context `{@Monoidal C}.
Context `{@Monoidal D}.
Context {F : C ⟶ D}.

Lemma ap_iso_to_from
      (ap_functor_iso : (⨂) ◯ F ∏⟶ F ≅[[C ∏ C, D]] F ◯ (⨂)) {x y} :
  transform (to ap_functor_iso) (x, y)
    ∘ transform (from ap_functor_iso) (x, y) ≈ id[F (x ⨂ y)].
Proof.
  spose (iso_to_from ap_functor_iso (x, y)) as X.
  rewrite !fmap_id in X.
  apply X.
Qed.

Lemma ap_iso_from_to
      (ap_functor_iso : (⨂) ◯ F ∏⟶ F ≅[[C ∏ C, D]] F ◯ (⨂)) {x y} :
  transform (from ap_functor_iso) (x, y) ∘ transform (to ap_functor_iso) (x, y)
    ≈ id[((⨂) ◯ F ∏⟶ F) (x, y)].
Proof.
  spose (iso_from_to ap_functor_iso (x, y)) as X.
  rewrite !fmap_id in X.
  apply X.
Qed.

Class MonoidalFunctor := {
  pure_iso : I ≅ F I;             (* unit comparison η, invertible *)

  (* tensor comparison μ as a natural isomorphism (⨂) ◯ F ∏⟶ F ≅ F ◯ (⨂) *)
  ap_functor_iso : (⨂) ◯ F ∏⟶ F ≅[[C ∏ C, D]] F ◯ (⨂);

  (* the component F x ⨂ F y ≅ F (x ⨂ y) of the tensor comparison *)
  ap_iso {x y} : F x ⨂ F y ≅ F (x ⨂ y) := {|
    to   := transform[to ap_functor_iso] (x, y);
    from := transform[from ap_functor_iso] (x, y);
    iso_to_from := @ap_iso_to_from ap_functor_iso x y;
    iso_from_to := @ap_iso_from_to ap_functor_iso x y
  |};

  pure_iso_left {x}  : I ⨂ F x ≅ F (I ⨂ x);  (* derived iso for left unitality *)
  pure_iso_right {x} : F x ⨂ I ≅ F (x ⨂ I);  (* derived iso for right unitality *)

  (* derived iso for the associativity coherence square *)
  ap_iso_assoc {x y z} : (F x ⨂ F y) ⨂ F z ≅ F (x ⨂ (y ⨂ z));

  monoidal_unit_left {x} :         (* left unitality: λ vs. μ and η *)
    to unit_left
       ≈ fmap[F] (to unit_left) ∘ to ap_iso ∘ bimap (to pure_iso) (id[F x]);

  monoidal_unit_right {x} :        (* right unitality: ρ vs. μ and η *)
    to unit_right
       ≈ fmap[F] (to unit_right) ∘ to ap_iso ∘ bimap (id[F x]) (to pure_iso);

  monoidal_assoc {x y z} :         (* associativity: α vs. two μ's *)
    fmap[F] (to (@tensor_assoc _ _ x y z)) ∘ to ap_iso ∘ bimap (to ap_iso) id
      ≈ to ap_iso ∘ bimap id (to ap_iso) ∘ to tensor_assoc
}.

Class LaxMonoidalFunctor := {
  lax_pure : I ~> F I;             (* unit comparison η : I → F I *)

  (* tensor comparison μ as a natural transformation (⨂) ◯ F ∏⟶ F ⟹ F ◯ (⨂) *)
  ap_functor_nat : ((⨂) ◯ F ∏⟶ F) ~{[C ∏ C, D]}~> (F ◯ (⨂));

  (* the component μ_{x,y} : F x ⨂ F y → F (x ⨂ y) of the tensor comparison *)
  lax_ap {x y} : F x ⨂ F y ~> F (x ⨂ y) := transform[ap_functor_nat] (x, y);

  pure_left {x}  : I ⨂ F x ≅ F (I ⨂ x);  (* derived iso for left unitality *)
  pure_right {x} : F x ⨂ I ≅ F (x ⨂ I);  (* derived iso for right unitality *)

  (* derived iso for the associativity coherence square *)
  ap_assoc {x y z} : (F x ⨂ F y) ⨂ F z ≅ F (x ⨂ (y ⨂ z));

  lax_monoidal_unit_left {x} :     (* left unitality: λ vs. μ and η *)
    to unit_left
       ≈ fmap[F] (to unit_left) ∘ lax_ap ∘ bimap lax_pure (id[F x]);

  lax_monoidal_unit_right {x} :    (* right unitality: ρ vs. μ and η *)
    to unit_right
       ≈ fmap[F] (to unit_right) ∘ lax_ap ∘ bimap (id[F x]) lax_pure;

  lax_monoidal_assoc {x y z} :     (* associativity: α vs. two μ's *)
    fmap[F] (to (@tensor_assoc _ _ x y z)) ∘ lax_ap ∘ bimap lax_ap id
      ≈ lax_ap ∘ bimap id lax_ap ∘ to tensor_assoc
}.

Program Definition MonoidalFunctor_Is_Lax (S : MonoidalFunctor) :
  LaxMonoidalFunctor := {|
  lax_pure := to (@pure_iso S);
  ap_functor_nat := to (@ap_functor_iso S)
|}.
Next Obligation. apply pure_iso_left. Qed.
Next Obligation. apply pure_iso_right. Qed.
Next Obligation. apply ap_iso_assoc. Qed.
Next Obligation. apply monoidal_unit_left. Qed.
Next Obligation. apply monoidal_unit_right. Qed.
Next Obligation. apply monoidal_assoc. Qed.

End MonoidalFunctor.

Notation "ap_iso[ F ]" := (@ap_iso _ _ _ _ F%functor _ _ _)
  (at level 9, format "ap_iso[ F ]").
Notation "ap_functor_iso[ F ]" := (@ap_functor_iso _ _ _ _ _ F%functor)
  (at level 9, format "ap_functor_iso[ F ]") : morphism_scope.

Notation "lax_pure[ F ]" := (@lax_pure _ _ _ _ F%functor _)
  (at level 9, format "lax_pure[ F ]") : morphism_scope.
Notation "lax_ap[ F ]" := (@lax_ap _ _ _ _ F%functor _ _ _)
  (at level 9, format "lax_ap[ F ]").
Notation "ap_functor_nat[ F ]" := (@ap_functor_nat _ _ _ _ _ F%functor)
  (at level 9, format "ap_functor_nat[ F ]") : morphism_scope.

Arguments LaxMonoidalFunctor {C D _ _} F.
Arguments MonoidalFunctor {C D _ _} F.
