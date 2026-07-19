Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Monoidal.
Require Import Category.Construction.Enriched.
Require Import Category.Construction.Enriched.Natural.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** V = Sets recovers ordinary category theory, at the transformation level.

    The companion theorems [Category_is_Enriched_over_Set] and
    [Functor_is_Enriched_over_Set] (in Construction/Enriched.v) show that a
    Sets-enriched category is an ordinary category and that a Sets-enriched
    functor is an ordinary functor.  This file completes the picture for the
    third leg: a Sets-enriched natural transformation between the enriched
    functors [EF], [EG] corresponding to ordinary functors [F], [G] is the same
    data as an ordinary natural transformation [F ⟹ G].

    In Sets the tensor unit is the singleton [I = {| carrier := poly_unit |}],
    so an enriched component [etransform x : I ~{Sets}~> ehom D (F x) (G x)] is a
    setoid map [poly_unit → (F x ~> G x)]; its value at [ttt] is an ordinary
    component [F x ~> G x].  Unfolding the enriched naturality square in Sets and
    evaluating at [f : x ~> y] gives exactly the ordinary naturality equation
    [etransform y ttt ∘ fmap[F] f ≈ fmap[G] f ∘ etransform x ttt] (the
    [naturality_sym] orientation, up to the left/right unitor plumbing). *)

Section EnrichedSetsTransform.

Context {C D : Category}.
Context (F G : C ⟶ D).

(* The enriched functors corresponding to the ordinary functors F and G, via
   the [Category → Enriched] / [(C ⟶ D) → EnrichedFunctor] halves of the two
   companion equivalences. *)
Definition EF : EnrichedFunctor Sets
                  (snd Category_is_Enriched_over_Set C)
                  (snd Category_is_Enriched_over_Set D) :=
  snd (Functor_is_Enriched_over_Set C D) F.

Definition EG : EnrichedFunctor Sets
                  (snd Category_is_Enriched_over_Set C)
                  (snd Category_is_Enriched_over_Set D) :=
  snd (Functor_is_Enriched_over_Set C D) G.

Theorem EnrichedTransform_is_Transform :
  @EnrichedTransform Sets Sets_Product_Monoidal _ _ EF EG ↔ (F ⟹ G).
Proof.
  split; intros X.
  - (* Forward: read each enriched component at [ttt] as an ordinary component,
       and derive ordinary naturality from enriched naturality. *)
    apply (Build_Transform' (fun x => @etransform _ _ _ _ EF EG X x ttt)).
    intros x y f.
    (* Enriched naturality at [x], [y], evaluated at [f], unfolds in Sets to the
       [naturality_sym] orientation; take its symmetry. *)
    symmetry.
    exact (@enaturality _ _ _ _ EF EG X x y f).
  - (* Backward: package each ordinary component as a constant setoid map out of
       the singleton, and derive enriched naturality from ordinary naturality. *)
    unshelve refine
      (@Build_EnrichedTransform
         Sets Sets_Product_Monoidal
         (snd Category_is_Enriched_over_Set C)
         (snd Category_is_Enriched_over_Set D)
         EF EG
         (fun x => {| morphism := fun _ => @transform _ _ F G X x |}) _).
    + proper.
    + intros x y f.
      (* The enriched naturality square in Sets reduces pointwise to the
         [naturality_sym] orientation of the ordinary naturality square. *)
      exact (@naturality_sym _ _ F G X x y f).
Defined.

End EnrichedSetsTransform.
