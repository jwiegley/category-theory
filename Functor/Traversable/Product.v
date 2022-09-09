Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Product.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Traversable.
Require Import Category.Functor.Applicative.

Generalizable All Variables.

Section ProductTraversable.

Context {C : Category}.
Context `{@ClosedMonoidal C}.
Context {F : C ⟶ C}.
Context {G : C ⟶ C}.

Existing Instance CC_Monoidal.

Lemma ProductFunctor_Traversable_ap_functor_nat :
  Traversable F → Traversable G
    → ∀ H : C ⟶ C, @Applicative _ _ H
    → (F :*: G) ◯ H ⟹ H ◯ (F :*: G).
Proof.
  intros O P ??.

  transform.
  - simpl.
    intro x.
    exact (lax_ap[H0] ∘ bimap (transform[@sequence _ _ _ O _ X] x)
                              (transform[@sequence _ _ _ P _ X] x)).
  - unfold lax_ap.
    spose (naturality[@ap_functor_nat _ _ _ _ H0 _]
                     (F x, G x) (F y, G y)
                     (fmap[F] f, fmap[G] f)) as X2.
    rewrite comp_assoc.
    rewrites.
    rewrite <- !comp_assoc.
    pose proof (naturality[@sequence _ _ _ O _ X]) as X3; simpl in *.
    pose proof (naturality[@sequence _ _ _ P _ X]) as X4; simpl in *.
    rewrite !comp_assoc.
    comp_left.
    rewrite bimap_fmap.
    rewrite <- !bimap_comp.
    rewrite X3, X4.
    reflexivity.
  - unfold lax_ap.
    spose (naturality[@ap_functor_nat _ _ _ _ H0 _]
                     (F x, G x) (F y, G y)
                     (fmap[F] f, fmap[G] f)) as X2.
    rewrite comp_assoc.
    rewrites.
    rewrite <- !comp_assoc.
    pose proof (naturality[@sequence _ _ _ O _ X]) as X3; simpl in *.
    pose proof (naturality[@sequence _ _ _ P _ X]) as X4; simpl in *.
    rewrite !comp_assoc.
    comp_left.
    rewrite bimap_fmap.
    rewrite <- !bimap_comp.
    rewrite X3, X4.
    reflexivity.
Defined.

(*
Program Definition ProductFunctor_Traversable :
  Traversable F → Traversable G
    → Traversable (F :*: G) := fun O P => {|
  sequence := ProductFunctor_Traversable_ap_functor_nat _ _;
  sequence_naturality  := _;
  sequence_Id  := _;
  sequence_Compose  := _
|}.
Next Obligation.
  pose proof (@sequence_naturality _ _ _ _ _ O G0 _ H3 _ _ f X) as X0.
  pose proof (@sequence_naturality _ _ _ _ _ P G0 _ H3 _ _ f X) as X1.
  repeat (unfold ap; simpl).
(*
  pose proof (naturality[@slm_transform _ _ _ _ _ _ _ _ f]).
  rewrite <- comp_assoc.
  rewrite <- bimap_comp.
  rewrites.
  rewrite bimap_comp.
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  (* This must be proven based on how slm_transform interacts with ap. *)
*)
Next Obligation.
  repeat (unfold ap; simpl).
  rewrite id_left.
  rewrite (@sequence_Id _ _ _ _ _ O), (@sequence_Id _ _ _ _ _ P).
  cat.
Qed.
(*
Next Obligation.
  repeat (unfold lax_ap; simpl).
  rewrite (@sequence_Compose _ _ _ _ _ O G0 H2 H3 H4 X),
          (@sequence_Compose _ _ _ _ _ P G0 H2 H3 H4 X).
  pose proof (naturality[@ap_functor_nat _ _ _ _ G0
                           (@is_lax_monoidal _ _ _ _ _ H2)]
                        (F (H3 X), G (H3 X))
                        (H3 (F X), H3 (G X))
                        (transform sequence X, transform sequence X)) as X3;
  simpl in *.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc _ (bimap _ _)).
  rewrites.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  reflexivity.
Qed.
*)
Next Obligation.
*)

End ProductTraversable.
