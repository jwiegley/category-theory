Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Export Category.Theory.Functor.
Require Export Category.Functor.Product.
Require Export Category.Functor.Strong.
Require Export Category.Functor.Strong.Product.
Require Export Category.Structure.Monoidal.
Require Export Category.Functor.Structure.Monoidal.
Require Export Category.Functor.Traversable.
Require Export Category.Functor.Applicative.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.

Section ProductTraversable.

Context `{C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.
Context `{@Closed C _}.
Context `{F : C ⟶ C}.
Context `{G : C ⟶ C}.

Existing Instance InternalProduct_Monoidal.

Lemma ProductFunctor_Traversable_ap_functor_nat :
  Traversable F → Traversable G
    → ∀ H : C ⟶ C, @Applicative _ _ _ _ H
    → (F :*: G) ○ H ⟹ H ○ (F :*: G).
Proof.
  intros O P ??.

  transform.
    simpl.
    intro x.
      exact (lax_ap[H2] ∘ bimap (transform[@sequence _ _ _ _ _ O H2 _] x)
                                (transform[@sequence _ _ _ _ _ P H2 _] x)).
  unfold lax_ap.
  pose proof (naturality[@ap_functor_nat _ _ _ _ H2 _]
                        (F X0, G X0) (F Y, G Y)
                        (fmap[F] f, fmap[G] f)) as X2; simpl in *.
  rewrite comp_assoc.
  rewrite X2; clear X2.
  rewrite <- !comp_assoc.
  pose proof (naturality[@sequence _ _ _ _ _ O H2 _]) as X3; simpl in *.
  pose proof (naturality[@sequence _ _ _ _ _ P H2 _]) as X4; simpl in *.
  Ltac unfork :=
    repeat (rewrite <- !fork_comp; cat;
            rewrite <- !comp_assoc; cat).
  unfork.
  rewrite !comp_assoc.
  rewrite X3, X4; clear X3 X4.
  reflexivity.
Defined.

(*
Program Definition ProductFunctor_Traversable :
  Traversable F -> Traversable G
    -> Traversable (F :*: G) := fun O P => {|
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
  rewrite <- X0, <- X1.
  rewrite bimap_comp.
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  (* This must be proven based on how slm_transform interacts with ap. *)
*)
Admitted.
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
  rewrite <- X3; clear X3.
  rewrite !comp_assoc.
  rewrite <- fmap_comp.
  reflexivity.
Qed.
*)
Next Obligation.
Admitted.
*)

End ProductTraversable.
