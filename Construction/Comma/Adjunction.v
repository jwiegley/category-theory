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

(*
Lemma comma_functoriality' {A B C} (S : A ⟶ C) (T : B ⟶ C)
      (F : A ∏ B ⟶ (S ↓ T)) X Y (f : X ~{A ∏ B}~> Y) :
  fmap[T] (snd f) ∘ projT2 (F X) ≈ projT2 (F Y) ∘ fmap[S] (fst f).
Proof.
  destruct F; simpl in *.
  destruct (fmap X Y f).
  simpl in X0.
*)

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

Corollary Left_Functor_fobj_to_iso_natural
          (iso : (F ↓ Id[C]) ≅[Cat] (Id[D] ↓ G))
          (projF : comma_proj ≈[Cat] comma_proj ○ to iso) :
  ∀ X Y (g : X ~{D}~> Y),
    fmap (fmap g)
      ∘ fmap[G] (snd (``projF (Left_Functor X))⁻¹)
      ∘ projT2 (to iso (Left_Functor X))
      ∘ fst (to (``projF (Left_Functor X)))
      ≈ fmap[G] (snd (``projF (Left_Functor Y))⁻¹)
          ∘ projT2 (to iso (Left_Functor Y))
          ∘ fst (to (``projF (Left_Functor Y))) ∘ g.
Proof.
  simpl; intros.
  destruct projF; simpl in *.
  given (g_morph : {f : (X ~{ D }~> Y) * (F X ~{ C }~> F Y)
                   & id[F Y] ∘ fmap[F] (fst f) ≈ snd f ∘ id[F X]}).
    exists (g, fmap g).
    abstract cat.
(*
  pose proof (naturality[from] ((X, F X); id[F X])
                        ((Y, F Y); id[F Y]) g_morph); simpl in X0.
  destruct X0.
  rewrite <- fmap_comp.
  rewrite e0; clear e e0.
  rewrite fmap_comp.
  comp_left.
  pose proof (naturality[to] ((X, F X); id[F X])
                        ((Y, F Y); id[F Y]) g_morph); simpl in X0.
  destruct X0.
  rewrite <- e; clear e e0.
  comp_right.
  destruct iso, to; simpl in *.
  destruct to0; simpl in *.
  pose proof fmap as F0.
  specialize (F0 ((X, F X); id[F X]) ((Y, F Y); id[F Y])
                 g_morph).
  destruct F0.
  destruct x; simpl in *.
  remember (snd `1 (fmap ((X, F X); id[F X]) ((Y, F Y); id[F Y]) g_morph)) as f.
*)
Abort.

Record fibered_equivalence := {
  fiber_iso : (F ↓ Id[C]) ≅[Cat] (Id[D] ↓ G);

  projG : comma_proj ≈[Cat] comma_proj ○ from fiber_iso;
  projF : comma_proj ≈[Cat] comma_proj ○ to fiber_iso;

  (* This should be a property of the functor [F]. *)
  comma_functoriality {A B C} (S : A ⟶ C) (T : B ⟶ C)
    (F : A ∏ B ⟶ (S ↓ T)) X Y (f : ``(F X) ~{A ∏ B}~> ``(F Y)) :
    fmap[T] (snd f) ∘ projT2 (F X) ≈ projT2 (F Y) ∘ fmap[S] (fst f)
}.

Lemma Left_Functoriality (eqv : fibered_equivalence) X Y
      (f : comma_proj (Left_Functor X) ~> comma_proj (Left_Functor Y)) :
  fmap[G] (snd f)
    ∘ fmap[G] (snd (``(projF eqv) (Left_Functor X))⁻¹)
    ∘ projT2 (to (fiber_iso eqv) (Left_Functor X))
    ∘ fst (to (``(projF eqv) (Left_Functor X)))
    ≈ fmap[G] (snd (``(projF eqv) (Left_Functor Y))⁻¹)
        ∘ projT2 (to (fiber_iso eqv) (Left_Functor Y))
        ∘ fst (to (``(projF eqv) (Left_Functor Y)))
        ∘ fst f.
Proof.
  pose proof (comma_functoriality eqv Id G
                (to (fiber_iso eqv) ○ Left_Functor ○ Fst) (X, F X) (Y, F Y));
  simpl in X0.
  rewrite <- fmap_comp.
  (* destruct eqv, fiber_iso0, to, projF0, from0; simpl in *. *)
Admitted.
(*
  rewrite (snd (naturality (Left_Functor X) (Left_Functor Y) f)).
  rewrite Functor.fmap_comp.
  simpl.
  comp_left.
  destruct to; simpl in *.
  rewrite <- (fst (naturality0 (Left_Functor X) (Left_Functor Y) f)).
  comp_right.
  apply X0.
Qed.
*)

Lemma Right_Functoriality (eqv : fibered_equivalence) X Y
      (f : comma_proj (Right_Functor X) ~> comma_proj (Right_Functor Y)) :
  snd f
    ∘ snd (``(projG eqv) (Right_Functor X))⁻¹
    ∘ projT2 ((fiber_iso eqv)⁻¹ (Right_Functor X))
    ∘ fmap[F] (fst (to (``(projG eqv) (Right_Functor X))))
    ≈ snd (``(projG eqv) (Right_Functor Y))⁻¹
        ∘ projT2 ((fiber_iso eqv)⁻¹ (Right_Functor Y))
        ∘ fmap[F] (fst (to (``(projG eqv) (Right_Functor Y))))
        ∘ fmap[F] (fst f).
Proof.
  pose proof (comma_functoriality eqv F Id
                (from (fiber_iso eqv) ○ Right_Functor ○ Snd)
                (G X, X) (G Y, Y));
  simpl in X0.
  rewrite <- !comp_assoc.
  rewrite <- fmap_comp.
  (* destruct eqv, fiber_iso0, from, projG0, to0; simpl in *. *)
Admitted.
(*
  rewrite <- (fst (naturality (Right_Functor X) (Right_Functor Y) f)).
  rewrite Functor.fmap_comp.
  simpl.
  comp_right.
  destruct from; simpl in *.
  rewrite (snd (naturality0 (Right_Functor X) (Right_Functor Y) f)).
  comp_left.
  apply X0.
Qed.
*)

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

Theorem Adjunction_Comma :
  F ⊣ G  <-->  fibered_equivalence.
Proof.
  split; intros H. {
    refine {| fiber_iso := Comma_F_Id_Id_G_Iso H |}.
    - simpl; unshelve eexists; intros; split;
      destruct f; simpl; cat.
    - simpl; unshelve eexists; intros; split;
      destruct f; simpl; cat.
    - intros.
      admit.
  }

  Opaque Left_Functor.
  given (unit : ∀ a, a ~{ D }~> G (F a)).
    intro a.
    exact (fmap (snd (``(projF H) (Left_Functor a))⁻¹)
                ∘ projT2 (to (fiber_iso H) (Left_Functor a))
                ∘ fst (to (``(projF H) (Left_Functor a)))).

  Opaque Right_Functor.
  given (counit : ∀ a, F (G a) ~{ C }~> a).
    intro a.
    exact (snd (``(projG H) (Right_Functor a))⁻¹
               ∘ projT2 ((fiber_iso H)⁻¹ (Right_Functor a))
               ∘ fmap (fst (to (``(projG H) (Right_Functor a))))).

  unshelve (eapply Adjunction_from_Transform).
  unshelve econstructor; auto.

  - transform; simpl; intros.
    + exact (unit X).
    + unfold unit; clear unit.
      do 2 rewrite comp_assoc.
      exact (Left_Functoriality H X Y (f, fmap[F] f)).
    + unfold unit; clear unit.
      do 2 rewrite comp_assoc.
      symmetry.
      exact (Left_Functoriality H X Y (f, fmap[F] f)).

  - transform; simpl; intros.
    + exact (counit X).
    + unfold counit; clear counit.
      do 2 rewrite comp_assoc.
      exact (Right_Functoriality H X Y (fmap[G] f, f)).
    + unfold counit; clear counit.
      do 2 rewrite comp_assoc.
      symmetry.
      exact (Right_Functoriality H X Y (fmap[G] f, f)).

  - simpl; intros.
    unfold unit, counit; clear unit counit.
    pose proof (comma_functoriality H Id G
                  (to (fiber_iso H) ○ Left_Functor ○ Fst));
    simpl in X0.
    rewrite <- !comp_assoc.
    rewrite <- fmap_comp.
    rewrite !comp_assoc.
    admit.                      (* DEFERRED *)

  - simpl in *; intros.
    admit.                      (* DEFERRED *)
Abort.                          (* DEFERRED *)

End AdjunctionComma.
