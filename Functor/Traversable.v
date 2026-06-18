Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Strong.
Require Import Category.Functor.Applicative.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Id.
Require Import Category.Functor.Structure.Monoidal.Compose.
Require Import Category.Functor.Structure.Monoidal.Pure.
Require Import Category.Natural.Transformation.Monoidal.
Require Import Category.Natural.Transformation.Applicative.
Require Import Category.Natural.Transformation.Strong.
Require Import Category.Structure.Monoidal.Closed.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Functor.Applicative.

Generalizable All Variables.

(** Traversable functors (the law-bearing, categorical version) *)

(* nLab: https://ncatlab.org/nlab/show/distributive+law
   nLab: https://ncatlab.org/nlab/show/applicative+functor

   No dedicated nLab or Wikipedia page exists for "traversable functor": the
   nLab pages above are the closest (a traversable functor is precisely a
   functor carrying a coherent distributive law over every applicative
   functor), and the Haskell-level account lives on the HaskellWiki rather
   than in the Wikipedia main namespace
   (https://wiki.haskell.org/Foldable_and_Traversable).  The defining laws
   below are those of Jaskelioff and Rypacek, "An Investigation of the Laws of
   Traversals", MSFP 2012 (https://arxiv.org/abs/1202.2919).

   Following McBride-Paterson, a traversable functor is an endofunctor
   [F : C ⟶ C] equipped with a distributive law

     sequence : F ◯ G ⟹ G ◯ F     (the traversal, Haskell's [sequenceA])

   natural in the applicative functor [G] (a lax monoidal endofunctor with
   tensorial strength), subject to three coherence laws.  Writing the
   component at [X] as [δ_G X : F (G X) ~> G (F X)], and taking [N : G ⟹ H] an
   applicative transformation (the morphisms of the monoidal category of
   applicative functors), the laws are:

     naturality in G   transform[N] (F X) ∘ δ_G X
                         ≈ δ_H X ∘ fmap[F] (transform[N] X)
                       (sequence commutes with applicative transformations);
     identity          δ_Id X ≈ id
                       (traversing in the identity applicative is a no-op, so
                       no element is skipped);
     composition       δ_(G ◯ H) X ≈ fmap[G] (δ_H X) ∘ δ_G X
                       (traversals in [G] then [H] fuse into one traversal in
                       the composite applicative [G ◯ H], so no element is
                       visited twice).

   These are precisely the coherence axioms making [Traversable] functors form
   a monoidal category under composition.  By the Bird-Gibbons /
   Jaskelioff-O'Connor representation theorem the lawful traversable functors
   on Set are exactly the finitary containers.  This is the law-bearing
   counterpart of the lawless Coq/Haskell-style class in
   [Category.Theory.Coq.Traversable]. *)

Section Traversable.

Context {C : Category}.
Context `{@ClosedMonoidal C}.
Context {F : C ⟶ C}.

#[local] Obligation Tactic := idtac.

Program Instance Id_Applicative : @Applicative C _ (Id[C]) := {
  applicative_is_strong := Id_StrongFunctor;
  applicative_is_lax_monoidal := Id_LaxMonoidalFunctor
}.

Program Instance Compose_Applicative
  `{@Applicative C _ G}
  `{@Applicative C _ K} :
  @Applicative C _ (Compose G K) := {
  applicative_is_strong := Compose_StrongFunctor G K _ _;
  applicative_is_lax_monoidal := Compose_LaxMonoidalFunctor _ _
}.

Class Traversable := {
  (* the distributive law F ◯ G ⟹ G ◯ F, natural in the applicative G *)
  sequence {G : C ⟶ C} `{@Applicative C _ G} : F ◯ G ⟹ G ◯ F;

  (* naturality: sequence commutes with applicative transformations N : G ⟹ H *)
  sequence_naturality {G : C ⟶ C} `{@Applicative C _ G}
                      {H : C ⟶ C} `{@Applicative C _ H} (N : G ⟹ H)
                      (f : @Applicative_Transform C _ _ _ _ _ N) {X} :
    transform[N] (F X) ∘ transform[@sequence G _] X
      ≈ transform[@sequence H _] X ∘ fmap[F] (transform[N] _);

  (* identity: traversing in the identity applicative is a no-op *)
  sequence_Id {X} : transform[@sequence Id _] X ≈ id;
  (* composition: traversals in G then H fuse into one in G ◯ H *)
  sequence_Compose {G : C ⟶ C} `{@Applicative C _ G}
                   {H : C ⟶ C} `{@Applicative C _ H} {X} :
    transform[@sequence (Compose G H) _] X
      ≈ fmap[G] (transform[sequence] X) ∘ transform[sequence] _
}.

End Traversable.

Arguments Traversable {_ _} F.

#[export]
Program Instance Id_Traversable `{@ClosedMonoidal C} (x : C) :
  Traversable (@Id C) := {
  sequence := fun _ _ => {| transform := fun _ => id |}
}.

Require Import Category.Functor.Diagonal.

#[export]
Program Instance Diagonal_Traversable
  {C J : Category} `{@ClosedMonoidal C} (x : C) :
  Traversable (Diagonal C x) := {
  sequence := fun G _ => {| transform := fun _ => pure[G] |}
}.
Next Obligation.
  unfold pure.
  simpl; normal.
  rewrite <- !comp_assoc.
  normal.
  rewrite <- naturality.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  rewrite (lax_pure_transform[N]).
  rewrite <- strength_transform; simpl.
  rewrite <- !comp_assoc; cat.
  apply compose_respects; [reflexivity|].
  now rewrite bimap_comp_id_left.
Qed.
Next Obligation.
  unfold pure, bimap; simpl; cat.
  apply iso_to_from.
Qed.
Next Obligation.
  unfold pure; simpl.
  normal.
  rewrite <- !comp_assoc.
  rewrite !fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  apply compose_respects; [|reflexivity].
  rewrite <- !comp_assoc.
  apply compose_respects; [reflexivity|].
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  rewrite <- !comp_assoc; cat.
  rewrite iso_from_to, id_right.
  rewrite bimap_comp_id_left.
  rewrite !comp_assoc.
  comp_right.
  symmetry.
  spose (@strength_natural _ _ G _ x _ id _ _ lax_pure) as X0.
  rewrite bimap_id_id in X0.
  rewrite fmap_id in X0.
  rewrite id_right in X0.
  rewrite X0.
  cat.
Qed.
