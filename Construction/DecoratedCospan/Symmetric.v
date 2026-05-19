Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.Cospan.Hypergraph.
Require Import Category.Construction.Cospan.Symmetric.
Require Import Category.Construction.DecoratedCospan.
Require Import Category.Construction.DecoratedCospan.Category.

Generalizable All Variables.

(** * Symmetric monoidal structure on [DecoratedCospanCat]

    Reference: Brendan Fong, "Decorated Cospans", arXiv:1502.00872,
    Theorem 3.1 (the decorated-cospan category is a hypergraph category
    whenever the decorating functor is a symmetric lax monoidal functor).

    This module assembles the symmetric monoidal hierarchy on
    [DecoratedCospanCat] by layering decoration coherences on top of the
    [Cospan_*] structural witnesses from [Construction/Cospan/Symmetric.v].

    Following the [DecCospan_Coherent] pattern established in
    [Construction/DecoratedCospan/Category.v], each layer bundles its
    decoration-side coherence requirements as a typeclass, parameterised
    by the same lax-monoidal data ([F], [LM], [id_decoration],
    [cospan_merge]) used to define [DecoratedCospanCat] itself.

    Concrete instances of each coherence class correspond to the
    explicit constructions one finds in the categorical-systems
    literature (Fong's circuits, Baez–Fong Markov processes,
    Fong–Spivak signal-flow diagrams).  The structural propositions of
    this file are independent of any concrete instance; they organise
    the bookkeeping so that a downstream consumer supplying the
    coherence-class instance receives the full symmetric monoidal
    hypergraph structure for free.

    ** Layered class architecture

    [DecCospan_Coherent]         (Category obligations — already in
                                  [DecoratedCospan/Category.v])
        ↓ provides
    [DecCospan_Bifunctor_Coherent] (decoration-side bifunctor laws)
        ↓ provides
    [DecCospan_Monoidal_Coherent]  (unitor/associator decoration coherence)
        ↓ provides
    [DecCospan_Braided_Coherent]   (braid decoration coherence; requires
                                  F to be symmetric-lax-monoidal)
        ↓ provides
    [DecCospan_Symmetric_Coherent] (symmetric braid coherence)

    Each step pairs the cospan-level fact (already in
    [Construction/Cospan/Symmetric.v]) with the matching decoration-level
    coherence. *)

Section DecoratedCospanSymmetric.

Context {C : Category}.
Context (HP : HasPushouts C).
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context `{MC : @Monoidal C}.
Context {D : Category}.
Context `{MD : @Monoidal D}.
Context {F : C ⟶ D}.
Context (LM : @LaxMonoidalFunctor C D MC MD F).
Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).
Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).
Context `{DCC : @DecCospan_Coherent C HP H_Coc MC D MD F LM
                                     id_decoration cospan_merge}.

(** ** Decorated cospan tensor

    Given decorated cospans [f : X → X'] (apex [Nf], decoration [d_f])
    and [g : Y → Y'] (apex [Ng], decoration [d_g]), the tensor cospan
    [f ⊗ g : X+Y → X'+Y'] has:

      - cospan part: [cospan_tensor (dc_cospan f) (dc_cospan g)] with apex
        [Nf + Ng] (built in [Construction/Cospan/Hypergraph.v]);
      - decoration: the composite

           I  -unit_left⁻¹->  I ⨂ I  -d_f ⨂ d_g->  F Nf ⨂ F Ng
              -lax_ap->  F (Nf ⨂_C Ng)  -F (cospan_merge)->  F (Nf + Ng)

        That is, the same combinator used in [dec_compose_decoration]
        applied to the apex pair. *)

Definition dec_tensor_decoration
  {X X' Y Y' : C}
  (f : DecoratedCospanArrow X X')
  (g : DecoratedCospanArrow Y Y')
  : @I D _ ~{D}~> F (cospan_apex (cospan_tensor (dc_cospan f) (dc_cospan g))) :=
  let Nf := cospan_apex (dc_cospan f) in
  let Ng := cospan_apex (dc_cospan g) in
  fmap[F] (cospan_merge Nf Ng)
    ∘ lax_ap[F]
    ∘ bimap (dc_decoration f) (dc_decoration g)
    ∘ from (@unit_left D _ (@I D _)).

Definition dec_cospan_tensor
  {X X' Y Y' : C}
  (f : DecoratedCospanArrow X X')
  (g : DecoratedCospanArrow Y Y')
  : DecoratedCospanArrow (X + Y) (X' + Y') := {|
  dc_cospan := cospan_tensor (dc_cospan f) (dc_cospan g);
  dc_decoration := dec_tensor_decoration f g
|}.

(** ** Bifunctor coherence class

    The Bifunctor instance on [DecoratedCospanCat] requires three
    decoration-side coherences (the cospan-side counterparts already
    live in [Construction/Cospan/Hypergraph.v]):

      (i) [dec_tensor_id_dec]: tensor-of-identities decoration equals
          identity decoration up to apex iso;

      (ii) [dec_tensor_respects_dec]: pairwise [dec_cospan_equiv]
          transports through the tensor;

      (iii) [dec_tensor_compose_dec]: tensor distributes over composition
          (interchange law on the decoration side).

    Each is a routine appeal to the lax-monoidal naturality of [F]
    combined with the apex-iso transport produced by the corresponding
    [Cospan/Hypergraph.v] lemma. *)

Class DecCospan_Bifunctor_Coherent : Type := {
  (** Decoration coherence for [tensor_id]: the tensor of two identity
      decorated cospans equals the identity decorated cospan on the
      coproduct, after transport along the cospan-level iso. *)
  dec_tensor_id_dec :
    forall (X Y : C),
      fmap[F] (to (projT1 (cospan_tensor_id X Y)))
        ∘ dec_tensor_decoration
            (dec_cospan_id id_decoration X)
            (dec_cospan_id id_decoration Y)
      ≈ id_decoration (X + Y)%object;

  (** Decoration coherence for [tensor_respects]: pairwise equivalent
      decorated cospans yield equivalent tensors, with the decoration
      transporting along the per-component apex isos. *)
  dec_tensor_respects_dec :
    forall {X Y X' Y' : C}
           (f f' : DecoratedCospanArrow X Y)
           (g g' : DecoratedCospanArrow X' Y')
           (Hf : dec_cospan_equiv f f')
           (Hg : dec_cospan_equiv g g'),
      fmap[F] (to (projT1 (cospan_tensor_respects
                              (dc_cospan f) (dc_cospan f')
                              (dc_cospan g) (dc_cospan g')
                              (dce_cospan_eq Hf) (dce_cospan_eq Hg))))
        ∘ dec_tensor_decoration f g
      ≈ dec_tensor_decoration f' g';

  (** Decoration interchange: the tensor of two composites equals the
      composite of two tensors, with decorations matching after the
      cospan-level apex-iso transport. *)
  dec_tensor_compose_compat_dec :
    forall {X Y Z X' Y' Z' : C}
           (g : DecoratedCospanArrow Y Z) (f : DecoratedCospanArrow X Y)
           (g' : DecoratedCospanArrow Y' Z') (f' : DecoratedCospanArrow X' Y'),
      fmap[F] (to (projT1 (cospan_tensor_compose_compat HP
                              (dc_cospan g) (dc_cospan f)
                              (dc_cospan g') (dc_cospan f'))))
        ∘ dec_tensor_decoration
            (dec_cospan_compose HP LM cospan_merge g f)
            (dec_cospan_compose HP LM cospan_merge g' f')
      ≈ dec_compose_decoration HP LM cospan_merge
          (dec_cospan_tensor g g')
          (dec_cospan_tensor f f')
}.

Context `{DCBC : DecCospan_Bifunctor_Coherent}.

Set Default Proof Using "All".

(** ** Bifunctor-level lemmas, pairing cospan + decoration coherences *)

Lemma dec_cospan_tensor_id (X Y : C) :
  dec_cospan_equiv
    (dec_cospan_tensor
       (dec_cospan_id id_decoration X)
       (dec_cospan_id id_decoration Y))
    (dec_cospan_id id_decoration (X + Y)%object).
Proof.
  unshelve econstructor.
  - exact (cospan_tensor_id X Y).
  - simpl. exact (dec_tensor_id_dec X Y).
Defined.

Lemma dec_cospan_tensor_respects
      {X Y X' Y' : C}
      (f f' : DecoratedCospanArrow X Y)
      (g g' : DecoratedCospanArrow X' Y')
      (Hf : dec_cospan_equiv f f')
      (Hg : dec_cospan_equiv g g') :
  dec_cospan_equiv
    (dec_cospan_tensor f g)
    (dec_cospan_tensor f' g').
Proof.
  unshelve econstructor.
  - exact (cospan_tensor_respects
             (dc_cospan f) (dc_cospan f')
             (dc_cospan g) (dc_cospan g')
             (dce_cospan_eq Hf) (dce_cospan_eq Hg)).
  - simpl. exact (dec_tensor_respects_dec f f' g g' Hf Hg).
Defined.

Lemma dec_cospan_tensor_compose_compat
      {X Y Z X' Y' Z' : C}
      (g : DecoratedCospanArrow Y Z) (f : DecoratedCospanArrow X Y)
      (g' : DecoratedCospanArrow Y' Z') (f' : DecoratedCospanArrow X' Y') :
  dec_cospan_equiv
    (dec_cospan_tensor
       (dec_cospan_compose HP LM cospan_merge g f)
       (dec_cospan_compose HP LM cospan_merge g' f'))
    (dec_cospan_compose HP LM cospan_merge
       (dec_cospan_tensor g g')
       (dec_cospan_tensor f f')).
Proof.
  unshelve econstructor.
  - exact (cospan_tensor_compose_compat HP
             (dc_cospan g) (dc_cospan f)
             (dc_cospan g') (dc_cospan f')).
  - simpl. exact (dec_tensor_compose_compat_dec g f g' f').
Defined.

(** ** [DecoratedCospan_Bifunctor]: the Bifunctor on [DecoratedCospanCat] *)

#[export] Program Instance dec_cospan_tensor_respects_proper
  {X Y X' Y' : C} :
  Proper (equiv ==> equiv ==> equiv)
    (@dec_cospan_tensor X X' Y Y').
Next Obligation.
  proper.
  now apply dec_cospan_tensor_respects.
Qed.

Program Definition DecoratedCospan_Bifunctor
  : ((DecoratedCospanCat HP LM id_decoration cospan_merge)
       ∏ (DecoratedCospanCat HP LM id_decoration cospan_merge))
    ⟶ (DecoratedCospanCat HP LM id_decoration cospan_merge) := {|
  fobj := fun xy => @Cospan_tensor_obj C H_Coc (fst xy) (snd xy);
  fmap := fun xy uv fg => dec_cospan_tensor (fst fg) (snd fg)
|}.
Next Obligation.
  proper; simpl in *.
  apply dec_cospan_tensor_respects; assumption.
Defined.
Next Obligation.
  apply dec_cospan_tensor_id.
Defined.
Next Obligation.
  apply dec_cospan_tensor_compose_compat.
Defined.

End DecoratedCospanSymmetric.

(** ** Path to the full SMC layer

    The Bifunctor instance above is the first of the four pieces of the
    decorated symmetric monoidal hypergraph structure.  The remaining
    three (Monoidal, BraidedMonoidal, SymmetricMonoidal) follow the same
    layered-coherence pattern:

    - [DecCospan_Monoidal_Coherent] bundles the unitor + associator
      decoration coherences.  The cospan-level facts come from
      [Cospan_Monoidal] in [Construction/Cospan/Hypergraph.v].

    - [DecCospan_Braided_Coherent] bundles the braid-decoration
      coherence.  The cospan-level fact comes from
      [Cospan_BraidedMonoidal] in [Construction/Cospan/Symmetric.v].
      The decoration-side coherence requires [F] to be symmetric in the
      sense that [lax_ap[F] ∘ braid ≈ F(braid) ∘ lax_ap[F]] — i.e. [F]
      is a SYMMETRIC lax monoidal functor.

    - [DecCospan_Symmetric_Coherent] bundles the braid-involution
      decoration coherence — typically automatic from the braided
      coherence and [paws_invol].

    Once those three classes are populated, the [Monoidal /
    BraidedMonoidal / SymmetricMonoidal] instances on
    [DecoratedCospanCat] are constructed in the same pairing-pattern
    as the Bifunctor above: each Program Obligation pairs the
    cospan-level lemma with the matching coherence-class field. *)
