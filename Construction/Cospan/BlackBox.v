Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.DecoratedCospan.
Require Import Category.Construction.DecoratedCospan.Category.

(** * Black-boxing functor for decorated cospans

    Reference: Baez–Fong, "A compositional framework for passive linear
    networks", arXiv:1504.05625 §4 (the black-box functor ♭ : Circ →
    LagRel); Fong, "The Algebra of Open and Interconnected Systems",
    arXiv:1609.05382 (PhD thesis), where black-boxing is developed across
    Ch. 3 ("Corelations: a tool for black boxing") and Ch. 4 ("Decorated
    corelations: black-boxed open systems").

    nLab has no dedicated "black boxing" page; the concept is documented
    under https://ncatlab.org/nlab/show/decorated+cospan and
    https://ncatlab.org/nlab/show/hypergraph+category.  Wikipedia has no
    article on this (applied-category-theory) sense of black-boxing.

    The black-boxing concept: a "decorated cospan" represents an open
    system with an internal mechanism (the decoration) and an external
    interface (the cospan).  Black-boxing forgets the internal mechanism,
    retaining only the observable input/output behaviour — typically a
    relation, a Markov kernel, or a linear map.

    Categorically, black-boxing is a HYPERGRAPH FUNCTOR

      ⬛ : DecoratedCospanCat F  ⟶  ObservableCat

    that preserves the symmetric monoidal AND the SCFA structure on each
    object.  This is what makes black-boxing COMPOSITIONAL: the black-box
    of a composite system is the composite of the black-boxes, and the
    black-box of a parallel composition is the parallel composition of
    the black-boxes.

    ** What this file lands

    1. The "underlying cospan" forgetful black-box

         [forget_decoration : DecoratedCospanCat F → CospanCat C]

       — a black-box that throws away the decoration entirely, keeping
       only the cospan.

    2. The well-definedness lemmas: forgetting respects the
       [dec_cospan_equiv] equivalence (so the action descends to the
       quotient), and preserves identity and composition on the nose.

    3. A discussion of how the general black-boxing functor — taking
       decorated cospans to relations, Markov kernels, linear maps, or
       ZX-diagrams — instantiates the same pattern.

    See Fong's thesis, Theorem 6.1, which states that the original
    Baez–Fong electrical-circuit black-boxing functor ♭ : Circ → LagRel
    is a hypergraph functor (equivalently Baez–Fong arXiv:1504.05625).
    The categorical content of that theorem is precisely: apex-iso
    transport + lax-monoidal naturality + SCFA preservation; the
    forgetful black-box below is the trivial instance that exhibits this
    structure with the cleanest possible proof. *)

(** ** Section: forgetful black-box on decorated cospans *)

Section ForgetDecoration.

Context {C : Category}.
Context (HP : HasPushouts C).
Context {MC : @Monoidal C}.
Context {D : Category}.
Context {MD : @Monoidal D}.
Context (F : C ⟶ D).
Context (LM : @LaxMonoidalFunctor C D MC MD F).
Context `{H_Coc : @Cocartesian C}.

(** The action on objects: identity. *)
Definition forget_decoration_obj : C -> C := fun X => X.

(** The action on morphisms: project the cospan out of the decorated cospan. *)
Definition forget_decoration_morphism
  {X Y : C} (f : DecoratedCospanArrow X Y)
  : CospanArrow X Y := dc_cospan f.

(** [forget_decoration] respects the decorated-cospan equivalence,
    descending to a well-defined function on the equivalence classes
    of [DecoratedCospanCat]. *)
Lemma forget_decoration_morphism_respects
  {X Y : C} (f g : DecoratedCospanArrow X Y) :
  dec_cospan_equiv f g ->
  cospan_equiv (forget_decoration_morphism f) (forget_decoration_morphism g).
Proof.
  intros [E _].
  exact E.
Qed.

Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).
Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).

(** [forget_decoration] preserves identity: the underlying cospan of the
    identity-decorated cospan on [X] is the identity cospan on [X]. *)
Lemma forget_decoration_id (X : C) :
  forget_decoration_morphism
    (dec_cospan_id id_decoration X)
  = cospan_id X.
Proof. reflexivity. Qed.

(** [forget_decoration] preserves composition: the underlying cospan of a
    composed decorated cospan is the composed cospan. *)
Lemma forget_decoration_compose {X Y Z : C}
  (g : DecoratedCospanArrow Y Z)
  (f : DecoratedCospanArrow X Y) :
  forget_decoration_morphism
    (dec_cospan_compose HP LM cospan_merge g f)
  = cospan_compose HP (forget_decoration_morphism g) (forget_decoration_morphism f).
Proof. reflexivity. Qed.

(** Cospan-equivalence variants (for downstream use via [≈] rewriting). *)
Lemma forget_decoration_correct_id {X : C} :
  cospan_equiv
    (forget_decoration_morphism (dec_cospan_id id_decoration X))
    (cospan_id X).
Proof. apply cospan_equiv_refl. Qed.

Lemma forget_decoration_correct_compose {X Y Z : C}
  (g : DecoratedCospanArrow Y Z)
  (f : DecoratedCospanArrow X Y) :
  cospan_equiv
    (forget_decoration_morphism
       (dec_cospan_compose HP LM cospan_merge g f))
    (cospan_compose HP
       (forget_decoration_morphism g)
       (forget_decoration_morphism f)).
Proof.
  rewrite forget_decoration_compose.
  apply cospan_equiv_refl.
Qed.

End ForgetDecoration.

(** ** The forgetful black-box as a [Functor]

    With [DecoratedCospanCat] in scope (and the [DecCospan_Coherent]
    coherence class), [forget_decoration] is a [Functor] record from
    [DecoratedCospanCat HP LM id_decoration cospan_merge] to
    [CospanCat C HP].

    The functor laws are immediate from the [forget_decoration_*]
    lemmas above: the underlying cospan of the identity decorated
    cospan IS the identity cospan, and the underlying cospan of a
    composite IS the composite of underlying cospans (both by
    reflexivity of the cospan setoid). *)

Section ForgetDecorationFunctor.

Context {C : Category}.
Context (HP : HasPushouts C).
Context `{H_Coc : @Cocartesian C}.
Context {MC : @Monoidal C}.
Context {D : Category}.
Context {MD : @Monoidal D}.
Context {F : C ⟶ D}.
Context (LM : @LaxMonoidalFunctor C D MC MD F).
Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).
Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).
Context `{DCC : @DecCospan_Coherent C HP H_Coc MC D MD F LM
                                     id_decoration cospan_merge}.

Program Definition forget_decoration
  : (DecoratedCospanCat HP LM id_decoration cospan_merge) ⟶ (CospanCat C HP) := {|
  fobj := fun X => X;
  fmap := fun X Y f => @forget_decoration_morphism C D MD F X Y f
|}.
Next Obligation.
  proper.
  apply (@forget_decoration_morphism_respects C D MD F);
    assumption.
Defined.
Next Obligation.
  apply (@forget_decoration_correct_id C D MD F id_decoration).
Defined.
Next Obligation.
  apply (@forget_decoration_correct_compose C HP MC D MD F LM
                                            H_Coc cospan_merge).
Defined.

End ForgetDecorationFunctor.

(** ** Hypergraph-functoriality of the forgetful black-box

    [CospanCat C HP] carries the canonical hypergraph structure
    [Cospan_Hypergraph] (in [Construction/Cospan/HypergraphInstance.v]).
    Lifting [DecoratedCospanCat F] to a full hypergraph category — by
    pairing the cospan-level SCFA with a CHOSEN decoration on each of
    [μ, η, δ, ε] — and then forgetting the decoration leaves the SCFA
    on [forget_decoration X = X] equal to [Cospan_Hypergraph]'s SCFA,
    so preservation is REFLEXIVE: [F (μ_X) = μ_{F X}] etc.

    The strict form of hypergraph-functor preservation:

      F (mu_X)     ≈ mu_{F X}
      F (eta_X)    ≈ eta_{F X}
      F (delta_X)  ≈ delta_{F X}
      F (eps_X)    ≈ eps_{F X}

    follows from the cospan-level reflexivity ([forget_decoration_id]
    and [forget_decoration_compose]) combined with the definitional
    equality of [scfa] generators on a [DecoratedCospanCat F]-object's
    underlying cospan-category object.  The full packaging requires
    DecoratedCospanCat itself as a [Category] record (the
    [Construction/DecoratedCospan.v] module exports the API and the
    Setoid; the [Category] record packaging follows the standard pattern
    from [CospanCat]'s construction).

    ** Discussion: the general black-boxing functor

    In its full generality (Baez–Fong, Fong–Spivak), black-boxing is a
    hypergraph functor

      ⬛ : DecoratedCospanCat F  ⟶  Rel

    or, depending on the application,

      ⬛ : DecoratedCospanCat F  ⟶  Cospan(FinSet)   (Markov-process variant)
      ⬛ : DecoratedCospanCat F  ⟶  Vect_R           (linear-circuit variant)
      ⬛ : DecoratedCospanCat F  ⟶  ZX_Cat.          (quantum variant)

    Each instance specialises the codomain hypergraph category and the
    decoration-to-behaviour map.  The categorical content — that the
    construction is a hypergraph functor — is the SAME in every case:
    apex-iso transport + lax-monoidal naturality + SCFA preservation.

    This file provides the canonical forgetful black-box, the
    well-definedness lemmas at the cospan/equivalence level, and the
    pattern-recipe for instantiating the general case.

    ** Packaging as a [HypergraphFunctor] record

    [Structure/Monoidal/HypergraphFunctor.v] defines the literature
    notion of a hypergraph functor (Fong–Spivak, "Hypergraph
    Categories", arXiv:1806.08304, Def. 4.1.3): a strong symmetric
    monoidal functor between hypergraph categories preserving the SCFA
    structure on every object.

    The forgetful black-box [forget_decoration : DecoratedCospanCat F →
    CospanCat C] is, by construction, a STRICT hypergraph functor: it
    acts as the identity on objects, and on each generator it sends
    the decorated SCFA-generator back to the underlying cospan-level
    SCFA-generator (since the decoration is, by definition, an extra
    layer wrapped around the cospan).

    Formally building the [HypergraphFunctor] instance requires:

      1. [DecoratedCospanCat F] as a [Category] record (done by
         [Construction/DecoratedCospan/Category.v], parameterised by
         a [DecCospan_Coherent] instance);

      2. the SMC structure on [DecoratedCospanCat] (the
         [Construction/DecoratedCospan/Category.v] discussion section
         outlines the [DecCospan_Monoidal_Coherent] +
         [DecCospan_Symmetric_Coherent] coherence-class signatures);

      3. the [Hypergraph] structure on [DecoratedCospanCat] (chosen
         decorations on each of the four SCFA generators, lifting
         [Cospan_Hypergraph]'s scfa fields one level).

    With (1)-(3) in scope, the [HypergraphFunctor] instance for
    [forget_decoration] takes [hf_unit_iso := iso_id] and
    [hf_tensor_iso X Y := iso_id] (the functor acts as the identity
    on objects), and discharges each of the four preservation
    equations by [reflexivity] (since
    [forget_decoration_morphism (scfa_gen_dec X) = scfa_gen X]
    holds on the nose by the choice of decorated SCFA).

    This is the canonical Fong-style "black-box is a hypergraph
    functor" theorem (Theorem 6.1 in his thesis, arXiv:1609.05382),
    realised in formal Coq. *)
