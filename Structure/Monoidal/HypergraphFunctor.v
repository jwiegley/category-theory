Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Structure.Monoidal.Hypergraph.

Generalizable All Variables.

(** * Hypergraph functors

    Reference: Fong, "The Algebra of Open and Interconnected Systems"
    (arXiv:1609.05382), Definition 4.1.3; Fong–Spivak, "Hypergraph
    categories" (Journal of Pure and Applied Algebra 223, 2019).

    A HYPERGRAPH FUNCTOR between hypergraph categories [(C, ⨂_C, I_C, …)]
    and [(D, ⨂_D, I_D, …)] is a symmetric monoidal functor preserving the
    SCFA structure on each object.  Concretely, the functor acts as a
    *strict* symmetric monoidal functor (or up to canonical isomorphism)
    AND sends μ_X, η_X, δ_X, ε_X to μ_{F X}, η_{F X}, δ_{F X}, ε_{F X}.

    This is the morphism notion in the category [HypGraph] of hypergraph
    categories.  Examples include the BLACK-BOXING functors of
    Baez–Fong–Spivak: every concrete black-box (electrical-circuit,
    Markov-process, signal-flow) factors as a hypergraph functor from a
    decorated-cospan domain into a target hypergraph category (relations,
    linear maps, ZX-diagrams).

    ** Coq-specific organisation

    To keep the record self-contained in the present library and avoid
    the typeclass-resolution loops that arise when nesting
    [#[export] Instance Hypergraph] under another typeclass that itself
    triggers Hypergraph resolution on the codomain, we present
    [HypergraphFunctor] as a RECORD parameterised by the two ambient
    [Hypergraph] instances (and their underlying [SymmetricMonoidal]
    structures).  Instances of this record are built locally and are
    NOT auto-marked as [#[export] Instance].

    The record records (i) the underlying functor [F : C ⟶ D] and
    (ii) preservation of the four SCFA generators on every object,
    stated up to the [≈] equivalence in [D] modulo the canonical
    transport along the strict-monoidal coherences that identify
    [F X ⨂_D F Y] with [F (X ⨂_C Y)] and [I_D] with [F I_C].  In the
    fully-strict / on-the-nose case those transports are identities,
    yielding the literature definition verbatim.

    ** Known scoping limitation: missing monoidal coherences

    Per Fong–Spivak (Definition 4.1.3), a hypergraph functor is a
    (symmetric) STRONG monoidal functor that ALSO preserves the SCFA
    generators.  The record below carries [hf_unit_iso] and
    [hf_tensor_iso] as raw isomorphisms, BUT omits the standard
    lax-monoidal coherence equations:

      - associator hexagon for [hf_tensor_iso] vs. [tensor_assoc];
      - unitor squares for [hf_tensor_iso] vs. [unit_left] /
        [unit_right];
      - naturality of [hf_tensor_iso] in both arguments;
      - braid-compatibility ([F braid ≈ braid ∘ hf_tensor_iso]).

    Consequence: two distinct choices of [hf_tensor_iso] / [hf_unit_iso]
    could each satisfy the four SCFA-preservation equations without
    [F] actually being a symmetric monoidal functor.  Downstream code
    that assumes "a [HypergraphFunctor] is in particular a symmetric
    monoidal functor" does NOT get that property from this record.

    The trivial [Id_HypergraphFunctor] instance below is fine
    ([hf_tensor_iso := iso_id], [hf_unit_iso := iso_id] discharge all
    coherences definitionally).  A non-trivial instance — e.g. the
    [forget_decoration] black-boxing functor — would need to
    additionally re-establish the missing coherences separately, or
    the record would need to be re-factored to extend an existing
    [Functor/Structure/Monoidal.v:MonoidalFunctor] (a deferred
    refactor).

    A more rigorous future redesign of this record either (a) adds
    the missing coherence fields here verbatim, or (b) re-parameterises
    on the library's [MonoidalFunctor] class (plus a fictional
    [SymmetricMonoidalFunctor] subclass, currently absent from the
    library) and inherits the coherence equations from there. *)

Section HypergraphFunctor.

Context {C : Category}.
Context `{SC : @SymmetricMonoidal C}.
Context `{HG_C : @Hypergraph C SC}.

Context {D : Category}.
Context `{SD : @SymmetricMonoidal D}.
Context `{HG_D : @Hypergraph D SD}.

(** A hypergraph functor [F : C ⟶ D] consists of an underlying functor
    together with *witnesses* that
      - tensor on objects is preserved up to a *fixed* iso [hf_tensor X Y :
        F X ⨂ F Y ≅ F (X ⨂ Y)];
      - the monoidal unit is preserved up to a *fixed* iso [hf_unit :
        I ≅ F I];
      - the SCFA generators on every [X] are preserved up to those
        transports (one equation per generator).

    The strict-on-the-nose case takes [hf_tensor X Y := id] and
    [hf_unit := id]; the SCFA preservation equations then reduce to the
    literature form [F (μ_X) ≈ μ_{F X}], etc.  We keep the iso
    parameterisation in the record because the standard library's
    [Functor] type does not record monoidality, so any concrete
    hypergraph-functor instance must supply these comparison iso's
    explicitly. *)

Record HypergraphFunctor : Type := {
  hf_functor :> C ⟶ D;

  (** Comparison isomorphisms (the lax-monoidal data on [hf_functor],
      packaged here since [Functor] does not record it). *)
  hf_unit_iso : @I D _ ≅ hf_functor (@I C _);
  hf_tensor_iso : forall (X Y : C),
    (hf_functor X ⨂ hf_functor Y)%object ≅ hf_functor (X ⨂ Y)%object;

  (** SCFA preservation: the four generators on every [X] are sent to
      the corresponding generators on [F X], up to transport along the
      comparison isomorphisms.

      For [mu]:
        F (μ_X)  ∘  hf_tensor_iso X X  ≈  μ_{F X}.
      For [delta]: the corresponding equation in the opposite direction.
      For [eta]: the unit-comparison transports the source.
      For [epsilon]: the unit-comparison transports the codomain. *)

  hf_preserves_mu : forall (X : C),
    fmap[hf_functor] (scfa_mu (scfa X)) ∘ to (hf_tensor_iso X X)
      ≈ scfa_mu (scfa (hf_functor X));

  hf_preserves_eta : forall (X : C),
    fmap[hf_functor] (scfa_eta (scfa X)) ∘ to hf_unit_iso
      ≈ scfa_eta (scfa (hf_functor X));

  hf_preserves_delta : forall (X : C),
    from (hf_tensor_iso X X) ∘ fmap[hf_functor] (scfa_delta (scfa X))
      ≈ scfa_delta (scfa (hf_functor X));

  hf_preserves_epsilon : forall (X : C),
    from hf_unit_iso ∘ fmap[hf_functor] (scfa_epsilon (scfa X))
      ≈ scfa_epsilon (scfa (hf_functor X))
}.

End HypergraphFunctor.

Arguments HypergraphFunctor {C SC} HG_C {D SD} HG_D.
Arguments hf_functor {C SC HG_C D SD HG_D} _.
Arguments hf_unit_iso {C SC HG_C D SD HG_D} _.
Arguments hf_tensor_iso {C SC HG_C D SD HG_D} _ _ _.
Arguments hf_preserves_mu {C SC HG_C D SD HG_D} _ _.
Arguments hf_preserves_eta {C SC HG_C D SD HG_D} _ _.
Arguments hf_preserves_delta {C SC HG_C D SD HG_D} _ _.
Arguments hf_preserves_epsilon {C SC HG_C D SD HG_D} _ _.

(** ** The identity hypergraph functor

    For any hypergraph category [(C, HG_C)], the identity functor
    [Id C : C ⟶ C] is canonically a hypergraph functor with
    [hf_unit_iso := iso_id] and [hf_tensor_iso X Y := iso_id].

    All four preservation equations follow from [fmap[Id] f = f] (the
    definitional equation of the identity functor), combined with
    [iso_id]'s components reducing to [id] under composition. *)

Section IdHypergraphFunctor.

Context {C : Category}.
Context `{SC : @SymmetricMonoidal C}.
Context `{HG_C : @Hypergraph C SC}.

Program Definition Id_HypergraphFunctor : HypergraphFunctor HG_C HG_C := {|
  hf_functor := Id[C] ;
  hf_unit_iso := iso_id ;
  hf_tensor_iso := fun X Y => iso_id
|}.

End IdHypergraphFunctor.

(** ** Discussion: the BlackBox / forget-decoration use case

    The forgetful "drop the decoration" functor from [DecoratedCospanCat F]
    to [CospanCat C] is a hypergraph functor: it acts as the identity on
    objects, projects out the cospan part of every morphism, and the SCFA
    on a cospan-category object is given by the [Cospan_Hypergraph]
    instance — which by definition is the SCFA the forgetful functor
    preserves on the nose.

    Fully packaging [forget_decoration] as a [HypergraphFunctor] requires
    [DecoratedCospanCat F] to be a [Category] record (the
    [Construction/DecoratedCospan.v] module exports the API, the [Setoid],
    identity, and composition; the full [Category] obligations are
    discharged at the cospan level by [Construction/Cospan/Category.v]
    and at the decoration level by the lax-monoidal functor coherences).

    See [Construction/Cospan/BlackBox.v] for the cospan-equivalence
    well-definedness lemmas that this record-form encapsulates. *)

(** ** Composition of hypergraph functors

    [HypergraphFunctor (HG_B, HG_C) -> HypergraphFunctor (HG_C, HG_D) ->
       HypergraphFunctor (HG_B, HG_D)]: composing the underlying functors,
    pairing the comparison iso's via [iso_compose] interleaved with
    [fmap]-transport, and combining the preservation equations.

    The composition law is mechanical but volumetric (each comparison
    iso composes through one [fmap], each preservation equation is the
    sum of the two component preservations).  We leave the explicit
    composition data to downstream sites that genuinely need it
    (the present library's main BlackBox use case only requires the
    identity instance and the literature pattern). *)
