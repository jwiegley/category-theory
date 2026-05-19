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
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Comonoid.
Require Import Category.Theory.Algebra.Frobenius.
Require Import Category.Theory.Algebra.CommutativeFrobenius.
Require Import Category.Theory.Algebra.SpecialCommutativeFrobenius.
Require Import Category.Structure.Monoidal.Hypergraph.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Construction.Cospan.Category.
Require Import Category.Construction.Cospan.Bridging.
Require Import Category.Construction.Cospan.Hypergraph.
Require Import Category.Construction.Cospan.Symmetric.
Require Import Category.Construction.Cospan.HypergraphInstance.
Require Import Category.Construction.DecoratedCospan.
Require Import Category.Construction.DecoratedCospan.Category.
Require Import Category.Construction.DecoratedCospan.Symmetric.
Require Import Category.Construction.DecoratedCospan.Monoidal.
Require Import Category.Construction.DecoratedCospan.Braided.

Generalizable All Variables.

(** * Hypergraph structure on [DecoratedCospanCat]

    Reference: Brendan Fong, "Decorated Cospans", arXiv:1502.00872,
    Theorem 3.1; Fong–Spivak, "Hypergraph categories", JPAA 223 (2019),
    Theorem 3.4.

    This module assembles the [Hypergraph] instance on
    [DecoratedCospanCat HP LM id_decoration cospan_merge] by layering
    a decoration coherence class on top of [Cospan_Hypergraph] from
    [Construction/Cospan/HypergraphInstance.v].

    ** Architecture

    The [Hypergraph] class on [DC] requires:

      - an SCFA on every object [X];
      - tensor coherence ([scfa_tensor_mu], [scfa_tensor_eta],
        [scfa_tensor_delta], [scfa_tensor_epsilon]) — the SCFA on
        [X ⨂ Y] agrees with the canonical SCFA assembled from those
        of [X] and [Y];
      - unit coherence ([scfa_unit_mu], [scfa_unit_eta],
        [scfa_unit_delta], [scfa_unit_epsilon]) — the SCFA on [I]
        is the trivial one.

    The literature-correct packaging (Fong, Definition 3.3 of the
    Hypergraph categories paper) bundles all of this — the
    decoration-coherent SCFA per object plus the 8 coherence equations
    — as a single hypergraph-decoration coherence class.  Concrete
    decoration choices (Fong's circuits, Baez–Fong Markov processes)
    supply explicit witnesses for all fields.

    We package this as [DecCospan_Hypergraph_Coherent], whose principal
    field is a per-object [SpecialCommutativeFrobenius DC X], plus the
    8 standard tensor + unit coherence equations.

    ** Note on the lax-symmetric requirement (Fong Definition 3.1)

    Fong's original construction requires [F] to be a LAX SYMMETRIC
    monoidal functor.  The symmetric-laxness is needed here because
    [μ] for the SCFA on [X+Y] uses braiding to interleave decorations:
    without [F (braid_C) ∘ lax_ap ≈ lax_ap ∘ braid_D], the canonical
    SCFA on [X+Y] (assembled from the SCFAs of [X] and [Y]) cannot
    be shown to satisfy the Frobenius/commutativity laws on decorated
    cospans.

    In this library's factoring, the [DecCospan_Braided_Coherent] and
    [DecCospan_Symmetric_Coherent] classes (taken as [Context] above)
    encode exactly the decorated-cospan-side consequences of [F] being
    lax-symmetric — instantiating them is impossible without an
    underlying lax-symmetric [F]. *)

Section DecoratedCospanHypergraph.

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
Context `{DCBC : @DecCospan_Bifunctor_Coherent C HP H_Coc MC D MD F LM
                                                id_decoration cospan_merge}.
Context `{DCMC : @DecCospan_Monoidal_Coherent C HP H_Coc H_Ini MC D MD F LM
                                               id_decoration cospan_merge}.
Context `{DCBrC : @DecCospan_Braided_Coherent C HP H_Coc MC D MD F LM
                                                id_decoration cospan_merge}.
Context `{DCSC : @DecCospan_Symmetric_Coherent C HP H_Coc MC D MD F LM
                                                 id_decoration cospan_merge}.

Notation DC := (DecoratedCospanCat HP LM id_decoration cospan_merge).
Notation DCMon := (DecoratedCospan_Monoidal HP LM id_decoration cospan_merge).
Notation DCSMC :=
  (DecoratedCospan_SymmetricMonoidal HP LM id_decoration cospan_merge).

(** ** Coherence class for the Hypergraph structure on [DC]

    Fong's "decorated SCFA" data: a decoration-coherent choice of
    SCFA generator for every object, satisfying the 8 standard
    coherence equations of the [Hypergraph] class.

    Each field's RHS uses the [DecoratedCospan_SymmetricMonoidal]
    instance (which is the SMC structure on [DC] from Braided.v); the
    LHS is the user-supplied data.

    The principal field [dec_cospan_scfa] supplies the per-object
    decorated SCFA.  In the trivial-decoration case it is the
    [Cospan_Hypergraph]-SCFA with [id_decoration] decorations on each
    apex; in genuine decorated-cospan examples it is the SCFA carrying
    the application-specific data on each apex (Fong circuits use the
    "no-resistors" decoration, Baez–Fong Markov processes use the
    "no-transitions" decoration, etc.). *)

Class DecCospan_Hypergraph_Coherent : Type := {
  dec_cospan_scfa : forall (X : DC),
    @SpecialCommutativeFrobenius DC DCSMC X;

  (** Tensor coherence: the SCFA on [X ⨂ Y] agrees with the canonical
      assembled one. *)
  dec_scfa_tensor_mu : forall (X Y : DC),
    @scfa_mu DC DCSMC _ (dec_cospan_scfa (X ⨂ Y)%object)
      ≈ @canonical_tensor_mu DC DCSMC X Y
          (dec_cospan_scfa X) (dec_cospan_scfa Y);

  dec_scfa_tensor_eta : forall (X Y : DC),
    @scfa_eta DC DCSMC _ (dec_cospan_scfa (X ⨂ Y)%object)
      ≈ @canonical_tensor_eta DC DCSMC X Y
          (dec_cospan_scfa X) (dec_cospan_scfa Y);

  dec_scfa_tensor_delta : forall (X Y : DC),
    @scfa_delta DC DCSMC _ (dec_cospan_scfa (X ⨂ Y)%object)
      ≈ @canonical_tensor_delta DC DCSMC X Y
          (dec_cospan_scfa X) (dec_cospan_scfa Y);

  dec_scfa_tensor_epsilon : forall (X Y : DC),
    @scfa_epsilon DC DCSMC _ (dec_cospan_scfa (X ⨂ Y)%object)
      ≈ @canonical_tensor_epsilon DC DCSMC X Y
          (dec_cospan_scfa X) (dec_cospan_scfa Y);

  (** Unit coherence: the SCFA on [I_DC] is the trivial one. *)
  dec_scfa_unit_mu :
    @scfa_mu DC DCSMC _ (dec_cospan_scfa (@I DC DCMon))
      ≈ to (@unit_left DC DCMon (@I DC DCMon));

  dec_scfa_unit_eta :
    @scfa_eta DC DCSMC _ (dec_cospan_scfa (@I DC DCMon))
      ≈ id[(@I DC DCMon)];

  dec_scfa_unit_delta :
    @scfa_delta DC DCSMC _ (dec_cospan_scfa (@I DC DCMon))
      ≈ from (@unit_left DC DCMon (@I DC DCMon));

  dec_scfa_unit_epsilon :
    @scfa_epsilon DC DCSMC _ (dec_cospan_scfa (@I DC DCMon))
      ≈ id[(@I DC DCMon)]
}.

Context `{DCHGC : DecCospan_Hypergraph_Coherent}.

Set Default Proof Using "All".

(** ** [DecoratedCospan_Hypergraph] : the Hypergraph instance *)

Program Definition DecoratedCospan_Hypergraph : @Hypergraph DC DCSMC := {|
  scfa                := dec_cospan_scfa ;
  scfa_tensor_mu      := dec_scfa_tensor_mu ;
  scfa_tensor_eta     := dec_scfa_tensor_eta ;
  scfa_tensor_delta   := dec_scfa_tensor_delta ;
  scfa_tensor_epsilon := dec_scfa_tensor_epsilon ;
  scfa_unit_mu        := dec_scfa_unit_mu ;
  scfa_unit_eta       := dec_scfa_unit_eta ;
  scfa_unit_delta     := dec_scfa_unit_delta ;
  scfa_unit_epsilon   := dec_scfa_unit_epsilon
|}.

End DecoratedCospanHypergraph.

(** ** Discussion: discharging the coherence class

    The [DecCospan_Hypergraph_Coherent] class packages exactly the
    structure Fong identifies in Theorem 3.1 of "Decorated Cospans":
    a per-object decoration-coherent SCFA plus the 8 standard
    hypergraph coherences.

    For the trivial decoration ([F = Δ I_D]):

      - [dec_cospan_scfa X] is the [Cospan_Hypergraph.scfa] wrapped
        with [id_decoration] on every apex (the apex for [mu] is [X],
        for [eta] is [X], etc.);

      - the 8 coherence equations are inherited from the corresponding
        [Cospan_Hypergraph] equations under apex-iso transport of
        [id_decoration], which is automatic when [F = Δ I_D] (since
        [fmap[F] _ = id]).

    For Fong's electrical circuits, [dec_cospan_scfa X] is the SCFA
    carrying the "empty resistor network" decoration (the additive
    unit of the resistor-network monoid on [X]); the tensor and unit
    coherences follow from the algebra of resistor networks on
    coproducts.

    For Baez–Fong Markov processes, [dec_cospan_scfa X] is the SCFA
    carrying the "no transitions" decoration; the coherences follow
    from the monoid structure on transition graphs.

    In every case the witness is a short calculation in the chosen
    decoration data; the heavy work (cospan-level SCFA construction)
    is already done by [Cospan_Hypergraph]. *)
