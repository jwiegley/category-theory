Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Construction.Span.Category.
Require Import Category.Construction.Cospan.Category.

Generalizable All Variables.

(** * Hypergraph structure on [CospanCat C]

    Mathematical content (cf. Carboni–Walters, Fong–Spivak):

    Given a category [C] with finite colimits (an initial object [0],
    binary coproducts [+], and binary pushouts), the cospan category
    [CospanCat C] is a symmetric monoidal category with tensor given by
    the coproduct of [C]:

      X ⨂ Y   :=  X + Y               (in C)
      I       :=  0                    (initial object of C)
      f ⨂ g  :=  the cospan with apex [apex f + apex g] and legs
                   [cover (cospan_in1 f) (cospan_in1 g)],
                   [cover (cospan_in2 f) (cospan_in2 g)]

    Each object [X] carries a canonical SCFA built from the cocartesian
    structure:

      μ_X     : cospan X+X ~> X via apex X, leg1 = [id ▽ id], leg2 = id
      η_X     : cospan 0 ~> X via apex X, leg1 = zero, leg2 = id
      δ_X     : cospan X ~> X+X (the opposite of μ as a cospan)
      ε_X     : cospan X ~> 0 (the opposite of η as a cospan)

    --------------------------------------------------------------------

    Status: V2a delivers the typed *data* of this construction —
    [Cospan_tensor_obj], [Cospan_unit_obj], [cospan_tensor] (tensor of
    morphisms), and the SCFA-witness cospans [cospan_scfa_mu],
    [cospan_scfa_eta], [cospan_scfa_delta], [cospan_scfa_epsilon].

    The full [Monoidal (CospanCat C)] / [SymmetricMonoidal] / [Hypergraph]
    proof obligations (naturality of associator/unitors, triangle and
    pentagon, braid coherence, SCFA axioms in the cospan setoid, and
    tensor/unit coherence on the [Hypergraph] class) decompose into a
    large body of cospan-equiv pushout diagrams.  Each individual
    diagram is mechanical, but the aggregate (~500-1000 lines of
    structured pushout coherence proofs) exceeds the V2a budget; these
    obligations are deferred to V2b.

    For V2a consumers who need a concrete [Hypergraph] instance now:

      (a) Instantiate [Hypergraph] directly for your concrete category
          (e.g. [Cospan(Sets)]) using the data definitions below plus
          your category's specific axioms, OR
      (b) Work at the level of the algebraic classes [Monoid] /
          [Comonoid] / [Frobenius] / [SpecialCommutativeFrobenius]
          directly on your objects — V2a fully delivers these, plus the
          [Hypergraph_CompactClosed] derivation and the [Spider] lemmas.

    See [docs/HYPERGRAPH_MIGRATION.md] for the migration story. *)

Section CospanHypergraphData.

Context {C : Category}.
Context `{@Cocartesian C}.
Context `{@Initial C}.
Context (HP : HasPushouts C).

(** ** Object-level tensor and unit *)

Definition Cospan_tensor_obj (X Y : C) : C := X + Y.
Definition Cospan_unit_obj : C := initial_obj.

(** ** Cospan-level tensor of morphisms

    Given cospans [f : X ~> Y] (apex [Nf]) and [g : X' ~> Y'] (apex [Ng]),
    the tensor cospan [f ⨂ g : X+X' ~> Y+Y'] has apex [Nf + Ng] and legs
    obtained by [cover]-ing the legs of [f] and [g]. *)
Definition cospan_tensor
           {X Y X' Y' : C}
           (f : CospanArrow X Y) (g : CospanArrow X' Y')
  : CospanArrow (X + X') (Y + Y') :=
  Build_CospanArrow (cospan_apex f + cospan_apex g)
                    (cover (cospan_in1 f) (cospan_in1 g))
                    (cover (cospan_in2 f) (cospan_in2 g)).

(** ** SCFA-witness data on each object [X] *)

(** Multiplication [μ_X] : a cospan from [X + X] to [X] with apex [X],
    leg1 = codiagonal [id ▽ id], leg2 = identity. *)
Definition cospan_scfa_mu (X : C) : CospanArrow (X + X) X :=
  Build_CospanArrow X (id[X] ▽ id[X]) id[X].

(** Unit [η_X] : a cospan from [0] to [X] with apex [X],
    leg1 = [zero], leg2 = identity. *)
Definition cospan_scfa_eta (X : C) : CospanArrow Cospan_unit_obj X :=
  Build_CospanArrow X zero id[X].

(** Comultiplication [δ_X] : a cospan from [X] to [X + X] with apex [X],
    leg1 = identity, leg2 = codiagonal.

    Note: as a cospan from X to X+X, leg1 : X ~> apex and leg2 : X+X ~> apex. *)
Definition cospan_scfa_delta (X : C) : CospanArrow X (X + X) :=
  Build_CospanArrow X id[X] (id[X] ▽ id[X]).

(** Counit [ε_X] : a cospan from [X] to [0] with apex [X], leg1 = id, leg2 = zero. *)
Definition cospan_scfa_epsilon (X : C) : CospanArrow X Cospan_unit_obj :=
  Build_CospanArrow X id[X] zero.

End CospanHypergraphData.

Arguments Cospan_tensor_obj {C _} X Y.
Arguments Cospan_unit_obj   {C _}.
Arguments cospan_tensor     {C _} {X Y X' Y'} f g.
Arguments cospan_scfa_mu      {C _} X.
Arguments cospan_scfa_eta     {C _} X.
Arguments cospan_scfa_delta   {C _} X.
Arguments cospan_scfa_epsilon {C _} X.

(** ** Pending coherence obligations (V2b)

    To upgrade the above DATA to a full [Hypergraph (CospanCat C)]
    instance, the following coherence proofs are needed.  Each is a
    cospan-equiv diagram involving pushouts in [C]:

    1. [cospan_tensor] is a bifunctor [CospanCat C ∏ CospanCat C ⟶ CospanCat C]
       (preserves identity and composition, up to cospan-equiv).  This
       requires the pushout-of-coproducts compatibility:
       [pushout (cover f1 g1) (cover f2 g2)] is iso to
       [pushout f1 f2 + pushout g1 g2], which uses the universal property
       of coproducts twice.
    2. The unitor cospans [unit_left], [unit_right] are isomorphisms in
       [CospanCat C] (built from [coprod_zero_l] / [coprod_zero_r] of
       [Structure/Cocartesian.v]), with naturality through the tensor.
    3. The associator cospan [tensor_assoc] is an isomorphism (built
       from [coprod_assoc]), with naturality.
    4. The triangle and pentagon coherence diagrams commute in the
       cospan setoid.
    5. The braid cospan [braid] is an isomorphism with [braid_invol]
       and hexagon coherence (built from [coprod_comm] / [paws] of
       [Structure/Cocartesian.v]).
    6. The SCFA data above satisfies the monoid, comonoid, Frobenius,
       commutativity, and specialness axioms — in the cospan setoid.
       The Frobenius axiom in particular requires showing
       [(μ ⨂ id) ∘ α⁻¹ ∘ (id ⨂ δ) ≈ δ ∘ μ] as cospans, which
       reduces to a pushout-of-pushout diagram in [C] that ultimately
       collapses to the codiagonal identity [(id ▽ id) ∘ (id ▽ id) = id ▽ id].
    7. The tensor coherence of the [Hypergraph] class:
       [scfa_tensor_mu], [scfa_tensor_eta], [scfa_tensor_delta],
       [scfa_tensor_epsilon] for [X ⨂ Y = X + Y].
    8. The unit coherence: [scfa_unit_mu], [scfa_unit_eta],
       [scfa_unit_delta], [scfa_unit_epsilon] — the SCFA on [0] is trivial.

    Together (1)-(8) amount to ~500-1000 lines of structured cospan-equiv
    pushout diagrams.  Each individual obligation is mechanical via the
    [cospan_compose_apex] / [cospan_compose_in1] / [cospan_compose_in2]
    accessors plus the pushout universal property, but the aggregate
    exceeds the V2a budget.

    Sticking point identified during V2a scoping: even the bifunctoriality
    of [cospan_tensor] (obligation 1) requires constructing, for each
    composable pair of cospan-pairs [(f1, g1), (f2, g2)], a canonical iso
    of pushout apexes
      [pushout (cover (cospan_in2 f1) (cospan_in2 g1))
               (cover (cospan_in1 f2) (cospan_in1 g2))]
      ≅
      [pushout (cospan_in2 f1) (cospan_in1 f2)
        + pushout (cospan_in2 g1) (cospan_in1 g2)]
    which is itself a non-trivial pushout-pasting lemma.  This needs to
    be proved once and re-used in obligations 2-8; the lemma alone is
    ~150 lines.  *)

(* TODO(V2b): cospan_tensor as a Bifunctor on CospanCat C *)
(* TODO(V2b): Monoidal (CospanCat C) instance (associator, unitors, coherence) *)
(* TODO(V2b): SymmetricMonoidal (CospanCat C) (braid + hexagon + invol) *)
(* TODO(V2b): SCFA axioms for cospan_scfa_{mu,eta,delta,epsilon} as cospans *)
(* TODO(V2b): Hypergraph (CospanCat C) instance (tensor + unit coherence) *)
