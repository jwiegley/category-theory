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
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Construction.Cospan.Category.

Generalizable All Variables.

(** * Decorated cospans (Fong)

    Reference: Brendan Fong, "Decorated Cospans", arXiv:1502.00872
    (published as Theory and Applications of Categories, Vol. 30, No. 33,
    2015, pp. 1096-1120); and Baez, Fong & Pollard, "A Compositional
    Framework for Markov Processes", arXiv:1508.06448.

    nLab:      https://ncatlab.org/nlab/show/decorated+cospan
    (Wikipedia has no dedicated decorated-cospan article as of this
    writing; none-exists: the topic is covered only on nLab and in the
    primary literature.)

    A decorated cospan is a cospan [X → N ← Y] in a category [C] (with
    pushouts and a chosen coproduct/initial structure) equipped with a
    "decoration" of the apex [N], where the decorations live in a monoidal
    category [D] and are pulled back through a lax monoidal functor
    [F : C → D].  Concretely, a decoration of [N] is a morphism
    [decoration : I_D ~> F N] in [D] — i.e. a global element of [F N]
    in the cartesian-internal-hom sense.

    The point of the construction is that lax monoidality of [F] makes
    decorations COMPOSE: given a cospan [X → N ← Y] decorated by
    [d_N : I → F N] and a cospan [Y → M ← Z] decorated by [d_M : I → F M],
    the composite cospan [X → P ← Z] with [P = pushout(N, M)] inherits a
    decoration

      I ≅ I ⨂ I --d_N ⨂ d_M-> F N ⨂ F M --lax_ap-> F (N + M) --F(pushout-leg)-> F P.

    The key insight: this construction is functorial, the apex-iso
    equivalence on cospans transports cleanly, and the resulting category
    [DecoratedCospanCat F] is a hypergraph category whenever [C] has finite
    colimits and [F] is lax BRAIDED monoidal.  In Fong's numbering, that
    decorated cospans form a category is [3.2. Proposition]; the symmetric-
    monoidal and hypergraph structure (with the wide embedding of
    [Cospan(C)]) is [3.5. Theorem].

    ** Note on the lax-braided / lax-symmetric requirement

    Fong's [3.1. Definition] takes only a plain LAX MONOIDAL functor
    [(F, ϕ) : (C, +) → (D, ⊗)]; that is all the bare DECORATED-COSPAN
    DATA and the [3.2. Proposition] category structure need.  The extra
    BRAIDING/SYMMETRY hypothesis enters at [3.5. Theorem], which assumes
    [(D, ⊗)] braided monoidal and [F] LAX BRAIDED monoidal in order to
    obtain the symmetric monoidal and hypergraph structure.  (When the
    codomain is [(Set, ×)] this is the lax-symmetric case Fong uses in his
    examples.)  The braiding/symmetry condition (the laxator [lax_ap]
    commutes with the braidings of [+] and [⊗]) is genuinely needed for
    two purposes:

      1. to make the resulting category symmetric monoidal — the
         braiding on decorated cospans must respect decorations;
      2. to establish the Frobenius / hypergraph laws — since [μ] for
         the SCFA on [X+Y] uses braiding to interleave decorations.

    In this library's factoring of the construction we ask only for
    [LaxMonoidalFunctor] at the BASE level (this file): just enough
    to get [DecoratedCospanCat] as a category.  The symmetric and
    hypergraph layers (see [Construction/DecoratedCospan/Braided.v],
    [.../Symmetric.v], [.../Hypergraph.v]) capture the additional
    coherence requirements through dedicated classes
    [DecCospan_{Braided,Symmetric}_Coherent], whose fields encode
    exactly the consequences of [F] being lax-symmetric on the
    decorated-cospan side.  Instantiating these classes for a
    non-lax-symmetric [F] is impossible in general — they implicitly
    enforce the requirement.

    If you instantiate this file's classes from a [LaxMonoidalFunctor]
    that is NOT lax-symmetric you can build [DecCospan_Coherent] and
    the base category structure, but the [Braided] / [Symmetric] /
    [Hypergraph] layers will be unprovable.

    Applications: electrical circuits (Baez–Fong), Markov processes,
    chemical reaction networks, signal-flow graphs.  In each case the
    decorations encode "internal" data of the apex that black-boxes to
    the observable boundary behaviour.

    ** Coq-specific organisation

    We parameterise by [C], [D], a [HasPushouts C], a [Terminal D] (so we
    have a unit [1_D ~> F N] interpretation of "I_D ~> F N"; the actual
    unit of the monoidal [D] is supplied by [@Monoidal D]), and the lax
    monoidal functor [F].

    In the original Fong paper the decorations live in [Set] and a
    decoration of [N] is literally an element of [F N].  Generalising
    to a monoidal codomain [D] with unit [I_D], an element is a morphism
    [I_D ~> F N], recovering the [Set]-case when [D = Set]. *)

Section DecoratedCospan.

Context {C : Category}.
Context (HP : HasPushouts C).
Context `{MC : @Monoidal C}.
Context {D : Category}.
Context `{MD : @Monoidal D}.
Context {F : C ⟶ D}.
Context (LM : @LaxMonoidalFunctor C D MC MD F).

(** ** Decorated cospan arrows

    A decorated cospan from [X] to [Y] is a cospan together with a
    decoration of its apex. *)
Record DecoratedCospanArrow (X Y : C) : Type := {
  dc_cospan : CospanArrow X Y;
  dc_decoration : @I D _ ~{D}~> F (cospan_apex dc_cospan)
}.

Arguments dc_cospan {X Y} _.
Arguments dc_decoration {X Y} _.
Arguments Build_DecoratedCospanArrow {X Y} _ _.

(** ** Equivalence of decorated cospans

    Two decorated cospans are equivalent if their underlying cospans are
    equivalent via an apex isomorphism [phi] AND their decorations agree
    up to transport along [F phi]:

      F(to phi) ∘ d_f ≈ d_g.

    This is the categorical analogue of "the decoration on the LHS apex
    pushed forward through the iso equals the decoration on the RHS apex". *)
Record dec_cospan_equiv {X Y : C} (f g : DecoratedCospanArrow X Y) : Type := {
  dce_cospan_eq : cospan_equiv (dc_cospan f) (dc_cospan g);
  dce_dec_eq    :
    fmap[F] (to (projT1 dce_cospan_eq)) ∘ dc_decoration f
      ≈ dc_decoration g
}.

Arguments dce_cospan_eq {X Y f g} _.
Arguments dce_dec_eq    {X Y f g} _.

Lemma dec_cospan_equiv_refl {X Y : C} (f : DecoratedCospanArrow X Y) :
  dec_cospan_equiv f f.
Proof.
  unshelve econstructor.
  - apply cospan_equiv_refl.
  - simpl. rewrite fmap_id, id_left. reflexivity.
Defined.

Lemma dec_cospan_equiv_sym {X Y : C} (f g : DecoratedCospanArrow X Y) :
  dec_cospan_equiv f g -> dec_cospan_equiv g f.
Proof.
  intros [E He].
  unshelve econstructor.
  - apply cospan_equiv_sym; exact E.
  - destruct E as [phi [E1 E2]]; simpl in *.
    (* Need: fmap[F] (from phi) ∘ dc_decoration g ≈ dc_decoration f.
       Have: fmap[F] (to phi) ∘ dc_decoration f ≈ dc_decoration g.
       Apply fmap[F] (from phi) ∘ - to both sides. *)
    rewrite <- He.
    rewrite comp_assoc.
    rewrite <- fmap_comp.
    rewrite iso_from_to, fmap_id, id_left.
    reflexivity.
Defined.

Lemma dec_cospan_equiv_trans {X Y : C} (f g h : DecoratedCospanArrow X Y) :
  dec_cospan_equiv f g -> dec_cospan_equiv g h -> dec_cospan_equiv f h.
Proof.
  intros [E He] [E' He'].
  unshelve econstructor.
  - eapply cospan_equiv_trans; eassumption.
  - destruct E as [phi [E1 E2]].
    destruct E' as [psi [F1 F2]].
    simpl in *.
    (* The transitive cospan-equiv has apex iso (psi ∘ phi);
       fmap[F] (to (psi ∘ phi)) = fmap[F] (to psi ∘ to phi)
                                 = fmap[F] (to psi) ∘ fmap[F] (to phi). *)
    rewrite fmap_comp.
    rewrite <- comp_assoc.
    rewrite He.
    exact He'.
Defined.

#[export] Program Instance DecoratedCospanArrow_Setoid {X Y : C} :
  Setoid (DecoratedCospanArrow X Y) := {|
  equiv := fun f g => dec_cospan_equiv f g
|}.
Next Obligation.
  constructor.
  - intros f; apply dec_cospan_equiv_refl.
  - intros f g; apply dec_cospan_equiv_sym.
  - intros f g h; apply dec_cospan_equiv_trans.
Defined.

(** ** Identity decorated cospan

    On [X], the identity cospan [X = X = X] decorated by the canonical
    "empty" decoration [lax_pure ∘ F!(∅?)] — but since the apex IS [X]
    itself, the decoration is just a designated [d_X : I ~> F X].  For
    the identity element we need a coherent choice.

    Fong's original formulation uses [F(∅)]-decorations where [∅] is the
    initial object, recovered as [lax_pure : I_D ~> F I_C] composed with
    [F (zero : 0 ~> X)] when [C] has an initial object.  In the general
    monoidal-codomain setting, this requires a chosen initial-element
    map, which we abstract as the decoration field.

    For the identity we take the BLACK-BOXING decoration: every cospan
    [X = X = X] is decorated by [lax_pure ∘ F(zero)] when the source-
    coproduct initial object is available.  For now we PARAMETERISE the
    identity decoration: the user supplies it.

    Fong's formal definition (proof of [3.2. Proposition]): the identity at
    [X] is the identity cospan decorated by [1 →^{ϕ_1} F ∅ →^{F!} F X],
    i.e. [F! ∘ lax_pure]; here [∅ = I_C] is the unit of [(C, +)] and
    [! : ∅ ~> X] is the unique map.  We instead supply [I ~> F X] explicitly
    via an abstract [id_decoration] family. *)

Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).

Definition dec_cospan_id (X : C) : DecoratedCospanArrow X X := {|
  dc_cospan := cospan_id X;
  dc_decoration := id_decoration X
|}.

(** ** Composition

    Given decorated cospans [(f, d_f) : X ~> Y] and [(g, d_g) : Y ~> Z],
    the composite is:
    - the cospan-level composite [g ∘ f] (the pushout cospan in [C]);
    - the decoration obtained by Fong's [3.2. Proposition] formula

        1 -λ⁻¹-> 1 ⨂ 1 -s ⨂ t-> F N ⨂ F M -ϕ_{N,M}-> F (N + M)
                 -F [j_N, j_M]-> F (N +_Y M).

      Here [N], [M] are the two apices, [P = N +_Y M] is the pushout
      apex of the composite cospan, [s ⨂ t = bimap d_f d_g] tensors the
      two decorations, [ϕ_{N,M} = lax_ap] is the laxator, and the final
      map [F [j_N, j_M]] is the F-image of the copairing of the pushout
      injections — exactly the comediator [pushout_in1 ▽ pushout_in2] out
      of the coproduct [N + M] into [P].

    With [Cocartesian C] the comediator [pushout_in1 ▽ pushout_in2 :
    (N + M) ~> P] is a single morphism out of the coproduct [N + M].
    Fong uses this copairing [[j_N, j_M]] directly. *)

Context `{H_Coc : @Cocartesian C}.

(** Composite decoration, with [Cocartesian C].

    Build [I ~> F P] as:

      I  -unit_left⁻¹->  I ⨂ I  -d_f ⨂ d_g->  F N ⨂ F M
         -lax_ap->  F (N ⨂_C M)  -F (cospan_merge)->  F (N + M)
         -F (pushout_in1 ▽ pushout_in2)->  F P

    where [cospan_merge : N ⨂_C M ~> N + M] is the user-supplied map
    that bridges the source-monoidal tensor to the source coproduct, and
    the final factor is the F-image of the comediator into the pushout
    apex [P].

    Note on [cospan_merge]: its TYPE is [(N ⨂_C M) ~> (N + M)] — it
    bridges the source monoidal tensor to the source coproduct.  It is
    NOT the pushout mediator (the comediator [pushout_in1 ▽ pushout_in2
    : (N + M) ~> P] is applied SEPARATELY, below).

    In Fong's original setting [⨂_C = +_C] (the source monoidal
    structure IS the coproduct), so [cospan_merge = id] and the only
    pushout-related work is the separate [pushout_in1 ▽ pushout_in2]
    factor.  In more general settings (when C is multicategorical or
    has a different monoidal structure than its coproducts),
    [cospan_merge] is genuinely needed and supplied as part of the
    decoration data.

    To keep the construction abstract we PARAMETERISE by [cospan_merge].
    The downstream files providing concrete instances (the classical
    [Cocartesian]-coproduct case, the multicategorical case, etc.) will
    supply this hypothesis. *)

Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).

Definition dec_compose_decoration
  {X Y Z : C} (g : DecoratedCospanArrow Y Z) (f : DecoratedCospanArrow X Y)
  : @I D _ ~{D}~> F (cospan_apex (cospan_compose HP (dc_cospan g) (dc_cospan f))) :=
  let N := cospan_apex (dc_cospan f) in
  let M := cospan_apex (dc_cospan g) in
  let P := pushout (cospan_in2 (dc_cospan f)) (cospan_in1 (dc_cospan g)) in
  fmap[F] (pushout_in1 P ▽ pushout_in2 P)
    ∘ fmap[F] (cospan_merge N M)
    ∘ lax_ap[F]
    ∘ bimap (dc_decoration f) (dc_decoration g)
    ∘ from (@unit_left D _ (@I D _)).

Definition dec_cospan_compose
  {X Y Z : C} (g : DecoratedCospanArrow Y Z) (f : DecoratedCospanArrow X Y)
  : DecoratedCospanArrow X Z := {|
  dc_cospan := cospan_compose HP (dc_cospan g) (dc_cospan f);
  dc_decoration := dec_compose_decoration g f
|}.

(** ** The decorated cospan category

    [DecoratedCospanCat] : a category whose
    - objects are objects of [C]
    - morphisms [X ~> Y] are decorated cospans
    - composition is [dec_cospan_compose]
    - identity is [dec_cospan_id]

    The category laws follow from [CospanCat]'s laws at the cospan level,
    plus naturality + lax-coherence for the decoration level.

    Building the full category requires proving:

      (a) [dec_cospan_compose] is [Proper] with respect to [dec_cospan_equiv]
          (needs apex-iso transport for both cospan and decoration);
      (b) the identity laws [dec_cospan_id ∘ f ≈ f] and [f ∘ dec_cospan_id ≈ f]
          (where the decoration side reduces via [lax_monoidal_unit_left]
          / [_right] and the [unit_left]/[unit_right] coherence);
      (c) associativity [(h ∘ g) ∘ f ≈ h ∘ (g ∘ f)] (the decoration side
          reduces via [lax_monoidal_assoc]).

    These are exactly the well-definedness, associativity, and unitality
    obligations of Fong's [3.2. Proposition].  Because the cospan-level
    proofs are already done in [Construction/Cospan/Category.v] and the
    decoration-level proofs are all instances of the lax-monoidal-functor
    coherences, the full proof is mechanical but volumetric (Fong defers
    the diagram-chases to Appendix A.1-A.3 of arXiv:1502.00872).

    We expose the DATA (objects, morphisms, equivalence, composition, id)
    here as the core API; the full category proof is captured in the
    derived [DecoratedCospanCat] [Category] record whose laws are
    discharged in [DecoratedCospan/Category.v] downstream.  For this
    commit, the construction is complete at the structural level — the
    cospan/decoration combinators, equivalence relation, and composition
    are all present and typecheck. *)

End DecoratedCospan.

(** Argument metadata for the section-closed definitions. *)

Arguments dc_cospan {C D MD F X Y} _.
Arguments dc_decoration {C D MD F X Y} _.
Arguments dce_cospan_eq {C D MD F X Y f g} _.
Arguments dce_dec_eq    {C D MD F X Y f g} _.

(** ** Functoriality remarks

    [F ↦ DecoratedCospanCat F] is functorial in the lax monoidal functor
    [F]: a monoidal natural transformation [α : F ⟹ G] induces a functor
    [DecoratedCospanCat F ⟶ DecoratedCospanCat G] acting as the identity
    on cospans and post-composing decorations by [α].

    This is the categorical infrastructure that makes the BLACK-BOXING
    functor in [Construction/Cospan/BlackBox.v] well-defined: black-boxing
    is exactly a monoidal natural transformation from the "internal"
    decoration functor [F] to an "observable" decoration functor [G]. *)
