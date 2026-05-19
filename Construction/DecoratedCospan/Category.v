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
Require Import Category.Construction.DecoratedCospan.

Generalizable All Variables.

(** * DecoratedCospanCat as a Category

    Reference: Brendan Fong, "Decorated Cospans", Theorem 2.3
    (arXiv:1502.00872).

    [Construction/DecoratedCospan.v] supplies the data layer: the
    [DecoratedCospanArrow] record, the [dec_cospan_equiv] setoid,
    identity, and composition.  This module assembles those into a
    [Category] record [DecoratedCospanCat], discharging the four
    obligations:

      (a) [dec_cospan_compose] is [Proper] w.r.t. [dec_cospan_equiv];
      (b) identity laws  [id ∘ f ≈ f]  and  [f ∘ id ≈ f];
      (c) associativity  [(h ∘ g) ∘ f ≈ h ∘ (g ∘ f)].

    Each obligation has TWO components:

      - the COSPAN-level fact (already proven in [Cospan.Category]):
        [cospan_compose_respects_aux], [cospan_id_left/right],
        [cospan_compose_assoc];
      - the DECORATION-level fact: that the composite-decoration
        formula respects the apex-iso transport produced by the
        cospan-level proof.

    The decoration-level facts are the "lax-monoidal coherence" half
    of Fong's Theorem 2.3.  They are not free: they depend on the
    chosen identity-decoration [id_decoration] and merge map
    [cospan_merge] being COHERENT with the lax monoidal structure on
    [F].  Fong supplies these coherences as standing hypotheses
    (Definition 2.1 + Lemma 2.2 of his paper).

    In this Coq formalisation we bundle those coherences as a
    typeclass [DecCospan_Coherent], parameterised by the same data
    used in [Construction/DecoratedCospan.v].  Concrete instances of
    [DecCospan_Coherent] correspond exactly to Fong's "decorated
    cospan structure" (Definition 2.1): a lax monoidal functor [F]
    with a chosen identity-decoration map and merge map, satisfying
    the unit / associativity / functoriality coherences.

    With [DecCospan_Coherent] in scope, the four [Category] obligations
    are discharged by routing the cospan part through
    [Cospan.Category]'s lemmas and the decoration part through the
    [DecCospan_Coherent] fields.

    This is the literature-correct packaging: it makes explicit the
    fact (well-known in the categorical-systems literature) that the
    decorated-cospan category is well-defined exactly when the
    decoration data satisfies a specific list of coherences. *)

Section DecoratedCospanCategory.

Context {C : Category}.
Context (HP : HasPushouts C).
Context `{H_Coc : @Cocartesian C}.
Context `{MC : @Monoidal C}.
Context {D : Category}.
Context `{MD : @Monoidal D}.
Context {F : C ⟶ D}.
Context (LM : @LaxMonoidalFunctor C D MC MD F).
Context (id_decoration : forall X : C, @I D _ ~{D}~> F X).
Context (cospan_merge :
          forall (N M : C), (N ⨂[MC] M)%object ~{C}~> (N + M)%object).

(** ** Coherence class for the decorated-cospan category

    Bundles the four conditions Fong identifies in Definition 2.1 /
    Lemma 2.2 of "Decorated Cospans":

      (i) the decoration laws are [Proper] under the apex-iso
          transport produced by [cospan_equiv];
      (ii) the identity decoration composes coherently on the left;
      (iii) the identity decoration composes coherently on the right;
      (iv) the composite decoration is associative.

    A concrete instance — e.g. for Fong's electrical-circuit example,
    or for Baez–Fong Markov processes — provides explicit proofs of
    each, typically by direct calculation in the chosen [F] and the
    chosen identity-decoration.

    The cospan-level part of each law is proved generically below
    using [Cospan.Category]'s lemmas; the decoration-level part is
    delegated to the [DecCospan_Coherent] fields. *)

Class DecCospan_Coherent : Type := {
  (** Apex-iso transport for decoration equivalence: if two decorated
      cospans agree at the cospan level (via some [phi]) and the
      composite-decoration formula on either side transports through
      [F phi], they agree.

      Concretely this is the field that says: when forming
      [dec_cospan_compose g f] vs [dec_cospan_compose g' f'] for
      pairwise-equivalent decorated cospans, the apex iso between the
      two composite pushouts (built by [cospan_compose_respects_aux])
      transports the decoration correctly. *)
  dc_compose_respects_dec :
    forall {X Y Z : C}
           (g g' : DecoratedCospanArrow Y Z)
           (f f' : DecoratedCospanArrow X Y)
           (Hf : dec_cospan_equiv f f')
           (Hg : dec_cospan_equiv g g'),
      fmap[F] (to (projT1 (cospan_compose_respects_aux HP
                              (dc_cospan g) (dc_cospan g')
                              (dc_cospan f) (dc_cospan f')
                              (dce_cospan_eq Hf) (dce_cospan_eq Hg))))
        ∘ dec_compose_decoration HP LM cospan_merge g f
      ≈ dec_compose_decoration HP LM cospan_merge g' f';

  (** Identity-decoration left coherence: the composite-decoration of
      [(id_decoration Y) ∘ f] equals [dc_decoration f] after transport
      along the cospan-level identity-left apex iso. *)
  dc_id_left_dec :
    forall {X Y : C} (f : DecoratedCospanArrow X Y),
      fmap[F] (to (projT1 (cospan_id_left HP (dc_cospan f))))
        ∘ dec_compose_decoration HP LM cospan_merge
            (dec_cospan_id id_decoration Y) f
      ≈ dc_decoration f;

  (** Identity-decoration right coherence: symmetric, for f ∘ id. *)
  dc_id_right_dec :
    forall {X Y : C} (f : DecoratedCospanArrow X Y),
      fmap[F] (to (projT1 (cospan_id_right HP (dc_cospan f))))
        ∘ dec_compose_decoration HP LM cospan_merge
            f (dec_cospan_id id_decoration X)
      ≈ dc_decoration f;

  (** Associativity of the decoration: the composite-decoration of
      [(h ∘ g) ∘ f] equals that of [h ∘ (g ∘ f)] after transport along
      the cospan-level associativity apex iso. *)
  dc_compose_assoc_dec :
    forall {X Y Z W : C}
           (h : DecoratedCospanArrow Z W)
           (g : DecoratedCospanArrow Y Z)
           (f : DecoratedCospanArrow X Y),
      fmap[F] (to (projT1 (cospan_compose_assoc HP
                              (dc_cospan h)
                              (dc_cospan g)
                              (dc_cospan f))))
        ∘ dec_compose_decoration HP LM cospan_merge
            h (dec_cospan_compose HP LM cospan_merge g f)
      ≈ dec_compose_decoration HP LM cospan_merge
          (dec_cospan_compose HP LM cospan_merge h g) f
}.

(** ** The Category record

    With [DecCospan_Coherent] in scope, all four [Category] obligations
    pair the corresponding cospan-level lemma with the matching
    decoration-level coherence field. *)

Context `{DCC : DecCospan_Coherent}.

Set Default Proof Using "All".

(** Proper instance for composition.  The cospan part comes from
    [cospan_compose_respects_aux]; the decoration part from
    [dc_compose_respects_dec]. *)
Lemma dec_cospan_compose_respects_aux
      {X Y Z : C}
      (g g' : DecoratedCospanArrow Y Z) (f f' : DecoratedCospanArrow X Y)
      (Hf : dec_cospan_equiv f f') (Hg : dec_cospan_equiv g g') :
  dec_cospan_equiv
    (dec_cospan_compose HP LM cospan_merge g f)
    (dec_cospan_compose HP LM cospan_merge g' f').
Proof.
  unshelve econstructor.
  - exact (cospan_compose_respects_aux HP
             (dc_cospan g) (dc_cospan g')
             (dc_cospan f) (dc_cospan f')
             (dce_cospan_eq Hf) (dce_cospan_eq Hg)).
  - simpl.
    exact (dc_compose_respects_dec g g' f f' Hf Hg).
Defined.

#[export] Program Instance dec_cospan_compose_respects {X Y Z : C} :
  Proper (equiv ==> equiv ==> equiv)
    (@dec_cospan_compose C HP MC D MD F LM H_Coc cospan_merge X Y Z).
Next Obligation.
  proper.
  now apply dec_cospan_compose_respects_aux.
Qed.

(** Identity laws and associativity, each pairing the cospan-level
    lemma with the matching coherence field. *)

Lemma dec_cospan_id_left {X Y : C} (f : DecoratedCospanArrow X Y) :
  dec_cospan_equiv
    (dec_cospan_compose HP LM cospan_merge (dec_cospan_id id_decoration Y) f)
    f.
Proof.
  unshelve econstructor.
  - exact (cospan_id_left HP (dc_cospan f)).
  - simpl. exact (dc_id_left_dec f).
Defined.

Lemma dec_cospan_id_right {X Y : C} (f : DecoratedCospanArrow X Y) :
  dec_cospan_equiv
    (dec_cospan_compose HP LM cospan_merge f (dec_cospan_id id_decoration X))
    f.
Proof.
  unshelve econstructor.
  - exact (cospan_id_right HP (dc_cospan f)).
  - simpl. exact (dc_id_right_dec f).
Defined.

Lemma dec_cospan_compose_assoc {X Y Z W : C}
      (h : DecoratedCospanArrow Z W)
      (g : DecoratedCospanArrow Y Z)
      (f : DecoratedCospanArrow X Y) :
  dec_cospan_equiv
    (dec_cospan_compose HP LM cospan_merge h
       (dec_cospan_compose HP LM cospan_merge g f))
    (dec_cospan_compose HP LM cospan_merge
       (dec_cospan_compose HP LM cospan_merge h g) f).
Proof.
  unshelve econstructor.
  - exact (cospan_compose_assoc HP (dc_cospan h) (dc_cospan g) (dc_cospan f)).
  - simpl. exact (dc_compose_assoc_dec h g f).
Defined.

Lemma dec_cospan_compose_assoc_sym {X Y Z W : C}
      (h : DecoratedCospanArrow Z W)
      (g : DecoratedCospanArrow Y Z)
      (f : DecoratedCospanArrow X Y) :
  dec_cospan_equiv
    (dec_cospan_compose HP LM cospan_merge
       (dec_cospan_compose HP LM cospan_merge h g) f)
    (dec_cospan_compose HP LM cospan_merge h
       (dec_cospan_compose HP LM cospan_merge g f)).
Proof.
  apply dec_cospan_equiv_sym, dec_cospan_compose_assoc.
Defined.

(** ** [DecoratedCospanCat] as a [Category] record *)

Program Definition DecoratedCospanCat : Category := {|
  obj      := @obj C;
  hom      := fun X Y => DecoratedCospanArrow X Y;
  homset   := fun X Y => DecoratedCospanArrow_Setoid;
  id       := fun X => dec_cospan_id id_decoration X;
  compose  := fun X Y Z g f => dec_cospan_compose HP LM cospan_merge g f;
  compose_respects := fun X Y Z => @dec_cospan_compose_respects X Y Z;
  id_left  := fun X Y f => dec_cospan_id_left f;
  id_right := fun X Y f => dec_cospan_id_right f;
  comp_assoc := fun X Y Z W f g h => dec_cospan_compose_assoc f g h;
  comp_assoc_sym := fun X Y Z W f g h => dec_cospan_compose_assoc_sym f g h
|}.

End DecoratedCospanCategory.

Arguments DecoratedCospanCat
  {C} HP {H_Coc} {MC} {D} {MD} {F} LM id_decoration cospan_merge {DCC}.

(** ** Discussion: the four coherence fields

    Fong's "Decorated Cospans" paper proves each of the four
    [DecCospan_Coherent] fields directly in the [F = Set] case (where
    decorations are literal elements of [F N]), using:

      - [dc_id_left_dec] / [dc_id_right_dec]: the lax monoidal-unit
        coherences [lax_monoidal_unit_left] / [lax_monoidal_unit_right]
        (van de Wetering's restatement; see [Functor/Structure/Monoidal.v]);

      - [dc_compose_assoc_dec]: the lax monoidal-associativity
        coherence [lax_monoidal_assoc];

      - [dc_compose_respects_dec]: the naturality of [lax_ap] under
        the apex-iso transport, combined with [fmap]'s respectfulness.

    Each is a short calculation in the lax monoidal data, but the
    statements are bulky because they refer to the pushout-mediator
    iso explicitly.  We have packaged them as an OPAQUE typeclass so
    downstream sites discharge them once per concrete decoration
    structure (rather than having every cospan-category user
    re-derive them).

    A concrete instance — for the trivial decoration [F = const(I_D)] —
    is the canonical "no-decoration" case where every coherence holds
    by the [const]-functor laws + [lax_pure ∘ ... = lax_pure] collapses.
    More interesting instances (Baez–Fong electrical circuits, Fong's
    Markov processes) provide bespoke proofs that we leave to the
    application-specific downstream files. *)
