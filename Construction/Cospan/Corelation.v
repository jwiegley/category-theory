Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Construction.Span.Category.
Require Import Category.Construction.Cospan.Category.

Generalizable All Variables.

(** * Corelations: jointly-epic cospans

    A *corelation* from [X] to [Y] is a cospan [X -in1-> N <-in2- Y] whose
    copairing
        [in1, in2] := cospan_in1 ▽ cospan_in2 : X + Y ~> N
    is an epimorphism in [C].  Equivalently, the cospan apex is the
    image of [X + Y] under the cocone formed by its two legs.

    Corelations form a subcategory of [CospanCat C] when [C] has the
    "epi-stable pushouts" property: pushouts of epis along arbitrary
    morphisms are again epis.  This property is automatic in pretoposes
    (sets, presheaves, …) but must be carried as a hypothesis in the
    general setting.  We expose it as a typeclass [EpiStablePushouts].

    Reference: Fong–Spivak, "The Algebra of Open and Interconnected
    Systems" — corelations are introduced as the image factorisation of
    cospans through their jointly-surjective representative. *)

Section Corelation.

Context {C : Category}.
Context `{@Cocartesian C}.

(** A corelation is a cospan together with a proof that its copairing
    is epic.  We package this as a record so that downstream code can
    extract the copairing-epi witness without re-deriving it. *)
Record CorelationArrow (X Y : C) : Type := {
  corelation_cospan : CospanArrow X Y;
  corelation_copairing_epic :
    Epic (cospan_in1 corelation_cospan ▽ cospan_in2 corelation_cospan)
}.

Arguments corelation_cospan {X Y} _.
Arguments corelation_copairing_epic {X Y} _.

(** Coercion: a corelation IS a cospan. *)
Coercion corelation_cospan : CorelationArrow >-> CospanArrow.

(** Two corelations are equivalent iff their underlying cospans are. *)
Definition corelation_equiv {X Y : C} (f g : CorelationArrow X Y) : Type :=
  cospan_equiv (corelation_cospan f) (corelation_cospan g).

#[export] Program Instance CorelationArrow_Setoid {X Y : C} :
  Setoid (CorelationArrow X Y) := {|
  equiv := fun f g => corelation_equiv f g
|}.
Next Obligation.
  unfold corelation_equiv.
  constructor.
  - intros f.
    apply (@Equivalence_Reflexive _ _
             (@setoid_equiv _ (@CospanArrow_Setoid C X Y))).
  - intros f g.
    apply (@Equivalence_Symmetric _ _
             (@setoid_equiv _ (@CospanArrow_Setoid C X Y))).
  - intros f g h.
    apply (@Equivalence_Transitive _ _
             (@setoid_equiv _ (@CospanArrow_Setoid C X Y))).
Defined.

(** The identity cospan is a corelation: its copairing is
    [id ▽ id : X + X ~> X], which is the codiagonal — an epi. *)
Lemma id_copairing_epic (X : C) :
  Epic (cospan_in1 (cospan_id X) ▽ cospan_in2 (cospan_id X)).
Proof.
  unfold cospan_id, cospan_in1, cospan_in2; simpl.
  constructor.
  intros Z g1 g2 Heq.
  (* g1 ∘ (id ▽ id) ≈ g2 ∘ (id ▽ id) implies g1 ≈ g2.
     Compose both sides with inl: g1 ∘ (id ▽ id) ∘ inl ≈ g2 ∘ (id ▽ id) ∘ inl.
     But (id ▽ id) ∘ inl = id, so g1 ≈ g2. *)
  assert (Hl : g1 ≈ g2).
  { specialize (Heq).
    pose proof (compose_respects _ _ Heq id[X + X] id[X + X] (reflexivity _)) as _.
    rewrite <- (id_right g1).
    rewrite <- (@inl_merge _ _ X X X id[X] id[X]).
    rewrite comp_assoc.
    rewrite Heq.
    rewrite <- comp_assoc.
    rewrite (@inl_merge _ _ X X X id[X] id[X]).
    apply id_right. }
  exact Hl.
Qed.

Definition corelation_id (X : C) : CorelationArrow X X :=
  {| corelation_cospan := cospan_id X;
     corelation_copairing_epic := id_copairing_epic X |}.

(** ** Composition: requires epi-stable pushouts

    The composite of two corelations is a corelation only when pushouts
    preserve epimorphisms.  We carry this as a typeclass hypothesis. *)

Context (HP : HasPushouts C).

Class EpiStablePushouts : Type := {
  pushout_preserves_epic :
    forall {x y z : C} (f : x ~> y) (g : x ~> z),
      Epic f -> Epic (@pushout_in2 C x y z f g (pushout f g));

  pushout_preserves_epic_sym :
    forall {x y z : C} (f : x ~> y) (g : x ~> z),
      Epic g -> Epic (@pushout_in1 C x y z f g (pushout f g))
}.

Context `{EpiStablePushouts}.

(** Composition of corelations is the corelation whose underlying cospan is
    the cospan composition. The copairing of the composite is epic because
    the underlying pushout coprojections preserve epicity (by the
    [EpiStablePushouts] hypothesis) and epis compose.

    The full proof that [composite copairing is epic] is non-trivial:
    one shows that the composite copairing factors as a composition of
    epis built from [f]'s and [g]'s copairings and the pushout
    injections.

    The key sub-lemma — that the composite copairing of the cospan
    composition is epic when the input copairings are epic, modulo the
    [EpiStablePushouts] hypothesis — is structurally a diagram chase.
    For V2a we record the composition data and leave the [Epic] proof
    obligation as a marker; downstream users supplying concrete
    categories with explicit epi-stability arguments can discharge it
    directly.

    See the [TODO(V2b)] note at the end of this file. *)

(** Underlying cospan-level composition of corelations. *)
Definition corelation_underlying_compose
           {X Y Z : C}
           (g : CorelationArrow Y Z) (f : CorelationArrow X Y)
  : CospanArrow X Z :=
  cospan_compose HP (corelation_cospan g) (corelation_cospan f).

End Corelation.

Arguments CorelationArrow {C _} X Y.
Arguments corelation_cospan {C _ X Y} _.
Arguments corelation_copairing_epic {C _ X Y} _.
Arguments corelation_id {C _} X.

(** ** Pending V2b obligations

    To upgrade [CorelationArrow] into a full [Category], we need:

    1. A proof that [corelation_underlying_compose] yields an epic
       copairing whenever the inputs do.  This requires
       [EpiStablePushouts] PLUS a diagram chase establishing that the
       composite copairing factors through the pushout injections and
       the input copairings.

    2. The category laws (id_left, id_right, assoc) come for free from
       [CospanCat C] via the coercion.

    Obligation 1 alone is ~30-50 lines of careful diagram chasing, and
    has a separate sticking point in pretoposes vs general categories
    (where the pushout-of-epis condition needs to be stated more
    carefully).  The current file delivers the typed record and the
    identity construction; V2b can pick up the composition.

    Alternatively, for the common case where [C] is a pretopos (sets,
    presheaves, etc.), the epi-stability is automatic and the
    composition proof simplifies.  A concrete [CorelCat Sets] instance
    is a natural V2b starting point.

    Reference: nLab "corelation", Fong–Spivak "Algebra of Open
    Systems" Theorem 4.2.5. *)

(* TODO(V2b): Prove that corelation composition preserves epic copairing *)
(* TODO(V2b): Construct CorelCat C HP : Category given EpiStablePushouts *)
(* TODO(V2b): Prove CorelCat is a wide subcategory of CospanCat *)
(* TODO(V2b): Instance EpiStablePushouts (Sets) once Sets has pushouts *)
