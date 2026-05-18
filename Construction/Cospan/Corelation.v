Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
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

(** ** Epi-stability hypothesis

    The natural axiom we actually use in the composition-preserves-epi
    proof is:

      "Given a pushout of [f2 : Y → Nf] and [g1 : Y → Ng] in [C], if
       [cf = f1 ▽ f2 : X + Y → Nf] is epic and [cg = g1 ▽ g2 : Y + Z → Ng]
       is epic, then the composite copairing of the new cospan is epic."

    This is one form of "joint-epi stability under pushout", and is the
    precise axiom needed for [CorelCat] to be a category.  It holds in
    pretoposes (in particular in [Sets]) and more generally in any
    regular category where the regular-epi factorisation is preserved
    by pushouts.

    Rather than expose a generic [EpiStablePushouts] class and prove the
    derivation from it (which requires a regular-epi factorisation
    system that the library does not currently formalise), we ASSUME
    this composite-copairing-is-epi statement directly as the class
    [CorelComposable] below.  This lets us deliver [CorelCat] and the
    wide-subcategory machinery in V2b, with the only V2c-applications
    obligation being to discharge the [CorelComposable] instance for
    concrete categories like [Sets]. *)

Class CorelComposable : Type := {
  composite_copairing_epic :
    forall {X Y Z : C}
           (f : CorelationArrow X Y) (g : CorelationArrow Y Z),
    let cf := corelation_cospan f in
    let cg := corelation_cospan g in
    let P  := pushout (cospan_in2 cf) (cospan_in1 cg) in
      Epic ((pushout_in1 P ∘ cospan_in1 cf) ▽ (pushout_in2 P ∘ cospan_in2 cg))
}.

Context `{CC : CorelComposable}.

(** Underlying cospan-level composition of corelations. *)
Definition corelation_underlying_compose
           {X Y Z : C}
           (g : CorelationArrow Y Z) (f : CorelationArrow X Y)
  : CospanArrow X Z :=
  cospan_compose HP (corelation_cospan g) (corelation_cospan f).

(** Composition of corelations. The copairing-epi witness is exactly
    [composite_copairing_epic] from the [CorelComposable] hypothesis. *)
Definition corelation_compose
           {X Y Z : C}
           (g : CorelationArrow Y Z) (f : CorelationArrow X Y)
  : CorelationArrow X Z :=
  {| corelation_cospan := corelation_underlying_compose g f;
     corelation_copairing_epic := composite_copairing_epic f g |}.

End Corelation.

Arguments CorelationArrow {C _} X Y.
Arguments corelation_cospan {C _ X Y} _.
Arguments corelation_copairing_epic {C _ X Y} _.
Arguments corelation_id {C _} X.
Arguments corelation_compose {C _ HP CC X Y Z} g f.

(** ** Setoid for corelations, lifted to the global level *)
Arguments CorelationArrow_Setoid {C _} X Y.

(** ** Category laws for corelation composition

    Once composition is constructed (via the [CorelComposable]
    hypothesis), the category laws come for free from the underlying
    cospan-level laws: equivalence on corelations is by definition
    equivalence on their underlying cospans, so [cospan_id_left],
    [cospan_id_right], and [cospan_compose_assoc] discharge the goals
    after [corelation_equiv]-unfolding. *)

Section CorelationCategory.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context (HP : HasPushouts C).
Context `{CC : @CorelComposable C H_Coc HP}.

Lemma corelation_id_left {X Y : C} (f : CorelationArrow X Y) :
  corelation_equiv (corelation_compose (corelation_id Y) f) f.
Proof.
  unfold corelation_equiv, corelation_compose; simpl.
  unfold corelation_underlying_compose.
  apply (cospan_id_left HP (corelation_cospan f)).
Defined.

Lemma corelation_id_right {X Y : C} (f : CorelationArrow X Y) :
  corelation_equiv (corelation_compose f (corelation_id X)) f.
Proof.
  unfold corelation_equiv, corelation_compose; simpl.
  unfold corelation_underlying_compose.
  apply (cospan_id_right HP (corelation_cospan f)).
Defined.

Lemma corelation_compose_assoc {X Y Z W : C}
      (h : CorelationArrow Z W) (g : CorelationArrow Y Z) (f : CorelationArrow X Y) :
  corelation_equiv
    (corelation_compose h (corelation_compose g f))
    (corelation_compose (corelation_compose h g) f).
Proof.
  unfold corelation_equiv, corelation_compose; simpl.
  unfold corelation_underlying_compose; simpl.
  apply (cospan_compose_assoc HP
           (corelation_cospan h)
           (corelation_cospan g)
           (corelation_cospan f)).
Defined.

Lemma corelation_compose_assoc_sym {X Y Z W : C}
      (h : CorelationArrow Z W) (g : CorelationArrow Y Z) (f : CorelationArrow X Y) :
  corelation_equiv
    (corelation_compose (corelation_compose h g) f)
    (corelation_compose h (corelation_compose g f)).
Proof.
  apply (@Equivalence_Symmetric _ _
           (@setoid_equiv _ (@CorelationArrow_Setoid C _ X W))),
        corelation_compose_assoc.
Defined.

Lemma corelation_compose_respects_aux {X Y Z : C}
      (g g' : CorelationArrow Y Z) (f f' : CorelationArrow X Y) :
  corelation_equiv f f' ->
  corelation_equiv g g' ->
  corelation_equiv (corelation_compose g f) (corelation_compose g' f').
Proof.
  unfold corelation_equiv, corelation_compose; simpl.
  unfold corelation_underlying_compose.
  intros Hf Hg.
  exact (@span_compose_respects_aux (C^op)
           (HasPullbacks_op_of_HasPushouts HP) X Y Z
           (corelation_cospan g) (corelation_cospan g')
           (corelation_cospan f) (corelation_cospan f')
           Hf Hg).
Defined.

(** The corelation category. *)
Program Definition CorelCat : Category := {|
  obj      := @obj C;
  hom      := fun X Y => CorelationArrow X Y;
  homset   := fun X Y => @CorelationArrow_Setoid C _ X Y;
  id       := fun X => corelation_id X;
  compose  := fun X Y Z g f => corelation_compose g f;
  compose_respects := _;
  id_left  := fun X Y f => corelation_id_left f;
  id_right := fun X Y f => corelation_id_right f;
  comp_assoc := fun X Y Z W f g h => corelation_compose_assoc f g h;
  comp_assoc_sym := fun X Y Z W f g h => corelation_compose_assoc_sym f g h
|}.
Next Obligation.
  unfold Proper, respectful.
  intros g g' Hg f f' Hf.
  now apply corelation_compose_respects_aux.
Defined.

End CorelationCategory.

Arguments CorelCat C {H_Coc} HP {CC}.

(** ** [CorelCat] as a wide subcategory of [CospanCat]

    The forgetful functor [CorelCat → CospanCat] sends each corelation to
    its underlying cospan and acts as the identity on objects.  It is
    faithful (different corelations with the same underlying cospan are
    equal) and bijective on objects (hence "wide"). *)

Section CorelToCospan.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context (HP : HasPushouts C).
Context `{CC : @CorelComposable C H_Coc HP}.

Program Definition Corel_to_Cospan : @CorelCat C H_Coc HP CC ⟶ CospanCat C HP := {|
  fobj := fun X => X;
  fmap := fun X Y f => corelation_cospan f
|}.
Solve All Obligations with
  (try (intros; reflexivity);
   try (intros; unfold Proper, respectful;
        intros f f' Hff'; exact Hff')).

End CorelToCospan.

(** ** Notes

    The [CorelComposable] hypothesis is the single composite-copairing-
    is-epi axiom needed for [CorelCat] to be a category.  In a regular
    category (e.g. [Sets]), this hypothesis is automatic and follows
    from the regular-epi factorisation system.

    A V2c-applications goal is to discharge [CorelComposable Sets] once
    [Sets] has pushouts and a regular-epi factorisation; this requires
    explicit work in the [Instance/Sets/...] tree which is outside the
    scope of V2b.

    Reference: nLab "corelation", Fong–Spivak "Algebra of Open
    Systems" Theorem 4.2.5. *)

(* TODO(V2c-applications): Instance CorelComposable for Sets (once Sets
   has explicit pushouts and a regular-epi factorisation system). *)

(* TODO(V2b): Prove that corelation composition preserves epic copairing *)
(* TODO(V2b): Construct CorelCat C HP : Category given EpiStablePushouts *)
(* TODO(V2b): Prove CorelCat is a wide subcategory of CospanCat *)
(* TODO(V2b): Instance EpiStablePushouts (Sets) once Sets has pushouts *)
