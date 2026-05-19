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
Require Import Category.Construction.Cospan.Bridging.
Require Import Category.Structure.Monoidal.

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

(** ** Basic cospan_tensor properties

    These are the equations that hold without needing the full bifunctor
    machinery.  They are stated here as a typed surface for downstream
    code, and as semantic anchors for the full V2c-applications
    coherence proofs. *)

Section CospanTensorBasics.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.

(** Tensor of identity cospans is the identity cospan, witnessed by the
    codiagonal identity [inl ▽ inr ≈ id]. *)
Lemma cospan_tensor_id (X Y : C) :
  cospan_equiv (cospan_tensor (cospan_id X) (cospan_id Y))
               (cospan_id (X + Y)).
Proof.
  unfold cospan_tensor, cospan_id; simpl.
  exists iso_id; simpl; split.
  - rewrite id_left.
    unfold cover.
    rewrite !id_right.
    apply merge_inl_inr.
  - rewrite id_left.
    unfold cover.
    rewrite !id_right.
    apply merge_inl_inr.
Defined.

(** [cospan_tensor] respects [cospan_equiv] in both arguments.

    With the direct CospanCat, the apex iso is just a C-iso of coproducts,
    built via [coprod_respects_iso] from the per-component isos. *)
Lemma cospan_tensor_respects
      {X Y X' Y' : C}
      (f f' : CospanArrow X Y) (g g' : CospanArrow X' Y') :
  cospan_equiv f f' ->
  cospan_equiv g g' ->
  cospan_equiv (cospan_tensor f g) (cospan_tensor f' g').
Proof.
  intros [phi [Hf1 Hf2]] [psi [Hg1 Hg2]].
  unfold cospan_tensor; simpl.
  exists (@coprod_respects_iso C H_Coc _ _ phi _ _ psi); simpl; split.
  - (* cover (to phi) (to psi) ∘ cover (cospan_in1 f) (cospan_in1 g)
       ≈ cover (cospan_in1 f') (cospan_in1 g') *)
    rewrite cover_comp.
    rewrite Hf1, Hg1.
    reflexivity.
  - rewrite cover_comp.
    rewrite Hf2, Hg2.
    reflexivity.
Defined.

End CospanTensorBasics.

(** ** A note on the remaining Cospan→Hypergraph coherence

    The general respect lemma [cospan_tensor f f' g g' : cospan_equiv f f'
    -> cospan_equiv g g' -> cospan_equiv (cospan_tensor f g) (cospan_tensor f' g')]
    requires constructing an iso of cospan apexes [apex f + apex g ≅ apex f' + apex g']
    in the cospan setoid (which lives in [C^op]).

    Two natural strategies were tried:

      (a) Use [coprod_respects_iso] from [Cocartesian.v] to build the
          coproduct iso in [C], then transport via [Isomorphism_Opposite]
          to [C^op].  This requires converting the [C^op]-isos phi and psi
          back into [C]-isos by swapping [to]/[from], but the swap creates
          equational obligations of the form [from ∘ to ≈ id] where the
          [id] is annotated with [C^op] vs [C], blocking type-equality
          even though the morphism equations agree.

      (b) Build the iso directly in [C^op] by manually filling
          [Build_Isomorphism] with [cover (to phi) (to psi)] etc.  This
          requires [Cocartesian (C^op)] (for the [cover] notation to
          resolve), which we do not assume.

    Both routes hit category-resolution friction that is mechanical but
    non-trivial to discharge cleanly.  The most natural way to close this
    is to first prove [@Cocartesian C -> @Cartesian (C^op)] (the
    library's [Notation 'Cocartesian' C := (@Cartesian (C^op))] does the
    reverse), giving us coproduct structure usable in either direction.
    That conversion is straightforward but is a separate piece of
    infrastructure.

    For V2b we deliver the [cospan_tensor_id] case (above), the SCFA
    data definitions, and a sharpened catalog of the remaining
    coherence diagrams.  *)

(** ** SCFA monoid/comonoid laws on the cocartesian witnesses

    These don't require the full Monoidal-on-cospans structure; they
    are equations between specific cospans, expressible directly via
    the cocartesian structure of [C]. *)

Section CospanSCFALaws.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context (HP : HasPushouts C).

(** ** μ-unit laws on the witness cospans

    These hold as cospan-equiv equations between
    [cospan_compose (cospan_scfa_mu X) (cospan_tensor (cospan_scfa_eta X) (cospan_id X))]
    and (the canonical "unit_left" cospan).  The proof is a pushout
    calculation in [C].

    The full SCFA proof requires having the [Monoidal (CospanCat C)]
    structure available so we can state the laws against [unit_left],
    [unit_right], [tensor_assoc] etc. on cospans — that infrastructure
    is the next layer (Cospan_Monoidal etc., deferred to V2c since it
    requires building all the unitor/associator cospans and proving
    their naturality through pushouts).

    What V2b CAN deliver: the [cospan_scfa_*] witnesses respect
    [cospan_equiv] under composition and tensor, and small structural
    equations between them — which is the building-block layer.

    The witness equation [μ ∘ δ ≈ id] (specialness) requires showing
    that pushing out the codiagonal against itself collapses to the
    identity cospan.  This is structurally a pushout calculation, but
    requires the [cospan_compose_apex] / [cospan_compose_in1] /
    [cospan_compose_in2] accessors and a careful UMP argument. *)

End CospanSCFALaws.

(** ** Status note

    V2b closes the trivial functoriality lemma
    [cospan_tensor_id] and [cospan_tensor_respects] (above), which
    are the [Proper]-instance ingredients for [cospan_tensor].

    The remaining structural obligations (full [Monoidal] instance,
    associator/unitors/braid as cospans + their naturality, SCFA
    axioms as cospans, [Hypergraph] tensor/unit coherence) reduce to
    a large body of pushout-cospan-equiv diagrams in [C].  Each is
    structurally a [pushout_med_eq]-and-[merge_inl_inr]-style
    calculation, but the aggregate (5 distinct instances × roughly 100
    lines each = ~500 lines of mechanical pushout reasoning) is too
    large for a single PR.

    These remaining obligations are sharpened to V2c-applications: a
    downstream consumer instantiating [Hypergraph (CospanCat Sets)] or
    [Hypergraph (CospanCat FinSet)] for a CONCRETE category can
    discharge them directly using the category's specific finite-
    colimit structure, which is typically much more tractable than the
    fully-abstract pushout reasoning required at the [HasPushouts]
    level.

    The V2b-V2c boundary is therefore drawn at: *abstract* coherence
    proofs (the rest of the cospan-as-hypergraph derivation) are deferred,
    but *typed data* for downstream concrete-category instantiation is
    fully provided.  *)

(** ** Morphism-as-cospan: lifting C-morphisms into [CospanCat C]

    Any morphism [f : X ~> Y] in [C] induces a cospan from [X] to [Y]:
    apex = [Y], leg1 = [f], leg2 = [id].  This gives a functor
    [C → CospanCat C] (the "left embedding") which we use throughout
    the Monoidal structure: the unitor and associator cospans are the
    lifts of the corresponding C-coproduct isos. *)

Section MorphismAsCospan.

Context {C : Category}.

Definition mor_as_cospan {X Y : C} (f : X ~> Y) : CospanArrow X Y :=
  Build_CospanArrow Y f id[Y].

(** Identity in C lifts to the identity cospan. *)
Lemma mor_as_cospan_id (X : C) :
  cospan_equiv (mor_as_cospan id[X]) (cospan_id X).
Proof.
  unfold mor_as_cospan, cospan_id; simpl.
  exists iso_id; simpl; split; cat.
Defined.

(** A C-iso [phi : X ≅ Y] induces a CospanCat-iso (mor_as_cospan phi)⁻¹
    via the obvious reverse cospan. *)
Definition mor_iso_as_cospan_iso {X Y : C} (phi : X ≅ Y) :
  CospanArrow X Y := mor_as_cospan (to phi).

(** [mor_as_cospan] respects [≈] on the C-morphism. *)
Lemma mor_as_cospan_proper {X Y : C} (f g : X ~> Y) :
  f ≈ g -> cospan_equiv (mor_as_cospan f) (mor_as_cospan g).
Proof.
  intros Hfg.
  unfold mor_as_cospan; simpl.
  exists iso_id; simpl; split.
  - rewrite id_left.
    exact Hfg.
  - cat.
Defined.

#[export] Program Instance mor_as_cospan_Proper {X Y : C} :
  Proper (equiv ==> equiv) (mor_as_cospan (X := X) (Y := Y)).
Next Obligation.
  intros f g Hfg.
  apply mor_as_cospan_proper, Hfg.
Defined.

(** ** Unitor cospans on [CospanCat C]

    These are the cospan-lifts of the corresponding coproduct isos in C. *)

Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.

(** Left unitor cospan:  cospan from [0 + X] to [X]. *)
Definition cospan_unit_left (X : C) : CospanArrow (0 + X)%object X :=
  mor_as_cospan (to (@coprod_zero_l C H_Coc H_Ini X)).

(** Right unitor cospan:  cospan from [X + 0] to [X]. *)
Definition cospan_unit_right (X : C) : CospanArrow (X + 0)%object X :=
  mor_as_cospan (to (@coprod_zero_r C H_Coc H_Ini X)).

(** Associator cospan:  cospan from [(X + Y) + Z] to [X + (Y + Z)]. *)
Definition cospan_tensor_assoc (X Y Z : C)
  : CospanArrow ((X + Y) + Z)%object (X + (Y + Z))%object :=
  mor_as_cospan (to (@coprod_assoc C H_Coc X Y Z)).

(** Braid cospan:  cospan from [X + Y] to [Y + X]. *)
Definition cospan_braid (X Y : C) : CospanArrow (X + Y)%object (Y + X)%object :=
  mor_as_cospan (to (@coprod_comm C H_Coc X Y)).

End MorphismAsCospan.

Arguments mor_as_cospan {C X Y} f.
Arguments cospan_unit_left {C _ _} X.
Arguments cospan_unit_right {C _ _} X.
Arguments cospan_tensor_assoc {C _} X Y Z.
Arguments cospan_braid {C _} X Y.

(** ** Pushout-of-id-with-g collapse

    The pushout of [(id : Y → Y, g : Y → Z)] is canonically isomorphic
    to [Z].  This is the key calculation behind the morphism-as-cospan
    functoriality. *)

Section PushoutIdCollapse.

Context {C : Category}.
Context (HP : HasPushouts C).

(** Pushout of [(id_Y, g)] collapses to Z (the codomain of g). *)
Lemma pushout_id_left_apex {Y Z : C} (g : Y ~> Z) :
  pushout_apex (pushout id[Y] g) ≅ Z.
Proof.
  set (P := pushout id[Y] g).
  assert (Hcomm : g ∘ id ≈ id ∘ g) by cat.
  set (m := pushout_med P Hcomm).
  assert (Hm1 : m ∘ pushout_in1 P ≈ g) by (apply pushout_med_in1).
  assert (Hm2 : m ∘ pushout_in2 P ≈ id[Z]) by (apply pushout_med_in2).
  refine {| to   := m;
            from := pushout_in2 P;
            iso_to_from := _;
            iso_from_to := _ |}.
  - exact Hm2.
  - (* pushout_in2 P ∘ m ≈ id at apex P, by uniqueness on identity cocone. *)
    transitivity (pushout_med P (pushout_commutes P)).
    + symmetry.
      apply pushout_med_unique.
      * rewrite <- comp_assoc, Hm1.
        pose proof (pushout_commutes P) as PC.
        rewrite <- PC; cat.
      * rewrite <- comp_assoc, Hm2; cat.
    + apply pushout_med_unique; cat.
Defined.

(** Pushout of [(g, id_Y)] collapses to Z (codomain of g). *)
Lemma pushout_id_right_apex {Y Z : C} (g : Y ~> Z) :
  pushout_apex (pushout g id[Y]) ≅ Z.
Proof.
  set (P := pushout g id[Y]).
  assert (Hcomm : id ∘ g ≈ g ∘ id) by cat.
  set (m := pushout_med P Hcomm).
  assert (Hm1 : m ∘ pushout_in1 P ≈ id[Z]) by (apply pushout_med_in1).
  assert (Hm2 : m ∘ pushout_in2 P ≈ g) by (apply pushout_med_in2).
  refine {| to   := m;
            from := pushout_in1 P;
            iso_to_from := _;
            iso_from_to := _ |}.
  - exact Hm1.
  - transitivity (pushout_med P (pushout_commutes P)).
    + symmetry.
      apply pushout_med_unique.
      * rewrite <- comp_assoc, Hm1; cat.
      * rewrite <- comp_assoc, Hm2.
        pose proof (pushout_commutes P) as PC.
        rewrite PC; cat.
    + apply pushout_med_unique; cat.
Defined.

End PushoutIdCollapse.

(** ** [mor_as_cospan] is functorial

    Composition of two morphism-as-cospans agrees with the morphism-as-
    cospan of the composite.  Witnessed via the pushout-of-id collapse. *)

Section MorAsCospanFunctorial.

Context {C : Category}.
Context (HP : HasPushouts C).

(** [mor_as_cospan] respects composition.

    The composite cospan's apex is the pushout of [(id, g)], which by
    [pushout_id_left_apex] is isomorphic to [Z] (the codomain of [g]).
    Under that iso, the composite legs agree with [g ∘ f] and [id_Z]
    respectively. *)
Lemma mor_as_cospan_compose {X Y Z : C} (g : Y ~> Z) (f : X ~> Y) :
  cospan_equiv
    (cospan_compose HP (mor_as_cospan g) (mor_as_cospan f))
    (mor_as_cospan (g ∘ f)).
Proof.
  unfold cospan_compose, mor_as_cospan; simpl.
  pose (P := pushout (id[Y] : Y ~{C}~> Y) g).
  (* Apex of LHS is pushout_apex P; apex of RHS is Z.
     pushout_id_left_apex gives the iso pushout_apex P ≅ Z. *)
  exists (pushout_id_left_apex HP g); simpl.
  split.
  - (* to (collapse) ∘ (pushout_in1 P ∘ f) ≈ g ∘ f *)
    rewrite comp_assoc.
    apply compose_respects; [|reflexivity].
    (* to (collapse) ∘ pushout_in1 P ≈ g; by definition of pushout_id_left_apex,
       [to] is the [pushout_med P (Hcomm: g ∘ id ≈ id ∘ g)], and its first
       leg equation is [m ∘ pushout_in1 P ≈ g]. *)
    apply pushout_med_in1.
  - (* to (collapse) ∘ (pushout_in2 P ∘ id) ≈ id *)
    rewrite (id_right (pushout_in2 _)).
    apply pushout_med_in2.
Defined.

End MorAsCospanFunctorial.

(** ** Pushout-coproduct compatibility: the bifunctor key lemma

    The pushout of two [cover]s is canonically isomorphic to the coproduct
    of the per-component pushouts.  This is the key compatibility behind
    [cospan_tensor]'s functoriality. *)

Section PushoutCoproductCompat.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context (HP : HasPushouts C).

(** The "split" cocone: given a pushout [P] of [(f, g)], the maps
    [inl ∘ pushout_in1 P : Y → P + P'] and [inl ∘ pushout_in2 P]
    form a cocone over [(f, g)]. *)

(** The cocone for the forward direction: from the pushout-of-covers
    apex to the coproduct of the per-component pushout apexes. *)
Lemma pushout_cover_split_cocone
  {X X' Y Y' Z Z' : C}
  (f : X ~> Y) (g : X ~> Z)
  (f' : X' ~> Y') (g' : X' ~> Z')
  (P : IsPushout f g) (P' : IsPushout f' g') :
  cover (pushout_in1 P) (pushout_in1 P') ∘ cover f f'
  ≈ cover (pushout_in2 P) (pushout_in2 P') ∘ cover g g'.
Proof.
  rewrite !cover_comp.
  pose proof (pushout_commutes P) as PC.
  pose proof (pushout_commutes P') as PC'.
  unfold pushout_in1, pushout_in2 in *.
  rewrite PC, PC'.
  reflexivity.
Qed.

(** Forward iso direction: pushout of covers ⟶ coproduct of pushouts. *)
Definition pushout_cover_split
  {X X' Y Y' Z Z' : C}
  (f : X ~> Y) (g : X ~> Z)
  (f' : X' ~> Y') (g' : X' ~> Z')
  (P : IsPushout f g) (P' : IsPushout f' g')
  (Pcov : IsPushout (cover f f' : (X + X')%object ~> (Y + Y')%object)
                    (cover g g'))
  : pushout_apex Pcov ~> (pushout_apex P + pushout_apex P')%object
  := pushout_med Pcov (pushout_cover_split_cocone f g f' g' P P').

(** Sub-cocone: pushout_in1 Pcov composed with [inl] is a leg into the
    pushout-of-covers apex via the X-side of the coproduct. *)
Lemma pushout_cover_left_cocone
  {X X' Y Y' Z Z' : C}
  (f : X ~> Y) (g : X ~> Z)
  (f' : X' ~> Y') (g' : X' ~> Z')
  (Pcov : IsPushout (cover f f' : (X + X')%object ~> (Y + Y')%object)
                    (cover g g')) :
  (pushout_in1 Pcov ∘ inl) ∘ f
  ≈ (pushout_in2 Pcov ∘ inl) ∘ g.
Proof.
  pose proof (pushout_commutes Pcov) as PC.
  rewrite <- !comp_assoc.
  rewrite <- (cover_inl f f').
  rewrite <- (cover_inl g g').
  rewrite !comp_assoc.
  rewrite PC.
  reflexivity.
Qed.

Lemma pushout_cover_right_cocone
  {X X' Y Y' Z Z' : C}
  (f : X ~> Y) (g : X ~> Z)
  (f' : X' ~> Y') (g' : X' ~> Z')
  (Pcov : IsPushout (cover f f' : (X + X')%object ~> (Y + Y')%object)
                    (cover g g')) :
  (pushout_in1 Pcov ∘ inr) ∘ f'
  ≈ (pushout_in2 Pcov ∘ inr) ∘ g'.
Proof.
  pose proof (pushout_commutes Pcov) as PC.
  rewrite <- !comp_assoc.
  rewrite <- (cover_inr f f').
  rewrite <- (cover_inr g g').
  rewrite !comp_assoc.
  rewrite PC.
  reflexivity.
Qed.

(** Reverse iso direction: coproduct of pushouts ⟶ pushout of covers.
    Built via two applications of [pushout_med] (one per component),
    combined by [merge]. *)
Definition pushout_cover_combine
  {X X' Y Y' Z Z' : C}
  (f : X ~> Y) (g : X ~> Z)
  (f' : X' ~> Y') (g' : X' ~> Z')
  (P : IsPushout f g) (P' : IsPushout f' g')
  (Pcov : IsPushout (cover f f' : (X + X')%object ~> (Y + Y')%object)
                    (cover g g'))
  : (pushout_apex P + pushout_apex P')%object ~> pushout_apex Pcov :=
  merge (pushout_med P (pushout_cover_left_cocone f g f' g' Pcov))
        (pushout_med P' (pushout_cover_right_cocone f g f' g' Pcov)).

(** ** Pushout-coproduct compatibility iso

    The pushout of covers IS the coproduct of pushouts.  Witnessed by the
    split/combine maps above being mutual inverses. *)

Lemma pushout_cover_split_combine
  {X X' Y Y' Z Z' : C}
  (f : X ~> Y) (g : X ~> Z)
  (f' : X' ~> Y') (g' : X' ~> Z')
  (P : IsPushout f g) (P' : IsPushout f' g')
  (Pcov : IsPushout (cover f f' : (X + X')%object ~> (Y + Y')%object)
                    (cover g g')) :
  pushout_cover_combine f g f' g' P P' Pcov
    ∘ pushout_cover_split f g f' g' P P' Pcov
  ≈ id.
Proof.
  unfold pushout_cover_combine, pushout_cover_split.
  (* Use joint-epi via [fork_inv]: a morphism on a coproduct is determined
     by its restrictions to inl/inr.  The plan:
       1. transitive through pushout_med Pcov (pushout_commutes Pcov)
       2. apply pushout_med_unique
       3. for each pushout-in, use cover_inl / cover_inr to split. *)
  transitivity (pushout_med Pcov (pushout_commutes Pcov)).
  - symmetry.
    apply pushout_med_unique.
    + (* Goal: (m1 ▽ m2) ∘ pushout_med Pcov (...) ∘ pushout_in1 Pcov ≈ pushout_in1 Pcov. *)
      rewrite <- comp_assoc, (pushout_med_in1 Pcov).
      pose proof (pushout_med_in1 P (pushout_cover_left_cocone f g f' g' Pcov)) as Hl.
      pose proof (pushout_med_in1 P' (pushout_cover_right_cocone f g f' g' Pcov)) as Hr.
      (* Goal: (m1 ▽ m2) ∘ cover (in1 P) (in1 P') ≈ pushout_in1 Pcov.
         Unfold cover, distribute via merge_comp:
         = (m1 ∘ in1 P) ▽ (m2 ∘ in1 P')
         By Hl, Hr: = (in1 Pcov ∘ inl) ▽ (in1 Pcov ∘ inr)
                   = in1 Pcov ∘ (inl ▽ inr)
                   = in1 Pcov ∘ id = in1 Pcov. *)
      unfold cover.
      rewrite <- !merge_comp.
      rewrite (comp_assoc _ inl), (comp_assoc _ inr).
      rewrite inl_merge, inr_merge.
      rewrite Hl, Hr.
      rewrite merge_comp.
      rewrite merge_inl_inr.
      cat.
    + rewrite <- comp_assoc, (pushout_med_in2 Pcov).
      pose proof (pushout_med_in2 P (pushout_cover_left_cocone f g f' g' Pcov)) as Hl.
      pose proof (pushout_med_in2 P' (pushout_cover_right_cocone f g f' g' Pcov)) as Hr.
      unfold cover.
      rewrite <- !merge_comp.
      rewrite (comp_assoc _ inl), (comp_assoc _ inr).
      rewrite inl_merge, inr_merge.
      rewrite Hl, Hr.
      rewrite merge_comp.
      rewrite merge_inl_inr.
      cat.
  - apply pushout_med_unique; cat.
Qed.

Lemma pushout_cover_combine_split
  {X X' Y Y' Z Z' : C}
  (f : X ~> Y) (g : X ~> Z)
  (f' : X' ~> Y') (g' : X' ~> Z')
  (P : IsPushout f g) (P' : IsPushout f' g')
  (Pcov : IsPushout (cover f f' : (X + X')%object ~> (Y + Y')%object)
                    (cover g g')) :
  pushout_cover_split f g f' g' P P' Pcov
    ∘ pushout_cover_combine f g f' g' P P' Pcov
  ≈ id.
Proof.
  unfold pushout_cover_combine, pushout_cover_split.
  rewrite <- merge_inl_inr.
  rewrite <- merge_comp.
  apply (snd (merge_inv _ _ _ _)).
  split.
  - (* Goal: split ∘ m1 ≈ inl
       Cocone for P that gives `inl` as mediator: legs (inl ∘ pushout_in1 P, inl ∘ pushout_in2 P).
       But that's just the inl-of-identity cocone.
       Use pushout_med_unique to derive both [split ∘ m1] and [inl] equal the same
       cocone-mediator. *)
    assert (HC : (@inl C _ (pushout_apex P) (pushout_apex P')) ∘ pushout_in1 P ∘ f
                 ≈ (@inl C _ (pushout_apex P) (pushout_apex P')) ∘ pushout_in2 P ∘ g).
    { rewrite <- !comp_assoc.
      apply compose_respects; [reflexivity|].
      apply (pushout_commutes P). }
    transitivity (pushout_med P HC).
    + symmetry.
      apply pushout_med_unique.
      * rewrite <- comp_assoc.
        rewrite (pushout_med_in1 P).
        rewrite (comp_assoc _ (pushout_in1 Pcov)).
        rewrite (pushout_med_in1 Pcov).
        unfold cover.
        apply inl_merge.
      * rewrite <- comp_assoc.
        rewrite (pushout_med_in2 P).
        rewrite (comp_assoc _ (pushout_in2 Pcov)).
        rewrite (pushout_med_in2 Pcov).
        unfold cover.
        apply inl_merge.
    + apply pushout_med_unique; cat.
  - assert (HC : (@inr C _ (pushout_apex P) (pushout_apex P')) ∘ pushout_in1 P' ∘ f'
                 ≈ (@inr C _ (pushout_apex P) (pushout_apex P')) ∘ pushout_in2 P' ∘ g').
    { rewrite <- !comp_assoc.
      apply compose_respects; [reflexivity|].
      apply (pushout_commutes P'). }
    transitivity (pushout_med P' HC).
    + symmetry.
      apply pushout_med_unique.
      * rewrite <- comp_assoc.
        rewrite (pushout_med_in1 P').
        rewrite (comp_assoc _ (pushout_in1 Pcov)).
        rewrite (pushout_med_in1 Pcov).
        unfold cover.
        apply inr_merge.
      * rewrite <- comp_assoc.
        rewrite (pushout_med_in2 P').
        rewrite (comp_assoc _ (pushout_in2 Pcov)).
        rewrite (pushout_med_in2 Pcov).
        unfold cover.
        apply inr_merge.
    + apply pushout_med_unique; cat.
Qed.

End PushoutCoproductCompat.

(** ** Bifunctoriality: [cospan_tensor (g ∘ f) (g' ∘ f')
                       ≈ cospan_tensor g g' ∘ cospan_tensor f f']

    With the direct CospanCat, the iso of cospan apexes is built directly
    from [pushout_cover_combine] (going from coproduct-of-pushouts
    to pushout-of-covers).  The leg conditions reduce to
    pushout-mediator-of-cover calculations. *)

Section CospanTensorBifunctoriality.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context (HP : HasPushouts C).

(** Helper: [merge] distributes through [cover]. *)
Lemma merge_cover_compose {a b c d e : C}
      (m1 : c ~> e) (m2 : d ~> e) (h1 : a ~> c) (h2 : b ~> d) :
  (m1 ▽ m2) ∘ cover h1 h2 ≈ (m1 ∘ h1) ▽ (m2 ∘ h2).
Proof.
  unfold cover.
  rewrite <- !merge_comp.
  rewrite (comp_assoc _ inl).
  rewrite (comp_assoc _ inr).
  rewrite inl_merge, inr_merge.
  reflexivity.
Qed.

Lemma cospan_tensor_compose_compat
  {X Y Z X' Y' Z' : C}
  (g : CospanArrow Y Z) (f : CospanArrow X Y)
  (g' : CospanArrow Y' Z') (f' : CospanArrow X' Y') :
  cospan_equiv
    (cospan_tensor (cospan_compose HP g f) (cospan_compose HP g' f'))
    (cospan_compose HP (cospan_tensor g g') (cospan_tensor f f')).
Proof.
  unfold cospan_tensor, cospan_compose; simpl.
  pose (P  := pushout (cospan_in2 f)  (cospan_in1 g)).
  pose (P' := pushout (cospan_in2 f') (cospan_in1 g')).
  pose (Pcov := pushout (cover (cospan_in2 f) (cospan_in2 f'))
                        (cover (cospan_in1 g) (cospan_in1 g'))).
  (* Iso of apexes: pushout_apex P + pushout_apex P' ≅ pushout_apex Pcov,
     given by pushout_cover_combine / pushout_cover_split. *)
  unshelve refine (existT _ _ _).
  - refine {| to   := pushout_cover_combine _ _ _ _ P P' Pcov;
              from := pushout_cover_split   _ _ _ _ P P' Pcov;
              iso_to_from := pushout_cover_split_combine _ _ _ _ P P' Pcov;
              iso_from_to := pushout_cover_combine_split _ _ _ _ P P' Pcov |}.
  - simpl; split; fold P P' Pcov.
    + (* pushout_cover_combine ∘ cover (in1 P ∘ in1 f) (in1 P' ∘ in1 f')
         ≈ in1 Pcov ∘ cover (in1 f) (in1 f') *)
      unfold pushout_cover_combine.
      rewrite merge_cover_compose.
      pose proof (pushout_med_in1 P
                    (pushout_cover_left_cocone _ _ _ _ Pcov)) as Hl.
      pose proof (pushout_med_in1 P'
                    (pushout_cover_right_cocone _ _ _ _ Pcov)) as Hr.
      rewrite !comp_assoc.
      rewrite Hl, Hr.
      (* Goal: (in1 Pcov ∘ inl) ∘ in1 f ▽ (in1 Pcov ∘ inr) ∘ in1 f'
              ≈ in1 Pcov ∘ cover (in1 f) (in1 f') *)
      rewrite <- (comp_assoc (pushout_in1 Pcov) inl).
      rewrite <- (comp_assoc (pushout_in1 Pcov) inr).
      rewrite merge_comp.
      reflexivity.
    + (* pushout_cover_combine ∘ cover (in2 P ∘ in2 g) (in2 P' ∘ in2 g')
         ≈ in2 Pcov ∘ cover (in2 g) (in2 g') *)
      unfold pushout_cover_combine.
      rewrite merge_cover_compose.
      pose proof (pushout_med_in2 P
                    (pushout_cover_left_cocone _ _ _ _ Pcov)) as Hl.
      pose proof (pushout_med_in2 P'
                    (pushout_cover_right_cocone _ _ _ _ Pcov)) as Hr.
      rewrite !comp_assoc.
      rewrite Hl, Hr.
      rewrite <- (comp_assoc (pushout_in2 Pcov) inl).
      rewrite <- (comp_assoc (pushout_in2 Pcov) inr).
      rewrite merge_comp.
      reflexivity.
Defined.

End CospanTensorBifunctoriality.

(** ** Cospan_Bifunctor: [cospan_tensor] as a bifunctor on [CospanCat C]

    Builds the [Functor (CospanCat C ∏ CospanCat C) (CospanCat C)] from
    the per-component data: object mapping is [Cospan_tensor_obj],
    morphism mapping is [cospan_tensor], with [fmap_id] and [fmap_comp]
    discharged by [cospan_tensor_id] and [cospan_tensor_compose_compat]. *)

Section CospanBifunctor.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context (HP : HasPushouts C).

Program Definition Cospan_Bifunctor
  : ((CospanCat C HP) ∏ (CospanCat C HP)) ⟶ (CospanCat C HP) := {|
  fobj := fun xy => @Cospan_tensor_obj C H_Coc (fst xy) (snd xy);
  fmap := fun xy uv fg => cospan_tensor (fst fg) (snd fg)
|}.
Next Obligation.
  proper; simpl in *.
  apply cospan_tensor_respects; assumption.
Defined.
Next Obligation.
  (* fmap id ≈ id  i.e.  cospan_tensor (cospan_id x) (cospan_id y) ≈ cospan_id (x + y) *)
  apply cospan_tensor_id.
Defined.
Next Obligation.
  (* fmap (f ∘ g) ≈ fmap f ∘ fmap g
     i.e.  cospan_tensor (f1 ∘ g1) (f2 ∘ g2)
         ≈ cospan_tensor f1 f2 ∘ cospan_tensor g1 g2
     in CospanCat (composition is cospan_compose HP). *)
  apply cospan_tensor_compose_compat.
Defined.

End CospanBifunctor.

(** ** Cospan_Monoidal: the Monoidal structure on [CospanCat C]

    The unitor, associator, braid are [mor_as_cospan]s of the
    corresponding C-level coproduct isos.  The Monoidal naturality
    and coherence conditions lift through the [mor_as_cospan]
    embedding because [mor_as_cospan] respects composition (via
    [mor_as_cospan_compose]) and equivalence (via
    [mor_as_cospan_proper]). *)

Section CospanMonoidal.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.
Context `{H_Ini : @Initial C}.
Context (HP : HasPushouts C).

(** Lifting a C-iso to a cospan-iso (in CospanCat) via mor_as_cospan. *)
(** [cospan_tensor] of two [mor_as_cospan]s agrees with [mor_as_cospan]
    of the [cover] of the underlying C-morphisms. *)
Lemma cospan_tensor_mor_as_cospan
      {X Y X' Y' : C} (f : X ~> Y) (g : X' ~> Y') :
  cospan_equiv (cospan_tensor (mor_as_cospan f) (mor_as_cospan g))
               (mor_as_cospan (cover f g)).
Proof.
  unfold cospan_tensor, mor_as_cospan; simpl.
  exists iso_id; simpl; split.
  - rewrite id_left; reflexivity.
  - rewrite id_left.
    unfold cover.
    rewrite !id_right.
    apply merge_inl_inr.
Defined.

Definition mor_iso_lift {X Y : C} (phi : X ≅ Y)
  : @Isomorphism (CospanCat C HP) X Y.
Proof.
  unshelve refine
    {| to   := (mor_as_cospan (to phi) : X ~{CospanCat C HP}~> Y);
       from := (mor_as_cospan (from phi) : Y ~{CospanCat C HP}~> X);
       iso_to_from := _;
       iso_from_to := _ |}.
  - (* mor_as_cospan (to phi) ∘ mor_as_cospan (from phi) ≈ id in CospanCat *)
    eapply cospan_equiv_trans.
    + apply mor_as_cospan_compose.
    + eapply cospan_equiv_trans.
      * apply mor_as_cospan_proper. apply iso_to_from.
      * apply mor_as_cospan_id.
  - eapply cospan_equiv_trans.
    + apply mor_as_cospan_compose.
    + eapply cospan_equiv_trans.
      * apply mor_as_cospan_proper. apply iso_from_to.
      * apply mor_as_cospan_id.
Defined.

(** ** Unitor naturality (left): a pushout-UMP calculation

    For a generic cospan [g : x → y] with apex [N], legs [g1 : x → N]
    and [g2 : y → N], the left-unitor naturality in [CospanCat] requires

       cospan_compose HP g unit_left ≈ cospan_compose HP unit_left (bimap id g)

    where [unit_left = mor_as_cospan (zero ▽ id : 0+x → x)] and
    [bimap id g = cospan_tensor (cospan_id 0) g].

    The LHS apex is [pushout id g1], which collapses to [N] by
    [pushout_id_left_apex].  The RHS apex is the pushout of
    [(cover id g2, zero ▽ id)], which also collapses to [N] by a
    direct UMP calculation, exhibited below. *)

Lemma pushout_cover_id_unit_left_apex {y N : C} (g2 : y ~> N) :
  pushout_apex (pushout (cover id[0] g2 : (0 + y)%object ~> (0 + N)%object)
                        (zero ▽ id[y] : (0 + y)%object ~> y)) ≅ N.
Proof.
  set (P := pushout (cover id[0] g2 : (0 + y)%object ~> (0 + N)%object)
                    (zero ▽ id[y])).
  (* Mediator P -> N via cocone (zero ▽ id : 0+N → N, g2 : y → N). *)
  assert (HC : (zero ▽ id[N]) ∘ cover id[0] g2 ≈ g2 ∘ (zero ▽ id[y])).
  { unfold cover.
    rewrite <- merge_comp.
    rewrite (comp_assoc _ inl).
    rewrite (comp_assoc _ inr).
    rewrite inl_merge, inr_merge.
    rewrite id_left, id_right.
    rewrite <- merge_comp.
    rewrite id_right, zero_comp.
    reflexivity. }
  set (m := pushout_med P HC).
  assert (Hm1 : m ∘ pushout_in1 P ≈ zero ▽ id[N]) by (apply pushout_med_in1).
  assert (Hm2 : m ∘ pushout_in2 P ≈ g2) by (apply pushout_med_in2).
  unshelve refine
    {| to := m;
       from := pushout_in1 P ∘ inr;
       iso_to_from := _;
       iso_from_to := _ |}.
  - (* m ∘ (pushout_in1 P ∘ inr) ≈ id at N *)
    rewrite comp_assoc.
    rewrite Hm1.
    apply inr_merge.
  - (* (pushout_in1 P ∘ inr) ∘ m ≈ id at apex P. UMP against identity. *)
    apply (pushout_med_eq P (pushout_commutes P)
            ((pushout_in1 P ∘ inr) ∘ m) id).
    + (* ((pushout_in1 P ∘ inr) ∘ m) ∘ pushout_in1 P ≈ pushout_in1 P *)
      rewrite <- !comp_assoc.
      rewrite Hm1.
      (* Goal: pushout_in1 P ∘ (inr ∘ (zero ▽ id[N])) ≈ pushout_in1 P *)
      assert (Hinr : (@inr C _ 0 N) ∘ (zero[N] ▽ id[N]) ≈ id[0 + N]).
      { rewrite <- merge_comp.
        rewrite id_right.
        rewrite <- merge_inl_inr.
        apply (snd (merge_inv _ _ _ _)).
        split.
        - apply (@zero_unique C H_Ini _ _ _).
        - reflexivity. }
      rewrite Hinr.
      apply id_right.
    + (* ((pushout_in1 P ∘ inr) ∘ m) ∘ pushout_in2 P ≈ pushout_in2 P *)
      rewrite <- !comp_assoc.
      rewrite Hm2.
      (* Goal: pushout_in1 P ∘ (inr ∘ g2) ≈ pushout_in2 P *)
      pose proof (pushout_commutes P) as PC.
      (* PC : pushout_in1 P ∘ cover id g2 ≈ pushout_in2 P ∘ (zero ▽ id) *)
      rewrite <- (cover_inr id[0] g2).
      rewrite comp_assoc.
      rewrite PC.
      rewrite <- comp_assoc.
      rewrite inr_merge.
      apply id_right.
    + cat.
    + cat.
Defined.

(** ** Cover-associator interaction

    The C-iso [coprod_assoc] intertwines [cover (cover f g) h] with
    [cover f (cover g h)]. *)

(** Helpers for the associator-cover proofs. *)

Lemma assoc_to_inl_inl {x y z : C} :
  to (@coprod_assoc C H_Coc x y z) ∘ (inl ∘ inl) ≈ inl.
Proof.
  unfold to, coprod_assoc; simpl.
  rewrite comp_assoc.
  rewrite inl_merge.
  apply inl_merge.
Qed.

Lemma assoc_to_inl_inr {x y z : C} :
  to (@coprod_assoc C H_Coc x y z) ∘ (inl ∘ inr) ≈ inr ∘ inl.
Proof.
  unfold to, coprod_assoc; simpl.
  rewrite comp_assoc.
  rewrite inl_merge.
  apply inr_merge.
Qed.

Lemma assoc_to_inr {x y z : C} :
  to (@coprod_assoc C H_Coc x y z) ∘ inr ≈ inr ∘ inr.
Proof.
  unfold to, coprod_assoc; simpl.
  apply inr_merge.
Qed.

Lemma assoc_from_inl {x y z : C} :
  from (@coprod_assoc C H_Coc x y z) ∘ inl ≈ inl ∘ inl.
Proof.
  unfold from, coprod_assoc; simpl.
  apply inl_merge.
Qed.

Lemma assoc_from_inr_inl {x y z : C} :
  from (@coprod_assoc C H_Coc x y z) ∘ (inr ∘ inl) ≈ inl ∘ inr.
Proof.
  unfold from, coprod_assoc; simpl.
  rewrite comp_assoc.
  rewrite inr_merge.
  apply inl_merge.
Qed.

Lemma assoc_from_inr_inr {x y z : C} :
  from (@coprod_assoc C H_Coc x y z) ∘ (inr ∘ inr) ≈ inr.
Proof.
  unfold from, coprod_assoc; simpl.
  rewrite comp_assoc.
  rewrite inr_merge.
  apply inr_merge.
Qed.

(** Goal: [to coprod_assoc ∘ cover (cover f g) h ≈ cover f (cover g h) ∘ to coprod_assoc].

    The proof is "computational" — both sides equal the canonical morphism
    [(inl ∘ f) ▽ ((inr ∘ inl) ∘ g) ▽ ((inr ∘ inr) ∘ h)] (with appropriate
    associativity).  We split it via joint-epi and reduce each leg by
    explicit composition. *)

Lemma cover_assoc_from {a a' b b' c c' : C}
      (f : a ~> a') (g : b ~> b') (h : c ~> c') :
  from coprod_assoc ∘ cover f (cover g h)
  ≈ cover (cover f g) h ∘ from coprod_assoc.
Proof.
  apply coprod_ext.
  - (* ∘ inl: reduces to inl ∘ inl ∘ f *)
    rewrite <- !comp_assoc.
    rewrite cover_inl.
    rewrite (comp_assoc (from coprod_assoc) inl f).
    rewrite assoc_from_inl.
    rewrite assoc_from_inl.
    symmetry.
    rewrite <- comp_assoc.
    rewrite (comp_assoc (cover (cover f g) h) inl inl).
    rewrite cover_inl.
    rewrite <- comp_assoc.
    rewrite cover_inl.
    rewrite comp_assoc.
    reflexivity.
  - apply coprod_ext.
    + (* ∘ (inr ∘ inl) on (b+c) side → b → inl ∘ inr ∘ g *)
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (cover f (cover g h)) inr inl).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr (cover g h) inl).
      rewrite cover_inl.
      rewrite (comp_assoc inr inl g).
      rewrite (comp_assoc (from coprod_assoc) (inr ∘ inl) g).
      rewrite assoc_from_inr_inl.
      rewrite assoc_from_inr_inl.
      symmetry.
      rewrite <- comp_assoc.
      rewrite (comp_assoc (cover (cover f g) h) inl inr).
      rewrite cover_inl.
      rewrite <- comp_assoc.
      rewrite cover_inr.
      rewrite !comp_assoc.
      reflexivity.
    + (* ∘ (inr ∘ inr) on (b+c) side → c → inr ∘ h *)
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (cover f (cover g h)) inr inr).
      rewrite cover_inr.
      rewrite <- (comp_assoc inr (cover g h) inr).
      rewrite cover_inr.
      rewrite (comp_assoc inr inr h).
      rewrite (comp_assoc (from coprod_assoc) (inr ∘ inr) h).
      rewrite assoc_from_inr_inr.
      rewrite assoc_from_inr_inr.
      symmetry.
      apply cover_inr.
Qed.

Lemma cover_assoc_to {a a' b b' c c' : C}
      (f : a ~> a') (g : b ~> b') (h : c ~> c') :
  to coprod_assoc ∘ cover (cover f g) h
  ≈ cover f (cover g h) ∘ to coprod_assoc.
Proof.
  apply coprod_ext.
  - apply coprod_ext.
    + (* ∘ (inl ∘ inl): both reduce to inl ∘ f *)
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (cover (cover f g) h) inl inl).
      rewrite cover_inl.
      rewrite <- (comp_assoc inl (cover f g) inl).
      rewrite cover_inl.
      rewrite (comp_assoc inl inl f).
      rewrite (comp_assoc (to coprod_assoc) (inl ∘ inl) f).
      rewrite assoc_to_inl_inl.
      (* Goal: inl ∘ f ≈ cover f (cover g h) ∘ (to coprod_assoc ∘ (inl ∘ inl)) *)
      rewrite assoc_to_inl_inl.
      symmetry.
      apply cover_inl.
    + (* ∘ (inl ∘ inr): both reduce to inr ∘ inl ∘ g *)
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (cover (cover f g) h) inl inr).
      rewrite cover_inl.
      rewrite <- (comp_assoc inl (cover f g) inr).
      rewrite cover_inr.
      rewrite (comp_assoc inl inr g).
      rewrite (comp_assoc (to coprod_assoc) (inl ∘ inr) g).
      rewrite assoc_to_inl_inr.
      (* Goal now: inr ∘ inl ∘ g ≈ cover f (cover g h) ∘ (to coprod_assoc ∘ (inl ∘ inr)) *)
      rewrite assoc_to_inl_inr.
      (* Goal: inr ∘ inl ∘ g ≈ cover f (cover g h) ∘ (inr ∘ inl) *)
      symmetry.
      rewrite <- comp_assoc.
      rewrite (comp_assoc (cover f (cover g h)) inr inl).
      rewrite cover_inr.
      rewrite <- comp_assoc.
      rewrite cover_inl.
      rewrite comp_assoc.
      reflexivity.
  - (* ∘ inr: both reduce to inr ∘ inr ∘ h *)
    rewrite <- !comp_assoc.
    rewrite cover_inr.
    rewrite (comp_assoc (to coprod_assoc) inr h).
    rewrite assoc_to_inr.
    (* RHS *)
    rewrite assoc_to_inr.
    (* Goal: inr ∘ inr ∘ h ≈ cover f (cover g h) ∘ (inr ∘ inr) *)
    symmetry.
    rewrite <- comp_assoc.
    rewrite (comp_assoc (cover f (cover g h)) inr inr).
    rewrite cover_inr.
    rewrite <- comp_assoc.
    rewrite cover_inr.
    rewrite comp_assoc.
    reflexivity.
Qed.

(** ** Cover-paws (braid) interaction at C level

    The C-iso [paws ≈ to coprod_comm] intertwines [cover g h] and
    [cover h g].  Both directions are pure cocartesian calculations
    via [paws_fork] and the [paws ∘ inl ≈ inr] / [paws ∘ inr ≈ inl]
    base facts. *)

Lemma paws_inl {x y : C} :
  (@paws C H_Coc x y) ∘ inl ≈ inr.
Proof.
  unfold paws, swap, inl, inr; simpl.
  apply (@exl_fork _ H_Coc).
Qed.

Lemma paws_inr {x y : C} :
  (@paws C H_Coc x y) ∘ inr ≈ inl.
Proof.
  unfold paws, swap, inl, inr; simpl.
  apply (@exr_fork _ H_Coc).
Qed.

(** Braid-naturality at C level: [paws ∘ cover g h ≈ cover h g ∘ paws]. *)
Lemma cover_paws {a a' b b' : C} (g : a ~> a') (h : b ~> b') :
  paws ∘ cover g h ≈ cover h g ∘ paws.
Proof.
  apply coprod_ext.
  - (* ∘ inl: LHS = paws ∘ (cover g h ∘ inl) = paws ∘ (inl ∘ g) = (paws ∘ inl) ∘ g = inr ∘ g
       RHS = (cover h g ∘ paws) ∘ inl = cover h g ∘ (paws ∘ inl) = cover h g ∘ inr = inr ∘ g  *)
    rewrite <- comp_assoc.
    rewrite cover_inl.
    rewrite comp_assoc.
    rewrite paws_inl.
    rewrite <- comp_assoc.
    rewrite paws_inl.
    rewrite cover_inr.
    reflexivity.
  - (* ∘ inr: LHS = paws ∘ (cover g h ∘ inr) = paws ∘ (inr ∘ h) = (paws ∘ inr) ∘ h = inl ∘ h
       RHS = (cover h g ∘ paws) ∘ inr = cover h g ∘ (paws ∘ inr) = cover h g ∘ inl = inl ∘ h *)
    rewrite <- comp_assoc.
    rewrite cover_inr.
    rewrite comp_assoc.
    rewrite paws_inr.
    rewrite <- comp_assoc.
    rewrite paws_inr.
    rewrite cover_inl.
    reflexivity.
Qed.

(** ** Pushout-along-iso: the apex collapses

    For [m : Y → N] and a C-iso [phi : Y ≅ Z], the pushout of [(m, to phi)]
    is canonically [N], with [pushout_in1 ≈ id[N]] and
    [pushout_in2 ≈ m ∘ from phi]. *)

Lemma pushout_along_iso_apex {Y Z N : C} (m : Y ~> N) (phi : Y ≅ Z) :
  pushout_apex (pushout m (to phi)) ≅ N.
Proof.
  set (P := pushout m (to phi)).
  assert (HC : id[N] ∘ m ≈ (m ∘ from phi) ∘ to phi).
  { rewrite id_left.
    rewrite <- comp_assoc.
    rewrite iso_from_to.
    rewrite id_right.
    reflexivity. }
  pose (k := pushout_med P HC).
  assert (Hk1 : k ∘ pushout_in1 P ≈ id) by (apply pushout_med_in1).
  assert (Hk2 : k ∘ pushout_in2 P ≈ m ∘ from phi) by (apply pushout_med_in2).
  unshelve refine
    {| to := k;
       from := pushout_in1 P;
       iso_to_from := _;
       iso_from_to := _ |}.
  - exact Hk1.
  - apply (pushout_med_eq P (pushout_commutes P)
            (pushout_in1 P ∘ k) id).
    + rewrite <- comp_assoc.
      rewrite Hk1; cat.
    + rewrite <- comp_assoc.
      rewrite Hk2.
      pose proof (pushout_commutes P) as PC.
      rewrite comp_assoc.
      (* Need: pushout_in1 P ∘ m ∘ from phi ≈ pushout_in2 P.
         By PC: pushout_in1 P ∘ m ≈ pushout_in2 P ∘ to phi.
         Hence pushout_in1 P ∘ m ∘ from phi ≈ pushout_in2 P ∘ to phi ∘ from phi
                                            ≈ pushout_in2 P ∘ id ≈ pushout_in2 P. *)
      rewrite PC.
      rewrite <- comp_assoc.
      rewrite iso_to_from.
      apply id_right.
    + cat.
    + cat.
Defined.

(** ** Bridging lemma: composing a cospan with a [mor_as_cospan] on the right

    For [f : Y ~{CospanCat}~> Z] (a generic cospan) and [h : X ~> Y] a
    C-morphism, [cospan_compose f (mor_as_cospan h)] simplifies under
    the pushout-id-collapse: the pushout of [(id[Y], cospan_in1 f)] is
    canonically the apex of [f], and the composite cospan becomes
    [Build_CospanArrow (apex f) (cospan_in1 f ∘ h) (cospan_in2 f)]. *)

Lemma cospan_compose_mor_as_cospan_right
      {X Y Z : C} (f : CospanArrow Y Z) (h : X ~> Y) :
  cospan_equiv (cospan_compose HP f (mor_as_cospan h))
               (Build_CospanArrow (cospan_apex f)
                                  (cospan_in1 f ∘ h)
                                  (cospan_in2 f)).
Proof.
  unfold cospan_compose, mor_as_cospan; simpl.
  exists (pushout_id_left_apex HP (cospan_in1 f)); simpl.
  split.
  - rewrite comp_assoc.
    apply compose_respects; [|reflexivity].
    apply pushout_med_in1.
  - rewrite comp_assoc.
    rewrite pushout_med_in2.
    apply id_left.
Defined.

(** Dual bridging: composing a cospan with [mor_as_cospan (to phi)] on
    the LEFT where [phi] is a C-iso. By [pushout_along_iso_apex], the
    apex collapses to apex(f), with adjusted in2. *)

Lemma cospan_compose_mor_iso_left
      {X Y Z : C} (f : CospanArrow X Y) (phi : Y ≅ Z) :
  cospan_equiv (cospan_compose HP (mor_as_cospan (to phi)) f)
               (Build_CospanArrow (cospan_apex f)
                                  (cospan_in1 f)
                                  (cospan_in2 f ∘ from phi)).
Proof.
  unfold cospan_compose, mor_as_cospan; simpl.
  pose (P := pushout (cospan_in2 f) (to phi)).
  assert (HC : id[cospan_apex f] ∘ cospan_in2 f
              ≈ (cospan_in2 f ∘ from phi) ∘ to phi).
  { rewrite id_left.
    rewrite <- comp_assoc.
    rewrite iso_from_to.
    rewrite id_right.
    reflexivity. }
  pose (k := pushout_med P HC).
  assert (Hk1 : k ∘ pushout_in1 P ≈ id) by (apply pushout_med_in1).
  assert (Hk2 : k ∘ pushout_in2 P ≈ cospan_in2 f ∘ from phi)
    by (apply pushout_med_in2).
  unshelve refine
    (existT _ {| to := k;
                 from := pushout_in1 P;
                 iso_to_from := _;
                 iso_from_to := _ |} _).
  - exact Hk1.
  - apply (pushout_med_eq P (pushout_commutes P)
            (pushout_in1 P ∘ k) id).
    + rewrite <- comp_assoc.
      rewrite Hk1; cat.
    + rewrite <- comp_assoc.
      rewrite Hk2.
      pose proof (pushout_commutes P) as PC.
      rewrite comp_assoc.
      rewrite PC.
      rewrite <- comp_assoc.
      rewrite iso_to_from.
      apply id_right.
    + cat.
    + cat.
  - simpl; split; fold P.
    + rewrite comp_assoc.
      rewrite Hk1.
      apply id_left.
    + rewrite id_right.
      exact Hk2.
Defined.

(** ** Left-unitor naturality

    For any cospan [g : x → y]:
      [g ∘ unit_left ≈ unit_left ∘ bimap id g]
    in [CospanCat C HP], where [unit_left = mor_as_cospan (zero ▽ id)]
    and [bimap id g = cospan_tensor (cospan_id 0) g].

    The iso of apexes is [pushout_cover_id_unit_left_apex (cospan_in2 g)],
    whose [to] is exactly the [pushout_med] making the legs match the
    bridging-lemma-simplified LHS. *)

Lemma cospan_unit_left_natural
      {x y : C} (g : CospanArrow x y) :
  cospan_equiv
    (cospan_compose HP g (mor_as_cospan (zero ▽ id[x])))
    (cospan_compose HP (mor_as_cospan (zero ▽ id[y]))
       (cospan_tensor (cospan_id 0%object) g)).
Proof.
  (* LHS simplifies via bridging. *)
  eapply cospan_equiv_trans;
    [apply cospan_compose_mor_as_cospan_right|].
  apply cospan_equiv_sym.
  unfold cospan_compose, mor_as_cospan, cospan_tensor; simpl.
  (* Inline the apex iso construction so [to] reduces by [pushout_med_in1/2]. *)
  pose (Pcov := pushout (cover id[0] (cospan_in2 g) : (0 + y)%object ~> (0 + cospan_apex g)%object)
                        (zero ▽ id[y] : (0 + y)%object ~> y)).
  assert (HC : (zero ▽ id[cospan_apex g]) ∘ cover id[0] (cospan_in2 g)
              ≈ cospan_in2 g ∘ (zero ▽ id[y])).
  { unfold cover.
    rewrite <- merge_comp.
    rewrite (comp_assoc _ inl).
    rewrite (comp_assoc _ inr).
    rewrite inl_merge, inr_merge.
    rewrite id_left, id_right.
    rewrite <- merge_comp.
    rewrite id_right, zero_comp.
    reflexivity. }
  pose (m := pushout_med Pcov HC).
  assert (Hm1 : m ∘ pushout_in1 Pcov ≈ zero ▽ id[cospan_apex g])
    by (apply pushout_med_in1).
  assert (Hm2 : m ∘ pushout_in2 Pcov ≈ cospan_in2 g)
    by (apply pushout_med_in2).
  unshelve refine
    (existT _ {| to := m;
                 from := pushout_in1 Pcov ∘ inr;
                 iso_to_from := _;
                 iso_from_to := _ |} _).
  - (* m ∘ (pushout_in1 Pcov ∘ inr) ≈ id at apex g *)
    rewrite comp_assoc.
    rewrite Hm1.
    apply inr_merge.
  - (* (pushout_in1 Pcov ∘ inr) ∘ m ≈ id at apex Pcov *)
    apply (pushout_med_eq Pcov (pushout_commutes Pcov)
            ((pushout_in1 Pcov ∘ inr) ∘ m) id).
    + rewrite <- !comp_assoc.
      rewrite Hm1.
      assert (Hinr : (@inr C _ 0 (cospan_apex g))
                       ∘ (zero[cospan_apex g] ▽ id[cospan_apex g])
                     ≈ id[0 + cospan_apex g]).
      { rewrite <- merge_comp.
        rewrite id_right.
        rewrite <- merge_inl_inr.
        apply (snd (merge_inv _ _ _ _)).
        split.
        - apply (@zero_unique C H_Ini _ _ _).
        - reflexivity. }
      rewrite Hinr.
      apply id_right.
    + rewrite <- !comp_assoc.
      rewrite Hm2.
      pose proof (pushout_commutes Pcov) as PC.
      rewrite <- (cover_inr id[0] (cospan_in2 g)).
      rewrite comp_assoc.
      rewrite PC.
      rewrite <- comp_assoc.
      rewrite inr_merge.
      apply id_right.
    + cat.
    + cat.
  - simpl; split; fold Pcov.
    + rewrite comp_assoc.
      rewrite Hm1.
      unfold cover.
      rewrite <- merge_comp.
      rewrite (comp_assoc _ inl).
      rewrite (comp_assoc _ inr).
      rewrite inl_merge, inr_merge.
      rewrite id_left, id_right.
      rewrite <- merge_comp.
      rewrite id_right, zero_comp.
      reflexivity.
    + rewrite id_right.
      exact Hm2.
Defined.

(** ** Right-unitor naturality, dual of left.

    [unit_right = mor_as_cospan (id ▽ zero : x + 0 → x)] and
    [bimap g id = cospan_tensor g (cospan_id 0)]. *)

Lemma cospan_unit_right_natural
      {x y : C} (g : CospanArrow x y) :
  cospan_equiv
    (cospan_compose HP g (mor_as_cospan (id[x] ▽ zero)))
    (cospan_compose HP (mor_as_cospan (id[y] ▽ zero))
       (cospan_tensor g (cospan_id 0%object))).
Proof.
  eapply cospan_equiv_trans;
    [apply cospan_compose_mor_as_cospan_right|].
  apply cospan_equiv_sym.
  unfold cospan_compose, mor_as_cospan, cospan_tensor; simpl.
  pose (Pcov := pushout (cover (cospan_in2 g) id[0] : (y + 0)%object ~> (cospan_apex g + 0)%object)
                        (id ▽ zero : (y + 0)%object ~> y)).
  assert (HC : (id[cospan_apex g] ▽ zero) ∘ cover (cospan_in2 g) id[0]
              ≈ cospan_in2 g ∘ (id ▽ zero)).
  { unfold cover.
    rewrite <- merge_comp.
    rewrite (comp_assoc _ inl).
    rewrite (comp_assoc _ inr).
    rewrite inl_merge, inr_merge.
    rewrite id_left, id_right.
    rewrite <- merge_comp.
    rewrite id_right, zero_comp.
    reflexivity. }
  pose (m := pushout_med Pcov HC).
  assert (Hm1 : m ∘ pushout_in1 Pcov ≈ id[cospan_apex g] ▽ zero)
    by (apply pushout_med_in1).
  assert (Hm2 : m ∘ pushout_in2 Pcov ≈ cospan_in2 g)
    by (apply pushout_med_in2).
  unshelve refine
    (existT _ {| to := m;
                 from := pushout_in1 Pcov ∘ inl;
                 iso_to_from := _;
                 iso_from_to := _ |} _).
  - rewrite comp_assoc.
    rewrite Hm1.
    apply inl_merge.
  - apply (pushout_med_eq Pcov (pushout_commutes Pcov)
            ((pushout_in1 Pcov ∘ inl) ∘ m) id).
    + rewrite <- !comp_assoc.
      rewrite Hm1.
      assert (Hinl : (@inl C _ (cospan_apex g) 0)
                       ∘ (id[cospan_apex g] ▽ zero[cospan_apex g])
                     ≈ id[cospan_apex g + 0]).
      { rewrite <- merge_comp.
        rewrite id_right.
        rewrite <- merge_inl_inr.
        apply (snd (merge_inv _ _ _ _)).
        split.
        - reflexivity.
        - apply (@zero_unique C H_Ini _ _ _). }
      rewrite Hinl.
      apply id_right.
    + rewrite <- !comp_assoc.
      rewrite Hm2.
      pose proof (pushout_commutes Pcov) as PC.
      rewrite <- (cover_inl (cospan_in2 g) id[0]).
      rewrite comp_assoc.
      rewrite PC.
      rewrite <- comp_assoc.
      rewrite inl_merge.
      apply id_right.
    + cat.
    + cat.
  - simpl; split; fold Pcov.
    + rewrite comp_assoc.
      rewrite Hm1.
      unfold cover.
      rewrite <- merge_comp.
      rewrite (comp_assoc _ inl).
      rewrite (comp_assoc _ inr).
      rewrite inl_merge, inr_merge.
      rewrite id_left, id_right.
      rewrite <- merge_comp.
      rewrite id_right, zero_comp.
      reflexivity.
    + rewrite id_right.
      exact Hm2.
Defined.

(** ** Tensor-associator naturality

    For arbitrary cospans [f : x → x'], [g : y → y'], [h : z → z']:
      [bimap f (bimap g h) ∘ tensor_assoc
       ≈ tensor_assoc ∘ bimap (bimap f g) h]
    in [CospanCat C HP], where [tensor_assoc = mor_as_cospan (to coprod_assoc)]
    and [bimap = cospan_tensor]. *)

Lemma cospan_tensor_assoc_natural
      {x x' y y' z z' : C}
      (f : CospanArrow x x') (g : CospanArrow y y') (h : CospanArrow z z') :
  cospan_equiv
    (cospan_compose HP (cospan_tensor f (cospan_tensor g h))
                       (mor_as_cospan (to coprod_assoc)))
    (cospan_compose HP (mor_as_cospan (to coprod_assoc))
                       (cospan_tensor (cospan_tensor f g) h)).
Proof.
  eapply cospan_equiv_trans;
    [apply cospan_compose_mor_as_cospan_right|].
  apply cospan_equiv_sym.
  eapply cospan_equiv_trans;
    [apply cospan_compose_mor_iso_left|].
  apply cospan_equiv_sym.
  unfold cospan_tensor; simpl.
  exists (iso_sym (@coprod_assoc C H_Coc (cospan_apex f) (cospan_apex g) (cospan_apex h))).
  simpl; split.
  - (* from coprod_assoc ∘ (cover (in1 f) (cover (in1 g) (in1 h)) ∘ to coprod_assoc)
       ≈ cover (cover (in1 f) (in1 g)) (in1 h) *)
    rewrite comp_assoc.
    rewrite cover_assoc_from.
    rewrite <- comp_assoc.
    rewrite iso_from_to.
    apply id_right.
  - (* from coprod_assoc ∘ cover (in2 f) (cover (in2 g) (in2 h))
       ≈ cover (cover (in2 f) (in2 g)) (in2 h) ∘ from coprod_assoc *)
    apply cover_assoc_from.
Defined.

(** ** From [to] to [from] naturality

    General principle: for any iso [phi : X ≅ Y] in a category [D],
    if [g ∘ to phi ≈ to phi ∘ h] (the "to" naturality) then
    [h ∘ from phi ≈ from phi ∘ g] (the "from" naturality). *)

Lemma from_naturality_of_to {D : Category} {X Y W : D}
      (phi : @Isomorphism D X Y)
      (g : Y ~{D}~> W) (h : X ~{D}~> W)
      (Hto : g ∘ to phi ≈ h) :
  g ≈ h ∘ from phi.
Proof.
  rewrite <- Hto.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  rewrite id_right.
  reflexivity.
Qed.

Lemma from_naturality_of_to_2 {D : Category} {X Y A B : D}
      (phi : @Isomorphism D X Y) (psi : @Isomorphism D A B)
      (g : Y ~{D}~> B) (h : X ~{D}~> A)
      (Hto : g ∘ to phi ≈ to psi ∘ h) :
  from psi ∘ g ≈ h ∘ from phi.
Proof.
  apply (from_naturality_of_to phi (from psi ∘ g) h).
  rewrite <- comp_assoc.
  rewrite Hto.
  rewrite comp_assoc.
  rewrite iso_from_to.
  apply id_left.
Qed.

(** Variant matching the Monoidal naturality shape:
      from to-naturality [g ∘ to phi_X ≈ to phi_Y ∘ h]
      derive from-naturality [h ∘ from phi_X ≈ from phi_Y ∘ g]. *)
Lemma from_naturality_of_to_M {D : Category} {X Y A B : D}
      (phi_X : @Isomorphism D X A) (phi_Y : @Isomorphism D Y B)
      (g : A ~{D}~> B) (h : X ~{D}~> Y)
      (Hto : g ∘ to phi_X ≈ to phi_Y ∘ h) :
  h ∘ from phi_X ≈ from phi_Y ∘ g.
Proof.
  assert (H1 : from phi_Y ∘ g ∘ to phi_X ≈ h).
  { rewrite <- comp_assoc.
    rewrite Hto.
    rewrite comp_assoc.
    rewrite iso_from_to.
    apply id_left. }
  rewrite <- H1.
  rewrite <- (comp_assoc _ (to phi_X) (from phi_X)).
  rewrite iso_to_from.
  apply id_right.
Qed.

(** ** Triangle identity at C level (for coproducts).

    [cover (to coprod_zero_r) id ≈ cover id (to coprod_zero_l) ∘ to coprod_assoc]
    i.e., (X+0)+Y → X+Y the two paths agree. *)

Lemma coprod_triangle_aux {x y : C} :
  cover (to (@coprod_zero_r C H_Coc H_Ini x)) id[y]
  ≈ cover id[x] (to (@coprod_zero_l C H_Coc H_Ini y))
    ∘ to (@coprod_assoc C H_Coc x 0 y).
Proof.
  apply coprod_ext.
  - apply coprod_ext.
    + (* ∘ (inl ∘ inl), i.e., x part *)
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (cover _ id[y]) inl inl).
      rewrite cover_inl.
      rewrite <- (comp_assoc inl (to coprod_zero_r) inl).
      (* RHS: cover id coprod_zero_l ∘ (coprod_assoc ∘ (inl ∘ inl)) = inl *)
      rewrite assoc_to_inl_inl.
      (* LHS: inl ∘ (to coprod_zero_r ∘ inl)
         to coprod_zero_r = id ▽ zero, so (id ▽ zero) ∘ inl = id *)
      assert (Hzr : to (@coprod_zero_r C H_Coc H_Ini x) ∘ (@inl C _ x 0) ≈ id[x]).
      { unfold to, coprod_zero_r; simpl. apply inl_merge. }
      rewrite Hzr.
      rewrite id_right.
      symmetry.
      rewrite cover_inl.
      apply id_right.
    + (* ∘ (inl ∘ inr), i.e., 0 part - both go to zero *)
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (cover _ id[y]) inl inr).
      rewrite cover_inl.
      rewrite <- (comp_assoc inl (to coprod_zero_r) inr).
      assert (Hzr_inr : to (@coprod_zero_r C H_Coc H_Ini x) ∘ (@inr C _ x 0) ≈ zero).
      { unfold to, coprod_zero_r; simpl. apply inr_merge. }
      rewrite Hzr_inr.
      (* RHS: cover id coprod_zero_l ∘ (coprod_assoc ∘ (inl ∘ inr)) *)
      rewrite assoc_to_inl_inr.
      (* Goal: inl ∘ zero[x] ≈ cover id coprod_zero_l ∘ (inr ∘ inl) *)
      rewrite (comp_assoc (cover id[x] _) inr inl).
      rewrite cover_inr.
      rewrite <- comp_assoc.
      assert (Hzl : to (@coprod_zero_l C H_Coc H_Ini y) ∘ (@inl C _ 0 y) ≈ zero).
      { unfold to, coprod_zero_l; simpl. apply inl_merge. }
      rewrite Hzl.
      apply (@zero_unique C H_Ini _ _ _).
  - (* ∘ inr, i.e., y part *)
    rewrite cover_inr.
    rewrite id_right.
    rewrite <- (comp_assoc (cover id[x] _) (to coprod_assoc) inr).
    rewrite assoc_to_inr.
    rewrite (comp_assoc (cover id[x] _) inr inr).
    rewrite cover_inr.
    rewrite <- (comp_assoc inr _ inr).
    assert (Hzl_inr : to (@coprod_zero_l C H_Coc H_Ini y) ∘ (@inr C _ 0 y) ≈ id[y]).
    { unfold to, coprod_zero_l; simpl. apply inr_merge. }
    rewrite Hzl_inr.
    symmetry. apply id_right.
Qed.

(** ** C-level pentagon identity for [coprod_assoc].

    [cover id (to coprod_assoc) ∘ to coprod_assoc ∘ cover (to coprod_assoc) id
     ≈ to coprod_assoc ∘ to coprod_assoc]
    at types [(((X+Y)+Z)+W) → (X+(Y+(Z+W)))]. *)

(** Auxiliary computations used in the C-level pentagon below.

    Strategy: each goal has shape [(EXPR) ∘ COMPOSITE_INJECTION ≈ TARGET].
    We use the [coprod_ext_eq] tactic-like trick: assert the helper equation
    and apply it. *)

(** Reduce one composite alpha against `inl ∘ inl ∘ inl` to inl.
    Key fact: alpha ∘ (inl ∘ inl) = inl by [assoc_to_inl_inl].  So
    alpha ∘ (inl ∘ inl) ∘ inl = inl ∘ inl, and then cover α id ∘ (inl ∘ inl)
    = inl ∘ α ∘ inl = inl ∘ inl... etc. *)

Lemma pentagon_lhs_iii {X Y Z W : C} :
  (cover (id[X]) (to (@coprod_assoc C H_Coc Y Z W))
   ∘ to (@coprod_assoc C H_Coc X (Y + Z) W)
   ∘ cover (to (@coprod_assoc C H_Coc X Y Z)) (id[W]))
  ∘ ((inl ∘ inl) ∘ inl)
  ≈ inl.
Proof.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (cover (to coprod_assoc) id[W]) inl (inl ∘ inl)).
  rewrite cover_inl.
  (* Goal: cover id α ∘ (α ∘ ((inl ∘ α) ∘ (inl ∘ inl))) *)
  rewrite <- (comp_assoc inl (to coprod_assoc) (inl ∘ inl)).
  (* Goal: cover id α ∘ (α ∘ (inl ∘ (α ∘ (inl ∘ inl)))) *)
  rewrite assoc_to_inl_inl.
  (* Goal: cover id α ∘ (α ∘ (inl ∘ inl)) *)
  rewrite assoc_to_inl_inl.
  (* Goal: cover id α ∘ inl *)
  rewrite cover_inl.
  apply id_right.
Qed.

Lemma pentagon_rhs_iii {X Y Z W : C} :
  (to (@coprod_assoc C H_Coc X Y (Z + W))
   ∘ to (@coprod_assoc C H_Coc (X + Y) Z W))
  ∘ ((inl ∘ inl) ∘ inl)
  ≈ inl.
Proof.
  rewrite <- !comp_assoc.
  (* Goal: α ∘ (α' ∘ (inl ∘ (inl ∘ inl))) where α, α' are at different types *)
  rewrite (comp_assoc inl inl inl).
  rewrite (comp_assoc (to coprod_assoc) (inl ∘ inl) inl).
  rewrite assoc_to_inl_inl.
  rewrite assoc_to_inl_inl.
  reflexivity.
Qed.

Lemma pentagon_lhs_iir {X Y Z W : C} :
  (cover (id[X]) (to (@coprod_assoc C H_Coc Y Z W))
   ∘ to (@coprod_assoc C H_Coc X (Y + Z) W)
   ∘ cover (to (@coprod_assoc C H_Coc X Y Z)) (id[W]))
  ∘ ((inl ∘ inl) ∘ inr)
  ≈ inr ∘ inl.
Proof.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (cover (to coprod_assoc) id[W]) inl (inl ∘ inr)).
  rewrite cover_inl.
  rewrite <- (comp_assoc inl (to coprod_assoc) (inl ∘ inr)).
  rewrite assoc_to_inl_inr.
  (* Goal: cover id α ∘ (α ∘ (inl ∘ (inr ∘ inl))) ≈ inr ∘ inl *)
  rewrite (comp_assoc inl inr inl).
  rewrite (comp_assoc (to coprod_assoc) (inl ∘ inr) inl).
  rewrite assoc_to_inl_inr.
  (* Goal: cover id α ∘ ((inr ∘ inl) ∘ inl) ≈ inr ∘ inl *)
  rewrite <- (comp_assoc inr inl inl).
  rewrite (comp_assoc (cover id[X] _) inr (inl ∘ inl)).
  rewrite cover_inr.
  rewrite <- (comp_assoc inr (to coprod_assoc) (inl ∘ inl)).
  rewrite assoc_to_inl_inl.
  reflexivity.
Qed.

Lemma pentagon_rhs_iir {X Y Z W : C} :
  (to (@coprod_assoc C H_Coc X Y (Z + W))
   ∘ to (@coprod_assoc C H_Coc (X + Y) Z W))
  ∘ ((inl ∘ inl) ∘ inr)
  ≈ inr ∘ inl.
Proof.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc inl inl inr).
  rewrite (comp_assoc (to coprod_assoc) (inl ∘ inl) inr).
  rewrite assoc_to_inl_inl.
  rewrite assoc_to_inl_inr.
  reflexivity.
Qed.

Lemma pentagon_lhs_ir {X Y Z W : C} :
  (cover (id[X]) (to (@coprod_assoc C H_Coc Y Z W))
   ∘ to (@coprod_assoc C H_Coc X (Y + Z) W)
   ∘ cover (to (@coprod_assoc C H_Coc X Y Z)) (id[W]))
  ∘ (inl ∘ inr)
  ≈ inr ∘ (inr ∘ inl).
Proof.
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (cover (to coprod_assoc) id[W]) inl inr).
  rewrite cover_inl.
  rewrite <- (comp_assoc inl (to coprod_assoc) inr).
  rewrite assoc_to_inr.
  (* Goal: cover id α ∘ (α ∘ (inl ∘ (inr ∘ inr))) *)
  rewrite (comp_assoc inl inr inr).
  rewrite (comp_assoc (to coprod_assoc) (inl ∘ inr) inr).
  rewrite assoc_to_inl_inr.
  (* Goal: cover id α ∘ ((inr ∘ inl) ∘ inr) *)
  rewrite <- (comp_assoc inr inl inr).
  rewrite (comp_assoc (cover id[X] _) inr (inl ∘ inr)).
  rewrite cover_inr.
  rewrite <- (comp_assoc inr (to coprod_assoc) (inl ∘ inr)).
  rewrite assoc_to_inl_inr.
  reflexivity.
Qed.

Lemma pentagon_rhs_ir {X Y Z W : C} :
  (to (@coprod_assoc C H_Coc X Y (Z + W))
   ∘ to (@coprod_assoc C H_Coc (X + Y) Z W))
  ∘ (inl ∘ inr)
  ≈ inr ∘ (inr ∘ inl).
Proof.
  rewrite <- !comp_assoc.
  rewrite assoc_to_inl_inr.
  (* Goal: α[X,Y,Z+W] ∘ (inr ∘ inl) *)
  rewrite (comp_assoc (to coprod_assoc) inr inl).
  rewrite assoc_to_inr.
  rewrite <- (comp_assoc inr inr inl).
  reflexivity.
Qed.

Lemma pentagon_lhs_r {X Y Z W : C} :
  (cover (id[X]) (to (@coprod_assoc C H_Coc Y Z W))
   ∘ to (@coprod_assoc C H_Coc X (Y + Z) W)
   ∘ cover (to (@coprod_assoc C H_Coc X Y Z)) (id[W]))
  ∘ inr
  ≈ inr ∘ (inr ∘ inr).
Proof.
  rewrite <- !comp_assoc.
  rewrite cover_inr.
  rewrite id_right.
  (* Goal: cover id α ∘ (α ∘ inr) *)
  rewrite assoc_to_inr.
  rewrite (comp_assoc (cover id[X] _) inr inr).
  rewrite cover_inr.
  rewrite <- (comp_assoc inr (to coprod_assoc) inr).
  rewrite assoc_to_inr.
  reflexivity.
Qed.

Lemma pentagon_rhs_r {X Y Z W : C} :
  (to (@coprod_assoc C H_Coc X Y (Z + W))
   ∘ to (@coprod_assoc C H_Coc (X + Y) Z W))
  ∘ inr
  ≈ inr ∘ (inr ∘ inr).
Proof.
  rewrite <- !comp_assoc.
  rewrite assoc_to_inr.
  rewrite (comp_assoc (to coprod_assoc) inr inr).
  rewrite assoc_to_inr.
  rewrite <- (comp_assoc inr inr inr).
  reflexivity.
Qed.

(** C-level pentagon for [coprod_assoc].

    Two coproduct iso composites out of [((X+Y)+Z)+W] are equal iff they
    agree on the four basis injections [(inl∘inl)∘inl], [(inl∘inl)∘inr],
    [inl∘inr], and [inr].  Each of those is closed by the corresponding
    [pentagon_lhs_*] / [pentagon_rhs_*] helper above. *)
Lemma coprod_pentagon_aux {X Y Z W : C} :
  cover (id[X]) (to (@coprod_assoc C H_Coc Y Z W))
    ∘ to (@coprod_assoc C H_Coc X (Y + Z) W)
    ∘ cover (to (@coprod_assoc C H_Coc X Y Z)) (id[W])
  ≈ to (@coprod_assoc C H_Coc X Y (Z + W))
    ∘ to (@coprod_assoc C H_Coc (X + Y) Z W).
Proof.
  apply coprod_ext.
  - (* outer inl case: domain (X+Y)+Z *)
    apply coprod_ext.
    + (* (inl ∘ inl) on (X+Y)+Z side: domain X+Y *)
      apply coprod_ext.
      * (* ((inl ∘ inl) ∘ inl): X-injection.
           Goal is left-associated, helpers use right-associated form.
           Bridge by an explicit assertion. *)
        assert (Hl : forall (u : (X + Y + Z + W) ~> X + (Y + (Z + W))),
                   (u ∘ inl) ∘ inl ∘ inl ≈ u ∘ ((inl ∘ inl) ∘ inl)).
        { intros u; rewrite !comp_assoc; reflexivity. }
        rewrite !Hl.
        rewrite pentagon_lhs_iii.
        symmetry; rewrite pentagon_rhs_iii; reflexivity.
      * (* ((inl ∘ inl) ∘ inr): Y-injection. *)
        assert (Hl : forall (u : (X + Y + Z + W) ~> X + (Y + (Z + W))),
                   (u ∘ inl) ∘ inl ∘ inr ≈ u ∘ ((inl ∘ inl) ∘ inr)).
        { intros u; rewrite !comp_assoc; reflexivity. }
        rewrite !Hl.
        rewrite pentagon_lhs_iir.
        symmetry; rewrite pentagon_rhs_iir; reflexivity.
    + (* (inl ∘ inr): Z-injection. *)
      assert (Hl : forall (u : (X + Y + Z + W) ~> X + (Y + (Z + W))),
                 (u ∘ inl) ∘ inr ≈ u ∘ (inl ∘ inr)).
      { intros u; rewrite !comp_assoc; reflexivity. }
      rewrite !Hl.
      rewrite pentagon_lhs_ir.
      symmetry; rewrite pentagon_rhs_ir; reflexivity.
  - (* outer inr: W-injection. *)
    rewrite pentagon_lhs_r.
    symmetry; rewrite pentagon_rhs_r; reflexivity.
Qed.

(** ** Triangle and Pentagon at cospan level

    These lift the C-level [coprod_triangle_aux] and [coprod_pentagon_aux]
    through [cospan_tensor_mor_as_cospan], [mor_as_cospan_compose], and
    [mor_as_cospan_proper]. *)

Lemma cospan_triangle_identity {x y : C} :
  cospan_equiv
    (cospan_tensor (mor_as_cospan (to (@coprod_zero_r C H_Coc H_Ini x))) (cospan_id y))
    (cospan_compose HP
       (cospan_tensor (cospan_id x) (mor_as_cospan (to (@coprod_zero_l C H_Coc H_Ini y))))
       (mor_as_cospan (to (@coprod_assoc C H_Coc x 0 y)))).
Proof.
  (* LHS = cospan_tensor (mor_as_cospan _) (mor_as_cospan id[y]) (since cospan_id = mor_as_cospan id)
        ≈ mor_as_cospan (cover (to coprod_zero_r) id[y])  [by cospan_tensor_mor_as_cospan]
     RHS = cospan_compose (cospan_tensor (mor_as_cospan id[x]) (mor_as_cospan _)) (mor_as_cospan _)
        ≈ cospan_compose (mor_as_cospan (cover id[x] (to coprod_zero_l))) (mor_as_cospan _)
        ≈ mor_as_cospan ((cover id[x] (to coprod_zero_l)) ∘ (to coprod_assoc))  [by mor_as_cospan_compose]
     Use coprod_triangle_aux to equate the C-level morphisms. *)
  eapply cospan_equiv_trans.
  { (* cospan_id x = mor_as_cospan id[x] up to cospan_equiv via mor_as_cospan_id (reversed) *)
    apply cospan_tensor_respects.
    - apply cospan_equiv_refl.
    - apply cospan_equiv_sym, mor_as_cospan_id. }
  eapply cospan_equiv_trans.
  { apply cospan_tensor_mor_as_cospan. }
  apply cospan_equiv_sym.
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_tensor_respects.
      + apply cospan_equiv_sym, mor_as_cospan_id.
      + apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_equiv_refl.
    - apply cospan_tensor_mor_as_cospan. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  symmetry.
  apply coprod_triangle_aux.
Defined.

(** ** Toward [Monoidal (CospanCat C HP)]

    All six naturality lemmas ([to/from] x [unit_left/unit_right/tensor_assoc])
    are now derivable from the proved [cospan_unit_left_natural],
    [cospan_unit_right_natural], [cospan_tensor_assoc_natural], and the
    [from_naturality_of_to_M] helper.

    The remaining obligations for the full [Monoidal] instance:

      - [triangle_identity]: at cospan level, this reduces to the C-level
        [coprod_triangle_aux] (proved above) lifted via
        [cospan_tensor_mor_as_cospan] and [mor_as_cospan_compose].

      - [pentagon_identity]: derived from [coprod_pentagon_aux] (C-level)
        via [mor_as_cospan_proper], [cospan_tensor_mor_as_cospan], and
        [mor_as_cospan_compose].  See [cospan_pentagon_identity] below. *)

(** Cospan-level pentagon, parallel to [cospan_triangle_identity]. *)
Lemma cospan_pentagon_identity {x y z w : C} :
  cospan_equiv
    (cospan_compose HP
       (cospan_tensor (cospan_id x)
          (mor_as_cospan (to (@coprod_assoc C H_Coc y z w))))
       (cospan_compose HP
          (mor_as_cospan (to (@coprod_assoc C H_Coc x (y + z) w)))
          (cospan_tensor (mor_as_cospan (to (@coprod_assoc C H_Coc x y z)))
                         (cospan_id w))))
    (cospan_compose HP
       (mor_as_cospan (to (@coprod_assoc C H_Coc x y (z + w))))
       (mor_as_cospan (to (@coprod_assoc C H_Coc (x + y) z w)))).
Proof.
  (* LHS lifts via cospan_tensor_mor_as_cospan + mor_as_cospan_compose to
     mor_as_cospan (cover id α ∘ α ∘ cover α id).
     RHS lifts via mor_as_cospan_compose to mor_as_cospan (α ∘ α).
     Equate via mor_as_cospan_proper from coprod_pentagon_aux. *)
  eapply cospan_equiv_trans.
  { (* Outer compose: g = cospan_tensor (cospan_id x) ..., f = compose ... *)
    apply cospan_compose_respects_aux.
    - (* f' = compose (mor_as_cospan α) (cospan_tensor (cospan_id w) ...)
         Want Hf : f ≈ f'. *)
      apply cospan_compose_respects_aux.
      + (* Inner f': cospan_tensor (mor_as_cospan id[w]) ... after subst *)
        apply cospan_tensor_respects.
        * apply cospan_equiv_refl.
        * apply cospan_equiv_sym, mor_as_cospan_id.
      + apply cospan_equiv_refl.
    - (* g': cospan_tensor (mor_as_cospan id[x]) ... *)
      apply cospan_tensor_respects.
      + apply cospan_equiv_sym, mor_as_cospan_id.
      + apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply cospan_compose_respects_aux.
      + apply cospan_tensor_mor_as_cospan.
      + apply cospan_equiv_refl.
    - apply cospan_tensor_mor_as_cospan. }
  eapply cospan_equiv_trans.
  { apply cospan_compose_respects_aux.
    - apply mor_as_cospan_compose.
    - apply cospan_equiv_refl. }
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply cospan_equiv_sym.
  eapply cospan_equiv_trans.
  { apply mor_as_cospan_compose. }
  apply mor_as_cospan_proper.
  rewrite comp_assoc.
  symmetry.
  apply coprod_pentagon_aux.
Defined.

(** ** Full Cospan_Monoidal instance

    The Monoidal structure on [CospanCat C HP], with:
      - unit object [I = 0] (initial object of C)
      - tensor = coproduct of apexes via [Cospan_Bifunctor]
      - unitors / associator = [mor_iso_lift] of the C-level coproduct isos
      - naturality conditions discharged by [cospan_unit_*_natural] and
        [cospan_tensor_assoc_natural]
      - triangle / pentagon discharged by [cospan_triangle_identity] /
        [cospan_pentagon_identity]. *)

#[export] Program Instance Cospan_Monoidal : @Monoidal (CospanCat C HP) := {|
  I := (@Cospan_unit_obj C H_Ini : CospanCat C HP);
  tensor := Cospan_Bifunctor HP;
  unit_left    := fun X => mor_iso_lift (@coprod_zero_l C H_Coc H_Ini X);
  unit_right   := fun X => mor_iso_lift (@coprod_zero_r C H_Coc H_Ini X);
  tensor_assoc := fun X Y Z => mor_iso_lift (@coprod_assoc C H_Coc X Y Z)
|}.
Next Obligation. apply cospan_unit_left_natural. Defined.
Next Obligation.
  apply (@from_naturality_of_to_M (CospanCat C HP)
           _ _ _ _
           (mor_iso_lift (@coprod_zero_l C H_Coc H_Ini x))
           (mor_iso_lift (@coprod_zero_l C H_Coc H_Ini y))
           g (cospan_tensor (cospan_id 0%object) g)).
  apply cospan_unit_left_natural.
Defined.
Next Obligation. apply cospan_unit_right_natural. Defined.
Next Obligation.
  apply (@from_naturality_of_to_M (CospanCat C HP)
           _ _ _ _
           (mor_iso_lift (@coprod_zero_r C H_Coc H_Ini x))
           (mor_iso_lift (@coprod_zero_r C H_Coc H_Ini y))
           g (cospan_tensor g (cospan_id 0%object))).
  apply cospan_unit_right_natural.
Defined.
Next Obligation. apply cospan_tensor_assoc_natural. Defined.
Next Obligation.
  apply (@from_naturality_of_to_M (CospanCat C HP)
           _ _ _ _
           (mor_iso_lift (@coprod_assoc C H_Coc x z v))
           (mor_iso_lift (@coprod_assoc C H_Coc y w u))
           (cospan_tensor g (cospan_tensor h i))
           (cospan_tensor (cospan_tensor g h) i)).
  apply cospan_tensor_assoc_natural.
Defined.
Next Obligation. (* triangle_identity *)
  apply cospan_triangle_identity.
Defined.
Next Obligation. (* pentagon_identity *)
  (* Reassociate via cospan_compose_assoc, then apply the proved identity. *)
  eapply cospan_equiv_trans.
  { apply cospan_equiv_sym. apply cospan_compose_assoc. }
  apply cospan_pentagon_identity.
Defined.

End CospanMonoidal.

(** ** Status of the full Cospan-Hypergraph derivation

    With the above [mor_as_cospan] embedding and the unitor / associator
    / braid cospans defined as data, the Monoidal coherence proofs at
    the CospanCat level reduce to:

      (i)  the corresponding C-level coproduct facts (provided by
           [Structure/Cocartesian.v]) — for triangle, pentagon,
           naturality of unitors;
     (ii)  the [cospan_compose] of two morphism-as-cospans agreeing
           with the morphism-as-cospan of the composite in C, which
           reduces to the pushout-of-id-with-anything collapse — i.e.,
           [pushout id g] is canonically [Y] (the codomain of g) and
           similarly for [pushout f id], a single pushout-UMP
           calculation per unitor / associator / braid;
    (iii)  the bifunctor [fmap_comp] for [cospan_tensor], requiring
           the pushout-of-covers compatibility lemma.

    These are still ~300-500 lines of pushout reasoning, but the
    [mor_as_cospan] embedding makes them mechanically tractable.

    The downstream consumer instantiation path is now: provide
    [Cocartesian C], [Initial C], [HasPushouts C], and (for SCFA axioms)
    a witness that pushouts of identity-style maps collapse — the
    latter is automatic in [Sets] and in any category with explicit
    finite colimits. *)

(** ** Progress on V2 Final Push (this branch)

    After refactoring [CospanCat] to a direct construction (no [C^op]
    shim), the following V2d-coherence machinery is now available:

    - [cospan_tensor_id], [cospan_tensor_respects],
      [cospan_tensor_compose_compat] — the three [Proper] + bifunctor
      ingredients for [cospan_tensor].

    - [Cospan_Bifunctor : (CospanCat C HP) ∏ (CospanCat C HP) ⟶ CospanCat C HP]
      — the bifunctor underlying the Monoidal tensor.

    - [mor_as_cospan_compose], [mor_as_cospan_id], [mor_as_cospan_proper]
      — functoriality of the embedding [C ⟶ CospanCat C].

    - [mor_iso_lift] — lift any [C]-iso to a [CospanCat C HP]-iso, used
      for the unitor / associator / braid as cospan-level isos.

    - [cospan_tensor_mor_as_cospan] — the bridge
      [cospan_tensor (mor_as_cospan f) (mor_as_cospan g) ≈ mor_as_cospan (cover f g)]
      that lets [mor_as_cospan]-lifted morphisms interact with [bimap]
      in the upcoming Monoidal naturality proofs.

    What remains for the full Monoidal instance:

      (a) The six naturality conditions ([to/from_unit_left_natural],
          [to/from_unit_right_natural], [to/from_tensor_assoc_natural]).
          Each requires showing
            [g ∘ unit_left ≈ unit_left ∘ bimap id g]
          for an *arbitrary* cospan [g], where [unit_left] is a lifted
          C-iso but [g] is a generic cospan with non-trivial apex.  The
          apex of the LHS composite collapses by [pushout_id_left_apex],
          but the apex of the RHS composite is a pushout of [cover id g_2]
          against [zero ▽ id], which is a non-trivial UMP calculation
          (~50-100 lines each, ~400-600 total).

      (b) Triangle + pentagon coherence identities, each a UMP
          calculation against the unitor/associator cospans (~100-200
          lines).

    Estimated total: ~600-1000 lines of mechanical-but-detailed pushout
    UMP reasoning.  Tractable but beyond a single dispatch session. *)
(* CLOSED(V2d-coherence): the full Monoidal (CospanCat C HP) instance is
   built as [Cospan_Monoidal] above. *)
(* CLOSED(V2d-coherence): The [Cospan_BraidedMonoidal] /
   [Cospan_SymmetricMonoidal] instances are built in
   [Construction/Cospan/Symmetric.v].  The SCFA-on-every-X instance
   [cospan_scfa] (and the underlying monoid / comonoid / Frobenius /
   commutative Frobenius pieces) is built in
   [Construction/Cospan/SCFA.v].  The full
   [Hypergraph (CospanCat C HP) Cospan_SymmetricMonoidal] instance is
   built as [Cospan_Hypergraph] in
   [Construction/Cospan/HypergraphInstance.v]:
   - 4 unit axioms ([scfa_unit_{mu,eta,delta,epsilon}]) — closed via
     initiality of [0];
   - 4 tensor axioms ([scfa_tensor_{mu,eta,delta,epsilon}]) — closed via
     the C-level identity [codiag_through_mid_swap] lifted through
     [cospan_mid_swap_as_mor] / [cospan_mid_swap_inv_as_mor] and the
     standard [mor_as_cospan_compose] /
     [cospan_tensor_mor_as_cospan] / [cospan_tensor_id_left_as_cospan]
     bridges over the 5-fold [mid_swap] composite. *)
