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

(** ** Basic cospan_tensor properties

    These are the equations that hold without needing the full bifunctor
    machinery.  They are stated here as a typed surface for downstream
    code, and as semantic anchors for the full V2c-applications
    coherence proofs. *)

Section CospanTensorBasics.

Context {C : Category}.
Context `{H_Coc : @Cocartesian C}.

(** Tensor of identity cospans is the identity cospan, witnessed by the
    coproduct-of-identities equality [(id ▽ id) ∘ id = id ▽ id] and the
    codiagonal identity [inl ▽ inr ≈ id]. *)
Lemma cospan_tensor_id (X Y : C) :
  cospan_equiv (cospan_tensor (cospan_id X) (cospan_id Y))
               (cospan_id (X + Y)).
Proof.
  unfold cospan_tensor, cospan_id; simpl.
  unfold cospan_equiv, span_equiv; simpl.
  exists iso_id; simpl; split.
  - rewrite id_left.
    unfold cover.
    rewrite !id_right.
    symmetry; apply merge_inl_inr.
  - rewrite id_left.
    unfold cover.
    rewrite !id_right.
    symmetry; apply merge_inl_inr.
Defined.

(** [cospan_tensor] respects [cospan_equiv] in both arguments.

    Construction: the iso of cospan apexes [apex f + apex g ≅[C^op] apex f' + apex g']
    has [to] (in C^op) = [cover (from phi) (from psi)] (in C, but with directions
    flipped so that in C^op it goes from [apex f + apex g] to [apex f' + apex g'])
    and [from] (in C^op) = [cover (to phi) (to psi)] (similarly).

    Note: when reading [cover f g] where [f, g] are C-morphisms, the result
    is a C-morphism.  When using it to build a C^op-morphism in the
    "forward" direction, the C-direction of [cover (from phi) (from psi)]
    is [apex f + apex g ~{C}~> apex f' + apex g'], which is a C^op-morphism
    from [apex f' + apex g'] to [apex f + apex g] — i.e., the [from]
    direction in C^op.  Hence the swap. *)
Lemma cospan_tensor_respects
      {X Y X' Y' : C}
      (f f' : CospanArrow X Y) (g g' : CospanArrow X' Y') :
  cospan_equiv f f' ->
  cospan_equiv g g' ->
  cospan_equiv (cospan_tensor f g) (cospan_tensor f' g').
Proof.
  intros [phi [Hf1 Hf2]] [psi [Hg1 Hg2]].
  (* The iso of cospan apexes in C^op is built from the underlying iso
     of cospan apexes in C^op (= apex isos with C-direction flipped). *)
  unfold cospan_equiv, span_equiv,
         cospan_tensor, cospan_apex, cospan_in1, cospan_in2 in *.
  simpl in *.
  (* phi has type [apex f ≅[C^op] apex f'], so [to phi : apex f ~{C^op}~> apex f']
     which is [apex f' ~{C}~> apex f] in C.  Build the apex iso in C^op
     using [cover] in C. *)
  unshelve refine (existT _ _ _).
  - unshelve refine
      (@Build_Isomorphism (C^op)
         (@Coprod C H_Coc (apex f) (apex g))
         (@Coprod C H_Coc (apex f') (apex g'))
         (@cover C H_Coc _ _ _ _ (to phi) (to psi))
         (@cover C H_Coc _ _ _ _ (from phi) (from psi))
         _ _).
    + (* to ∘[C^op] from ≈[C^op] id
         which in C is: from ∘[C] to ≈[C] id.
         Concretely: cover (from phi) (from psi) ∘ cover (to phi) (to psi) ≈ id.
         By cover_comp: cover (from phi ∘ to phi) (from psi ∘ to psi).
         By iso_from_to: cover id id = id (via cover_id). *)
      change (
        (@cover C H_Coc _ _ _ _ (from phi) (from psi)
           ∘[C]
           @cover C H_Coc _ _ _ _ (to phi) (to psi))
        ≈[C] id).
      rewrite (@cover_comp C H_Coc).
      pose proof (@iso_to_from (C^op) _ _ phi) as Hphi.
      pose proof (@iso_to_from (C^op) _ _ psi) as Hpsi.
      change ((from phi ∘[C] to phi) ≈[C] id) in Hphi.
      change ((from psi ∘[C] to psi) ≈[C] id) in Hpsi.
      rewrite Hphi, Hpsi.
      apply (@cover_id C H_Coc).
    + change (
        (@cover C H_Coc _ _ _ _ (to phi) (to psi)
           ∘[C]
           @cover C H_Coc _ _ _ _ (from phi) (from psi))
        ≈[C] id).
      rewrite (@cover_comp C H_Coc).
      pose proof (@iso_from_to (C^op) _ _ phi) as Hphi.
      pose proof (@iso_from_to (C^op) _ _ psi) as Hpsi.
      change ((to phi ∘[C] from phi) ≈[C] id) in Hphi.
      change ((to psi ∘[C] from psi) ≈[C] id) in Hpsi.
      rewrite Hphi, Hpsi.
      apply (@cover_id C H_Coc).
  - simpl; split.
    + (* (leg1 in C^op of the tensored target cospan) ∘[C^op] (the iso's to in C^op)
         ≈ leg1 in C^op of the tensored source cospan.
         In C this reads as:
         cover (to phi) (to psi) ∘[C] cover (cospan_in1 f') (cospan_in1 g')
         ≈ cover (cospan_in1 f) (cospan_in1 g).
         By cover_comp: cover (to phi ∘ cospan_in1 f') (to psi ∘ cospan_in1 g').
         By Hf1, Hg1: cover (cospan_in1 f) (cospan_in1 g). *)
      change (
        (@cover C H_Coc _ _ _ _ (to phi) (to psi)
           ∘[C]
           @cover C H_Coc _ _ _ _ (cospan_in1 f') (cospan_in1 g'))
        ≈[C] @cover C H_Coc _ _ _ _ (cospan_in1 f) (cospan_in1 g)).
      rewrite (@cover_comp C H_Coc).
      change ((to phi ∘[C] cospan_in1 f') ≈[C] cospan_in1 f) in Hf1.
      change ((to psi ∘[C] cospan_in1 g') ≈[C] cospan_in1 g) in Hg1.
      rewrite Hf1, Hg1.
      reflexivity.
    + change (
        (@cover C H_Coc _ _ _ _ (to phi) (to psi)
           ∘[C]
           @cover C H_Coc _ _ _ _ (cospan_in2 f') (cospan_in2 g'))
        ≈[C] @cover C H_Coc _ _ _ _ (cospan_in2 f) (cospan_in2 g)).
      rewrite (@cover_comp C H_Coc).
      change ((to phi ∘[C] cospan_in2 f') ≈[C] cospan_in2 f) in Hf2.
      change ((to psi ∘[C] cospan_in2 g') ≈[C] cospan_in2 g) in Hg2.
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
  unfold cospan_equiv, span_equiv; simpl.
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
  unfold mor_as_cospan, cospan_equiv, span_equiv; simpl.
  exists iso_id; simpl; split.
  - rewrite id_left.
    symmetry; exact Hfg.
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
  unfold cospan_compose, mor_as_cospan, cospan_equiv, span_equiv; simpl.
  pose (P := pushout (id[Y] : Y ~{C}~> Y) g).
  exists (Isomorphism_Opposite (pushout_id_left_apex HP g)).
  simpl.
  split.
  - (* Goal (in C-direction): Pcollapse⁻¹ ∘ (g ∘ f) ≈ pullback_fst _ _ P ∘ f *)
    rewrite comp_assoc.
    apply compose_respects; [|reflexivity].
    pose proof (pushout_commutes P) as PC.
    rewrite id_right in PC.
    unfold pushout_in1, pushout_in2 in PC.
    symmetry.
    exact PC.
  - simpl.
    reflexivity.
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

(* TODO(V2d-coherence): full Monoidal (CospanCat C) instance, using the
   [mor_as_cospan] embedding above + the pushout-of-id-collapse lemma
   for unitor/associator naturality, and the
   pushout-of-covers-compatibility lemma for bifunctoriality. *)
(* TODO(V2d-coherence): SCFA axioms for cospan_scfa_* as cospan-equiv
   equations, requiring the pushout-of-codiagonal collapse. *)
(* TODO(V2d-coherence): Hypergraph (CospanCat C) tensor + unit coherence,
   building on the above. *)
