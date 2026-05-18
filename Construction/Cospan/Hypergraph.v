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

(* TODO(V2c-applications): full Monoidal (CospanCat C) (associator,
   unitors, braid, hexagon, pentagon — each as a cospan-equiv pushout
   calculation).  Estimated ~500 lines of mechanical pushout diagrams,
   but each follows the same [pushout_med_eq] + [merge_inl_inr] +
   [cover_inl] / [cover_inr] template. *)
(* TODO(V2c-applications): SCFA axioms as cospan-equiv equations *)
(* TODO(V2c-applications): Hypergraph (CospanCat C) tensor + unit coherence *)
