Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Product.Limit.
Require Import Category.Functor.Opposite.
Require Import Category.Functor.Diagonal.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Theory.Equivalence.Colimit.
Require Import Category.Instance.Cat.
Require Import Category.Instance.One.
Require Import Category.Adjunction.Diagonal.Limit.

Generalizable All Variables.

(** * The limit as a functor on the category of all diagrams *)

(* Mac Lane §V.2 Exercise 5 (book p. 115; maclane:V.2:ex5), with the scope
   increment from §IX.7 Exercise 3 (book p. 229; maclane:IX.7:ex3) measured
   and declined below.
   nLab: https://ncatlab.org/nlab/show/limit
         https://ncatlab.org/nlab/show/comma+category

   BACKGROUND.  Beyond its functoriality in the diagram at a fixed shape
   (Adjunction/Diagonal/Limit.v:434 [LimitFunctor], issue #353), the limit
   is functorial in the SHAPE as well.  Mac Lane's "super-comma" category
   has as objects all diagrams (J, F : J ⟶ C) in a fixed target and as
   arrows (J', F') → (J, F) a functor W : J' ⟶ J together with a natural
   transformation F ◯ W ⟹ F'; over a complete target, lim is a functor from
   the OPPOSITE of that category: the limit cone of F restricts along W
   (Structure/Limit/Comparison.v's [cone_reindex]), is pushed along the
   transformation (Theory/Equivalence/Colimit.v:471 [cone_along]) into a
   cone over F', and mediates into lim F'.

   THE DIRECTION OF THE TRANSFORMATION.  The issue defers it to the book;
   Mac Lane's arrows (J', F') → (J, F) carry W : J' ⟶ J with a
   transformation F ◯ W ⟹ F', and [DHom] below is stated in that direction:
   for X → Y, [dtau : ddiag Y ◯ dW ⟹ ddiag X].  It is also the direction
   Construction/Comma.v:131-133 produces for Id[Cat] ↓ Δ(C)
   ([F ◯ W ≈ Id ◯ F'] in Cat's hom setoid).  The reverse direction,
   F' ⟹ F ◯ W, ALSO forms a category under the same setoid recipe (the fess
   audit compiled it), but limits are not functorial on it: with it both
   lim F' and lim F map INTO lim (F ◯ W), so there is no mediator in either
   variance.  An earlier revision of this paragraph said that direction
   "does not compose" and attributed it to the issue; both statements were
   wrong.

   STALE PREMISES, RE-MEASURED.
     - "the limit functor at a fixed shape is #353's obligation": #353
       landed — Adjunction/Diagonal/Limit.v:363 [HasLimitsOfShape], :381
       [lim_obj], :422 [Lim_map], :434 [LimitFunctor], :527 the adjunction
       with the diagonal, :696 [ColimitFunctor]; the docs/INDEX.md bullet
       for that file (:164) already lists "no functoriality in J" as the
       remaining gap — this file.
     - "no category of diagrams, no super-comma, no Cat ↓": true as
       measured (0 hits for `Cat ↓` and `↓ Cat`; no category whose objects
       pair an index category with a diagram — Structure/AbCategory.v:223's
       [AbCatObj] is a sigma over [Category] of another kind), but of the
       issue's four prose citations only
       Instance/Fun/Topos.v:52 and Structure/Cone/Const.v:32 still carry
       the phrase "category of diagrams"; Theory/Adamek.v:64 and
       Structure/Complete.v:76 no longer do.
     - The mediator half the issue does not name already exists:
       Theory/Equivalence/Colimit.v:440 [isalimit_cone], :471 [cone_along]
       (needing only naturality), :487 [limit_induced] with its laws to
       :527, :551 the colimit duals — the object-level shadows of this
       functor.
     - "the comma-category form over Cat is the sub-case where the
       transformation is the identity": false on both halves — see (5).

   WHAT IS DELIVERED (39 constants, every one closed under the global
   context).
     (1) THE CATEGORY OF DIAGRAMS.  [DObj C] (an index category with a
         diagram), [DHom X Y] (a shape functor [dW] with
         [dtau : ddiag Y ◯ dW ⟹ ddiag X]), [DHom_equiv]: a pointwise
         isomorphism of the shape functors satisfying Cat's own
         [Functor_Setoid] clause (Theory/Functor.v:149; Instance/Cat.v:145)
         together with agreement of the transformations THROUGH THE
         ISOMORPHISM'S IMAGE — the dependent-setoid problem (τ's type moves
         with W) is solved by stating the τ clause at the image rather than
         by transport.  [Did] and [Dcomp] are built COMPONENTWISE because
         [◯] is neither strictly unital nor strictly associative (probe
         N1-N4); [Dcomp_respects] is one use of [naturality]; [Diagrams C :
         Category] with all four laws witnessed by [iso_id].  Readbacks
         [Diagrams_obj], [Diagrams_hom] at [eq_refl].
     (2) THE LIMIT FUNCTOR.  Under [L : Complete C]: [dlim], [dlim_is],
         [dlim_cone f := cone_along (dtau f) (cone_reindex (dW f)
         (isalimit_cone (dlim_is Y)))], [dlim_map f := limit_med (dlim_is X)
         (dlim_cone f)] with [dlim_map_commutes] and [dlim_map_unique], and
         [LimDiagrams : (Diagrams C)^op ⟶ C].  Respectfulness closes by
         [limit_leg_coherence]: the limit cone's own coherence absorbs the
         hom-setoid's isomorphism, which is why the Cat-style setoid is the
         right one and no [StrictCat] deviation (Instance/Cat/Limit.v:55-72)
         is needed.  Comparison.v's [reindex_comparison] is NOT the arrow
         part: it targets a separately supplied limit of the reindexed
         diagram and would need a second mediation.
     (3) AT A FIXED SHAPE, THIS IS #353.  [fixed_hom b] reads a
         transformation [b : F ⟹ G] as the arrow (J, G) → (J, F) with the
         identity shape functor; [lim_obj_is_dlim] at [eq_refl] and
         [dlim_map_fixed : dlim_map L (fixed_hom b) ≈ Lim_map b]
         (Adjunction/Diagonal/Limit.v:422, at [Complete_HasLimitsOfShape L J]).
     (4) THE COLIMIT DUAL.  [Cocomplete C] and [Complete (C^op)] are not
         convertible (probe N5) but interderivable because [(F^op)^op] IS
         [F] by conversion: Construction/Product/Limit.v:389's
         [Complete_op_of_Cocomplete] — REUSED, not re-defined; an earlier
         revision of this file re-defined it under another name, which the
         fess audit caught — and the new [cocomplete_of_complete_op],
         round-tripping at [eq_refl].  Then
         [ColimDiagrams (L : Cocomplete C) : Diagrams (C^op) ⟶ C :=
         Opposite_Functor (LimDiagrams …)], read through
         [Opposite (Opposite C) = C].  [Diagrams (C^op)] IS the covariant
         colimit category: an object is [F^op] for [F : K^op ⟶ C], and an
         arrow X → Y is [dW : didx X ⟶ didx Y] with [F_X ⟹ F_Y ◯ dW^op] in
         C.  Readbacks [ColimDiagrams_fobj], [dcolim_is_colimit_apex] at
         [eq_refl].
     (5) THE COMMA FORM.  [CommaDiagrams C := Id[Cat] ↓ Δ(C)]
         (Construction/Comma.v:127; Functor/Diagonal.v's [Diagonal])
         elaborates, also at [Sets] and [Coq] (measured): "Comma is never
         instantiated with Cat" was a fact about the tree, not an
         obstruction.  Its square is a natural ISOMORPHISM (Cat's hom
         setoid), not required to be an identity — the comma form is the
         INVERTIBLE sub-case, not the identity one — and its hom setoid compares
         the functor components only ([CommaDiagrams_equiv] at [eq_refl];
         Comma.v:135-136), so the square is forgotten.
         [comma_diagrams_obj] and [comma_diagrams_arrow] read every comma
         arrow as a [Diagrams] arrow ([dW] at [eq_refl]) — as a FUNCTION
         only: the probe's countermodel in [CommaDiagrams Sets]
         ([p420_f_id ≈ p420_f_negb], squares [id] and [negb], and
         [p420_no_respectful_arrow_part]) shows that no [Proper] assignment
         of arrows can return the square's component on both, so the
         canonical arrow part — the mediator the square determines — is not
         respectful and the comma form cannot carry it; a functor with some
         OTHER arrow part is not excluded.

   UNIVERSES (measured by [About] under [Set Printing Universes] on all 39
   constants).
     - No word-bounded [Set] in any block; no [JMeq], [EqdepFacts] or
       [eq_rect_r] cap anywhere ([prod_rect] caps from the comma's product
       category appear).
     - [Diagrams@{u u0 u1 u2 u3 u4} : Category@{u2 u4 u4} → Category@{u u0 u0}]
       with [u3 < u], [u4 < u], [u3 <= u0], [u4 <= u0]: the object universe
       sits strictly above the index categories' object level [u3] and hom
       level [u4], exactly the shape [Cat] has, and the target's hom level
       IS the index categories' ([Category@{u2 u4 u4}]).  Nothing was
       annotated.
     - [LimDiagrams@{u u0 u1 u2 u3 u4}] over [C : Category@{u u0 u0}]
       carries [u2 <= u0]: the index categories' OBJECT level at or below
       the target's HOM level — the smallness side condition, arriving on
       its own from [Complete]'s quantification (Structure/Complete.v:115).
     - [dlim_map_fixed] and [lim_obj_is_dlim] carry [u0 = u3] and
       [u1 = u4]: [Complete]'s index levels identified with the fixed
       shape's, the identification [HasLimitsOfShape] makes; [fixed_hom],
       whose type does not mention [Complete], carries only [u1 = u4].
     - [DHom] carries [u2 < u0]; [DObj] carries no constraint.

   COUNTS AND CONVENTIONS.
     - 39 constants (28 [def], 4 [prf], 1 [inst], 4 [proj], 2 [rec] in the
       [.glob]), all "Closed under the global context", zero [Axioms:]
       lines, all gated fully qualified.  Two [Defined]
       ([comma_diagrams_arrow], for its [dW] readback; [fixed_hom], for
       [dlim_map_fixed]); thirteen [Qed].
     - Closure 78 files excluding self: Adjunction/Diagonal/Limit.v costs
       26 at the margin (the #353 bridge of (3)), Theory/Equivalence/
       Colimit.v 6, Structure/Limit/Comparison.v 5,
       Construction/Product/Limit.v 4 (the reused bridge), the other
       fifteen [Require]s 0.
     - Test/ProbeDiagrams420.v mirrors the [Require] list (plus
       Instance/Sets.v for the countermodel) and carries 7 refutation
       commands (1 instrument + 6 negatives of two kinds: three conversion,
       three typing), each stripped one at a time in a copy of the whole
       file; the compiled countermodel; readbacks at [eq_refl]; guard
       coverage 37 identifier tokens inside the refutation commands / 27 of
       them also named outside, comments stripped, with ten exhaustive
       exceptions (the keyword, two binder names, the six names the refuted
       declarations would introduce, the absent name); rename-simulated 5/5
       ([Compose], [nat_id], [nat_compose], [Cocomplete] and
       [Complete_op_of_Cocomplete], each renamed throughout a copy) with
       every first break on a guard line.  [make todo] grows by
       those 7 lines only (2202 → 2209), so the issue's "adds no new hits"
       box is not met as written; disclosed.

   NOT DELIVERED.
     - The §IX.7 Exercise 3 increment — the functoriality of lim through the
       limit's expression as an end and the functoriality of ends: the tree
       has neither in the general form.  Structure/End.v carries only
       [Class End] (:35) and [Coend] (:58); no limit-as-end statement exists,
       and the only functoriality of a (co)end in the tree is
       Theory/Coend/Fubini.v:226's [Inner], a concrete coend functor into
       Sets rather than Proposition IX.7.1 (grep over Structure/End.v,
       Structure/Wedge.v and the Theory/Coend directory).
     - A limit functor on the comma form: its canonical arrow part is
       refuted by the countermodel; no other arrow part is attempted.  No
       functor between [CommaDiagrams C] and [Diagrams C] in
       either direction ([comma_diagrams_arrow] is a function on arrows,
       not a setoid morphism).
     - The colimit dual is stated on [Diagrams (C^op)], not on a separately
       built covariant category of C-diagrams with [F' ⟹ F ◯ W] arrows; the
       two coincide up to [K ↦ K^op] on shapes, and no equivalence between
       them is built.
     - At a fixed [W], the sharper natural-transformation form
       [LimitFunctor_J ⟹ LimitFunctor_J' ◯ Induced W]
       (Theory/Kan/Extension.v:131) is not stated.
     - Functoriality of [Diagrams] in the target, and any colimit-side
       counterpart of [dlim_map_fixed] against [Colim_map]. *)

(** ** The category of all diagrams in a fixed target *)

(* An object: an index category together with a diagram of that shape. *)
Record DObj (C : Category) : Type := {
  didx  : Category;
  ddiag : didx ⟶ C
}.

Arguments didx {C} _.
Arguments ddiag {C} _.

(* An arrow X → Y: a functor between the shapes and a transformation from
   the reindexed diagram of Y to the diagram of X.  This is the direction
   in which limits are contravariant: lim (ddiag Y) restricts along [dW]
   and pushes along [dtau] into a cone over [ddiag X]. *)
Record DHom {C : Category} (X Y : DObj C) : Type := {
  dW   : didx X ⟶ didx Y;
  dtau : ddiag Y ◯ dW ⟹ ddiag X
}.

Arguments dW {C X Y} _.
Arguments dtau {C X Y} _.

(* Two arrows are equivalent when their shape functors are naturally
   isomorphic (Cat's own hom setoid, Theory/Functor.v's [Functor_Setoid])
   and their transformations agree through that isomorphism's image. *)
Definition DHom_equiv {C : Category} {X Y : DObj C} (f g : DHom X Y) : Type :=
  { i : ∀ j : didx X, dW f j ≅ dW g j
  & ((∀ (x y : didx X) (h : x ~> y),
        fmap[dW f] h ≈ from (i y) ∘ fmap[dW g] h ∘ to (i x))
     * (∀ j : didx X,
        transform[dtau f] j ≈ transform[dtau g] j ∘ fmap[ddiag Y] (to (i j))))%type }.

#[export] Program Instance DHom_Setoid {C : Category} {X Y : DObj C} :
  Setoid (DHom X Y) := {| equiv := DHom_equiv |}.
Next Obligation.
  constructor.
  - intro f.
    exists (fun j => iso_id).
    split; intros; simpl.
    + now rewrite id_left, id_right.
    + now rewrite fmap_id, id_right.
  - intros f g [i [Hm Ht]].
    exists (fun j => iso_sym (i j)).
    split; intros; simpl.
    + rewrite Hm.
      rewrite <- !comp_assoc.
      rewrite iso_to_from, id_right.
      rewrite comp_assoc, iso_to_from, id_left.
      reflexivity.
    + rewrite Ht.
      rewrite <- comp_assoc.
      rewrite <- (@fmap_comp _ _ (ddiag Y) _ _ _ (to (i j)) (from (i j))).
      rewrite (iso_to_from (i j)).
      rewrite fmap_id, id_right.
      reflexivity.
  - intros f g h [i [Hmi Hti]] [k [Hmk Htk]].
    exists (fun j => iso_compose (k j) (i j)).
    split; intros; simpl.
    + rewrite Hmi, Hmk.
      rewrite <- !comp_assoc.
      reflexivity.
    + rewrite Hti, Htk.
      rewrite <- comp_assoc.
      rewrite <- (@fmap_comp _ _ (ddiag Y) _ _ _ (to (k j)) (to (i j))).
      reflexivity.
Qed.

(* Identity and composition are built componentwise: [◯] is neither
   strictly unital nor strictly associative, so [nat_id] lands at
   [ddiag X ◯ Id ⟹ ddiag X ◯ Id] and a whiskered composite at the wrong
   bracketing (the probe pins both). *)
Program Definition Did {C : Category} (X : DObj C) : DHom X X := {|
  dW := Id[didx X];
  dtau := {| transform := fun j => id[ddiag X j] |}
|}.

Program Definition Dcomp {C : Category} {X Y Z : DObj C}
  (f : DHom Y Z) (g : DHom X Y) : DHom X Z := {|
  dW := dW f ◯ dW g;
  dtau := {| transform :=
               fun j => transform[dtau g] j ∘ transform[dtau f] (dW g j) |}
|}.
Next Obligation.
  rewrite comp_assoc.
  rewrite (naturality (dtau g) x y f0).
  change (@fmap _ _ (ddiag Y ◯ dW g) x y f0)
    with (fmap[ddiag Y] (fmap[dW g] f0)).
  rewrite <- !comp_assoc.
  rewrite (naturality (dtau f) (dW g x) (dW g y) (fmap[dW g] f0)).
  change (@fmap _ _ (ddiag Z ◯ dW f) (dW g x) (dW g y) (fmap[dW g] f0))
    with (fmap[ddiag Z] (fmap[dW f] (fmap[dW g] f0))).
  reflexivity.
Qed.
Next Obligation.
  symmetry.
  rewrite comp_assoc.
  rewrite (naturality (dtau g) x y f0).
  change (@fmap _ _ (ddiag Y ◯ dW g) x y f0)
    with (fmap[ddiag Y] (fmap[dW g] f0)).
  rewrite <- !comp_assoc.
  rewrite (naturality (dtau f) (dW g x) (dW g y) (fmap[dW g] f0)).
  change (@fmap _ _ (ddiag Z ◯ dW f) (dW g x) (dW g y) (fmap[dW g] f0))
    with (fmap[ddiag Z] (fmap[dW f] (fmap[dW g] f0))).
  reflexivity.
Qed.

Lemma Dcomp_respects {C : Category} {X Y Z : DObj C}
  (f f' : DHom Y Z) (Ef : DHom_equiv f f')
  (g g' : DHom X Y) (Eg : DHom_equiv g g') :
  DHom_equiv (Dcomp f g) (Dcomp f' g').
Proof.
  destruct Ef as [i [Hmi Hti]].
  destruct Eg as [k [Hmk Htk]].
  unshelve eexists.
  - intro j.
    exact (iso_compose (@fobj_iso _ _ (dW f') _ _ (k j)) (i (dW g j))).
  - split.
    + intros x y h; simpl.
      rewrite Hmi.
      rewrite Hmk.
      rewrite !fmap_comp.
      rewrite <- !comp_assoc.
      reflexivity.
    + intro j; simpl.
      rewrite Htk.
      rewrite Hti.
      rewrite <- !comp_assoc.
      rewrite (comp_assoc (fmap[ddiag Y] (to (k j)))
                          (transform[dtau f'] (dW g j))
                          (fmap[ddiag Z] (to (i (dW g j))))).
      rewrite (naturality (dtau f') (dW g j) (dW g' j) (to (k j))).
      change (@fmap _ _ (ddiag Z ◯ dW f') (dW g j) (dW g' j) (to (k j)))
        with (fmap[ddiag Z] (fmap[dW f'] (to (k j)))).
      rewrite <- !comp_assoc.
      rewrite <- (@fmap_comp _ _ (ddiag Z) _ _ _
                    (fmap[dW f'] (to (k j))) (to (i (dW g j)))).
      reflexivity.
Qed.

Program Definition Diagrams (C : Category) : Category := {|
  obj := DObj C;
  hom := @DHom C;
  homset := @DHom_Setoid C;
  id := @Did C;
  compose := @Dcomp C
|}.
Next Obligation.
  intros f f' Ef g g' Eg.
  exact (Dcomp_respects f f' Ef g g' Eg).
Qed.
Next Obligation.
  exists (fun j => iso_id).
  split; intros; simpl.
  - now rewrite id_left, id_right.
  - now rewrite fmap_id, !id_right.
Qed.
Next Obligation.
  exists (fun j => iso_id).
  split; intros; simpl.
  - now rewrite id_left, id_right.
  - now rewrite fmap_id, id_left, id_right.
Qed.
Next Obligation.
  exists (fun j => iso_id).
  split; intros; simpl.
  - now rewrite id_left, id_right.
  - now rewrite fmap_id, id_right, comp_assoc.
Qed.
Next Obligation.
  exists (fun j => iso_id).
  split; intros; simpl.
  - now rewrite id_left, id_right.
  - now rewrite fmap_id, id_right, comp_assoc.
Qed.

Example Diagrams_obj (C : Category) : obj[Diagrams C] = DObj C := eq_refl.

Example Diagrams_hom (C : Category) (X Y : Diagrams C) :
  (X ~{Diagrams C}~> Y) = DHom X Y := eq_refl.

(** ** The limit functor on the opposite of the category of diagrams *)

Section LimDiagrams.

Context {C : Category}.
Context (L : @Complete C).

Definition dlim (X : DObj C) : C :=
  vertex_obj[@limit_cone (didx X) C (ddiag X) (L (didx X) (ddiag X))].

Definition dlim_is (X : DObj C) : IsALimit (ddiag X) (dlim X) :=
  limit_is_alimit (L (didx X) (ddiag X)).

(* The cone over [ddiag X] with apex [dlim Y]: the limit cone of [ddiag Y]
   restricted along [dW f] (Comparison.v's [cone_reindex]) and pushed along
   [dtau f] (Theory/Equivalence/Colimit.v's [cone_along]). *)
Definition dlim_cone {X Y : DObj C} (f : DHom X Y) : Cone (ddiag X) :=
  cone_along (dtau f)
    (cone_reindex (dW f) (isalimit_cone (dlim_is Y))).

Example dlim_cone_apex {X Y : DObj C} (f : DHom X Y) :
  vertex_obj[dlim_cone f] = dlim Y := eq_refl.

(* The arrow part: the unique mediator into the limit of [ddiag X]. *)
Definition dlim_map {X Y : DObj C} (f : DHom X Y) : dlim Y ~{C}~> dlim X :=
  limit_med (dlim_is X) (dlim_cone f).

Lemma dlim_map_commutes {X Y : DObj C} (f : DHom X Y) (j : didx X) :
  limit_leg (dlim_is X) j ∘ dlim_map f
    ≈ transform[dtau f] j ∘ limit_leg (dlim_is Y) (dW f j).
Proof. exact (limit_med_commutes (dlim_is X) (dlim_cone f) j). Qed.

Lemma dlim_map_unique {X Y : DObj C} (f : DHom X Y)
  (v : dlim Y ~{C}~> dlim X) :
  (∀ j : didx X, limit_leg (dlim_is X) j ∘ v
                 ≈ transform[dtau f] j ∘ limit_leg (dlim_is Y) (dW f j)) →
  dlim_map f ≈ v.
Proof. intro Hv. exact (limit_med_unique (dlim_is X) (dlim_cone f) v Hv). Qed.

(* Mac Lane V.2 Exercise 5: over a complete target, taking limits is a
   functor on the opposite of the category of diagrams. *)
Program Definition LimDiagrams : (Diagrams C)^op ⟶ C := {|
  fobj := dlim;
  fmap := fun X Y f => dlim_map f
|}.
Next Obligation.
  intros f g [i [Hm Ht]].
  symmetry.
  apply dlim_map_unique; intro j.
  rewrite dlim_map_commutes.
  rewrite Ht.
  rewrite <- comp_assoc.
  rewrite (limit_leg_coherence (dlim_is x) (to (i j))).
  reflexivity.
Qed.
Next Obligation.
  apply dlim_map_unique; intro j.
  simpl.
  now rewrite id_left, id_right.
Qed.
Next Obligation.
  apply dlim_map_unique; intro j.
  simpl.
  rewrite comp_assoc.
  rewrite (dlim_map_commutes f j).
  rewrite <- comp_assoc.
  rewrite (dlim_map_commutes g (dW f j)).
  rewrite comp_assoc.
  reflexivity.
Qed.

Example LimDiagrams_fobj (X : DObj C) : LimDiagrams X = dlim X := eq_refl.

Example LimDiagrams_fmap {X Y : DObj C} (f : DHom X Y) :
  fmap[LimDiagrams] f = dlim_map f := eq_refl.

End LimDiagrams.

(** ** The colimit dual *)

(* [Cocomplete C] and [Complete (C^op)] are not convertible (the probe pins
   the [eq_refl]), but they are interderivable because [(F^op)^op] IS [F]
   by conversion: Construction/Product/Limit.v:389's
   [Complete_op_of_Cocomplete] goes one way, and the converse below the
   other; the two round-trip at [eq_refl]. *)
Definition cocomplete_of_complete_op {C : Category} (L : @Complete (Opposite C)) :
  @Cocomplete C :=
  fun D F => L (Opposite D) (Opposite_Functor F).

Example cocomplete_roundtrip {C : Category} (L : @Cocomplete C) :
  cocomplete_of_complete_op (Complete_op_of_Cocomplete L) = L := eq_refl.

Example complete_op_roundtrip {C : Category} (L : @Complete (Opposite C)) :
  Complete_op_of_Cocomplete (cocomplete_of_complete_op L) = L := eq_refl.

(* An object of [Diagrams (C^op)] is a diagram [G : K ⟶ C^op], i.e. [F^op] for
   [F : K^op ⟶ C]; an arrow X → Y is a shape functor [dW] with
   [ddiag Y ◯ dW ⟹ ddiag X] in [C^op], i.e. [F_X ⟹ F_Y ◯ dW^op] in [C] —
   exactly the arrows along which colimits are COVARIANT.  So the colimit
   functor is the limit functor of the opposite target, read back through
   [Opposite (Opposite C) = C]. *)
Definition ColimDiagrams {C : Category} (L : @Cocomplete C) :
  Diagrams (Opposite C) ⟶ C :=
  Opposite_Functor (LimDiagrams (Complete_op_of_Cocomplete L)).

Definition dcolim {C : Category} (L : @Cocomplete C) (X : DObj (Opposite C)) : C :=
  dlim (Complete_op_of_Cocomplete L) X.

Example ColimDiagrams_fobj {C : Category} (L : @Cocomplete C) (X : DObj (Opposite C)) :
  ColimDiagrams L X = dcolim L X := eq_refl.

(* At a diagram given as [F^op], the object part is the colimit apex the
   hypothesis chooses for [F]. *)
Example dcolim_is_colimit_apex {C : Category} (L : @Cocomplete C)
  {J : Category} (F : J ⟶ C) :
  dcolim L {| didx := Opposite J; ddiag := Opposite_Functor F |}
  = vertex_obj[@limit_cone (Opposite J) (Opposite C) (Opposite_Functor F) (L J F)]
  := eq_refl.

(** ** The comma form over Cat, and why it cannot carry the arrow part *)

(* The issue names the comma category [Id[Cat] ↓ Δ(C)] as "the sub-case where
   the transformation is the identity".  Its objects are the same pairs; its
   arrows pair a shape functor with a commuting square, which in Cat's hom
   setoid is a natural ISOMORPHISM [F' ◯ W ≅ F], never an identity; and its
   hom setoid compares the functor components only (Construction/Comma.v's
   [homset]), so the square is forgotten.  The probe carries the concrete
   countermodel: two comma arrows equivalent in this setoid whose squares
   would demand different mediators. *)
Definition CommaDiagrams (C : Category) : Category :=
  @Comma Cat 1 Cat Id[Cat] (@Diagonal Cat 1 C).

Example CommaDiagrams_equiv (C : Category) (x y : CommaDiagrams C)
  (f g : x ~{CommaDiagrams C}~> y) :
  (f ≈ g) = ((fst `1 f ≈ fst `1 g) * (snd `1 f ≈ snd `1 g))%type := eq_refl.

(* Every comma arrow does give a [Diagrams] arrow — its square, read as the
   transformation — but only as a FUNCTION on arrows: the assignment depends on
   the square, which the comma setoid discards, so it is not a morphism of
   setoids (the probe's countermodel exhibits two equivalent comma arrows with
   different transformations). *)
Definition comma_diagrams_obj {C : Category} (x : CommaDiagrams C) : DObj C :=
  {| didx := fst `1 x; ddiag := `2 x |}.

Definition comma_diagrams_arrow {C : Category} {x y : CommaDiagrams C}
  (f : x ~{CommaDiagrams C}~> y) :
  DHom (comma_diagrams_obj x) (comma_diagrams_obj y).
Proof.
  unshelve refine (@Build_DHom C (comma_diagrams_obj x) (comma_diagrams_obj y) (fst `1 f)
                     (@Build_Transform _ _ (`2 y ◯ fst `1 f) (`2 x)
                        (fun j => to (`1 (`2 f) j)) _ _)).
  - intros a b h; simpl in *.
    pose proof (`2 (`2 f) a b h) as Hn; simpl in Hn.
    rewrite Hn.
    rewrite !comp_assoc.
    rewrite iso_to_from, id_left.
    reflexivity.
  - intros a b h; simpl in *.
    pose proof (`2 (`2 f) a b h) as Hn; simpl in Hn.
    rewrite Hn.
    rewrite !comp_assoc.
    rewrite iso_to_from, id_left.
    reflexivity.
Defined.

Example comma_diagrams_arrow_W {C : Category} {x y : CommaDiagrams C}
  (f : x ~{CommaDiagrams C}~> y) :
  dW (comma_diagrams_arrow f) = fst `1 f := eq_refl.

(** ** At a fixed shape, the arrow part is #353's [Lim_map] *)

Section FixedShape.

Context {C : Category} (L : @Complete C) {J : Category}.

(* A natural transformation [b : F ⟹ G] as an arrow (J, G) → (J, F) of
   [Diagrams C] with the identity shape functor. *)
Definition fixed_hom {F G : J ⟶ C} (b : F ⟹ G) :
  DHom {| didx := J; ddiag := G |} {| didx := J; ddiag := F |}.
Proof.
  unshelve refine (@Build_DHom C {| didx := J; ddiag := G |} {| didx := J; ddiag := F |}
                     Id[J] (@Build_Transform _ _ (F ◯ Id[J]) G (fun j => transform[b] j) _ _)).
  - intros; simpl. apply naturality.
  - intros; simpl. apply naturality_sym.
Defined.

Example lim_obj_is_dlim (F : J ⟶ C) :
  @lim_obj J C (Complete_HasLimitsOfShape L J) F = dlim L {| didx := J; ddiag := F |}
  := eq_refl.

(* Adjunction/Diagonal/Limit.v's fixed-shape limit functor is the restriction
   of [LimDiagrams] to the identity shape functor. *)
Lemma dlim_map_fixed {F G : J ⟶ C} (b : F ⟹ G) :
  dlim_map L (fixed_hom b) ≈ @Lim_map J C (Complete_HasLimitsOfShape L J) F G b.
Proof.
  apply dlim_map_unique; intro j.
  exact (@Lim_map_commutes J C (Complete_HasLimitsOfShape L J) F G b j).
Qed.

End FixedShape.
