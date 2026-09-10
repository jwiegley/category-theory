Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Terminal.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Image.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Pullback.

Generalizable All Variables.

(** * Coreflexive pairs, coreflexive equalizers, and Manes' criterion *)

(* Mac Lane §V.2 Exercise 1 (book p. 114; maclane:V.2:ex1).
   nLab: https://ncatlab.org/nlab/show/equalizer
         https://ncatlab.org/nlab/show/complete+category

   BACKGROUND.  Theorem 1 of §V.2 (Structure/Limit/FromProducts.v, #416)
   builds the limit of F : J ⟶ C as the equalizer of two canonical maps
   s, t : ∏_{x} F x ⇉ ∏_{f} F (cod f).  Manes' sharpening (part (a)) observes
   that this pair always has a COMMON LEFT INVERSE — the map back into the
   object product whose component at x is the arrow product's projection at
   the identity arrow of x — so a category with small products needs
   equalizers only of such "coreflexive" pairs to be complete.  Part (b) is
   the elementary characterisation, in Sets, of the pairs with a common RIGHT
   inverse: those whose induced map into the square of the codomain has an
   image containing the diagonal.  Note the two halves speak of two
   different notions: (a) is about coreflexive pairs (a common retraction),
   (b) about reflexive ones (a common section, Structure/Coequalizer/
   Reflexive.v's [ReflexivePair]).

   STALE PREMISES, RE-MEASURED.
     - "the base theorem the exercise refines is itself absent": it landed
       as Structure/Limit/FromProducts.v (#416; docs/INDEX.md:150) — the
       arrow index [ArrowIx] (:286) with [mk_arrow] (:292), the generating
       closure [Gen] (:316) with [gen_id] (:318) and [Generates] (:326),
       [ArrowIx_Generates] (:339), the elementary core [pe_cone] (:400) and
       [pe_limiting], the pair [pe_s]/[pe_t] (:494/:498) with their component
       equations (:502/:509), [limit_of_products_equalizer] (:537) and
       [Complete_from_products_equalizers] (:555).  The core consumes an
       ELEMENTARY [IsEqualizer] (:376), never the class — the decisive fact
       here: Manes' criterion needs no [HasEqualizers] anywhere.
     - "coreflexive returns 0 hits": Structure/Topos/Monadic.v:595 proves
       [coreflexive_equalizer_pullback] for a pair with a common retraction
       (a step of Paré's theorem; Test/ProbeToposColimits405.v:138 guards
       it).  The NOTION is in the tree and load-bearing; what was absent is
       the packaging — no record, no class.  [common left inverse] is indeed
       unused, but Theory/Morphisms.v:56's [Section] is the split-mono
       record with exactly that field, and a coreflexive pair is two such
       splittings sharing one retraction.
     - "reflexive pairs appear ten times across Structure/Coequalizer/
       Reflexive.v and Monad/Monadicity/*": the token [ReflexivePair] occurs
       in four files (Reflexive.v, Monad/Lifting.v, Monad/Monadicity/
       BeckObjects.v, Monad/Monadicity/Crude.v), and with
       [HasReflexiveCoequalizers] fourteen lines sit outside those two
       places (Theory/Lawvere/Monad.v, Instance/Sets/Coequalizer.v,
       Structure/Topos/Monadic.v, Structure/Topos/Colimits.v, the 405 probe).

   WHAT IS DELIVERED (45 constants, every one closed under the global
   context).
     (1) THE NOTION.  [CoreflexivePair f g] (a common retraction with its
         two laws), [HasCoreflexiveEqualizers C] (an elementary equalizer
         for every coreflexive pair), [common_retraction_coreflexive], the
         [#[export] Instance] [HasEqualizers_HasCoreflexiveEqualizers], and
         [functor_preserves_coreflexive] — mirroring Reflexive.v:40, :54,
         :64, :75 and :86 line for line.
     (2) THE DUAL, MEASURED.  A common left inverse in C is a common section
         in C^op field for field, so the pair repackages by [:=] both ways
         ([CoreflexivePair_of_op], [op_ReflexivePair_of_Coreflexive]) with
         both round trips at [eq_refl]; the record TYPES are not the same
         type, nor are the classes (probe N1, N2), whose bridges
         ([HasCoreflexiveEqualizers_of_op],
         [op_HasReflexiveCoequalizers_of_Coreflexive]) perform the
         destruct-and-repackage of Structure/Pullback/Reduction.v:675/:681/
         :697 because the existential bodies are Structure/Equalizer/Fork.v:52's
         [IsEqualizer] and Structure/Coequalizer.v:52's [IsCoequalizer].
         The notion is therefore declared on its own — an alias of
         [ReflexivePair] at [C^op] would force the [y x] argument order and
         [∘[C^op]] on every user and be invisible to the grep that already
         misled the issue — and bridged.
     (3) MAC LANE'S HINT AS A LEMMA.  The identity arrow at x is an index of
         the FULL arrow family with codomain x on the nose ([id_index_cod],
         [id_index_dom], [id_index_arr] at [eq_refl]); [pe_retract] is the
         map into the object product with components the arrow product's
         projections at the identities; [pe_retract_s] and [pe_retract_t]
         are three lines each by FromProducts.v:265's [pe_iprod_ext];
         [pe_coreflexive : CoreflexivePair (pe_s HP F) (pe_t HP F)].  The
         generating-family variant is NOT stated: [Gen]'s [gen_id] closes
         the generated arrows under identities but puts no identity into the
         index TYPE, so the projection at an abstract family is refused
         (probe N4; a transported variant is formable and was measured, at
         the price of a transport).
     (4) MANES' CRITERION.  [mc_equalizer], [mc_apex], [mc_incl],
         [mc_IsEqualizer], [mc_cone], [mc_limiting], [mc_limit], and
         [Complete_from_coreflexive_equalizers : HasIndexedProducts C →
         HasCoreflexiveEqualizers C → Complete C] — FromProducts.v's core fed
         the coreflexive equalizer in place of an arbitrary one; Theorem 2's
         explicit description reads back at [eq_refl] ([mc_limit_apex],
         [mc_limit_leg]) exactly as in FromProducts.v:542-549.
     (5) PART (b), THE CATEGORICAL HALF.  In any cartesian category a common
         section IS a factorization of the diagonal [id △ id] through
         [f △ g]: [fork_diagonal_of_reflexive], [reflexive_of_fork_diagonal],
         and the packaged [ReflexivePair_iff_diagonal_factors] (Type-valued
         ↔, empty constraint block).
     (6) PART (b) IN SETS.  [diagonal_in_image f g := ∀ b, ∃ a, (f a ≈ b) *
         (g a ≈ b)]; [diagonal_in_image_of_reflexive] is unconditional; the
         converse [reflexive_of_diagonal_in_image] takes a PROPERNESS
         hypothesis on the chosen witnesses, because [∃] is [sigT] — the
         choice function is present — but a Sets morphism also needs
         [proper_morphism] (probe N5; [diagonal_section]).  The morphism-
         level reading through Instance/Sets/Image.v ([diagonal_through_image]:
         the diagonal factors through [Sets_Image_mono (f △ g)]) is
         delivered in the unconditional direction only: [Sets_Image]'s
         setoid (:69) compares codomain components, so the stored preimage
         is not a Sets morphism and the reverse would split the epi leg — a
         choice principle, neither derived nor refuted here.
     (7) NON-VACUITY, AND ITS LIMIT.  [Sets_HasCoreflexiveEqualizers] and
         [Sets_Complete_via_Manes : Complete Sets] compile closed — but the
         only route to the hypothesis in the tree is the STRONGER
         [HasEqualizers Sets] (Reduction.v:654 from [Sets_HasPullbacks]).
         No category in the tree is known to have coreflexive equalizers
         without all equalizers, so the criterion is instantiated only
         where Theorem 1's hypothesis already holds; nothing here separates
         it from [Complete_from_products_equalizers].

   UNIVERSES (measured by [About] under [Set Printing Universes] on all 45
   constants).
     - No word-bounded [Set] in any block; no [JMeq], [EqdepFacts] or
       [eq_rect_r] cap.
     - [CoreflexivePair@{u u0}], [HasCoreflexiveEqualizers@{u u0}],
       [HasCoreflexiveEqualizers_of_op@{u u0}] and
       [ReflexivePair_iff_diagonal_factors@{u u0}] carry EMPTY constraint
       blocks.  [Complete_from_coreflexive_equalizers@{u u0 u1} :
       ∀ {C : Category@{u u0 u0}}, HasIndexedProducts C →
       HasCoreflexiveEqualizers C → Complete@{u0 u0 u0 u}] carries bounds
       only, the same shape as [Complete_from_products_equalizers@{u u0 u1}].
     - Two inherited identifications: [mc_cone] carries [u = u3] and
       [u2 = u4] (FromProducts.v's [Core] section, where the products'
       levels meet the limit's), and the six Sets constants carry
       [u = u0 = u1 = u2] with [u < u3] — the carrier and proof universes of
       the two setoids identified, the standard Sets discipline.
       [Sets_Complete_via_Manes@{u u0} : Complete@{u u u u0}] with [u < u0]
       is the universe shape of Instance/Sets/Complete.v:73's
       [Sets_Complete].

   COUNTS AND CONVENTIONS.
     - 45 constants (31 [def], 7 [prf], 1 [inst], 4 [proj], 2 [rec] in the
       [.glob]), all "Closed under the global context", zero [Axioms:]
       lines, all gated fully qualified.  Seven [Defined]: one is
       load-bearing by flipping alone to [Qed] ([diagonal_section], whose
       body [reflexive_of_diagonal_in_image] reduces); the other six
       ([common_retraction_coreflexive], [functor_preserves_coreflexive], the
       two class bridges, [reflexive_of_diagonal_in_image],
       [diagonal_through_image]) flip freely and are kept [Defined] by the
       data convention.  Five [Qed].
     - Closure 50 files excluding self: Instance/Sets/Image.v and
       Instance/Sets/Products.v cost 4 each at the margin,
       Instance/Sets/Pullback.v, Structure/Limit/FromProducts.v and
       Structure/Coequalizer/Reflexive.v 1 each, the other twenty [Require]s
       0.  (Forty-one Structure/ files already require Instance/Sets; the
       Sets half sits here rather than in a second file for that reason.)
     - Test/ProbeCoreflexive421.v mirrors the [Require] list and carries 6
       refutation commands (1 instrument + 5 negatives of two kinds: three
       conversion, two typing), each stripped one at a time in a copy of the
       whole file, plus the positive TRAP that an implicit [idx_cod] makes
       the refused ascription succeed on a different product; readbacks at
       [eq_refl]; guard coverage 38 identifier tokens inside the refutations /
       31 also named outside, comments stripped, with seven exhaustive
       exceptions (the keyword, the five names the refuted declarations would
       introduce, the absent name); rename-simulated 5/5 ([CoreflexivePair],
       [HasCoreflexiveEqualizers], [HasReflexiveCoequalizers], [pe_gen_proj],
       [diagonal_in_image], each renamed throughout a copy) with every first
       break on a positive line.  [make todo] grows by those 6 lines only
       (2202 → 2208), so the issue's "adds no new hits" box is not met as
       written; disclosed.

   NOT DELIVERED.
     - A category with coreflexive equalizers but not all equalizers: none
       is built, so the criterion's strict gain over Theorem 1 has no
       witness in the tree (docs/INHABITATION.md should record it).
     - The generating-family form of [pe_coreflexive] (transport needed,
       measured formable, not stated).
     - The unconditional Sets converse of part (b), and the reverse of
       [diagonal_through_image]: a choice principle, not refuted.
     - Any relocation of Structure/Topos/Monadic.v:595's
       [coreflexive_equalizer_pullback] onto the new record: it stays where
       it is (surfaced in the PR, not settled).
     - No edit to Structure/Coequalizer/Reflexive.v, Structure/Limit/
       FromProducts.v or Instance/Sets/Image.v. *)

(** ** Coreflexive pairs *)

(* The equational data: one map that retracts both f and g.  A coreflexive
   pair is two split monomorphisms (Theory/Morphisms.v's [Section]) sharing
   one retraction. *)
Record CoreflexivePair {C : Category} {x y : C} (f g : x ~> y) := {
  corefl_retract   : y ~> x;                    (* the common retraction *)
  corefl_retract_f : corefl_retract ∘ f ≈ id;   (* it retracts f *)
  corefl_retract_g : corefl_retract ∘ g ≈ id    (* and g *)
}.

Arguments corefl_retract   {_ _ _ _ _} _.
Arguments corefl_retract_f {_ _ _ _ _} _.
Arguments corefl_retract_g {_ _ _ _ _} _.

(* A category has coreflexive equalizers when every coreflexive pair
   carries an elementary equalizer (Structure/Equalizer/Fork.v's
   [IsEqualizer]).  Compare [HasEqualizers], which asks the same of every
   parallel pair, and Structure/Coequalizer/Reflexive.v's
   [HasReflexiveCoequalizers], the dual. *)
Class HasCoreflexiveEqualizers (C : Category) := {
  coreflexive_eq {x y : C} (f g : x ~> y) :
    CoreflexivePair f g → ∃ (q : C) (e : q ~> x), IsEqualizer f g q e
}.

Lemma common_retraction_coreflexive {C : Category} {x y : C} (f g : x ~> y)
  (r : y ~> x) (Hf : r ∘ f ≈ id) (Hg : r ∘ g ≈ id) : CoreflexivePair f g.
Proof.
  exact {| corefl_retract   := r
         ; corefl_retract_f := Hf
         ; corefl_retract_g := Hg |}.
Defined.

(* Every category with equalizers has coreflexive ones. *)
#[export] Instance HasEqualizers_HasCoreflexiveEqualizers
  {C : Category} `{H : @HasEqualizers C} : HasCoreflexiveEqualizers C := {|
  coreflexive_eq := fun x y f g _ => @equalizer C H x y f g
|}.

(* Two equations with no quantification over the ambient category, so
   arbitrary functors preserve coreflexivity — as they do reflexivity
   (Structure/Coequalizer/Reflexive.v's [functor_preserves_reflexive]). *)
Theorem functor_preserves_coreflexive {C D : Category} (F : C ⟶ D)
  {x y : C} (f g : x ~> y) :
  CoreflexivePair f g → CoreflexivePair (fmap[F] f) (fmap[F] g).
Proof.
  intros R.
  unshelve refine {| corefl_retract := fmap[F] (corefl_retract R) |}.
  - rewrite <- fmap_comp, (corefl_retract_f R); apply fmap_id.
  - rewrite <- fmap_comp, (corefl_retract_g R); apply fmap_id.
Defined.

(** ** The dual reading: a coreflexive pair in C is a reflexive pair in C^op *)

(* The FIELD types convert — a common left inverse in C is literally a
   common section in C^op — so the pair repackages by [:=] in both
   directions and round-trips at [eq_refl].  The record TYPES are not the
   same type, nor are the classes (the probe pins both), so the notion is
   declared on its own and bridged. *)
Definition CoreflexivePair_of_op {C : Category} {x y : C} {f g : x ~> y}
  (R : @ReflexivePair (C^op) y x f g) : CoreflexivePair f g :=
  @Build_CoreflexivePair C x y f g
    (refl_section R) (refl_section_f R) (refl_section_g R).

Definition op_ReflexivePair_of_Coreflexive {C : Category} {x y : C}
  {f g : x ~> y} (R : CoreflexivePair f g) : @ReflexivePair (C^op) y x f g :=
  @Build_ReflexivePair (C^op) y x f g
    (corefl_retract R) (corefl_retract_f R) (corefl_retract_g R).

Example corefl_op_round {C : Category} {x y : C} {f g : x ~> y}
  (R : CoreflexivePair f g) :
  CoreflexivePair_of_op (op_ReflexivePair_of_Coreflexive R) = R := eq_refl.

Example op_corefl_round {C : Category} {x y : C} {f g : x ~> y}
  (R : @ReflexivePair (C^op) y x f g) :
  op_ReflexivePair_of_Coreflexive (CoreflexivePair_of_op R) = R := eq_refl.

(* The classes need the destruct-and-repackage Structure/Pullback/
   Reduction.v performs for [HasEqualizers_op_of_HasCoequalizers]: the
   existential body is [IsCoequalizer] on one side and [IsEqualizer] on
   the other. *)
Definition HasCoreflexiveEqualizers_of_op {C : Category}
  (H : HasReflexiveCoequalizers (C^op)) : HasCoreflexiveEqualizers C.
Proof.
  constructor; intros x y f g R.
  destruct (@reflexive_coeq (C^op) H y x f g
              (op_ReflexivePair_of_Coreflexive R)) as [q [e Eq]].
  exists q, e.
  exact (IsEqualizer_op_of_IsCoequalizer Eq).
Defined.

Definition op_HasReflexiveCoequalizers_of_Coreflexive {C : Category}
  (H : HasCoreflexiveEqualizers C) : HasReflexiveCoequalizers (C^op).
Proof.
  constructor; intros x y f g R.
  destruct (@coreflexive_eq C H y x f g (CoreflexivePair_of_op R))
    as [q [e Eq]].
  exists q, e.
  exact (@IsCoequalizer_of_IsEqualizer_op (C^op) x y f g q e Eq).
Defined.

(** ** Mac Lane's pair is coreflexive *)

Section Manes.

Context {C : Category} (HP : HasIndexedProducts C).
Context {J : Category} (F : J ⟶ C).

(* The identity arrow at x is an index of the FULL arrow family of
   Structure/Limit/FromProducts.v, and its codomain is x on the nose. *)
Example id_index_cod (x : J) : aix_cod (mk_arrow (@id J x)) = x := eq_refl.
Example id_index_dom (x : J) : aix_dom (mk_arrow (@id J x)) = x := eq_refl.
Example id_index_arr (x : J) : aix_arr (mk_arrow (@id J x)) = @id J x := eq_refl.

(* Mac Lane's candidate retraction: the map into the object product whose
   component at x is the arrow product's projection at the identity of x. *)
Definition pe_retract : pe_arrow_product HP F ~> pe_obj_product HP F :=
  unique_obj (iprod_desc (pe_obj_product_ump HP F)
    (fun x : J => pe_arrow_proj HP F (mk_arrow (@id J x)))).

Lemma pe_retract_proj (x : J) :
  pe_obj_proj HP F x ∘ pe_retract ≈ pe_arrow_proj HP F (mk_arrow (@id J x)).
Proof.
  exact (unique_property (iprod_desc (pe_obj_product_ump HP F)
    (fun x : J => pe_arrow_proj HP F (mk_arrow (@id J x)))) x).
Qed.

Lemma pe_retract_s : pe_retract ∘ pe_s HP F ≈ id.
Proof.
  apply (pe_iprod_ext (pe_obj_product_ump HP F)); intro x.
  rewrite comp_assoc, pe_retract_proj.
  rewrite (pe_s_proj HP F (mk_arrow (@id J x))).
  rewrite id_right.
  reflexivity.
Qed.

Lemma pe_retract_t : pe_retract ∘ pe_t HP F ≈ id.
Proof.
  apply (pe_iprod_ext (pe_obj_product_ump HP F)); intro x.
  rewrite comp_assoc, pe_retract_proj.
  rewrite (pe_t_proj HP F (mk_arrow (@id J x))).
  simpl.
  rewrite fmap_id, id_left, id_right.
  reflexivity.
Qed.

(* Mac Lane's hint, as a proved lemma. *)
Definition pe_coreflexive : CoreflexivePair (pe_s HP F) (pe_t HP F) :=
  common_retraction_coreflexive _ _ pe_retract pe_retract_s pe_retract_t.

(** ** Manes' criterion *)

Context (HE : HasCoreflexiveEqualizers C).

Definition mc_equalizer :=
  coreflexive_eq (pe_s HP F) (pe_t HP F) pe_coreflexive.

Definition mc_apex : C := `1 mc_equalizer.

Definition mc_incl : mc_apex ~> pe_obj_product HP F := `1 (`2 mc_equalizer).

Definition mc_IsEqualizer : IsEqualizer (pe_s HP F) (pe_t HP F) mc_apex mc_incl
  := `2 (`2 mc_equalizer).

(* The limit is FromProducts.v's construction fed the coreflexive
   equalizer in place of an arbitrary one; its core consumes the
   elementary [IsEqualizer], never the class. *)
Definition mc_cone : Cone F :=
  pe_cone F (pe_obj_proj HP F) (pe_obj_product_ump HP F) ArrowIx_Generates
    (pe_arrow_proj HP F) (pe_arrow_product_ump HP F)
    (pe_s HP F) (pe_t HP F) (pe_s_proj HP F) (pe_t_proj HP F)
    mc_incl mc_IsEqualizer.

Definition mc_limiting : IsLimitCone mc_cone :=
  pe_limiting F (pe_obj_proj HP F) (pe_obj_product_ump HP F) ArrowIx_Generates
    (pe_arrow_proj HP F) (pe_arrow_product_ump HP F)
    (pe_s HP F) (pe_t HP F) (pe_s_proj HP F) (pe_t_proj HP F)
    mc_incl mc_IsEqualizer.

Definition mc_limit : Limit F := limitcone_limit mc_cone mc_limiting.

Example mc_limit_apex :
  vertex_obj[@limit_cone _ _ _ mc_limit] = mc_apex := eq_refl.

Example mc_limit_leg (x : J) :
  cone_leg (@limit_cone _ _ _ mc_limit) x = pe_obj_proj HP F x ∘ mc_incl
  := eq_refl.

End Manes.

(* Mac Lane §V.2 Exercise 1(a): small products and coreflexive equalizers
   give completeness. *)
Definition Complete_from_coreflexive_equalizers {C : Category}
  (HP : HasIndexedProducts C) (HE : HasCoreflexiveEqualizers C) : @Complete C :=
  fun J F => mc_limit HP F HE.

(** ** Exercise 1(b), the categorical half: a common section is a
       factorization of the diagonal through the induced map *)

(* Part (b) is about REFLEXIVE pairs (a common right inverse), not the
   coreflexive pairs of part (a); in any cartesian category the section is
   exactly a factorization of the diagonal [id △ id] through [f △ g]. *)
Section CartesianHalf.

Context {C : Category} `{@Cartesian C}.
Context {x y : C} (f g : x ~> y).

Lemma fork_diagonal_of_reflexive (s : y ~> x) (Hf : f ∘ s ≈ id)
  (Hg : g ∘ s ≈ id) : (f △ g) ∘ s ≈ id △ id.
Proof.
  rewrite <- fork_comp.
  rewrite Hf, Hg.
  reflexivity.
Qed.

Lemma reflexive_of_fork_diagonal (s : y ~> x) (Hd : (f △ g) ∘ s ≈ id △ id) :
  (f ∘ s ≈ id) * (g ∘ s ≈ id).
Proof.
  split.
  - rewrite <- (exl_fork f g), <- comp_assoc, Hd.
    apply exl_fork.
  - rewrite <- (exr_fork f g), <- comp_assoc, Hd.
    apply exr_fork.
Qed.

Definition ReflexivePair_of_diagonal_factors :
  (∃ s : y ~> x, (f △ g) ∘ s ≈ id △ id) → ReflexivePair f g :=
  fun sd => let (s, Hd) := sd in
    let (Hf, Hg) := reflexive_of_fork_diagonal s Hd in
    common_section_reflexive f g s Hf Hg.

Definition diagonal_factors_of_ReflexivePair (R : ReflexivePair f g) :
  ∃ s : y ~> x, (f △ g) ∘ s ≈ id △ id :=
  (refl_section R;
     fork_diagonal_of_reflexive (refl_section R)
       (refl_section_f R) (refl_section_g R)).

Definition ReflexivePair_iff_diagonal_factors :
  ReflexivePair f g ↔ (∃ s : y ~> x, (f △ g) ∘ s ≈ id △ id) :=
  (diagonal_factors_of_ReflexivePair, ReflexivePair_of_diagonal_factors).

End CartesianHalf.

(** ** Exercise 1(b) in Sets *)

Section SetsHalf.

Context {X Y : SetoidObject}.
Context (f g : X ~{Sets}~> Y).

(* "The image of ⟨f, g⟩ contains the diagonal", pointwise: every point of Y
   is hit by f and g at one common point of X. *)
Definition diagonal_in_image : Type :=
  ∀ b : Y, ∃ a : X, (f a ≈ b) * (g a ≈ b).

(* One direction is unconditional: the section supplies the witness. *)
Definition diagonal_in_image_of_reflexive (R : ReflexivePair f g) :
  diagonal_in_image :=
  fun b => (refl_section R b; (refl_section_f R b, refl_section_g R b)).

(* The converse needs the chosen witnesses to respect ≈, which the
   statement of [diagonal_in_image] does not supply: [∃] is [sigT], so a
   choice function is present, but a Sets morphism also needs
   [proper_morphism]. *)
Definition diagonal_section (D : diagonal_in_image)
  (Hproper : ∀ b b' : Y, b ≈ b' → `1 (D b) ≈ `1 (D b')) : Y ~{Sets}~> X.
Proof.
  unshelve refine {| morphism := fun b => `1 (D b) |}.
  repeat intro; now apply Hproper.
Defined.

Definition reflexive_of_diagonal_in_image (D : diagonal_in_image)
  (Hproper : ∀ b b' : Y, b ≈ b' → `1 (D b) ≈ `1 (D b')) :
  ReflexivePair f g.
Proof.
  unshelve refine (common_section_reflexive f g (diagonal_section D Hproper) _ _).
  - intro b; exact (fst (`2 (D b))).
  - intro b; exact (snd (`2 (D b))).
Defined.

(* The morphism-level reading through Instance/Sets/Image.v: the diagonal
   factors through the mono leg of the (epi, mono) factorization of the
   induced map.  Unconditional in this direction. *)
Definition diagonal_through_image (R : ReflexivePair f g) :
  ∃ d : Y ~{Sets}~> Sets_Image (f △ g),
    Sets_Image_mono (f △ g) ∘ d ≈ id △ id.
Proof.
  unshelve eexists.
  - unshelve refine {| morphism := fun b =>
        ((f △ g) (refl_section R b); (refl_section R b; _)) |}.
    + reflexivity.
    + repeat intro.
      simpl.
      split; apply proper_morphism; now apply proper_morphism.
  - intro b; simpl.
    split; [exact (refl_section_f R b) | exact (refl_section_g R b)].
Defined.

End SetsHalf.

(** ** Non-vacuity, and its limit *)

(* [Sets] has coreflexive equalizers — but the only route in the tree is
   through the STRONGER [HasEqualizers Sets], so Manes' criterion is
   instantiated here only where Theorem 1's hypothesis already holds. *)
Definition Sets_HasCoreflexiveEqualizers : HasCoreflexiveEqualizers Sets :=
  @HasEqualizers_HasCoreflexiveEqualizers Sets
    (HasEqualizers_of_HasPullbacks_Terminal Sets_HasPullbacks).

Definition Sets_Complete_via_Manes : @Complete Sets :=
  Complete_from_coreflexive_equalizers
    Sets_HasIndexedProducts Sets_HasCoreflexiveEqualizers.
