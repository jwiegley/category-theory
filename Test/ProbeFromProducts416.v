Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.Two.

Generalizable All Variables.

Open Scope category_scope.

(** * Probe: the measured boundaries of Structure/Limit/FromProducts.v *)

(* Companion to Structure/Limit/FromProducts.v (Mac Lane, Categories for
   the Working Mathematician, 2nd ed., §V.2 Theorems 1 and 2, Corollary 2,
   §V.4 Exercise 2; Riehl, Category Theory in Context, 2nd ed., Theorems
   3.2.11 and 3.5.11, Exercise 3.2.ii).  Everything that file claims at
   [eq_refl] is shipped there as an [Example]; what it cannot guard from
   inside are the REFUSALS its header records and the universe boundaries
   a consumer meets.  Those are pinned here, from OUTSIDE the target,
   because an in-file [Fail] renames in lockstep with the constant it
   guards and so cannot detect a rename.  The [Sets] instantiation and the
   walking-arrow generating family live here too, because they cost
   modules the target should not carry.

   The negatives are of THREE kinds, told apart by the error TEXT — the
   kinds were read off the messages produced by stripping each [Fail] in
   turn, in a copy of this WHOLE file — plus one scope-free instrument
   check.

     N1  CONVERSION  The refinement at the FULL arrow index is the
                   construction in apex and in every leg (three controls
                   at [eq_refl]) but NOT as a cone RECORD: the coherence
                   field of [pe_cone] mentions the two component lemmas
                   [Hs] and [Ht], and the [Refinement] section's
                   [pe_gen_s_proj]/[pe_gen_t_proj] are different [Qed]
                   constants from [pe_s_proj]/[pe_t_proj].
     N2  CONVERSION  A leg of [pe_image_cone] is [fmap[G] proj ∘ fmap[G] e]
                   while the leg of [FCone G (pe_limit_cone …)] is
                   [fmap[G] (proj ∘ e)] — one [fmap_comp] apart, which
                   [fmap_comp] being a law FIELD does not convert; the
                   apex is the control.  This is why the target transports
                   along [pe_image_ConeIso] rather than ascribing.
     N3  CONVERSION  The two cones of N2 as whole records.
     N4  TYPING    [Complete_from_products_equalizers] fed a
                   [HasCoequalizers] where it asks for [HasEqualizers]: a
                   plain has-type mismatch with no [cannot unify] clause
                   and no universe clause.
     N5  TYPING    [Cocomplete_from_coproducts_coequalizers] fed the
                   products-and-equalizers pair: [HasIndexedProducts C] is
                   not [HasIndexedCoproducts C] — the latter is that class
                   at [C^op], and [C] is not [C^op] on the nose.
     N6  UNIVERSE  At a category whose hom level is declared strictly BELOW
                   its proof level, the hom-set, the identity and an
                   endofunctor are ACCEPTED while [HasIndexedProducts],
                   [HasEqualizers], [IsIndexedProduct], [IsEqualizer],
                   [Limit] and [Complete] are each refused ALONE — six
                   donors of the hom = proof identification every binder
                   in the target carries, none introduced there.
     N7  UNIVERSE  At a shape whose homs are declared strictly BELOW the
                   ambient category's, the diagram, a [Cone] over it and
                   the arrow index [ArrowIx] are ACCEPTED while [Limit]
                   and [IsLimitCone] are refused — the shape-hom =
                   ambient-hom identification is the limit vocabulary's.
                   [pe_cone] is refused there too, at its AMBIENT
                   argument [Cu] with the same [Cannot enforce ch = jh]
                   (no argument of it is already refused: [Fu], [Cone Ju
                   Cu Fu] and [ArrowIx Ju] all pass): the identification
                   sits in [pe_cone]'s OWN binder, [{J : Category@{u u0
                   u0}} {C : Category@{u1 u0 u0}}], whose donor is not
                   isolated here, and since [Cone] is accepted at those
                   levels this refusal corroborates nothing about the
                   attribution to [Limit]/[IsLimitCone].  (An earlier
                   draft said it fired at the diagram argument; an audit
                   stripped the command and read the message.)
     N8  UNIVERSE  At a category whose hom level is declared strictly above
                   [Set], the class [HasIndexedProducts], its
                   [indexed_product] and [Complete_from_products_equalizers]
                   are ACCEPTED while [iprod] — the discrete-diagram
                   presentation the issue's work item 4 asks the
                   construction to route through — is refused with
                   [Cannot enforce Set = ch]: [iprod]'s binder is
                   [C : Category@{_ Set Set}] through [DiscreteCat_Functor]
                   and [Limit].  This is the measured reason the target
                   is stated over the CLASS and never over [iprod].

   Every constant a negative names also appears in a [Check] outside every
   [Fail], so a rename breaks this file loudly instead of turning a [Fail]
   vacuously green. *)

(** ** Instrument check *)

Fail Check probe416_no_such_constant.

(** ** Guards *)

Check @limit_of_products_equalizer.
Check @Complete_from_products_equalizers.
Check @Cocomplete_from_coproducts_coequalizers.
Check @continuous_from_products_equalizers.
Check @pe_cone.
Check @pe_limiting.
Check @pe_limit_cone.
Check @pe_gen_cone.
Check @pe_gen_apex.
Check @pe_apex.
Check @pe_image_cone.
Check @pe_image_ConeIso.
Check @ArrowIx.
Check @ArrowIx_Generates.
Check @Generates.
Check @Gen.
Check @gen_id.
Check @gen_idx.
Check @IsIdArrow.
Check @is_id_arrow.
Check @nonid_Generates.
Check @pe_gen_restrict_iso.
Check @HasIndexedProducts.
Check @HasIndexedCoproducts.
Check @HasEqualizers.
Check @HasCoequalizers.
Check @IsIndexedProduct.
Check @IsEqualizer.
Check @indexed_product.
Check @iprod.
Check @Limit.
Check @IsLimitCone.
Check @Cone.
Check @Complete.
Check @FCone.
Check @cone_leg.
Check @vertex_obj.

(** ** N1: the refinement at the full index *)

Section FullIndex.

Context {C : Category} (HP : HasIndexedProducts C) (HE : HasEqualizers C).
Context {J : Category} (F : J ⟶ C).

(* Controls: apex, apex object and every leg agree on the nose. *)
Example probe416_ctrl_full_apex :
  vertex_obj[pe_gen_cone HP HE F ArrowIx_Generates]
    = vertex_obj[pe_limit_cone HP F HE] := eq_refl.

Example probe416_ctrl_full_apex_obj :
  pe_gen_apex HP HE F (idx_arr := @aix_arr J) = pe_apex HP F HE := eq_refl.

Example probe416_ctrl_full_leg (x : J) :
  cone_leg (pe_gen_cone HP HE F ArrowIx_Generates) x
    = cone_leg (pe_limit_cone HP F HE) x := eq_refl.

(* N1: CONVERSION — not as records. *)
Fail Example probe416_n1 :
  pe_gen_cone HP HE F ArrowIx_Generates = pe_limit_cone HP F HE := eq_refl.

(* The delivered limit's cone IS the constructed cone. *)
Example probe416_ctrl_limit_cone :
  @limit_cone _ _ _ (limit_of_products_equalizer HP F HE)
    = pe_limit_cone HP F HE := eq_refl.

Example probe416_ctrl_complete_cone :
  @limit_cone _ _ _ (Complete_from_products_equalizers HP HE J F)
    = pe_limit_cone HP F HE := eq_refl.

End FullIndex.

(** ** N2, N3: the image cone against the image of the cone *)

Section Image.

Context {C D : Category} (HP : HasIndexedProducts C) (HE : HasEqualizers C).
Context (G : C ⟶ D) (GP : PreservesIndexedProducts G)
  (GE : PreservesEqualizers G).
Context {J : Category} (K : J ⟶ C).

(* Control: the apexes agree. *)
Example probe416_ctrl_image_apex :
  vertex_obj[pe_image_cone HP HE G GP GE K]
    = vertex_obj[FCone G (pe_limit_cone HP K HE)] := eq_refl.

(* N2: CONVERSION — a leg is one [fmap_comp] away. *)
Fail Example probe416_n2 (x : J) :
  cone_leg (pe_image_cone HP HE G GP GE K) x
    = cone_leg (FCone G (pe_limit_cone HP K HE)) x := eq_refl.

(* N3: CONVERSION — the whole records. *)
Fail Example probe416_n3 :
  pe_image_cone HP HE G GP GE K = FCone G (pe_limit_cone HP K HE) := eq_refl.

(* Control: the transport the target ships. *)
Check (pe_image_ConeIso HP HE G GP GE K).

End Image.

(** ** N4, N5: the hypotheses are the ones named *)

Section Handedness.

Context {C : Category} (HP : HasIndexedProducts C) (HE : HasEqualizers C).
Context (HC : HasIndexedCoproducts C) (HQ : HasCoequalizers C).

(* Controls. *)
Check (Complete_from_products_equalizers HP HE).
Check (Cocomplete_from_coproducts_coequalizers HC HQ).

(* N4: TYPING. *)
Fail Check (Complete_from_products_equalizers HP HQ).

(* N5: TYPING. *)
Fail Check (Cocomplete_from_coproducts_coequalizers HP HE).

End Handedness.

(** ** N6: hom = proof, six donors *)

Section HomProof.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}) (x y : Cu) (f : x ~> y).

(* Controls. *)
Check (x ~> y).
Check (id[x]).
Check (@Functor Cu Cu).

Fail Check (@HasIndexedProducts Cu).
Fail Check (@HasEqualizers Cu).
Fail Check (@IsIndexedProduct Cu).
Fail Check (@IsEqualizer Cu x y f f).
Fail Check (@Limit Cu).
Fail Check (@Complete Cu).

End HomProof.

(** ** N7: shape hom = ambient hom, the limit vocabulary's *)

Section ShapeHom.

Universes jo jh co ch.
Constraint jh < ch.

Context (Ju : Category@{jo jh jh}) (Cu : Category@{co ch ch}).
Context (Fu : Ju ⟶ Cu).

(* Controls. *)
Check Fu.
Check (@Cone Ju Cu Fu).
Check (@ArrowIx Ju).

Fail Check (@Limit Ju Cu Fu).
Fail Check (@IsLimitCone Ju Cu Fu).

(* Inherited: fires at the diagram argument [Fu]. *)
Fail Check (@pe_cone Ju Cu Fu).

End ShapeHom.

(** ** N8: the [iprod] route is pinned to [Set]; the class is not *)

Section AboveSet.

Universes co ch.
Constraint Set < ch.

Context (Cu : Category@{co ch ch}).
Context (HP : HasIndexedProducts Cu) (HE : HasEqualizers Cu).

(* Controls. *)
Check HP.
Check (@indexed_product Cu HP).
Check (@Complete_from_products_equalizers Cu HP HE).

(* N8: UNIVERSE. *)
Fail Check (@iprod Cu).

End AboveSet.

(** ** The [Sets] instantiation *)

(* Riehl's Theorem 3.2.11 is the general theorem at [Sets]: a SECOND
   inhabitant of [@Complete Sets] beside Instance/Sets/Complete.v's
   [Sets_Complete], NOT compared with it — and built WITHOUT it.  The
   products are Instance/Sets/Products.v's [Sets_HasIndexedProducts] and
   the equalizers are [HasEqualizers_of_HasPullbacks_Terminal] at
   Instance/Sets/Pullback.v's [Sets_HasPullbacks] (the route
   Adjunction/CokernelPair.v takes), so Instance/Sets/Complete.v is
   absent from this file's closure (coqdep: 47 modules).  The obvious
   supply, Adjunction/GAFT/Sets.v's [Sets_HasEqualizers], would NOT do:
   it is [Complete_HasEqualizers Sets_Complete], equalizers read off the
   very inhabitant this one stands beside — an audit caught a first
   draft that used it while calling the two "independent". *)

Definition sets_pe_complete : @Complete Sets :=
  Complete_from_products_equalizers Sets_HasIndexedProducts
    (HasEqualizers_of_HasPullbacks_Terminal Sets_HasPullbacks).

Check sets_pe_complete.

(** ** A generating family on the walking arrow *)

(* Riehl's Exercise 3.2.ii, non-vacuously: [_2] has three arrows, and the
   family with ONE index — the non-identity arrow — generates.  So the
   refined arrow product is indexed by [unit] where the full one is
   indexed by [ArrowIx _2]. *)

Definition two_gen_fam (_ : unit) : TwoX ~{_2}~> TwoY := TwoXY.

Definition two_Generates : Generates two_gen_fam.
Proof.
  intros x y f.
  destruct f.
  - exact (@gen_id _2 unit _ _ two_gen_fam TwoX).
  - exact (@gen_id _2 unit _ _ two_gen_fam TwoY).
  - exact (@gen_idx _2 unit _ _ two_gen_fam tt).
Defined.

(* The full index has (at least) two distinct elements the refined one
   does not: the two identities. *)

Example two_arrowix_apart :
  @mk_arrow _2 _ _ TwoXY = @mk_arrow _2 _ _ TwoIdX → False.
Proof. intro H; apply (f_equal (fun a => snd (`1 a))) in H; discriminate. Qed.

(* Being an identity is decidable on [_2], so the non-identity family of
   the target's [nonid_Generates] generates there too. *)

Definition two_isid_dec (x y : _2) (f : x ~{_2}~> y) :
  IsIdArrow x y f + (IsIdArrow x y f → False).
Proof.
  destruct f.
  - left; exact (@is_id_arrow _2 TwoX TwoIdX (reflexivity _)).
  - left; exact (@is_id_arrow _2 TwoY TwoIdY (reflexivity _)).
  - right; intro H; inversion H.
Defined.

Check (nonid_Generates two_isid_dec).

(* The restriction does not change the limit: the one-index equalizer is
   canonically isomorphic, as a cone, to the full construction. *)

Check (fun F : _2 ⟶ Sets =>
  pe_gen_restrict_iso Sets_HasIndexedProducts
    (HasEqualizers_of_HasPullbacks_Terminal Sets_HasPullbacks) F
    two_Generates).
