(** * Probe for Structure/Complete/Freyd.v (issue #423)

    Pins the measured boundaries of Freyd's collapse: a [Complete] instance
    reaches an indexed product WITHOUT a [Set] pin only through the
    annotated discrete-diagram donor, the op-dual of an [ArrowIndex] needs
    the explicit constructor, the smallness hypothesis is not vacuous, and
    the constructive wall is an INJECTION no refutation can pin.  Every
    refutation command below was stripped ONE AT A TIME in a copy of the
    whole file and compiled alone with its error read, so each refusal is
    of the kind its label says.

    Numbering:
     instrument      an absent name, refused — the refutation keyword is
                     live in this file.
     N1 UNIVERSE     under [Constraint Set < uh], feeding a [Complete]
                     instance to Structure/Limit/Product.v's
                     [limit_is_indexed_product] through the UNANNOTATED
                     [DiscreteCat_Functor] is refused with "Cannot enforce
                     Set = uh": that donor is stated at
                     [C : Category@{_ Set Set}].  Freyd.v's [complete_iprod]
                     at the same category is the control (it runs through
                     Structure/Limit/Comparison.v's [DiscreteCat_Functor']).
     N2 TYPING       the anonymous record literal for the dual elaborates
                     its binders at [obj[C]] and is refused against
                     [ArrowIndex (C^op)] ("has type ArrowIndex C while it
                     is expected to have type ArrowIndex C^op");
                     [ArrowIndex_op] with [@Build_ArrowIndex (C^op)] is the
                     control, and it is an involution at [eq_refl]
                     ([p423_op_round]).

    Positive controls, deliberately NOT written as refutations:
     - [canonical_ArrowIndex]: every category with decidable object
       equality carries an [ArrowIndex], so the hypothesis is not disguised
       thinness or finiteness.
     - [fr_inj_injective]: from [f ≉ g] alone an injection [(K → bool) → K]
       on the nose.  That this injection cannot be refuted without deciding
       the hom-setoid is METATHEORETIC (Hyland's effective-topos model,
       Structure/Complete.v:102-112); unprovability is not a refusal, so no
       refutation command is written for it.
     - [p423_small_and_products]: Theory/Size.v's [Small] and products over
       the category's own total arrow collection coexist in one binder.
       This is a coexistence check, not a refutation of a wall: [Small]'s
       extra levels are fresh and bounded only below by C's, so the binder
       adds no refutable constraint; what it witnesses is that
       [indexed_product] applies at [TotalMor C] beside [Small].  The one
       universe obstruction measured is the [Set] pin of N1.

    Guard coverage: every constant a refutation names is also named
    outside a refutation command (the guard block at the end) — the
    exceptions, under the plain identifier tokenization with comments
    stripped, being the keyword itself, the binder names and keywords of
    the record literal ([_], [fun], [d], [h], [m], [x], [y]), the notation
    token [op] of [C^op], the name the refuted declaration would introduce
    and the instrument's absent name — so a renamed or removed constant
    breaks the build on a positive line rather than letting a refutation
    pass for the wrong reason. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Size.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Comparison.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Product.Limit.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Limit.
Require Import Coq.Logic.Eqdep_dec.
Require Import Category.Structure.Complete.Freyd.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe423_absent_name.

(** ** A: the [Set] pin of the unannotated discrete-diagram donor *)

Section SetPin.

Universe uo uh.
Constraint Set < uh.

Context {C : Category@{uo uh uh}} (comp : @Complete C) (fam : TotalMor C → C).

(* N1 UNIVERSE: through Structure/Limit/Product.v's unannotated
   [DiscreteCat_Functor], a [Complete] instance yields an indexed product
   only at a category whose hom level IS [Set] *)
Fail Check (@limit_is_indexed_product C (TotalMor C) fam
              (comp _ (@DiscreteCat_Functor (TotalMor C) C fam))).

(* control: the annotated route of Freyd.v at the same category *)
Check (complete_iprod comp fam).
Check (complete_iprod_obj comp fam).

End SetPin.

(** ** B: the dual's record literal *)

Section OpLiteral.

Context {C : Category} (AI : ArrowIndex C).

(* N2 TYPING: the anonymous record literal elaborates its binders at
   [obj[C]] and is refused against [ArrowIndex (C^op)] *)
Fail Definition p423_op_literal : ArrowIndex (C^op) :=
  {| ai_index   := ai_index AI
   ; ai_enc     := fun x y h => ai_enc AI h
   ; ai_dec     := fun x y m d => ai_dec AI m d
   ; ai_dec_enc := fun x y h d => ai_dec_enc AI h d |}.

(* control: the explicit constructor at [C^op] *)
Check (ArrowIndex_op AI).

(* readback: the dual is an involution at [eq_refl] *)
Example p423_op_round : ArrowIndex_op (ArrowIndex_op AI) = AI := eq_refl.

End OpLiteral.

(** ** C: positive controls — the hypothesis is not vacuous, and the
       constructive wall is an injection *)

(* every category with decidable object equality carries an [ArrowIndex] *)
Check (@canonical_ArrowIndex).

(* from [f ≉ g] alone: an injection [(K → bool) → K] on the nose *)
Check (@fr_inj_injective).

(* Theory/Size.v's [Small] and products over the category's own arrows
   coexist: no universe wall *)
Definition p423_small_and_products {C : Category} `{@Small C}
  (HP : HasIndexedProducts C) (fam : TotalMor C → C) : C :=
  indexed_product fam.

(** ** D: the headline statements *)

Check (@freyd_no_separated_pair).
Check (@freyd_thin).
Check (@small_complete_is_thin).
Check (@small_cocomplete_is_thin).
Check (@complete_has_glbs).
Check (@complete_Proset_Complete).

(** ** Guard block *)

Check @ArrowIndex.
Check @ai_index.
Check @ai_enc.
Check @ai_dec.
Check @ai_dec_enc.
Check @ArrowIndex_op.
Check @ObjDecEq.
Check @canonical_ArrowIndex.
Check @DecHom.
Check @DecHom_op.
Check @freyd_thin_canonical.
Check @freyd_thin_dual.
Check @fr_inj.
Check @complete_iprod.
Check @complete_iprod_obj.
Check @complete_iprod_proj.
Check @limit_is_indexed_product.
Check @DiscreteCat_Functor.
Check @DiscreteCat_Functor'.
Check @Complete.
Check @TotalMor.
Check @Small.
Check @HasIndexedProducts.
Check @indexed_product.
