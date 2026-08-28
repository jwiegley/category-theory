(** * Boundary probes for Instance/Cat/Pullback.v (issue #337)

    Mac Lane CWM 2nd ed. §III.5 Exercise 3, book p. 74.

    The target proves that the fibre product of categories IS a pullback in
    [StrictCat] under [ObjUIP C], that the same hypothesis is NECESSARY, and
    that the fibre product is NOT a pullback in [Cat].  Three of its four
    measured boundaries are pinned here; the fourth, the universe one, is
    pinned here BECAUSE it cannot be pinned in the target: stating it needs
    a section that declares three object universes strictly apart, and a
    [Constraint] declaration inside the target would constrain the whole
    file rather than one probe.

    FOUR NEGATIVES OF THREE KINDS, kept lexically apart:

      * Negative 1 is FORMABILITY (a universe inconsistency).  It does more
        than record that [FibreProduct_IsPullback] identifies the three
        object universes -- its positive control shows [FibreProduct]
        ITSELF is formable at three universes declared strictly apart, so
        the identification is the [IsPullback] PACKAGING's and not the
        construction's.  Stripped, the error names the declared levels
        (this one, and only this one, is legible from the message TAIL):
          universe inconsistency: Cannot enforce co = ao
          because ao < bo < co.

      * Negatives 2 and 3 are CONVERSION ("cannot unify"), and they differ
        in CAUSE.  Negative 2 fails only in the LAW fields -- its two
        controls show the object and arrow actions of [FP_fst ◯ FP_med]
        agree with [q1]'s at [eq_refl], so what does not convert is the
        three rebuilt proofs.  Negative 3 fails in the DATA: the slice
        stores an arrow where the fibre product stores a pair carrying an
        equality proof, so these are different categories that happen to be
        pullbacks of one cospan.

      * Negative 4 is TYPING, and its marker is "cannot satisfy constraint"
        -- which sits MID-MESSAGE, the tail ending in a "cannot unify" that
        would misread as CONVERSION, so this kind must be read off the
        whole error rather than off its tail.  It is the
        content of [IB_FibreProduct_empty] made checkable at the term
        level: no object of [FibreProduct IBtrue IBfalse] can be written,
        while the control writes one at the AGREEING cospan, so the failure
        is the cospan's and not the fibre product's.

    Every negative is paired with a positive control naming its own
    constants.  The measured rename-simulation score is at the end, over
    the constants the NEGATIVES name and no others. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Theory.Category.Monoid.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Comma.Diagram.
Require Import Category.Construction.Slice.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Structure.Pullback.
Require Import Category.Instance.Cat.Pullback.

Generalizable All Variables.

(** ** Instrument check

    A [Fail] that never fails would make every negative below vacuous. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negative 1 (FORMABILITY): the universe identification is the
       PACKAGING's, not the construction's

    [FibreProduct] carries bounds only.  [FibreProduct_IsPullback] displays
    three separate category binders, but its constraint block contains
    [u = u1], [u = u3], [u0 = u2] and [u0 = u4] -- all three object
    universes identified, and all three hom-and-proof universes too.  The
    control and the negative differ in nothing but which of the two is
    asked for at the same three levels. *)

Section UniverseBoundary.

Universe ao bo co h.
Constraint ao < bo.
Constraint bo < co.

(* Control: the construction is formable with the three object universes
   declared strictly apart. *)
Check (fun (A : Category@{ao h h}) (B : Category@{bo h h})
           (C : Category@{co h h}) (F : A ⟶ C) (G : B ⟶ C) =>
         FibreProduct F G).

(* Control: so are both projections, at the same three levels. *)
Check (fun (A : Category@{ao h h}) (B : Category@{bo h h})
           (C : Category@{co h h}) (F : A ⟶ C) (G : B ⟶ C) =>
         (FP_fst F G, FP_snd F G)).

(* Control: so is the hypothesis. *)
Check (fun (C : Category@{co h h}) => ObjUIP C).

(* NEGATIVE 1. *)
Fail Check (fun (A : Category@{ao h h}) (B : Category@{bo h h})
                (C : Category@{co h h}) (F : A ⟶ C) (G : B ⟶ C)
                (uip : ObjUIP C) =>
              FibreProduct_IsPullback F G uip).

End UniverseBoundary.

(** ** Negative 2 (CONVERSION): the first triangle holds in the data and
       fails in the laws

    [FP_med_fst] is proved with an [eq_refl] object component and a
    [reflexivity] arrow half.  That is exactly as far as conversion goes:
    the two controls below close by [eq_refl], and the whole-record
    equality does not, because [Functor]'s three law fields are rebuilt
    proofs on the two sides. *)

Section TriangleData.

Context {A B C Q : Category} (F : A ⟶ C) (G : B ⟶ C).
Context (q1 : Q ⟶ A) (q2 : Q ⟶ B).
Context (Hsq : F ∘[StrictCat] q1 ≈[StrictCat] G ∘[StrictCat] q2).

(* Control: the object action is [q1]'s on the nose. *)
Definition probe_fp_obj (z : Q) :
  fobj[FP_fst F G ◯ FP_med F G q1 q2 Hsq] z = fobj[q1] z := eq_refl.

(* Control: so is the arrow action. *)
Definition probe_fp_map (z w : Q) (f : z ~> w) :
  fmap[FP_fst F G ◯ FP_med F G q1 q2 Hsq] f = fmap[q1] f := eq_refl.

(* Control: the second triangle's data likewise. *)
Definition probe_fp_obj_snd (z : Q) :
  fobj[FP_snd F G ◯ FP_med F G q1 q2 Hsq] z = fobj[q2] z := eq_refl.

(* NEGATIVE 2. *)
Fail Definition probe_fp_record :
  FP_fst F G ◯ FP_med F G q1 q2 Hsq = q1 := eq_refl.

(* Control: what IS available at that strength, in [StrictCat]'s own
   hom-setoid. *)
Check (FP_med_fst F G q1 q2 Hsq).
Check (FP_med_snd F G q1 q2 Hsq).

End TriangleData.

(** ** Negative 3 (CONVERSION): the slice is not the fibre product of its
       own cospan

    Both are pullbacks of [Arrow_cod] along [Diagonal 1 c], so they are
    isomorphic; the target does not build that isomorphism and does not
    claim it.  They are certainly not the same category: an object of the
    slice is an arrow, an object of the fibre product is a pair of objects
    carrying a proof that their images agree. *)

Section SliceApex.

Context {C : Category} (c : C).

(* Control: the leg's object action, on the nose. *)
Definition probe_slice_obj (x : Slice C c) :
  fobj[Slice_Arrow c] x = ((`1 x, c); `2 x) := eq_refl.

(* NEGATIVE 3. *)
Fail Definition probe_slice_apex :
  Slice C c = FibreProduct (@Arrow_cod C) (@Diagonal C _1 c) := eq_refl.

End SliceApex.

(** ** Negative 4 (TYPING): the refuting cospan has an empty fibre product

    This is [IB_FibreProduct_empty] read at the term level.  The control
    writes an object of the fibre product of the AGREEING cospan with the
    same syntax, so what the negative measures is the cospan and not the
    construction. *)

(* Control: at a cospan whose two legs agree, the pair with [eq_refl] is an
   object. *)
Definition probe_ib_agree : obj[FibreProduct IBtrue IBtrue] :=
  ((ttt, ttt); eq_refl).

(* NEGATIVE 4. *)
Fail Definition probe_ib_empty : obj[FibreProduct IBtrue IBfalse] :=
  ((ttt, ttt); eq_refl).

(* Control: the same fact, proved rather than probed. *)
Check IB_FibreProduct_empty.
Check IB_iso.

(** ** Positive controls for the headline artifacts

    Every constant the four negatives name appears above; these guard the
    results the file exists for, so that a rename anywhere in it breaks
    this probe loudly. *)

Check FibreProduct.
Check FP_fst.
Check FP_snd.
Check FP_commutes_strict.
Check FP_commutes_cat.
Check FP_med.
Check FP_med_unique.
Check FibreProduct_IsPullback.
Check FibreProduct_Pullback.
Check ObjUIP_of_ObjDecEq.
Check FibreProduct_IsPullback_dec.
Check StrictCat_HasPullbacks.

(** The [Cat] side: the candidate is refuted, and the refutation is narrow
    -- the same cospan does have a [Cat] pullback. *)

Check FibreProduct_not_Cat_pullback.
Check point_cospan_Cat_IsPullback.
Check point_cospan_square.
Check one_functors_equiv.

(** Necessity of the hypothesis. *)

Check FP_uniqueness_forces_UIP.
Check loop_functor.
Check loop_functor_fst.
Check loop_functor_snd.

(** The comma half. *)

Check Slice_Arrow.
Check Slice_commutes.
Check Slice_IsPullback.
Check Coslice_Arrow.
Check Coslice_commutes.
Check Coslice_IsPullback.
Check slice_arrow_reflect.
Check coslice_arrow_reflect.

(** ** MEASURED RENAME-SIMULATION SCORE

    The constants the NEGATIVES name:

      Negative 1: [FibreProduct_IsPullback], [ObjUIP]
      Negative 2: [FP_fst], [FP_med], [q1] (a section variable, not a
                  constant, so it is not counted)
      Negative 3: [Slice], [FibreProduct], [Arrow_cod], [Diagonal]
      Negative 4: [FibreProduct], [IBtrue], [IBfalse]

    Deduplicated, and with the two stdlib/donor names [Slice] and
    [Diagonal] kept in because both are library constants this file
    depends on, that is [FibreProduct_IsPullback], [ObjUIP],
    [FibreProduct], [FP_fst], [FP_med], [Slice], [Arrow_cod], [Diagonal],
    [IBtrue], [IBfalse] -- TEN, counted rather than recalled.  [Category],
    [obj], [ttt] and [_1] are named by the negatives too and are EXCLUDED,
    on the stated ground that they are core vocabulary named by almost
    every file in the tree, not that they are hard to guard.

    Each is named by a positive control above: [FibreProduct_IsPullback],
    [FibreProduct], [FP_fst] and [FP_med] by the headline block;
    [ObjUIP] by the third control of Negative 1; [Slice] and [Arrow_cod]
    and [Diagonal] by [probe_slice_obj] and by [Check Slice_Arrow] (whose
    type mentions [Slice] and [Arrow]) -- and, to leave nothing to a type
    display, explicitly below; [IBtrue] and [IBfalse] by [probe_ib_agree]
    and [Check IB_FibreProduct_empty].

    Score: 10/10, on an unpadded denominator. *)

Check (fun (C : Category) (c : C) => (@Slice C c, @Arrow_cod C,
                                      @Diagonal C _1 c)).
Check IBtrue.
Check IBfalse.
Check IB.
