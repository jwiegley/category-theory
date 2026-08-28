(** * Boundary probes for the indexed coproduct of categories (issue #338)

    Mac Lane CWM 2nd ed. §III.5 Exercise 4, book p. 74; Riehl 2nd ed. §3.6.

    The two target files pin FOUR refutations of their own, and not all
    of one kind: three CONVERSION
    (`Construction/Coproduct/Indexed.v:530`,
    `Instance/Cat/Coproduct.v:396` and `:399`) and one FORMABILITY
    (`Instance/Cat/Coproduct.v:418`, the smallness measurement).  This
    file pins the THREE boundaries they cannot state -- two because
    stating them needs a section declaring universe levels strictly
    apart, which a target cannot carry without constraining itself.

    THREE NEGATIVES OF TWO KINDS, kept lexically apart, plus one compiled
    POSITIVE that turns a header argument into a fact:

      * Negatives 1 and 2 are FORMABILITY, and they carry the file's two
        universe claims.  Negative 1 is why `SigmaCat` is written with
        EXPLICIT universe binders: the same body written unannotated
        minimizes so as to IDENTIFY the summands' hom and proof universes,
        and is then rejected under `Constraint uh < up` where the
        annotated form is accepted.  A target cannot pin this, since
        stating it needs a section that declares levels strictly apart.
        Negative 2 localizes the ONE identification the UMP-level results
        do carry (`C : Category@{a b b}`) to its donor: `Functor_Setoid`
        is rejected at separated levels while the functor TYPE `C ⟶ D`
        and the underlying `Unique` over a hom-setoid both elaborate.
        `Functor_Setoid` (`Theory/Functor.v:149`) is an unannotated
        `Program Instance`, and since `≈` on functors IS that setoid, no
        statement of the UMP in this library's vocabulary avoids it.  It
        is not introduced by #338 and is NOT claimed unavoidable.

      * Negative 3 is CONVERSION: the indexed construction at
        `I := bool` is not Leibniz-equal to the binary `Coproduct` even
        in its OBJECT type -- which is exactly why
        `SigmaBool_strict_iso` is an isomorphism of categories and
        nothing stronger.

      An earlier revision of this file had a FOURTH negative, asserting
      that the elementary coproduct record is not the bundled
      `HasIndexedCoproducts` datum on the nose.  It was wrong twice over
      and is recorded here rather than quietly dropped: it fired for the
      WRONG REASON (an over-application typing error, since
      `Cat_HasIndexedCoproducts` is not a function of the index), and
      the statement it was reaching for is FALSE -- the packaging is
      definitional all the way through.  What replaced it is the three
      `eq_refl` identifications of section "The packaging is
      transparent" below, which are a stronger and truer result.

      * The POSITIVE, `probe_forall_encoding_inhabited`, compiles the
        first half of the header's refutation of encoding (c).  The
        header argues that reading the hom as `∀ e : i = j, …` is wrong
        MATHEMATICS because for provably distinct `i` and `j` that type is
        INHABITED by the vacuous function, so the reading would add a
        morphism between every cross-summand pair -- the indiscrete
        category on the summands rather than their disjoint union.  That
        half is a one-line construction, so it is compiled here rather
        than left as prose.  The header's SECOND half (no identity is
        definable) and its fourth-encoding argument remain arguments; the
        target says so and this file does not change that.

    Every negative is paired with a positive control naming its own
    constants.  The measured rename-simulation score is at the end, over
    the constants the NEGATIVES name and no others. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Coproduct.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Cat.
Require Import Category.Construction.Coproduct.Indexed.
Require Import Category.Instance.Cat.Coproduct.

Generalizable All Variables.

(** ** Instrument check

    A [Fail] that never fails would make every negative below vacuous. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negative 1 (FORMABILITY): the explicit universe binders are
       load-bearing

    `SigmaCat` is declared `@{ui uo oh op us}` and its constraint block is
    ALL BOUNDS -- `ui <= us`, `uo <= us`, `oh <= op`, the last being
    `Class Category`'s own `h <= p`.  Written WITHOUT binders the same
    body minimizes to a shape that identifies the summands' hom and proof
    universes.  The control and the negative differ in nothing else. *)

Section BinderBoundary.

Universe uo uh up.
Constraint uh < up.

(* Control: the ANNOTATED construction is formable with the summands' hom
   and proof universes declared strictly apart. *)
Check (fun (I : Type) (C : I -> Category@{uo uh up}) => SigmaCat C).

(* Control: so is its injection, at the same levels. *)
Check (fun (I : Type) (C : I -> Category@{uo uh up}) (i : I) =>
         SigmaCat_inj C i).

(* The unannotated body, re-declared here so the negative is about the
   ANNOTATION and not about anything else in the file. *)
Definition sigma_obj_unann {I : Type} (C : I -> Category) : Type :=
  ∃ i : I, C i.

(* NEGATIVE 1. *)
Fail Check (fun (I : Type) (C : I -> Category@{uo uh up}) =>
              sigma_obj_unann C).

End BinderBoundary.

(** ** Negative 2 (FORMABILITY): the UMP's one identification is
       `Functor_Setoid`'s

    `SigmaCat_ump` displays `C : I → Category@{u7 u9 u9}` and
    `D : Category@{u8 u9 u9}` -- the two OBJECT universes stay apart while
    hom and proof are identified.  The controls show the functor type and
    the `Unique` packaging are both innocent. *)

Section SetoidBoundary.

Universe vo vh vp.
Constraint vh < vp.

(* Control: the functor TYPE elaborates at separated levels. *)
Check (fun (C D : Category@{vo vh vp}) => (C ⟶ D)).

(* Control: so does a `Unique` over a hom-setoid of such a category. *)
Check (fun (C : Category@{vo vh vp}) (x y : C)
           (P : (x ~> y) -> Type) => @Unique _ (@homset C x y) P).

(* Control: [Functor_Setoid] EXISTS and elaborates at UNCONSTRAINED
   levels -- without this the negative below would still "succeed" after
   a rename of [Functor_Setoid], on a reference-not-found error rather
   than on the universe boundary.  (That vacuity was measured, not
   guessed: an earlier revision of this file omitted this line and the
   rename simulation scored 3/4.) *)
Check @Functor_Setoid.

(* NEGATIVE 2. *)
Fail Check (fun (C D : Category@{vo vh vp}) => @Functor_Setoid C D).

End SetoidBoundary.

(** ** The packaging is transparent, in all THREE fields

    The construction is stated first at the apex-pinned
    `IsIndexedCoproduct` and only then packaged through
    `Build_HasIndexedCoproducts`, deliberately avoiding
    `Colimit`/`DiscreteCat_Functor`.  Nothing is lost in the packaging:
    the class's object field, its injection field AND its universal-
    property field all return the elementary data at `eq_refl`.  The
    third is the one worth having -- it says the bundled class carries
    the very record `SigmaCat_IsIndexedCoproduct` proves, not a rebuilt
    copy of it. *)

Check @SigmaCat_IsIndexedCoproduct.
Check Cat_HasIndexedCoproducts.

Definition probe_pkg_obj {I : Type} (C : I -> Cat) :
  @indexed_coproduct Cat Cat_HasIndexedCoproducts I C = SigmaCat C
  := eq_refl.

Definition probe_pkg_inj {I : Type} (C : I -> Cat) (i : I) :
  @indexed_coproduct_inj Cat Cat_HasIndexedCoproducts I C i
    = SigmaCat_inj C i := eq_refl.

Definition probe_pkg_ump {I : Type} (C : I -> Cat) :
  @indexed_coproduct_ump Cat Cat_HasIndexedCoproducts I C
    = SigmaCat_IsIndexedCoproduct C := eq_refl.

(** ** Negative 3 (CONVERSION): the binary comparison is an isomorphism
       and nothing stronger

    At `I := bool` the indexed construction and `Construction/Coproduct.v`'s
    binary `Coproduct` are isomorphic AS CATEGORIES
    (`SigmaBool_strict_iso`, in `StrictCat`, both round trips at
    `Functor_StrictEq_Setoid`).  They are not the same category, and the
    obstruction is already in the OBJECT type: a dependent pair against a
    tagged sum. *)

(* Control: the isomorphism that DOES hold. *)
Check @SigmaBool_strict_iso.
Check @SigmaBool_iso.
Check @BoolFam.

(* NEGATIVE 3. *)
Fail Definition probe_bool_obj (C D : Category) :
  obj[SigmaCat (BoolFam C D)] = (obj[C] + obj[D])%type := eq_refl.

(** ** The compiled half of the encoding-(c) refutation

    For provably distinct indices the type `∀ e : i = j, X e` is
    INHABITED, by the function that eliminates the empty equality.  So
    reading a cross-summand hom that way does not give an empty hom-set;
    it gives a one-element one, and the construction would be the
    indiscrete category on the summands rather than their disjoint union.
    The header argues this; here it is, compiled. *)

Definition probe_forall_encoding_inhabited
  (C : bool -> Category) (x : C true) (y : C false) :
  ∀ e : true = false, ob_cast C e x ~> y :=
  fun e => match (eq_ind true (fun b : bool => if b then True else False)
                          I false e) with end.

(* Contrast, from the target: the encoding actually used makes that hom
   EMPTY, which is the point. *)
Check @sigma_hom_cross_empty.
Check @bool_cross_empty_lr.
Check @bool_cross_empty_rl.

(** ** Positive controls for the headline artifacts *)

Check @SigmaCat.
Check @SigmaCat_inj.
Check @SigmaCat_case.
Check @SigmaCat_case_inj.
Check @SigmaCat_case_unique.
Check @SigmaCat_ump.
Check @ob_cast.
Check @mor_cast.

(** The hypothesis-free/hypothesis-bearing split, and the necessity
    theorem that makes the split principled rather than convenient. *)

Check @SigmaCat_inj_Full.
Check @sigma_inj_Full_forces_UIP.
Check @inj_Full_forces_UIP_at_One.
Check @SigmaCat_const_inj_Faithful.
Check @SigmaCat_inj_Faithful.
Check @Faithful_cancel.
Check @IdxUIP.

(** Non-vacuity. *)

Check @SigmaCat_empty_no_obj.
Check @SigmaCat_unit_iso.
Check @bool_summands_not_isomorphic.
Check @case_separates_summands.
Check @sigma_poly_unit_dec.

(** ** MEASURED RENAME-SIMULATION SCORE

    The constants the NEGATIVES name:

    Read off the `Fail` commands themselves, not off memory -- an
    earlier revision of this table was written from memory and got two
    of the three rows wrong, crediting Negative 1 with [SigmaCat] and
    [SigmaCat_inj] and Negative 2 with [homset], all three of which
    occur only in that section's positive CONTROLS:

      Negative 1 (:108) names [Type], [Category], [sigma_obj_unann]
      Negative 2 (:142) names [Category], [Functor_Setoid]
      Negative 3 (:189) names [Category], [obj], [SigmaCat], [BoolFam],
                        [eq_refl]

    Excluding core vocabulary ([Type], [Category], [obj], [eq_refl]) on
    the stated ground that it is named by almost every file in the tree
    rather than that it is hard to guard, and excluding the file-local
    [sigma_obj_unann] because renaming it renames both halves at once
    and so guards nothing, the constants a NEGATIVE names are THREE:
    [Functor_Setoid], [SigmaCat], [BoolFam].

    Each of the three is named by a positive control above.  Score:
    3/3, on an unpadded denominator, measured by compiling a renamed
    copy of this file against an instrument-checked baseline and
    confirming each one breaks it.  ([SigmaCat_inj] also breaks the
    file when renamed, via its controls; it is not counted here because
    no negative names it, and counting it was what padded the earlier
    4/4.) *)
