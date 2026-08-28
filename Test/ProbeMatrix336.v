(** * Boundary probe for Structure/Bicartesian/Matrix.v (issue #336)

    The target MEASURES three boundaries and ships no [Fail] of its own.
    THIS FILE IS WHERE THEY ARE PINNED, so that a later edit which quietly
    makes one of them SUCCEED breaks the build instead of silently
    invalidating the target's header.

    TWO KINDS, kept lexically apart:

      * CONVERSION (negatives 1-2) -- [Fail Definition … := eq_refl].
        The Kronecker delta does not reduce to [id] on the diagonal even
        at closed indices, and the n-ary comparison is not convertible
        with the hand-written binary one.

      * FORMABILITY (negative 3) -- [Fail Check] under a declared
        [Constraint uh < up].  The target's [mat_entry] carries EXPLICIT
        universe binders; written WITHOUT them the same body elaborates
        at [Category@{uo uh uh}] and is then rejected at that setting.
        The annotation is therefore load-bearing, and the identification
        it removes was universe MINIMIZATION rather than content.

    Each negative was stripped of its [Fail] once and its failure KIND
    confirmed by reading the error TAIL, not by observing that it failed.
    The import list is the target's own; a shortened one would let these
    pass vacuously.  The measured rename-simulation score is at the end,
    over the constants the NEGATIVES name and no others. *)

Require Import Coq.Vectors.Fin.
Require Import Coq.Logic.Eqdep_dec.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Bicartesian.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.Semiadditive.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Instance.Coq.
Require Import Category.Structure.Bicartesian.Matrix.

Generalizable All Variables.

(** ** Instrument check: [Fail] is live in this file *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Negative 1 (CONVERSION): the Kronecker delta is not [id] on the
       diagonal, even at two closed indices

    The target locates the cause precisely: the BRANCH SELECTION does
    reduce -- which is why its [kron_off_computes] succeeds off the
    diagonal -- but the equality proof [Fin.eq_dec] returns is not
    [eq_refl], so the [eq_rect] transport in the diagonal branch is
    stuck.  That is a property of the DECIDER, not of [kron]. *)

Section KroneckerDiagonal.

Context {C : Category} (Z : @ZeroObject C) (fam : Fin.t 2 → C).

Fail Definition probe_kron_diag_computes :
  @kron C Z (Fin.t 2) fam Fin.eq_dec Fin.F1 Fin.F1 = id := eq_refl.

End KroneckerDiagonal.

(** ** Negative 2 (CONVERSION): the n-ary comparison is not the binary one

    They ARE equal at [≈] -- that is the target's
    [binary_can_is_can_comparison] -- but not convertible: [binary_can]
    is a cotuple of tuples produced by two descent data, while
    [can_comparison] is the hand-written [(id △ zero_mor) ▽ (zero_mor △ id)]. *)

Section BinaryComparison.

Context {C : Category} (Z : @ZeroObject C).
Context (CP : @Cartesian C) (CC : @Cocartesian C).
Context (x y : C).

Fail Definition probe_binary_can_is_can_comparison :
  @binary_can C Z CP CC x y = can_comparison x y := eq_refl.

End BinaryComparison.

(** ** Controls for the conversion negatives *)

Check @kron.
Check @kron_diag.
Check @kron_off.
Check @binary_can.
Check @can_comparison.
Check @binary_can_is_can_comparison.
Check @Fin.eq_dec.

(** ** Negative 3 (FORMABILITY, universe): the explicit binders on
       [mat_entry] are load-bearing

    A DIFFERENT KIND from 1-2.  [mat_entry] as SHIPPED is annotated
    [@{uo uh up uj uk}] with constraint block [uh <= up], keeping the
    category's hom and proof universes APART.  Written WITHOUT binders
    the same body minimizes to [Category@{uo uh uh}], and is then
    rejected where the annotated form is accepted. *)

Section UniverseMinimization.

Universe uo uh up.
Constraint uh < up.

Context (C : Category@{uo uh up}).

(* Controls: the ambient vocabulary IS formable at these levels, so the
   rejection below is about the unannotated definition and not about C. *)
Check (fun x y : C => x ~{C}~> y).
Check (fun (x y z : C) (f : x ~{C}~> y) (g : y ~{C}~> z) => g ∘ f).

(* Control: the SHIPPED, annotated [mat_entry] is formable here. *)
Check (fun (J K : Type) (g : J → C) (fm : K → C)
           (q p : C) (inj : ∀ j, g j ~{C}~> q)
           (proj : ∀ k, p ~{C}~> fm k) (u : q ~{C}~> p) (j : J) (k : K) =>
         @mat_entry C J K g fm q p inj proj u j k).

(* The negative: the same body with the binders dropped.  Written as an
   unannotated local definition, elaboration minimizes its category to
   [Category@{uo uh uh}] and it cannot be applied to C. *)
Definition mat_entry_unannotated {D : Category}
  {J K : Type} {g : J → D} {fm : K → D} {q p : D}
  (inj : ∀ j, g j ~{D}~> q) (proj : ∀ k, p ~{D}~> fm k)
  (u : q ~{D}~> p) (j : J) (k : K) : g j ~{D}~> fm k :=
  proj k ∘ u ∘ inj j.

Fail Check (fun (J K : Type) (g : J → C) (fm : K → C)
                (q p : C) (inj : ∀ j, g j ~{C}~> q)
                (proj : ∀ k, p ~{C}~> fm k) (u : q ~{C}~> p) (j : J) (k : K) =>
              @mat_entry_unannotated C J K g fm q p inj proj u j k).

End UniverseMinimization.

(** ** Controls naming the constants of negative 3 *)

Check @mat_entry.
Check @mat_entry_unfold.

(** ** Controls for the delivered results *)

Check @matrix_ext.
Check @matrix_determined.
Check @matrix_mor.
Check @matrix_entry.
Check @matrix_ump.
Check @matrix_mor_entry.
Check @can_matrix.
Check @can_matrix_diag.
Check @can_matrix_off.
Check @can_matrix_unique.
Check @can_matrix_ump.
Check @indexed_inj_Section.
Check @indexed_inj_SplitMono.
Check @indexed_inj_Monic.
Check @inl_Section.
Check @inr_Section.
Check @inl_Monic.
Check @inr_Monic.
Check @fin_matrix.
Check @fin_matrix_entry.
Check @fin_matrix_ext.

(** ** Exercise 3.1.ix, witnessed at a concrete category

    Structure/Bicartesian/Matrix.v proves the injection results as
    CONDITIONALS on a zero object plus coproducts, and instantiates them
    at no concrete category -- its own witness category [Coq] has no zero
    object.  The tree has six registered [ZeroObject] instances, and [Ab]
    supplies both hypotheses as exported instances, so the witness is pure
    instantiation with no new proof.

    It is shipped HERE rather than in the target for a measured reason:
    [Instance/Ab] is not in that file's dependency closure (0 of 19
    modules) while Instance/Ab/Coproduct.v's own closure is 17, so
    importing it there would nearly double a [Structure/] file's footprint
    for two [Example]s.  A probe is a leaf and pays no such cost.

    Identified by the fess audit of this commit, which compiled it
    independently before it was added here. *)

Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.

Example ab_inl_Section (x y : Ab) : Section (@inl Ab Ab_Cocartesian x y) :=
  inl_Section x y.

Example ab_inl_Monic (x y : Ab) : Monic (@inl Ab Ab_Cocartesian x y) :=
  inl_Monic x y.

Example ab_inr_Monic (x y : Ab) : Monic (@inr Ab Ab_Cocartesian x y) :=
  inr_Monic x y.

(** ** MEASURED RENAME-SIMULATION SCORE

    The constants the NEGATIVES name:

      Negative 1: [kron]
      Negative 2: [binary_can], [can_comparison]
      Negative 3: [mat_entry_unannotated] (declared HERE, so a rename of
                  it is not a tree edit and is excluded), with [mat_entry]
                  named by its own positive control

    That is THREE renameable tree constants: [kron], [binary_can],
    [can_comparison].  The denominator is NOT padded with control-only
    names -- [kron_diag], [kron_off], [mat_entry], [mat_entry_unfold] and
    everything under "Controls for the delivered results" appear in no
    [Fail] here and are deliberately EXCLUDED.

    [Fin.eq_dec] is excluded on a DIFFERENT ground, and an earlier draft
    of this paragraph gave a false one: it listed [Fin.eq_dec] among the
    names appearing in no [Fail], but negative 1 names it.  The real
    ground is that it is a STDLIB constant, not a renameable constant of
    this tree, so renaming it is not an edit this simulation is meant to
    catch; it has its own [Check] control above regardless.  Excluding it
    therefore UNDERSTATES the score rather than padding it. *)
