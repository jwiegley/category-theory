(** * Boundary probe for Structure/Limit/Product/Finite.v (issue #335)

    Structure/Limit/Product/Finite.v measures ten refutations -- seven
    CONVERSION failures and three FORMABILITY (universe) rejections -- and
    ships no [Fail] of its own.  THIS FILE IS WHERE THEY ARE PINNED, so
    that a later edit which quietly makes one of them SUCCEED breaks the
    build instead of silently invalidating the target's header.  (An
    earlier draft of this paragraph said the ten were "checked in scratch
    files outside the tree" and that the target "pins none of them".  That
    described the state BEFORE this file existed, and both files ship in
    one commit; the target's header names this probe.)

    TWO KINDS, kept lexically apart:

      * CONVERSION (negatives 1-7) -- [Fail Definition … := eq_refl].
        The fold pads with the terminal object and the round trip through
        [HasFiniteProducts] does not return its inputs on the nose.

      * FORMABILITY (negatives 8-10) -- [Fail Check] under a declared
        [Constraint uh < up].  Each of [Cartesian], [Terminal] and
        [IsIndexedProduct] independently identifies the hom and proof
        universes; NO ONE of them is "the" cause, which is why all three
        are pinned rather than one.

    Every negative was stripped of its [Fail] once and its failure KIND
    confirmed -- "cannot unify" for 1-7, "universe inconsistency" for
    8-10.  The instrument check below guarantees [Fail] is live.  The
    import list is the target's own; a shortened one would let these pass
    vacuously.  The measured rename-simulation score is at the end, over
    the constants the NEGATIVES name and no others. *)

Require Import Coq.Vectors.Fin.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Instance.Coq.
Require Import Category.Structure.Limit.Product.Finite.

Generalizable All Variables.

(** ** Instrument check: [Fail] is live in this file *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

Section Conversions.

Context {C : Category}.
Context (CP : @Cartesian C) (T : @Terminal C).
Context (x y z : C) (f1 : Fin.t 1 → C) (f2 : Fin.t 2 → C).

(** ** Negative 1 (CONVERSION): the unary fold keeps its terminal pad *)

Fail Definition probe_fin_prod_one :
  @fin_prod C CP T 1 f1 = f1 Fin.F1 := eq_refl.

(** ** Negative 2 (CONVERSION): the binary fold keeps its terminal pad *)

Fail Definition probe_fin_prod_two :
  @fin_prod C CP T 2 f2 = (f2 Fin.F1 × f2 (Fin.FS Fin.F1))%object := eq_refl.

(** ** Negative 3 (CONVERSION): out to the class and back pads the product *)

Fail Definition probe_roundtrip_product_obj :
  @product_obj C (HasFiniteProducts_Cartesian
                    (Cartesian_Terminal_HasFiniteProducts CP T)) x y
  = (x × y)%object := eq_refl.

(** ** Negative 4 (CONVERSION): the recovered [Cartesian] is not the input *)

Fail Definition probe_roundtrip_cartesian :
  HasFiniteProducts_Cartesian (Cartesian_Terminal_HasFiniteProducts CP T)
  = CP := eq_refl.

(** ** Negative 5 (CONVERSION): the recovered [Terminal] is not the input *)

Fail Definition probe_roundtrip_terminal :
  HasFiniteProducts_Terminal (Cartesian_Terminal_HasFiniteProducts CP T)
  = T := eq_refl.

(** ** Negative 6 (CONVERSION): the whole round trip is not the identity

    Negative 3 propagated, not an independent fact -- the target's header
    says so, and it is pinned separately because a repair to 3 need not
    repair this one. *)

Fail Definition probe_roundtrip_whole :
  Cartesian_Terminal_HasFiniteProducts
    (HasFiniteProducts_Cartesian
       (Cartesian_Terminal_HasFiniteProducts CP T))
    (HasFiniteProducts_Terminal
       (Cartesian_Terminal_HasFiniteProducts CP T))
  = Cartesian_Terminal_HasFiniteProducts CP T := eq_refl.

(** ** Negative 7 (CONVERSION): right fold and left fold differ

    This is why [awodey_fold_iso] is an isomorphism and nothing stronger. *)

Fail Definition probe_right_vs_left_fold :
  @fin_prod C CP T 3 (fin3 x y z) = awodey_prod CP x y z := eq_refl.

End Conversions.

(** ** Controls for the conversion negatives

    Each names constants the negatives above name. *)

Check @fin_prod.
Check @fin_proj.
Check @fin3.
Check @awodey_prod.
Check @awodey_fold_iso.
Check @HasFiniteProducts.
Check @HasFiniteProducts_Cartesian.
Check @HasFiniteProducts_Terminal.
Check @Cartesian_Terminal_HasFiniteProducts.
Check @product_obj.

(** ** Positive identifications, pinned beside their refutations

    The target's header measured these outside the tree.  They are the
    POSITIVE counterparts of negatives 3-5, and pinning both halves is
    what makes the boundary exact -- in particular the [Terminal] RECORD
    is not recovered (negative 5) while the terminal OBJECT is (below). *)

Section Positives.

Context {C : Category}.
Context (CP : @Cartesian C) (T : @Terminal C).
Context (x y : C) (n : nat) (f : Fin.t n → C).

Example probe_class_returns_the_fold :
  @finite_product C (Cartesian_Terminal_HasFiniteProducts CP T) n f
  = @fin_prod C CP T n f := eq_refl.

Example probe_class_returns_the_projections :
  @finite_product_proj C (Cartesian_Terminal_HasFiniteProducts CP T) n f
  = @fin_proj C CP T n f := eq_refl.

Example probe_terminal_obj_is_recovered :
  @terminal_obj C
    (HasFiniteProducts_Terminal (Cartesian_Terminal_HasFiniteProducts CP T))
  = @terminal_obj C T := eq_refl.

Example probe_padded_product_is_what_it_is :
  @product_obj C (HasFiniteProducts_Cartesian
                    (Cartesian_Terminal_HasFiniteProducts CP T)) x y
  = (x × (y × 1))%object := eq_refl.

End Positives.

(** ** Negatives 8-10 (FORMABILITY, universe)

    A DIFFERENT KIND from 1-7.  With C's hom universe declared strictly
    below its proof universe, all three donors are rejected -- so the
    hom-and-proof identification the target inherits has three
    independent sources and cannot be attributed to any single one. *)

Section UniverseIdentification.

Universe uo uh up.
Constraint uh < up.

Context (C : Category@{uo uh up}).

(* Control: naming a hom at these levels IS formable, so the rejections
   below are about the three donors and not about C itself. *)
Check (fun x y : C => x ~{C}~> y).

Fail Check (@Cartesian C).
Fail Check (@Terminal C).
(* The category argument is given EXPLICITLY.  Written with [C] left
   implicit, this [Fail] fired on an unresolved evar ("expected to have
   type A → obj[?C]") rather than on the universe identification -- a
   FALSE GUARD, caught by stripping the [Fail] and reading the error
   KIND rather than merely observing that it failed. *)
Fail Check (fun (A : Type) (f : A → C) (p : C)
                (pr : ∀ a, p ~{C}~> f a) =>
              @IsIndexedProduct C A f p pr).

End UniverseIdentification.

(** ** Controls naming the three donors *)

Check @Cartesian.
Check @Terminal.
Check @IsIndexedProduct.

(** ** Controls for the delivered results *)

Check @fin_IsIndexedProduct.
Check @Cartesian_Terminal_HasFiniteProducts.
Check @HasFiniteProducts_iff.
Check @iprod_unique_iso.
Check @fin_prod_unique_iso.
Check @awodey_IsIndexedProduct.
Check @fin_zero_IsTerminalObj.
Check @fin_two_IsCartesianProduct.
Check @fin_coprod.
Check @HasFiniteCoproducts.
(* NOTE: written WITHOUT the [@].  Structure/Cocartesian.v:117 declares
   [Notation "@Cocartesian C"], which captures [@Cocartesian_Initial_...]
   and fails with "The reference _Initial_HasFiniteCoproducts was not
   found".  The bare name parses; measured both ways. *)
Check Cocartesian_Initial_HasFiniteCoproducts.

(** ** MEASURED RENAME-SIMULATION SCORE

    The constants the NEGATIVES name:

      Negatives 1-2:  [fin_prod]
      Negative  3:    [product_obj], [HasFiniteProducts_Cartesian],
                      [Cartesian_Terminal_HasFiniteProducts]
      Negatives 4-6:  [HasFiniteProducts_Terminal] (with the above)
      Negative  7:    [fin3], [awodey_prod]
      Negatives 8-10: [Cartesian], [Terminal], [IsIndexedProduct]

    That is TEN.  The denominator is not padded with control-only names:
    [fin_proj], [awodey_fold_iso], [HasFiniteProducts] and every constant
    under "Controls for the delivered results" appear in NO [Fail] here
    and are deliberately EXCLUDED from the score. *)
