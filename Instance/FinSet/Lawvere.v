Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Lawvere.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.FinSet.

Generalizable All Variables.

(** * FinSet^op as a Lawvere theory

    The base example: [FinSet^op] is the Lawvere theory of EQUALITY — the
    theory with no operations and no equations, of which every presented
    theory is a quotient-extension.  Classically, every Lawvere theory
    receives an (identity-on-naturals) theory morphism from this one —
    the initiality that puts it at the base of the functorial-semantics
    development.  Theory morphisms are not formalized in-tree, so that
    remark is orienting context, not a citation of an artifact.

    The structure is pure bookkeeping over [Instance/FinSet.v]:

    - [Structure/Initial.v] defines [Initial C] as literal NOTATION for
      [@Terminal (C^op)], so [FinSet_Initial] IS the terminal-object
      structure of [FinSet^op]: its terminal object is [0%nat].

    - [Structure/Cocartesian.v] defines [Cocartesian C] as literal
      NOTATION for [@Cartesian (C^op)], so [FinSet_Cocartesian] IS the
      cartesian structure of [FinSet^op]: its product object on [m], [n]
      is [(m + n)%nat] definitionally.

    Consequently BOTH strictness equalities of [LawvereTheory] compute:
    [law_zero_terminal] and [law_plus_product] are each [eq_refl], the
    latter even at open variables [m n], because [FinSet_Cocartesian]'s
    [product_obj] is the function [fun m n => (m + n)%nat]. *)

Definition FinSetOp_Lawvere : LawvereTheory := {|
  law_cat := FinSet^op;
  law_terminal := FinSet_Initial;
  law_cartesian := FinSet_Cocartesian;
  law_of_nat := fun n => n;
  law_zero_terminal := eq_refl;
  law_plus_product := fun m n => eq_refl
|}.
