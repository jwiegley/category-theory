Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Monad.Graded.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.

Generalizable All Variables.

(** * Rig connections: AndGrade, and the FinSet shadow

    The two reconciliations Theory/Algebra/Rig.v's header promises, kept
    in a companion file so the algebra spine does not import the graded
    monad machinery or the skeletal finite sets.

    ANDGRADE.  Monad/Graded.v's [AndGrade] is the grading monoid
    (bool, true, andb) of the exception-graded monad.  It is literally
    the multiplicative half of [Bool_Rig] — same carrier, same unit, same
    operation, on the nose — so the two developments cannot drift.

    THE FINSET SHADOW (Example 5.37, categorified).  On the skeletal
    [FinSet] the objects are literally the naturals, the coproduct object
    of m and n is [m + n] and the product object is [m * n]
    (Instance/FinSet.v's [FinSet_Cocartesian],
    Instance/FinSet/Product.v's [FinSet_Cartesian]).  The rig operations
    of [Nat_Rig] therefore agree definitionally with the object actions
    of the (co)cartesian structure: the rig of naturals is the
    decategorified shadow of finite sets under disjoint union and
    cartesian product — the direction of agreement the issue asks to
    record.  (The converse packaging — that the BiCCC isomorphisms of
    Structure/BiCCC.v descend to the equations of [Nat_Rig] along
    skeletality — is the deeper statement and remains outside this
    file's scope.) *)

(** ** AndGrade is the multiplicative half of Bool_Rig *)

Example Bool_Rig_carrier_AndGrade : carrier (rig_setoid Bool_Rig) = grade AndGrade
  := eq_refl.
Example Bool_Rig_one_AndGrade : rig_one Bool_Rig = gunit AndGrade := eq_refl.
Example Bool_Rig_mul_AndGrade : rig_mul Bool_Rig = gmul AndGrade := eq_refl.

(** ** Nat_Rig is the object-level shadow of FinSet *)

(* The coproduct object of FinSet is rig addition, on the nose. *)
Example Nat_Rig_add_FinSet_coproduct (m n : nat) :
  @product_obj _ FinSet_Cocartesian m n = rig_add Nat_Rig m n := eq_refl.

(* The product object of FinSet is rig multiplication, on the nose. *)
Example Nat_Rig_mul_FinSet_product (m n : nat) :
  @product_obj _ FinSet_Cartesian m n = rig_mul Nat_Rig m n := eq_refl.

(* The empty and singleton finite sets are the rig units. *)
Example Nat_Rig_zero_FinSet : rig_zero Nat_Rig = 0%nat := eq_refl.
Example Nat_Rig_one_FinSet : rig_one Nat_Rig = 1%nat := eq_refl.

(** ** An independent witness for the converse bridge direction

    [EndRig] applied to a preadditive category the Rig development did
    not itself build: Instance/CMon/Biproduct.v's [CMon_Preadditive].
    Every commutative monoid M thus yields the rig of its monoid
    endomorphisms — addition pointwise, multiplication composition —
    inhabiting the converse direction of the bridge away from the
    delooping it would otherwise be tested on. *)
Definition CMon_EndRig (M : CMonObject) : RigObject :=
  EndRig CMon_Preadditive M.
