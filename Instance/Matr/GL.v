(** * GL_n and the units functor *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Matr.
Require Import Category.Instance.Matr.Determinant.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §I.3, printed p. 14 (PDF 24), and §I.4, printed p. 16
              (PDF 26) — maclane:I.3:construction2 (with
              maclane:I.4:construction1 completed by
              Instance/Matr/Determinant.v)
   nLab:      https://ncatlab.org/nlab/show/general+linear+group
   Wikipedia: https://en.wikipedia.org/wiki/General_linear_group

   Mac Lane's §I.3 example: for each n, sending a commutative ring K
   to the group GL_n(K) of invertible n × n matrices is a functor
   CRng ⟶ Grp, and so is sending K to its group of units K^*.  Both
   are instances of ONE construction — the group of units of a
   monoid, taken at the multiplicative monoid of K and at the matrix
   monoid (the endomorphism monoid of n in Matr K) — and a ring
   homomorphism acts entrywise.  The determinant connecting them is
   Instance/Matr/Determinant.v's, and the natural transformation
   det : GL_n ⟹ (−)^* is assembled where the two meet.

     - [UnitsOf]: the group of units of any [MonObject] — carrier the
       two-sided-invertible elements compared by their underlying
       element, inverse by swapping the witness — with [UnitsOf_map]:
       monoid homomorphisms restrict to unit groups
     - [Ring_mul_mon]: the multiplicative monoid of a ring
     - [Units_Functor]: (−)^* : CRng ⟶ Grp
     - [mat_mon]: the n × n matrix monoid over a ring, as the
       endomorphism monoid of n in [Matr] (Construction/Deloop.v's
       [hom_monoid] — cited, not rebuilt)
     - [mat_map_hom]: a ring homomorphism acts entrywise as a monoid
       homomorphism of matrix monoids
     - [GL_n]: the general linear group functor CRng ⟶ Grp

   Design:

   1. UNITS OF A MONOID, ONCE.  A unit carries its two-sided inverse
      as DATA together with both cancellation laws; two units are
      identified when their underlying elements are — the inverse is
      determined up to ≈ (Construction/Deloop.v's
      [mon_inverse_unique]), so comparing first components is the
      right setoid, and it is what makes every group law reduce to
      monoid algebra on underlying elements.  [GrpObject] here is
      Instance/Grp.v's record (minimal axioms, left laws only), not
      Construction/Deloop.v's.

   2. GL_n IS UNITS OF THE ENDOMORPHISM MONOID.  The n × n matrices
      over K form exactly [hom_monoid (Matr (ring_rig K)) n], so
      invertible matrices are [UnitsOf] of it, and functoriality in K
      is [UnitsOf_map] applied to the entrywise homomorphism — whose
      monoid laws are precisely "ring maps commute with the matrix
      product", [fin_sum] naturality plus preservation of the
      Kronecker delta.

   3. COMMUTATIVITY IS NOT USED HERE.  Both functors below are
      defined on CRng because that is where Mac Lane states them and
      where the determinant lives; nothing in THIS file consumes the
      commutativity witness (matrix multiplication over any ring has
      units).  The witness is consumed by Determinant.v. *)

(** ** The group of units of a monoid *)

Definition unit_carrier (M : MonObject) : Type :=
  { u : carrier M
  & { v : carrier M
    & (mon_op u v ≈ mon_unit) * (mon_op v u ≈ mon_unit) } }.

Program Definition UnitsOf (M : MonObject) : GrpObject := {|
  grp_setoid :=
    {| carrier := unit_carrier M;
       is_setoid := {| equiv := fun x y => `1 x ≈ `1 y |} |};
  grp_unit := (mon_unit; (mon_unit; (_, _)));
  grp_mul := fun x y =>
    (mon_op (`1 x) (`1 y); (mon_op (`1 (`2 y)) (`1 (`2 x)); (_, _)));
  grp_inv := fun x => (`1 (`2 x); (`1 x; (snd (`2 (`2 x)), fst (`2 (`2 x)))))
|}.
Next Obligation.
  intro M; equivalence.
Qed.
Next Obligation.
  intro M; apply mon_op_unit_l.
Qed.
Next Obligation.
  intro M; apply mon_op_unit_l.
Qed.
Next Obligation.
  (* (u·u')·(v'·v) ≈ 1 *)
  intros M [u [v [pl pr]]] [u' [v' [pl' pr']]]; simpl.
  rewrite <- mon_op_assoc.
  rewrite (mon_op_assoc u' v' v).
  rewrite pl'.
  rewrite mon_op_unit_l.
  exact pl.
Qed.
Next Obligation.
  (* (v'·v)·(u·u') ≈ 1 *)
  intros M [u [v [pl pr]]] [u' [v' [pl' pr']]]; simpl.
  rewrite <- mon_op_assoc.
  rewrite (mon_op_assoc v u u').
  rewrite pr.
  rewrite mon_op_unit_l.
  exact pr'.
Qed.
Next Obligation.
  intros M x y Hxy x' y' Hxy'; simpl.
  apply mon_op_respects; [ exact Hxy | exact Hxy' ].
Qed.
Next Obligation.
  intros M x y z; simpl.
  symmetry; apply mon_op_assoc.
Qed.
Next Obligation.
  intros M x; simpl.
  apply mon_op_unit_l.
Qed.
Next Obligation.
  intros M [u [v [pl pr]]]; simpl.
  exact pr.
Qed.

(* Monoid homomorphisms restrict to the unit groups: the image of a
   two-sided inverse is a two-sided inverse of the image. *)
Program Definition UnitsOf_map {M N : MonObject} (h : MonHom M N) :
  GrpHom (UnitsOf M) (UnitsOf N) := {|
  grp_map :=
    {| morphism := fun x =>
         (h (`1 x); (h (`1 (`2 x)); (_, _))) |}
|}.
Next Obligation.
  intros M N h [u [v [pl pr]]]; simpl.
  rewrite <- mon_map_op.
  rewrite pl.
  apply mon_map_unit.
Qed.
Next Obligation.
  intros M N h [u [v [pl pr]]]; simpl.
  rewrite <- mon_map_op.
  rewrite pr.
  apply mon_map_unit.
Qed.
Next Obligation.
  intros M N h x y Hxy; simpl.
  apply mon_map_respects; exact Hxy.
Qed.
Next Obligation.
  intros M N h; simpl.
  apply mon_map_unit.
Qed.
Next Obligation.
  intros M N h x y; simpl.
  apply mon_map_op.
Qed.

(** ** The units functor on commutative rings *)

(* The multiplicative monoid of a ring. *)
Program Definition Ring_mul_mon (K : RingObject) : MonObject := {|
  mon_setoid := rig_setoid (ring_rig K);
  mon_unit := rig_one (ring_rig K);
  mon_op := rig_mul (ring_rig K);
  mon_op_respects := rig_mul_respects (ring_rig K);
  mon_op_unit_l := rig_mul_one_l (ring_rig K);
  mon_op_unit_r := rig_mul_one_r (ring_rig K)
|}.
Next Obligation.
  intros K a b c; symmetry; apply rig_mul_assoc.
Qed.

(* A rig homomorphism is a monoid homomorphism of the multiplicative
   monoids. *)
Program Definition mul_MonHom {K K' : RingObject}
        (h : RigHom (ring_rig K) (ring_rig K')) :
  MonHom (Ring_mul_mon K) (Ring_mul_mon K') := {|
  mon_map := fun a => rig_map h a;
  mon_map_respects := proper_morphism (rig_map h)
|}.
Next Obligation.
  intros K K' h; apply rig_map_one.
Qed.
Next Obligation.
  intros K K' h a b; apply rig_map_mul.
Qed.

(* (−)^* : CRng ⟶ Grp — the group of units, functorially.  A CRng
   morphism is a Subcategory hom: the underlying RigHom carrying a
   (trivial) membership witness. *)
Program Definition Units_Functor : CRng ⟶ Grp := {|
  fobj := fun K => UnitsOf (Ring_mul_mon (`1 K));
  fmap := fun K K' h => UnitsOf_map (mul_MonHom (`1 h))
|}.
Next Obligation.
  intros K K' f g Hfg [u [v p]]; simpl.
  exact (Hfg u).
Qed.
Next Obligation.
  intros K [u [v p]]; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros K K' K'' f g [u [v p]]; simpl.
  reflexivity.
Qed.

(** ** The general linear group functor *)

(* The n × n matrix monoid over a ring: the endomorphism monoid of the
   object n of Matr. *)
Definition mat_mon (K : RingObject) (n : nat) : MonObject :=
  hom_monoid (Matr (ring_rig K)) n.

(* Ring maps commute with finite sums: Determinant.v's
   [rig_map_fin_sum] (consumed, not rebuilt). *)

(* Ring maps preserve the Kronecker delta. *)
Lemma rig_map_delta {K K' : RigObject} (h : RigHom K K')
      {n : nat} (i j : Fin.t n) :
  rig_map h (delta K i j) ≈ delta K' i j.
Proof.
  unfold delta.
  destruct (Fin.eq_dec i j).
  - apply rig_map_one.
  - apply rig_map_zero.
Qed.

(* A ring homomorphism acts entrywise on matrices, as a homomorphism
   of the matrix monoids: preservation of the identity is preservation
   of delta, and preservation of the product is fin_sum naturality
   plus preservation of + and ·. *)
Program Definition mat_map_hom {K K' : RingObject}
        (h : RigHom (ring_rig K) (ring_rig K')) (n : nat) :
  MonHom (mat_mon K n) (mat_mon K' n) := {|
  mon_map := fun A => (fun i j => rig_map h (A i j))
             : @Matrix (ring_rig K') n n
|}.
Next Obligation.
  intros K K' h n A B HAB i j; simpl.
  apply (proper_morphism (rig_map h)); exact (HAB i j).
Qed.
Next Obligation.
  intros K K' h n i j; simpl.
  apply rig_map_delta.
Qed.
Next Obligation.
  intros K K' h n A B i j; simpl.
  rewrite (rig_map_fin_sum K K' h).
  apply fin_sum_respects; intro l.
  apply rig_map_mul.
Qed.

(* GL_n : CRng ⟶ Grp — invertible n × n matrices, functorially. *)
Program Definition GL_n (n : nat) : CRng ⟶ Grp := {|
  fobj := fun K => UnitsOf (mat_mon (`1 K) n);
  fmap := fun K K' h => UnitsOf_map (mat_map_hom (`1 h) n)
|}.
Next Obligation.
  intros n K K' f g Hfg [A [B p]] i j; simpl.
  exact (Hfg (A i j)).
Qed.
Next Obligation.
  intros n K [A [B p]] i j; simpl.
  reflexivity.
Qed.
Next Obligation.
  intros n K K' K'' f g [A [B p]] i j; simpl.
  reflexivity.
Qed.

(** ** The determinant as a natural transformation *)

(* det restricted to the unit groups: an invertible matrix has a unit
   determinant — the inverse matrix's determinant inverts it, by
   multiplicativity and det of the identity. *)
Program Definition det_GrpHom (n : nat) (K : obj[CRng]) :
  GrpHom (UnitsOf (mat_mon (`1 K) n)) (UnitsOf (Ring_mul_mon (`1 K))) := {|
  grp_map := {| morphism := fun x =>
    (det (`1 K) (`1 x);
     (det (`1 K) (`1 (`2 x)); (_, _))) |}
|}.
Next Obligation.
  intros n K [A [B [pl pr]]]; simpl.
  rewrite <- (det_compose (`1 K) (`2 K) A B).
  etransitivity; [ apply (det_respects (`1 K)); exact pl | apply det_id ].
Qed.
Next Obligation.
  intros n K [A [B [pl pr]]]; simpl.
  rewrite <- (det_compose (`1 K) (`2 K) B A).
  etransitivity; [ apply (det_respects (`1 K)); exact pr | apply det_id ].
Qed.
Next Obligation.
  intros n K x y Hxy; simpl.
  apply (det_respects (`1 K)); exact Hxy.
Qed.
Next Obligation.
  intros n K; simpl.
  apply det_id.
Qed.
Next Obligation.
  intros n K x y; simpl.
  apply (det_compose (`1 K) (`2 K)).
Qed.

(* Mac Lane's §I.4 flagship: the determinant is a natural
   transformation det : GL_n ⟹ (−)^*.  Naturality in the ring is the
   reviewer's square det_{K'} ∘ GL_n f ≈ f^* ∘ det_K — the polynomial
   formula commutes with every ring homomorphism ([det_map]). *)
Program Definition det_Transform (n : nat) :
  GL_n n ⟹ Units_Functor := {|
  transform := fun K => det_GrpHom n K
|}.
Next Obligation.
  intros n K K' h [A [B p]]; simpl.
  apply (det_map (`1 K) (`1 K') (`1 h) A).
Qed.
Next Obligation.
  intros n K K' h [A [B p]]; simpl.
  symmetry.
  apply (det_map (`1 K) (`1 K') (`1 h) A).
Qed.
