(** * Products of categories subsume the classical products *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Product.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Cat.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §II.3 Exercise 1, printed p. 39 (PDF p. 49) — maclane:II.3:ex1
   nLab:      https://ncatlab.org/nlab/show/product+category

   Mac Lane's exercise: the product of categories restricts, along the
   standard full embeddings, to the familiar products of algebraic
   structures — a note carried here in prose, as the exercise states it:
   no Mon ⟶ Cat or Set ⟶ Cat embedding functor exists in-tree yet, and
   the three isomorphisms below are their object-level content —
   delooped monoids (and groups) multiply componentwise, and discrete
   categories multiply as sets.  Three specializations, each an
   isomorphism in [Cat] (up to the natural isomorphisms of
   [Functor_Setoid], the library's hom-equivalence there — in this
   library the strength of an equivalence of categories, per
   Instance/Cat.v's header; the issue's StrictCat alternative is not
   taken, though the discrete case is morally strict, because strict
   functor equality would need the transport machinery of
   Functor_StrictEq, out of proportion for this exercise):

     - [Deloop_prod_iso]   : Deloop (M × N) ≅ Deloop M ∏ Deloop N
     - [Deloop_grp_prod]   : the same statement read at product groups —
                             the monoid part of [GrpObject_prod] IS
                             [MonObject_prod] definitionally, so the
                             isomorphism is literally the same term
     - [Discrete_Product]  : DiscreteCat (A * B) ≅ DiscreteCat A ∏
                             DiscreteCat B

   Design:

   1. THE HOM-SIDES ARE DEFINITIONALLY EQUAL.  A hom of
      [Deloop (MonObject_prod M N)] is an element of [carrier M * carrier N],
      and a hom of [Deloop M ∏ Deloop N] is exactly the same pair type; both
      functors of [Deloop_prod_iso] are the identity on arrows, and the
      whole isomorphism is object-side bookkeeping about [poly_unit]
      (whose two-component tuples are collapsed by unit-morphism
      conjugation, not by eta).  Likewise [Discrete_Product]'s object
      types agree on the nose — [A * B] both times — and only the
      MORPHISM encodings differ: one equality of pairs versus a pair of
      equalities, converted by [f_equal] projections one way and the
      local transparent [pair_eta]/[pair_equal] kit the other — local
      because the stdlib's [surjective_pairing] and [f_equal2] are
      opaque, and an arrow action built on them would be stuck,
      sinking every functor law.

   2. NO UIP.  [DiscreteCat]'s hom-setoid is strict equality of equality
      proofs, so the functor laws and round trips are equations between
      proof terms; each is closed by destructing the objects (exposing
      the pairs) and then the morphisms (collapsing to [eq_refl]),
      never by an axiom.  [Print Assumptions] on every artifact here is
      closed under the global context.

   3. THE GROUP CASE IS A RESTRICTION, NOT A SECOND PROOF.  [Deloop]
      consumes only the monoid part, and [GrpObject_prod] is built so
      its [grp_monoid] projection is [MonObject_prod] of the parts by
      [eq_refl]; Mac Lane's "the same statement restricted to groups"
      is therefore delivered by applying [Deloop_prod_iso] at the
      underlying monoids, with the componentwise inverse supplied only
      to close the group structure itself.

   4. NAMESPACE NOTE.  [MonObject]/[GrpObject] here are
      Construction/Deloop.v's setoid records; Instance/Grp.v defines a
      DIFFERENT record also named [GrpObject] (with carrier-level
      fields) and already carries its own componentwise [Grp_product]
      with projections and [Grp_Cartesian].  The two products live at
      different layers and neither subsumes the other; this file's is
      the one the delooping dictionary consumes. *)


(** ** The product monoid, and the product group *)

(* The product setoid is Lib/Datatypes.v's [prod_setoid], the same idiom
   Instance/Grp.v's [Grp_product] uses — reusing it keeps the registered
   [Proper] instances ([pair_respects], [fst_respects], [snd_respects])
   applicable to the product carrier. *)
Definition prod_SetoidObject (M N : MonObject) : SetoidObject := {|
  carrier := carrier M * carrier N;
  is_setoid := @prod_setoid _ _ (is_setoid M) (is_setoid N)
|}.

Program Definition MonObject_prod (M N : MonObject) : MonObject := {|
  mon_setoid := prod_SetoidObject M N;
  mon_unit := (mon_unit, mon_unit);
  mon_op := fun p q => (mon_op (fst p) (fst q), mon_op (snd p) (snd q))
|}.
Next Obligation.
  intros M N p p' [Hp1 Hp2] q q' [Hq1 Hq2]; split; simpl.
  - exact (mon_op_respects M _ _ Hp1 _ _ Hq1).
  - exact (mon_op_respects N _ _ Hp2 _ _ Hq2).
Qed.
Next Obligation.
  intros M N a b c; split; simpl; apply mon_op_assoc.
Qed.
Next Obligation.
  intros M N a; split; simpl; apply mon_op_unit_l.
Qed.
Next Obligation.
  intros M N a; split; simpl; apply mon_op_unit_r.
Qed.

Program Definition GrpObject_prod (G H : GrpObject) : GrpObject := {|
  grp_monoid := MonObject_prod G H;
  grp_inv := fun p => (grp_inv (fst p), grp_inv (snd p))
|}.
Next Obligation.
  intros G H a; split; simpl; apply grp_inv_l.
Qed.
Next Obligation.
  intros G H a; split; simpl; apply grp_inv_r.
Qed.

Example GrpObject_prod_monoid (G H : GrpObject) :
  grp_monoid (GrpObject_prod G H) = MonObject_prod G H := eq_refl.

(** ** Delooping preserves products *)

(* Both functors are the identity on arrows (design note 1); only the
   single objects need shuttling. *)
Program Definition Deloop_prod_to (M N : MonObject) :
  Deloop (MonObject_prod M N) ⟶ Deloop M ∏ Deloop N := {|
  fobj := fun _ => (ttt, ttt);
  fmap := fun _ _ p => p
|}.
Next Obligation.
  intros M N x y p q Hpq; exact Hpq.
Qed.
Next Obligation.
  intros M N x; simpl; split; reflexivity.
Qed.
Next Obligation.
  intros M N x y z p q; simpl; split; reflexivity.
Qed.

Program Definition Deloop_prod_from (M N : MonObject) :
  Deloop M ∏ Deloop N ⟶ Deloop (MonObject_prod M N) := {|
  fobj := fun _ => ttt;
  fmap := fun _ _ p => p
|}.
Next Obligation.
  intros M N x y p q Hpq; exact Hpq.
Qed.
Next Obligation.
  intros M N x; simpl; split; reflexivity.
Qed.
Next Obligation.
  intros M N x y z p q; simpl; split; reflexivity.
Qed.

(* The isomorphism in Cat: the composites are the identity on arrows, and
   the object round trips are closed by unit-morphism conjugation. *)
Program Definition Deloop_prod_iso (M N : MonObject) :
  Deloop (MonObject_prod M N) ≅[Cat] Deloop M ∏ Deloop N := {|
  to   := Deloop_prod_to M N;
  from := Deloop_prod_from M N
|}.
Next Obligation.
  intros M N; unshelve eexists.
  - intros [a b].
    unshelve refine
      (@Build_Isomorphism (Deloop M ∏ Deloop N) (ttt, ttt) (a, b)
         (mon_unit, mon_unit) (mon_unit, mon_unit) _ _).
    + split; simpl; apply mon_op_unit_l.
    + split; simpl; apply mon_op_unit_l.
  - intros [a b] [c d] [f g]; simpl; split;
    exact (symmetry
             (transitivity (mon_op_unit_r _) (mon_op_unit_l _))).
Qed.
Next Obligation.
  intros M N; unshelve eexists.
  - intros x.
    unshelve refine
      (@Build_Isomorphism (Deloop (MonObject_prod M N)) ttt x
         (mon_unit, mon_unit) (mon_unit, mon_unit) _ _).
    + split; simpl; apply mon_op_unit_l.
    + split; simpl; apply mon_op_unit_l.
  - intros x y p; simpl; split;
    exact (symmetry
             (transitivity (mon_op_unit_r _) (mon_op_unit_l _))).
Qed.

(* Mac Lane's "the group case is the same statement restricted to groups":
   the isomorphism at product groups is the monoid isomorphism verbatim,
   because [Deloop] consumes only the monoid part (design note 3). *)
Definition Deloop_grp_prod (G H : GrpObject) :
  Deloop (GrpObject_prod G H) ≅[Cat] Deloop G ∏ Deloop H :=
  Deloop_prod_iso G H.

(** ** Discrete categories multiply as sets *)

Program Definition Discrete_Product_to (A B : Type) :
  DiscreteCat (A * B) ⟶ DiscreteCat A ∏ DiscreteCat B := {|
  fobj := fun p => p;
  fmap := fun x y e => (f_equal fst e, f_equal snd e)
|}.
Next Obligation.
  intros A B x; simpl; split; reflexivity.
Qed.
Next Obligation.
  intros A B x y z e e'; simpl.
  destruct e, e'; simpl; split; reflexivity.
Qed.

(* Transparent equality kit for pairs: the stdlib's [surjective_pairing]
   and [f_equal2] are opaque, which would leave the arrow action stuck
   and sink every functor law; these compute. *)
Definition pair_eta {A B : Type} (p : A * B) : p = (fst p, snd p) :=
  match p with (a, b) => eq_refl end.

Definition pair_equal {A B : Type} {a c : A} {b d : B}
  (e1 : a = c) (e2 : b = d) : (a, b) = (c, d) :=
  match e1 in _ = c', e2 in _ = d' return (a, b) = (c', d') with
  | eq_refl, eq_refl => eq_refl
  end.

Program Definition Discrete_Product_from (A B : Type) :
  DiscreteCat A ∏ DiscreteCat B ⟶ DiscreteCat (A * B) := {|
  fobj := fun p => p;
  fmap := fun x y e =>
    eq_trans (pair_eta x)
      (eq_trans (pair_equal (fst e) (snd e))
         (eq_sym (pair_eta y)))
|}.
Next Obligation.
  intros A B x y e e' He; simpl in *.
  destruct He as [He1 He2]; simpl in *.
  rewrite He1, He2; reflexivity.
Qed.
Next Obligation.
  intros A B [a b]; simpl; reflexivity.
Qed.
Next Obligation.
  intros A B [a b] [c d] [e f] p q; simpl.
  destruct p as [p1 p2], q as [q1 q2]; simpl in *.
  destruct p1, p2, q1, q2; simpl; reflexivity.
Qed.

Program Definition Discrete_Product (A B : Type) :
  DiscreteCat (A * B) ≅[Cat] DiscreteCat A ∏ DiscreteCat B := {|
  to   := Discrete_Product_to A B;
  from := Discrete_Product_from A B
|}.
Next Obligation.
  intros A B; exists (fun p => iso_id).
  intros [a b] [c d] [e1 e2]; simpl in *.
  destruct e1, e2; simpl; split; reflexivity.
Qed.
Next Obligation.
  intros A B; exists (fun x => iso_id).
  intros x y e; simpl.
  destruct e; simpl.
  destruct x; simpl; reflexivity.
Qed.

(** ** Witnesses *)

(* The product monoid computes at Construction/Deloop.v's inhabitants,
   and the discrete comparison is the identity on a concrete pair. *)
Example MonObject_prod_computes :
  @mon_op (MonObject_prod Nat_Plus Bool_Xor) (3%nat, true) (2%nat, true)
    = (5%nat, false) := eq_refl.

Example Discrete_Product_computes :
  fobj[to (Discrete_Product bool nat)] (true, 7%nat)
    = (true, 7%nat) := eq_refl.
