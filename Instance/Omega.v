Require Import Category.Lib.
Require Import Category.Theory.Category.

Generalizable All Variables.

(** * The ordinal ω as a thin category *)

(* nLab:      https://ncatlab.org/nlab/show/interval+category
   Wikipedia: https://en.wikipedia.org/wiki/Total_order

   [Omega] is the thin category whose objects are the natural numbers and whose
   morphisms [m ~> n] are proofs of [m ≤ n].  It is the shape category over which
   Adámek's initial-algebra chain [Instance ... Construction/Chain.v] is indexed:
   a functor [Omega ⟶ C] is exactly an ω-indexed diagram
   [X₀ ~> X₁ ~> X₂ ~> ...] in [C].

   The order is carried by a bespoke [Type]-valued relation [le_t] rather than
   the standard library's [le].  Two reasons: (1) [le] is [Prop]-valued and
   cannot eliminate into the [Type]-valued hom-sets of an arbitrary target
   category, which [Construction/Chain.v]'s [chain_hom] requires; (2) avoiding
   the stdlib keeps this file portable across Coq 8.19/8.20 and Rocq 9.1, whose
   [le] lemma names differ.  The explicit universe annotations
   ([le_t@{h}], [Morphism_equality@{o h p}]) are load-bearing: under the
   library-wide [Set Universe Polymorphism] a strictly-bound [Omega@{o h p}]
   must instantiate every polymorphic constant it mentions, exactly as
   [Instance/One.v] writes [Morphism_equality@{o h p}] and [poly_unit@{o}]. *)

Inductive le_t@{u} (n : nat) : nat → Type@{u} :=
  | le_t_n : le_t n
  | le_t_S {m} : le_t m → le_t (S m).

Arguments le_t_n {n}.
Arguments le_t_S {n m} _.

(* Transitivity, by recursion on the second derivation, so that composition in
   [Omega] reduces on closed inputs (needed by [chain_hom]). *)
Fixpoint le_t_trans@{u} {m n k} (f : le_t@{u} m n) (g : le_t@{u} n k) :
  le_t@{u} m k :=
  match g in le_t _ k' return le_t@{u} m k' with
  | le_t_n     => f
  | le_t_S g'  => le_t_S (le_t_trans f g')
  end.

(* Reflexivity is a strict left unit for [le_t_trans] by the [le_t_n] branch. *)
Lemma le_t_trans_id_l@{u} {m n} (f : le_t@{u} m n) :
  le_t_trans f le_t_n = f.
Proof. reflexivity. Qed.

Lemma le_t_trans_id_r@{u} {m n} (f : le_t@{u} m n) :
  le_t_trans le_t_n f = f.
Proof.
  induction f as [| n' f' IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma le_t_trans_assoc@{u} {m n k l}
  (f : le_t@{u} m n) (g : le_t@{u} n k) (h : le_t@{u} k l) :
  le_t_trans (le_t_trans f g) h = le_t_trans f (le_t_trans g h).
Proof.
  induction h as [| l' h' IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Program Definition Omega@{o h p} : Category@{o h p} := {|
  obj     := nat;
  hom     := le_t@{h};
  homset  := Morphism_equality@{o h p};
  id      := fun _ => le_t_n@{h};
  compose := fun _ _ _ f g => le_t_trans@{h} g f
|}.
Solve All Obligations with
  (simpl; intros; try subst;
   rewrite ?le_t_trans_id_l, ?le_t_trans_id_r, ?le_t_trans_assoc;
   try reflexivity).

(* The generating step morphism [n ~> S n]. *)
Definition omega_step (n : nat) : @hom Omega n (S n) := le_t_S le_t_n.
