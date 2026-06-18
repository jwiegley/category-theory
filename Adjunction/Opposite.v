Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(** * The opposite (dual) of a hom-set adjunction: F ⊣ U yields U^op ⊣ F^op. *)

(* nLab: https://ncatlab.org/nlab/show/adjoint+functor
   Wikipedia: https://en.wikipedia.org/wiki/Adjoint_functors

   An adjunction F ⊣ U (here F : D ⟶ C left, U : C ⟶ D right) is given in
   hom-set form by a natural family adj {x y} : (F x ~{C}~> y) ≊ (x ~{D}~> U y).
   Passing to opposite categories reverses every hom-set, so the left and right
   roles exchange: the dual is U^op ⊣ F^op, with U^op : C^op ⟶ D^op now the
   left adjoint and F^op : D^op ⟶ C^op the right adjoint. Concretely the dual
   iso at (x y), with x an object of C and y an object of D, has type
   (U^op x ~{D^op}~> y) ≊ (x ~{C^op}~> F^op y), which unfolds the reversed
   hom-sets to (y ~{D}~> U x) ≊ (F y ~{C}~> x). That is exactly the original
   adj at swapped arguments (y x), read backwards: so [to] of the dual is
   [from] of [adj y x] and [from] of the dual is [to] of [adj y x]. Both nLab
   (see its "Opposite adjoint functors" section) and Wikipedia state this
   flip; nLab phrases it as Hom_{D^op}(-, U^op -) ≃ Hom_{C^op}(F^op -, -).

   The four naturality fields transport accordingly. Because the dual swaps the
   two transposes (to ↔ from) and op reverses composition so the two hom-set
   arguments trade roles (left ↔ right), each field is supplied by the original
   field of the opposite kind and side: to_adj_nat_l from from_adj_nat_r,
   to_adj_nat_r from from_adj_nat_l, and dually for the from-side fields. *)

Program Definition Opposite_Adjunction `(F : D ⟶ C) `(U : C ⟶ D)
        (A : F ⊣ U) :
  U^op ⊣ F^op := {|
  adj := fun x y =>
    {| to          := from (@adj _ _ _ _ A y x)
     ; from        := to (@adj _ _ _ _ A y x)
     ; iso_to_from := iso_from_to (@adj _ _ _ _ A y x)
     ; iso_from_to := iso_to_from (@adj _ _ _ _ A y x) |};

  to_adj_nat_l   := fun _ _ _ f g => @from_adj_nat_r _ _ _ _ A _ _ _ g f;
  to_adj_nat_r   := fun _ _ _ f g => @from_adj_nat_l _ _ _ _ A _ _ _ g f;
  from_adj_nat_l := fun _ _ _ f g => @to_adj_nat_r  _ _ _ _ A _ _ _ g f;
  from_adj_nat_r := fun _ _ _ f g => @to_adj_nat_l  _ _ _ _ A _ _ _ g f
|}.

(* Mirrors the F^op notation on functors, at the same level/scope. *)

Notation "N ^op" := (@Opposite_Adjunction _ _ _ _ N)
  (at level 7, format "N ^op", left associativity) : adjunction_scope.

Open Scope adjunction_scope.

(* The op construction is an involution on adjunctions: since (C^op)^op = C and
   F^op reuse their underlying data on the nose, and the dual swaps the iso's
   to/from twice, applying op twice recovers A by [reflexivity]. *)

Corollary Opposite_Adjunction_invol `(F : D ⟶ C) `(U : C ⟶ D) (A : F ⊣ U) :
  (A^op)^op = A.
Proof. reflexivity. Qed.
