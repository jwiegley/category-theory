Set Warnings "-notation-overridden".

Require Import Coq.Program.Program.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Bool_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.PArith.PArith.
Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.
Require Import Coq.Wellfounded.Lexicographic_Product.
Require Import Recdef.

Require Import Category.Lib.
Require Import Category.Theory.Functor.

Require Import Solver.Lib.
Require Import Solver.Expr.

Generalizable All Variables.

Section Normal.

Inductive Arrow : Term -> Set :=
  | Here  : ∀ x y a, Arrow (Morph x y a)
  | Left  : ∀ (m : obj_idx) f g, Arrow f -> Arrow (Compose m f g)
  | Right : ∀ (m : obj_idx) f g, Arrow g -> Arrow (Compose m f g).

Definition Arrow_inv_t : forall t, Arrow t -> Type.
Proof.
  intros [] H.
  - exact False.
  - exact (H = Here x y a).
  - exact ((∃ H', H = Left m f g H') + (∃ H', H = Right m f g H')).
Defined.

Lemma Arrow_inv t f : Arrow_inv_t t f.
Proof.
  destruct f; simpl; equalities; simpl_eq; auto.
  - left. exists f0; auto.
  - right. exists f0; auto.
Defined.

Lemma Arrow_Morph `(H : Arrow (Morph x y a)) : H = Here x y a.
Proof. exact (Arrow_inv _ H). Defined.

Lemma Arrow_Compose `(H : Arrow (Compose m f g)) :
  (∃ H', H = Left m f g H') + (∃ H', H = Right m f g H').
Proof. exact (Arrow_inv _ H). Defined.

Fixpoint get_arrow `(f : Arrow t) : obj_idx * arr_idx :=
  match f with
  | Here x _ a    => (x, a)
  | Left _ _ _ x  => get_arrow x
  | Right _ _ _ x => get_arrow x
  end.

Function arrow_bequiv {t t' : Term} (p : Arrow t) (q : Arrow t') : bool :=
  match get_arrow p, get_arrow q with
  | (o, f), (o', f') => Eq_eqb o o' && Eq_eqb f f'
  end.

Function arrows (t : Term) : list (Arrow t) :=
  match t with
  | Identity _    => nil
  | Morph x y a   => [Here x y a]
  | Compose m f g => map (Left m f g) (arrows f) ++
                     map (Right m f g) (arrows g)
  end.

Function arrows_bequiv {t t' : Term}
         (ps : list (Arrow t)) (qs : list (Arrow t')) : bool :=
  term_beq t t' &&&
  match ps, qs with
  | nil, nil => true
  | cons p ps, cons q qs =>
    arrow_bequiv p q &&& arrows_bequiv ps qs
  | _, _ => false
  end.

End Normal.
