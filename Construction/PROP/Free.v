Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.

From Coq Require Import Arith.

Generalizable All Variables.

(** * The free PROP category on a signature *)

(* nLab: https://ncatlab.org/nlab/show/PROP
   nLab: https://ncatlab.org/nlab/show/free+category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Free_category

   A PROP is a strict symmetric monoidal category whose objects are the
   natural numbers and whose tensor on objects is addition, [m ⊗ n = m + n].
   The free PROP on a signature [S] has as its [m ~> n] arrows the [S]-terms
   [Term S m n] quotiented by the laws of a symmetric monoidal category; this
   is the standard "free = syntactic" construction, the symmetric-monoidal
   analogue of the path/quotient construction of a free category.

   This file assembles only the underlying [Category] layer of that quotient:

     - obj      := nat                         (objects are ℕ)
     - hom m n  := Term S m n  modulo  TermEq  (string-diagram terms / ≈)
     - id       := T_id                        (identity wires)
     - compose  := T_comp                      (sequential composition)

   The hom-equivalence ≈ is [TermEq S], so the [Category] laws (left/right
   unit, associativity) are exactly its [TE_id_left] / [TE_id_right] /
   [TE_assoc] constructors, and [compose_respects] is its [TE_comp_cong]
   congruence.  The [Monoidal], [SymmetricMonoidal], [StrictMonoidal], and
   [PROP] instances — which would complete [FreeCat S] to a free strict
   symmetric monoidal category — are not yet built.  The successor files
   so far only lay groundwork toward them: a tensor functor
   ([Construction/PROP/Tensor.v]), the structural isomorphisms
   ([Construction/PROP/Structural.v]), and their naturality lemmas
   ([Construction/PROP/Naturality.v]).  No [Monoidal] or [PROP] instance
   on [FreeCat S] exists in the library at present. *)

Section FreeCategory.

Context (S : Signature).

(** The hom-setoid: terms are quotiented by [TermEq]. *)
#[export] Program Instance Term_Setoid {m n : nat} : Setoid (Term S m n) := {|
  equiv := @TermEq S m n
|}.
Next Obligation.
  constructor.
  - intros t; apply TE_refl.
  - intros s t; apply TE_sym.
  - intros s t u; apply TE_trans.
Defined.

(** Composition is the [T_comp] constructor; it respects [TermEq] by
    [TE_comp_cong]. *)
#[export] Program Instance T_comp_respects {m n p : nat} :
  Proper (equiv ==> equiv ==> equiv) (@T_comp S m n p).
Next Obligation.
  proper.
  apply TE_comp_cong; assumption.
Qed.

(** Tensor (parallel composition) is also Proper for [TermEq], by
    [TE_tens_cong].  Allows [rewrite] under [T_tens]. *)
#[export] Program Instance T_tens_respects {m1 n1 m2 n2 : nat} :
  Proper (equiv ==> equiv ==> equiv) (@T_tens S m1 n1 m2 n2).
Next Obligation.
  proper.
  apply TE_tens_cong; assumption.
Qed.

(** The free category on [S]. *)
Program Definition FreeCat : Category := {|
  obj      := nat;
  hom      := @Term S;
  homset   := @Term_Setoid;
  id       := T_id;
  compose  := @T_comp S;
  compose_respects := @T_comp_respects;
  id_left  := fun m n f => TE_id_left f;
  id_right := fun m n f => TE_id_right f;
  comp_assoc := fun m n p q f g h => TE_sym _ _ (TE_assoc f g h);
  comp_assoc_sym := fun m n p q f g h => TE_assoc f g h
|}.

End FreeCategory.

Arguments FreeCat S : assert.
Arguments T_comp_respects {S m n p}.
