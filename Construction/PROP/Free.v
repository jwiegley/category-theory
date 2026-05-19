Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.

From Stdlib Require Import Arith.

Generalizable All Variables.

(** * The free PROP category on a signature

    Quotient the raw [Term S m n] type by [TermEq S], yielding a
    category whose objects are natural numbers and whose morphisms
    [m ~> n] are equivalence classes of [S]-labelled string-diagram
    expressions modulo the strict symmetric monoidal category axioms.

    This file delivers the underlying [Category] structure.  The
    [Monoidal], [SymmetricMonoidal], [StrictMonoidal], and [PROP]
    instances follow in successor files. *)

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
