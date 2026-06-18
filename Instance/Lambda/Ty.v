Require Import Category.Lib.

From Equations Require Import Equations.
Set Equations With UIP.

Set Transparent Obligations.

(** Simple types for the de Bruijn STLC *)

(* The grammar of simple types used to index the intrinsically-typed syntax
   [Exp Γ τ].  This is a closed type system generated from the unit type, with
   the two type formers of the simply-typed lambda calculus:

       τ ::= unit | τ × τ | τ ⟶ τ

   There are no extra base types: [TyUnit] is the only ground type, and every
   other type is built from it by product and arrow.  This is the internal
   language of a cartesian closed category (Lambek), and the type formers
   correspond exactly to the CCC structure later used to model it (see [Sem]):

       TyUnit      unit type     ↔  terminal object
       TyPair      product type  ↔  categorical product
       TyArrow     arrow type    ↔  exponential / internal hom

   simply typed lambda calculus:
     https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus
     https://ncatlab.org/nlab/show/simply+typed+lambda+calculus
   cartesian closed category (its internal language):
     https://ncatlab.org/nlab/show/cartesian+closed+category *)

Section Ty.

Inductive Ty : Set :=
  | TyUnit  : Ty                 (* unit type:    terminal object       *)
  | TyPair  : Ty → Ty → Ty       (* product type: categorical product   *)
  | TyArrow : Ty → Ty → Ty.      (* arrow type:   exponential / hom      *)

Derive NoConfusion NoConfusionHom Subterm EqDec for Ty.

End Ty.

Declare Scope Ty_scope.
Bind Scope Ty_scope with Ty.
Delimit Scope Ty_scope with ty.

Infix "⟶" := TyArrow (at level 51, right associativity) : Ty_scope.
Infix "×"  := TyPair  (at level 41, right associativity) : Ty_scope.
