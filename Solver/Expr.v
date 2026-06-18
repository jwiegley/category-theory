Require Import Category.Lib.
Require Import Category.Lib.IList.
Require Import Category.Theory.Category.

(** * Abstract syntax for the categorical solver

    This is the bottom of the [Solver/] reflective decision procedure: a
    first-order syntax of categorical expressions that goals are reified into
    (see Solver/Reify.v), interpreted back to real morphisms (Solver/Denote.v),
    normalized (Solver/Normal.v), and decided (Solver/Decide.v).  The technique
    is the standard "proof by reflection": represent the term as data, compute
    on that data, and relate the computation back to the original goal — see
    Adam Chlipala's "Certified Programming with Dependent Types" (CPDT), from
    which much of this solver is adapted.

    Objects and morphism variables are referred to by de Bruijn-style indices
    into ambient lists ([objs], [arrs]); the [Objects]/[Arrows] classes below
    package those lists together with the interpretation functions that resolve
    the indices to concrete objects and morphisms of a fixed category [cat]. *)

(* An object of the syntax is just an index into the ambient [objs] list. *)
Definition Obj := nat.

(* Resolve an object index to a concrete object of [C], falling back to the
   default [d] when the index is out of range (so the lookup is total). *)
Definition objD' {C : Category} (d : C) (objs : list C) (n : Obj) :=
  List.nth n objs d.

(* The hom-set type a morphism variable of typing [(dom, cod)] must inhabit;
   used below as the index family [B] of the heterogeneous [arrs]. *)
Definition arrD' {C : Category} (d : C) (objs : list C) '(dom, cod) :=
  objD' d objs dom ~> objD' d objs cod.

(* The objects an [Expr] may mention: a default object [def_obj] (used by the
   total lookup [objD]) together with the list [objs] they index into.  [objD]
   is a let-bound class field, i.e. a derived projection rather than a field
   the user must supply. *)
Class Objects (cat : Category) := {
  def_obj : cat;
  objs : list cat;
  objD := objD' def_obj objs;
}.

(* The morphism variables an [Expr] may mention.  [tys] gives the (dom, cod)
   index pair typing each variable, and [arrs] is the heterogeneous list (see
   Lib/IList.v) holding the concrete morphism for each variable, where entry
   [i] inhabits [arrD (nth i tys)].  A [Morph i] term thus denotes [arrs]'s
   [i]-th morphism. *)
Class Arrows (cat : Category) := {
  has_objects : Objects cat;

  arrD := arrD' def_obj objs;
  tys  : list (Obj * Obj);
  arrs : ilist (B:=arrD) tys;
}.
#[export] Existing Instance has_objects.

(* Syntax of a single morphism, built from identities, morphism variables, and
   composition.  This is exactly a term of the free category on the quiver
   whose edges are the variables [arrs]: morphisms there are paths of edges and
   identities are empty paths, and the category laws relating these terms are
   quotiented out by normalization in Solver/Normal.v.  [Morph a] indexes the
   ambient [arrs]/[tys].
   nLab: https://ncatlab.org/nlab/show/free+category *)
Inductive Term : Set :=
  | Ident
  | Morph (a : nat)
  | Comp  (f g : Term).

(* Syntax of a decidable goal: the propositional connectives over morphism
   equivalences.  [Equiv x y f g] asserts that terms [f] and [g], both typed
   [x ~> y] (with [x y : Obj] object indices), denote equivalent morphisms. *)
Inductive Expr : Set :=
  | Top
  | Bottom
  | And   (p q : Expr)
  | Or    (p q : Expr)
  | Impl  (p q : Expr)
  | Equiv (x y : Obj) (f g : Term).
