Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Construction.Product.
Require Import Category.Construction.Quotient.
Require Import Category.Functor.Construction.Product.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Map.
Require Import Category.Theory.Skeleton.

Generalizable All Variables.

(** * Boundary probe for Adjunction/Map.v (issue #393)

    Every boundary the header of Adjunction/Map.v records is pinned here as
    a [Fail] command, with a passing command outside any [Fail] for every
    constant a negative names.  Each negative was stripped one at a time,
    compiled alone, and its whole error read; the kind recorded beside it is
    read off that error text.

    This file mirrors Adjunction/Map.v's full [Require] list and adds
    Category.Theory.Skeleton, which that file deliberately does not take
    (measured there: 21 modules to 32).  Sections A and B below spend the
    import once, to check that the two square fields of [AdjSquares] really
    are the two arguments of [strict_equiv_of_id_cast_nat]. *)

(** ** Instrument check: a name that is in no file of the tree *)

Fail Check map_of_adjunctions_no_such_constant_anywhere.

(** ** Section A: controls *)

Section Controls.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'} (A' : F' ⊣ U').
Context (S : @AdjSquares C D F U C' D' F' U').
Context (M : MapOfAdjunctions A A').
Context (x : D) (a : C) (k : F x ~> a).

Check @AdjSquares.
Check @MapOfAdjunctions.
Check @SquaresHom.
Check @SquaresUnit.
Check @SquaresCounit.
Check @sq_K.
Check @sq_L.
Check @sq_left.
Check @sq_left_nat.
Check @sq_right.
Check @sq_right_nat.
Check @sq_unit_eq.
Check @sq_counit_eq.
Check @map_hom.
Check @map_squares.
Check @map_K.
Check @map_L.
Check @squares_unit_fused.
Check @squares_counit_fused.
Check @squares_hom_is_generic.
Check @strict_hom_is_weak_hom.
Check @map_adj_hom_is_conjugate.
Check @MapOfAdjunctions_id.
Check @MapOfAdjunctions_compose.
Check @MapAdjHom.
Check @WeakSquaresHom.
Check @WeakAdjSquares.
Check @adj.
Check @to.
Check @from.
Check @unit.
Check @counit.
Check @fmap.
Check @transform.
Check @Id.
Check @Isomorphism.
Check @Functor.
Check @Adjunction.
Check @id_cast.
Check @Conjugate.
Check @Functor_StrictEq_Setoid.
Check @strict_equiv_of_id_cast_nat.

(* The hom-set condition WITH the cast, which negative 1 removes. *)
Definition p393_control_cast :=
  to (@adj _ _ _ _ A' _ _) (fmap[sq_K S] k ∘ id_cast (eq_sym (sq_left S x))).

(* The fused Mac Lane spelling, which negative 2 asks for at [eq_refl]. *)
Definition p393_control_fused := squares_unit_fused A A' S.

(* The composite of the identity map with M, which negative 3 asks to be M. *)
Definition p393_control_compose :=
  MapOfAdjunctions_compose A A A' (MapOfAdjunctions_id A) M.

(** *** The claim the header makes about Theory/Skeleton.v

    Both passages are supplied by application alone: no tactic, no
    transport, no [change].  So the two square fields of [AdjSquares] ARE,
    up to conversion, the two arguments of [strict_equiv_of_id_cast_nat],
    whose conclusion is the tree's strict functor equality. *)

Definition p393_strict_left
  : @equiv _ (@Functor_StrictEq_Setoid D C') (sq_K S ◯ F) (F' ◯ sq_L S)
  := strict_equiv_of_id_cast_nat (sq_K S ◯ F) (F' ◯ sq_L S)
       (sq_left S) (sq_left_nat S).

Definition p393_strict_right
  : @equiv _ (@Functor_StrictEq_Setoid C D') (sq_L S ◯ U) (U' ◯ sq_K S)
  := strict_equiv_of_id_cast_nat (sq_L S ◯ U) (U' ◯ sq_K S)
       (sq_right S) (sq_right_nat S).

(** ** Negative 1 (TYPING): the double bar cannot be dropped

    [fmap[sq_K S] k] runs from [sq_K S (F x)], and the transpose of A' wants
    a morphism out of [F' ?x].  Those are the same object only through
    [sq_left S x], which is why the condition is stated with the cast.
    Stripped, the error is a plain "has type ... while it is expected to
    have type ...", with no "cannot unify" clause. *)

Fail Check (to (@adj _ _ _ _ A' _ _) (fmap[sq_K S] k)).

(** ** Negative 2 (CONVERSION): the fused spelling is a theorem, not a
       conversion

    [squares_unit_fused] is a genuine biconditional; the two statements are
    not the same type.  Stripped, the error ends
    (cannot unify "SquaresUnit A A' S" and "∀ y : obj[D], ..."). *)

Fail Definition p393_unit_fused_strict :
  SquaresUnit A A' S
    = (∀ y : D, id_cast (sq_unit_eq S y) ∘ fmap[sq_L S] (@unit _ _ _ _ A y)
                  ≈ @unit _ _ _ _ A' (sq_L S y)) := eq_refl.

(** ** Negative 3 (CONVERSION): no unit law on the nose

    Composition and identity are delivered, but no law relating them is:
    [AdjSquares_compose] builds [sq_K M ◯ Id[C]], which is not [sq_K M].
    Stripped, the error ends (cannot unify "MapOfAdjunctions_compose A A A'
    (MapOfAdjunctions_id A) M" and "M"). *)

Fail Definition p393_unit_law :
  MapOfAdjunctions_compose A A A' (MapOfAdjunctions_id A) M = M := eq_refl.

(** ** Negative 4 (TYPING): [Conjugate] is the same-categories case

    Adjunction/Conjugate.v fixes ONE pair of categories, so its relation
    cannot even be applied to two adjunctions over different ones.  This is
    why #393 is not subsumed by that file.  The error tail also reads
    "cannot unify", but between two CATEGORIES ("C'" and "C") rather than
    between two inhabitants of a single type, and the reported mismatch is
    the type of A'. *)

Fail Check (Conjugate A A').

End Controls.

(** ** Negative 5 (TYPING): the comparison data must be invertible

    The K = Id, L = Id case of [MapAdjHom] recovers exactly the conjugate
    pairs whose two transformations are pointwise invertible: a bare
    [Transform] does not inhabit the iso family [MapAdjHom] asks for. *)

Section Residue.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {F2 : D ⟶ C} {U2 : C ⟶ D} (A2 : F2 ⊣ U2).
Context (sigma : F2 ⟹ F) (tau : U ⟹ U2).

Check (Conjugate A A2 sigma tau).
Check (fun x : D => transform[sigma] x).
Check (fun a : C => transform[tau] a).

Fail Check (MapAdjHom A A2 Id[C] Id[D]
              (fun x : D => transform[sigma] x)
              (fun a : C => transform[tau] a)).

End Residue.

(** ** Negatives 6-8 (FORMABILITY): where hom = proof is forced

    [AdjSquares] is over a category whose hom and proof universes coincide.
    That is inherited, and the two donors are separated below: [id_cast] of
    Construction/Quotient.v forces it on its own, and [Adjunction] forces it
    on its own with no [id_cast] in the command.  [Isomorphism] and
    [Functor] are NOT donors -- both are accepted at the very levels where
    the three negatives are refused. *)

Section Formability.

Universes ao ah ap bo.
Constraint ah < ap.

Context (Cu : Category@{ao ah ap}) (Du : Category@{bo ah ap}).
Context (Fu : Du ⟶ Cu) (Uu : Cu ⟶ Du).

(* Controls at the declared levels. *)
Check Cu.
Check Du.
Check Fu.
Check Uu.
Check (fun x y : Cu => x ~{Cu}~> y).
Check (fun x : Cu => id[x]).
Check (fun x y : Cu => @Isomorphism Cu x y).
Check (fun (x y : Cu) (f g : x ~> y) => f ≈ g).

(* Negative 6: the record itself. *)
Fail Check (@AdjSquares Cu Du Fu Uu Cu Du Fu Uu).

(* Negative 7: [id_cast] alone, with no adjunction in the command. *)
Fail Check (fun (x y : Cu) (e : x = y) => @id_cast Cu x y e).

(* Negative 8: [Adjunction] alone, with no [id_cast] in the command; the
   control [Check Fu] above shows [Functor] is not what is refused. *)
Fail Check (Fu ⊣ Uu).

End Formability.
