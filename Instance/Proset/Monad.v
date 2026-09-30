Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Structure.Thin.
Require Import Category.Structure.Thin.Monad.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Proset.Order.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Proset.Galois.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.
From Coq Require Import Lia.

Generalizable All Variables.

(** * Monads on a preorder are closure operators *)

(* nLab: https://ncatlab.org/nlab/show/closure+operator
   nLab: https://ncatlab.org/nlab/show/idempotent+monad
   Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, SS VI.1, printed p. 139, and SS VI.2,
         printed p. 141 (the example "Closure.")
   Book: Awodey, "Category Theory" (1st ed., CMU pre-print, Sept 2005),
         SS 10.2, Example 10.4, printed p. 270
   Book: Fong and Spivak, "Seven Sketches in Compositionality", arXiv v3,
         SS 1.4.4, printed pp. 33-35: Exercise 1.119, Definition 1.120,
         Examples 1.121, 1.122 and 1.123
   Book: Riehl, "Category Theory in Context", 2nd ed., SS 5.1,
         Example 5.1.7, printed p. 186

   WHAT THE BOOKS SAY.  Mac Lane, p. 139: for a preorder P, a functor
   T : P → P is a monotone function, and the unit and multiplication exist
   "precisely when x ≤ Tx, T(Tx) ≤ Tx" (display (3)); "The first equation
   of (3) gives Tx ≤ T(Tx)"; and if P is a partial order "the Eqs. (3)
   imply that T(Tx) = Tx.  Hence a monad T in a partial order P is just a
   closure operation".  On p. 141: "A closure operation T on a preorder P
   is a monad in P ...; a T-algebra is then an x ∈ P with Tx ≤ x ... a
   T-algebra is simply an element x ∈ P with x ≤ Tx ≤ x.  If P is a
   partial order, this means that x = Tx".  Awodey's Example 10.4 (p. 270)
   states the poset case and derives T² = T.  Seven Sketches,
   Definition 1.120 (pp. 33-34): a closure operator on a preorder is a
   monotone j with p ≤ j(p) and j(j(p)) ≅ j(p), idempotent only up to the
   preorder's isomorphism.  Riehl's Example 5.1.7 (p. 186) states the
   preorder conditions p ≤ Tp and T²p ≤ Tp, and T²p = Tp for a poset.

   WHERE CLOSURE OPERATORS OCCUR, as the same pages record.  Riehl
   (p. 186): the closure of a subset of a topological space, with the
   interior as the dual kernel operator (both are
   Instance/Top/Interior.v).  Awodey (p. 270): the "possibility operator"
   ◇p of modal logic.  Seven Sketches: a program that rewrites expressions
   (Example 1.121), and the modal operator "assuming B, −" on
   propositions ordered by entailment (Example 1.123; it is
   Instance/Props/Modal.v).
   In the tree, the element-level closures of a Galois connection were
   already present, as Instance/Grp/Galois.v's [GalClosed_l] and
   [GalClosed_r] and Instance/Proset/Galois/FixedPoints.v's
   [unit_fixed_iff_closed_r]; this file states the operator itself and
   its identification with a monad.

   WHICH READING THE RECORD IMPLEMENTS.  [ClosureOperator] takes Mac
   Lane's display (3) as its fields over a PREORDER: a monotone map
   [cl_fun] (Instance/Proset/Monotone.v's [MonotoneFun]), extensivity
   [cl_ext], and the multiplication inequality [cl_mult].  Seven Sketches'
   isomorphism is DERIVED as [cl_idem], its inverse being extensivity at
   cl x, which is Mac Lane's "Tx ≤ T(Tx)"; conversely [closure_of_iso]
   builds the record from Definition 1.120's form.  The two readings are
   therefore interderivable over a preorder, and the equation of Mac
   Lane, Awodey and Riehl needs antisymmetry, supplied as an explicit
   hypothesis in [closure_idem_eq].  No book is contradicted: Mac Lane
   defines a closure operation for a partial order on p. 139
   (t(tx) = tx) and on p. 141 calls a monad on a preorder a closure
   operation; he writes "=" only for a partial order, as Awodey and
   Riehl do for a poset; Seven Sketches states ≅ in Definition 1.120 and
   writes "=" in Example 1.123 for propositions under entailment, where
   it reads as mutual entailment.
   The fields are display (3) rather than Definition 1.120 for
   a measured reason: with them the round trip closure → monad → closure
   is [eq_refl] on the WHOLE record ([closure_round_trip], through
   primitive-projection eta), while a record carrying the isomorphism as a
   field is refused there, because the rebuilt inverse is ret at cl x
   and not the given one.

   THE CORRESPONDENCE.  [closure_functor] is Monotone.v's
   [Functor_of_monotone]; [closure_monad] has every law [I], since the
   hom-setoid of Instance/Proset.v's [Proset] is [True].  It IS
   Structure/Thin/Monad.v's [thin_monad] at the thin witness
   [fun _ _ _ _ => I], on the WHOLE record by [eq_refl]
   ([closure_monad_is_thin]).  It is not DEFINED through [thin_monad]:
   that route is refused bare, the sort level of Structure/Thin.v's
   [Thin] being left in the body alone; pinned to u or h it adds
   h <= u or u <= h (measured); with + the thin level stays in the block
   only.  The direct [Build_Monad] keeps u and h unrelated.
   [closure_of_monad]
   reads the monotone map off the functor and the two inequalities off ret
   and join; [monad_closure_iff] packages both directions.
   Instance/Poset.v's [Poset] is [Proset] with the antisymmetry argument
   discarded (Instance/Proset/Order.v's [Poset_is_Proset], by [eq_refl]),
   so every statement here applies to a poset unchanged
   ([poset_closure_of_monad]).

   ALGEBRAS ARE THE CLOSED ELEMENTS, by two routes.  Directly,
   [talgebra_iff_closed]: an algebra is exactly Tx ≤ x.  And by
   INSTANTIATION of Construction/Reflective/Idempotent.v, which is what
   the issue asks for: [talgebra_iff_closed_via_idem] goes through that
   file's [algebra_ret_iso] and [local_algebra] at the witness
   [thin_IdempotentMonad] of Structure/Thin/Monad.v, the derivation of
   idempotency from thinness.  [closed_iff_fixed] is Mac Lane's
   "x ≤ Tx ≤ x" as Tx ≅ x, and [mlocal_iff_closed] identifies membership
   in Idempotent.v's [MLocal_Subcategory] (ret x invertible) with
   closedness.  Instantiated at the thin witness, Idempotent.v also gives
   [proset_EM_equivalence], the Eilenberg-Moore category as the closed
   elements, and [proset_fixed_adj], the reflection onto them (Seven
   Sketches Example 1.122's adjunction, and the first of the two routes to
   Awodey's p. 271 construction), whose composite is T on objects and on
   arrows by [eq_refl] ([proset_factorisation_obj],
   [proset_factorisation_fmap]).  The second, order-theoretic
   route is Instance/Proset/Monad/Awodey.v, and that the reflection
   induces T again, for any idempotent monad, is
   Construction/Reflective/Idempotent/Induced.v.

   WITNESSES, so that the correspondence is not vacuous.
   [succ_not_monad]: the successor functor [NatSucc] of
   Instance/Proset/Galois.v is monotone and extensive but carries no
   monad, since the multiplication at 0 would be 2 ≤ 1.  [max_closure k]
   is n ↦ max k n, and [max_closed_iff] says its algebras are exactly the
   n with k ≤ n.

   STRENGTHS, measured.
     - closure → monad → closure: [eq_refl] on the whole record
       ([closure_round_trip]).
     - [closure_monad] against Structure/Thin/Monad.v's [thin_monad]:
       [eq_refl] on the whole record ([closure_monad_is_thin]).
     - monad → closure → monad: at ≈ of functors, with identity
       components ([monad_round_trip], which IS Monotone.v's
       [Functor_of_monotone_of_Functor]); [fobj] and [fmap] by [eq_refl]
       ([monad_round_trip_fobj], [monad_round_trip_fmap]), and ret and
       join by eq_refl ([monad_round_trip_ret], [monad_round_trip_join]):
       the unit and multiplication come back on the nose; the equation
       [closure_functor (closure_of_monad M) = M] is refused by conversion.
       Flipped first: with the law fields written as transparent [I]
       terms, no [Qed] anywhere, it is refused the same way, because the
       law fields of a variable M are stuck projections.  So ≈ is the
       strongest available.
     - [closure_of_iso]: the [to] leg of [cl_idem] is the given one by
       [eq_refl] ([closure_of_iso_to]); the whole isomorphism is refused
       by conversion, its [from] leg being extensivity at f x.
     - The algebra structure map round-trips by [eq_refl]
       ([talgebra_round]).
     - Under antisymmetry, ≅ becomes Leibniz [=] on elements: [closed_eq]
       and [closure_idem_eq].

   UNIVERSES, read off [About].  [ClosureOperator@{u}] lives in
   [Type@{u}]: its fields mention only the carrier's level, and the hom
   level [h] enters with the category, as in [closure_functor@{u h}].  The
   caps [u <= Defs.u0, u <= Relation_Definition.u0] are those of the
   stdlib's [PreOrder] and [relation], whose universes are global.  The
   biconditionals [@{u h +}] add one level for [iffT]: free where one side
   is a [Prop], and bounded below by u and h in [monad_closure_iff], whose
   left side is a sigma over functors; [mlocal_iff_closed] adds a second,
   the third level of [MLocal_Subcategory], free in that constant's
   block.  [monad_round_trip] adds two, with [h < u1] first carried by
   Theory/Functor.v's [Functor_Setoid].  The three instantiations of
   Idempotent.v carry one strict bound [h < ·], which several donors in
   their statements introduce in their own blocks and the elaborator
   unifies: Construction/Subcategory.v's [Sub] in all three;
   Theory/Functor.v's [Compose], the earliest in dependency order, in
   [proset_factorisation_obj]; Instance/Sets.v's [Sets], through
   [Adjunction], in [proset_fixed_adj]; and Theory/Equivalence.v's
   [EquivalenceOfCategories] with Monad/Eilenberg/Moore.v's
   [EilenbergMoore] in [proset_EM_equivalence].  The same donors bring
   stdlib caps: [u <= Projections.u0, h <= Projections.u0,
   h <= Projections.u1] from [Sub] and [Incl] in all three and in
   [proset_factorisation_fmap], and [h <= compose.u0, compose.u1,
   compose.u2, ID.u0] from [Sets] ([Sets@{o so}] has them at its level
   o) in [proset_fixed_adj].  [closure_monad_is_thin@{u h t}] adds
   [Thin]'s own block, u <= t and h <= t.  [closed_eq],
   [closure_idem_eq] and [poset_closure_of_monad] add the cap
   [u <= equality.u0] first carried by Instance/Poset.v's [eq_equiv].
   A systematic check found no level that occurs only in a body, with
   one designed exception: transparent, [talgebra_iff_closed_via_idem]
   carried four such levels (the sort of [Thin], a free level of
   [MLocal_Subcategory], and two from [algebra_ret_iso] and
   [local_algebra], one strictly above h), so it is a [Qed] lemma, and
   Private Polymorphic Universes (on; Lib.v does not unset it) keeps them
   out of its instance, which is [@{u h u0}] as for the direct route.
   [Thin] and [proset_thin] are declared twice in the tree; this file
   loads both copies (it requires Structure/Thin.v directly, which
   Instance/Proset/Order.v also requires, and Instance/Proset/Galois.v
   for [NatSucc]) and writes [Order.proset_thin], the one typed by
   Structure/Thin.v's [Thin].  No constant carries [Set].

   NOT DELIVERED.  Only [Proset] here: nothing over a setoid-valued
   order, no category of closure operators, and no functoriality in P.
   The modal operator of Example 1.123 over [Props] is
   Instance/Props/Modal.v.  No lemma that a monad on a [Proset] is
   determined by its functor, although every two with the same functor
   agree componentwise, at the trivial hom-setoid.  The dual, interior
   operators and comonads, is Instance/Proset/Monad/Interior.v, and its
   instance at the subsets of a space, with the closure of Riehl's
   Example 5.2.6 (iv), is Instance/Top/Interior.v. *)

(** ** Closure operators: Mac Lane's display (3) *)

(* Mac Lane's display (3) as the fields: a monotone map, extensivity
   (the unit) and the multiplication inequality. *)
Record ClosureOperator@{u} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) := {
  cl_fun  : @MonotoneFun A R A R;
  cl_ext  : ∀ x, R x (cl_fun x);
  cl_mult : ∀ x, R (cl_fun (cl_fun x)) (cl_fun x)
}.

Arguments cl_fun {A R P} _.
Arguments cl_ext {A R P} _ _.
Arguments cl_mult {A R P} _ _.

(* Seven Sketches Definition 1.120 (b), derived: the inverse of the
   multiplication is extensivity at cl x. *)
Definition cl_idem@{u h} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (c : ClosureOperator@{u} P) (x : A) :
  cl_fun c (cl_fun c x) ≅[Proset@{u h} P] cl_fun c x :=
  @Build_Isomorphism (Proset@{u h} P) _ _
    (cl_mult c x) (cl_ext c (cl_fun c x)) I I.

(* The smart constructor from Definition 1.120's form. *)
Definition closure_of_iso@{u h} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) (f : @MonotoneFun A R A R) (ext : ∀ x, R x (f x))
  (idem : ∀ x, f (f x) ≅[Proset@{u h} P] f x) : ClosureOperator@{u} P :=
  {| cl_fun  := f
   ; cl_ext  := ext
   ; cl_mult := fun x => to (idem x) |}.

Example closure_of_iso_to@{u h} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) (f : @MonotoneFun A R A R) (ext : ∀ x, R x (f x))
  (idem : ∀ x, f (f x) ≅[Proset@{u h} P] f x) (x : A) :
  to (cl_idem@{u h} (closure_of_iso P f ext idem) x) = to (idem x)
  := eq_refl.

(** ** The correspondence *)

(* The endofunctor of the thin category, through Monotone.v. *)
Definition closure_functor@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  Proset@{u h} P ⟶ Proset@{u h} P :=
  Functor_of_monotone P P (cl_fun c).

(* Closure → monad: every law is [I], the hom-setoid being [True]. *)
Definition closure_monad@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  @Monad (Proset@{u h} P) (closure_functor c) :=
  @Build_Monad (Proset@{u h} P) (closure_functor c)
    (fun x => cl_ext c x) (fun x => cl_mult c x)
    (fun _ _ _ => I) (fun _ => I) (fun _ => I) (fun _ => I)
    (fun _ _ _ => I).

(* Monad → closure: the two inequalities are ret and join. *)
Definition closure_of_monad@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} : ClosureOperator@{u} P :=
  {| cl_fun  := monotone_of_Functor P P M
   ; cl_ext  := fun x => @ret _ M MM x
   ; cl_mult := fun x => @join _ M MM x |}.

(* The correspondence.  The pair is built with its family explicit, the
   8.19/8.20 idiom recorded in Monotone.v. *)
Definition monad_closure_iff@{u h +} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) :
  { M : Proset@{u h} P ⟶ Proset@{u h} P & @Monad (Proset@{u h} P) M }
    ↔ ClosureOperator@{u} P :=
  (fun p => match p with existT _ M MM => closure_of_monad M (MM := MM) end,
   fun c => existT (fun M : Proset@{u h} P ⟶ Proset@{u h} P =>
                      @Monad (Proset@{u h} P) M)
              (closure_functor c) (closure_monad c)).

(** ** Round trips *)

(* [closure_monad] is Structure/Thin/Monad.v's [thin_monad], on the WHOLE
   record. *)
Example closure_monad_is_thin@{u h t} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  closure_monad@{u h} c
    = @thin_monad@{t u h} (Proset@{u h} P) (fun _ _ _ _ => I)
        (closure_functor@{u h} c) (cl_ext c) (cl_mult c) := eq_refl.

(* closure → monad → closure is the identity on the WHOLE record. *)
Example closure_round_trip@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (c : ClosureOperator@{u} P) :
  closure_of_monad@{u h} (closure_functor@{u h} c) (MM := closure_monad c)
    = c := eq_refl.

(* monad → closure → monad is the identity up to ≈ of functors; [=] is
   refused by conversion. *)
Definition monad_round_trip@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} :
  closure_functor (closure_of_monad M (MM := MM)) ≈ M :=
  Functor_of_monotone_of_Functor P P M.

(* ...but its object and arrow maps are M's on the nose. *)
Example monad_round_trip_fobj@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  fobj[closure_functor (closure_of_monad M (MM := MM))] x = fobj[M] x
  := eq_refl.

Example monad_round_trip_fmap@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x y : A) (f : R x y) :
  fmap[closure_functor (closure_of_monad M (MM := MM))] f = fmap[M] f
  := eq_refl.

(* ...and the monad it rebuilds has M's unit and multiplication. *)
Example monad_round_trip_ret@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  @ret _ _ (closure_monad (closure_of_monad M (MM := MM))) x = @ret _ M MM x
  := eq_refl.

Example monad_round_trip_join@{u h} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  @join _ _ (closure_monad (closure_of_monad M (MM := MM))) x
    = @join _ M MM x := eq_refl.

(** ** Algebras are the closed elements *)

(* Mac Lane p. 141: an algebra is exactly an x with Tx ≤ x. *)
Definition talgebra_iff_closed@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  @TAlgebra (Proset@{u h} P) M MM x ↔ R (M x) x :=
  (fun alg => @t_alg (Proset@{u h} P) M MM x alg,
   fun h => @Build_TAlgebra (Proset@{u h} P) M MM x h I I).

Example talgebra_round@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) (h : R (M x) x) :
  match talgebra_iff_closed M x with
  | (to_closed, of_closed) => to_closed (of_closed h)
  end = h := eq_refl.

(* "x ≤ Tx ≤ x": closed means Tx ≅ x. *)
Definition closed_iff_fixed@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  R (M x) x ↔ (M x ≅[Proset@{u h} P] x) :=
  (fun h => @Build_Isomorphism (Proset@{u h} P) _ _ h (@ret _ M MM x) I I,
   fun i => to i).

(* Idempotent.v's M-local objects (ret x invertible) are the closed ones. *)
Definition mlocal_iff_closed@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  sobj (Proset@{u h} P) (@MLocal_Subcategory (Proset@{u h} P) M MM) x
    ↔ R (M x) x :=
  (fun H => @two_sided_inverse _ _ _ _ H,
   fun h => @Build_IsIsomorphism (Proset@{u h} P) x (M x)
              (@ret _ M MM x) h I I).

(* The same, by instantiating Idempotent.v at the thin witness.  [Qed]
   keeps four body-only universe levels private (see the header). *)
Lemma talgebra_iff_closed_via_idem@{u h +} {A : Type@{u}}
  {R : relation A} {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  @TAlgebra (Proset@{u h} P) M MM x ↔ R (M x) x.
Proof.
  exact (let IM := thin_IdempotentMonad (Order.proset_thin P) (MM := MM) in
         let (to_closed, of_closed) := mlocal_iff_closed M x in
         (fun alg => to_closed (@algebra_ret_iso _ M MM IM x alg),
          fun h => @local_algebra _ M MM IM x (of_closed h))).
Qed.

(** ** The Eilenberg-Moore category and the reflection, instantiated *)

(* The Eilenberg-Moore category is equivalent to the closed elements. *)
Definition proset_EM_equivalence@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} :=
  @Idempotent_EM_Equivalence (Proset@{u h} P) M MM
    (thin_IdempotentMonad (Order.proset_thin P)).

(* The reflection onto the closed elements, t ⊣ i. *)
Definition proset_fixed_adj@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} :=
  @idem_reflective_adj (Proset@{u h} P) M MM
    (thin_IdempotentMonad (Order.proset_thin P)).

(* T = i ∘ t on objects, on the nose. *)
Example proset_factorisation_obj@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x : A) :
  fobj[Incl (Proset@{u h} P) (@MLocal_Subcategory (Proset@{u h} P) M MM)
         ◯ @idem_reflector (Proset@{u h} P) M MM
             (thin_IdempotentMonad (Order.proset_thin P))] x = M x
  := eq_refl.

(* ...and on arrows. *)
Example proset_factorisation_fmap@{u h +} {A : Type@{u}} {R : relation A}
  {P : PreOrder R} (M : Proset@{u h} P ⟶ Proset@{u h} P)
  {MM : @Monad (Proset@{u h} P) M} (x y : A) (f : R x y) :
  fmap[Incl (Proset@{u h} P) (@MLocal_Subcategory (Proset@{u h} P) M MM)
         ◯ @idem_reflector (Proset@{u h} P) M MM
             (thin_IdempotentMonad (Order.proset_thin P))] f = fmap[M] f
  := eq_refl.

(** ** Partial orders: antisymmetry turns ≅ into = *)

(* Mac Lane p. 141: in a partial order an algebra is a fixed point. *)
Lemma closed_eq@{u h} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (AS : @Antisymmetric A eq eq_equiv R)
  (M : Proset@{u h} P ⟶ Proset@{u h} P) {MM : @Monad (Proset@{u h} P) M}
  (x : A) : @TAlgebra (Proset@{u h} P) M MM x → M x = x.
Proof. intro alg. exact (AS _ _ (@t_alg _ _ _ _ alg) (@ret _ M MM x)). Qed.

(* Mac Lane p. 139: in a partial order T(Tx) = Tx. *)
Lemma closure_idem_eq@{u} {A : Type@{u}} {R : relation A} {P : PreOrder R}
  (AS : @Antisymmetric A eq eq_equiv R) (c : ClosureOperator@{u} P)
  (x : A) : cl_fun c (cl_fun c x) = cl_fun c x.
Proof. exact (AS _ _ (cl_mult c x) (cl_ext c (cl_fun c x))). Qed.

(* A monad on a [Poset] is accepted as it stands. *)
Example poset_closure_of_monad@{u h} {A : Type@{u}} {R : relation A}
  (P : PreOrder R) (AS : @Antisymmetric A eq eq_equiv R)
  (M : @Poset A R P AS ⟶ @Poset A R P AS)
  {MM : @Monad (@Poset A R P AS) M} : ClosureOperator@{u} P :=
  closure_of_monad@{u h} M (MM := MM).

(** ** Witnesses *)

(* Monotone and extensive, yet not a monad: join at 0 would be 2 ≤ 1. *)
Theorem succ_not_monad@{u h} :
  @Monad (Proset@{u h} Nat.le_preorder) NatSucc@{u h u} → False.
Proof.
  intro MM.
  pose proof (@join _ NatSucc MM 0%nat) as H.
  simpl in H.
  lia.
Qed.

(* n ↦ max k n, a closure operator on (ℕ, ≤)... *)
Definition max_mono@{u} (k : nat) : @MonotoneFun@{u u} nat Nat.le nat Nat.le :=
  {| mono_map := Nat.max k
   ; mono_pres := fun x y H => Nat.max_le_compat_l x y k H |}.

Lemma max_mult@{} (k n : nat) : (Nat.max k (Nat.max k n) <= Nat.max k n)%nat.
Proof. lia. Qed.

Definition max_closure@{u} (k : nat) : ClosureOperator@{u} Nat.le_preorder :=
  {| cl_fun  := max_mono k
   ; cl_ext  := fun n => Nat.le_max_r k n
   ; cl_mult := fun n => max_mult k n |}.

(* ...whose algebras are exactly the n above k. *)
Lemma max_closed_iff@{u h +} (k n : nat) :
  @TAlgebra (Proset@{u h} Nat.le_preorder)
    (closure_functor@{u h} (max_closure@{u} k))
    (closure_monad@{u h} (max_closure@{u} k)) n ↔ (k <= n)%nat.
Proof.
  destruct (talgebra_iff_closed (closure_functor (max_closure k))
              (MM := closure_monad (max_closure k)) n) as [to_closed of_closed].
  split.
  - intro alg. pose proof (to_closed alg) as H. simpl in H. lia.
  - intro H. apply of_closed. simpl. lia.
Qed.
