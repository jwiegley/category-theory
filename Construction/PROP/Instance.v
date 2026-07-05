Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.TermEq.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Tensor.
Require Import Category.Construction.PROP.Cast.
Require Import Category.Construction.PROP.Monoidal.
Require Import Category.Construction.PROP.Braided.
Require Import Category.Construction.PROP.Symmetric.
Require Import Category.Construction.PROP.Strict.
Require Import Category.Construction.Quotient.

From Coq Require Import Arith.

Generalizable All Variables.

(** * The free PROP, bundled: the library's first inhabited [PROP] *)

(* nLab: https://ncatlab.org/nlab/show/PROP
   nLab: https://ncatlab.org/nlab/show/free+category
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)
   Wikipedia: https://en.wikipedia.org/wiki/Free_category

   This file assembles the bundled [PROP] instance [FreePROP S] on the
   free category [FreeCat S] of a signature [S] — the first inhabitant
   of the [PROP] class in the library.  The status notes written before
   this construction existed — [Construction/PROP/Free.v] (lines 35-42,
   "The [Monoidal], [SymmetricMonoidal], [StrictMonoidal], and [PROP]
   instances ... are not yet built") and [Construction/PROP.v] (the
   closing "Discussion: concrete PROP instances", lines 242-290, "none
   of the three kinds of PROP instance below is actually inhabited in
   the library today") — are superseded by this successor file; per the
   repository's append-only discipline for the PROP spine, those files
   are left untouched and the record is set straight here.

   Every equality field of [FreePROP] is [eq_refl], because the whole
   tower shares ONE [Monoidal] record:

     - [strict_is_monoidal (FreeCat_Strict S)] is, by iota reduction on
       the explicit record literal of [Strict.v], the literal term
       [FreeCat_Monoidal S];
     - [braided_is_monoidal (symmetric_is_braided (FreeCat_Symmetric S))]
       projects through [FreeCat_Braided S] to the SAME literal term;

   so [prop_monoidal_coherence] — propositional in general, with the
   use-site friction documented at length in [Construction/PROP.v] —
   is DEFINITIONAL for the free PROP.  Likewise [prop_of_nat] is the
   identity on [nat] (the objects of [FreeCat S] ARE the naturals),
   [prop_unit_zero] holds because the unit of [FreeCat_Monoidal S] is
   the literal [0], and [prop_tensor_plus] holds because the object
   action of [FreeCat_Tensor S] is [fun p => fst p + snd p], which
   reduces on the literal pair [(m, n)] to [m + n].

   The file also hosts the two side-condition instances that the
   interpretation and universal-property files require of [FreeCat S],
   both drawn from the fully general kit of [Construction/Quotient.v]:

     - [HomEqProp (FreeCat S)]: the hom-setoid equivalence of
       [FreeCat S] IS the [Prop]-valued [TermEq S] after delta/beta
       reduction of [Free.v]'s [Term_Setoid], so both directions of the
       reflection are the identity;
     - [ObjDecEq (FreeCat S)]: objects are [nat], so [Nat.eq_dec]
       decides object equality, giving axiom-free UIP on objects.

   Machine-checked [Example]s at the end pin the definitional
   behaviour, so any regression in the shared-record wiring is caught
   here rather than at a distant use site. *)

Section FreePROP.

Context (S : Signature).

Open Scope nat_scope.

(** ** The bundled instance

    All three structure fields name records that project to THE shared
    [FreeCat_Monoidal S], so each equality field below is [eq_refl].
    If [prop_monoidal_coherence := eq_refl] ever stops typechecking,
    the shared-record wiring broke — fix the wiring; do not generalize
    the field. *)

Definition FreePROP : PROP := {|
  prop_cat       := FreeCat S;
  prop_strict    := FreeCat_Strict S;
  prop_symmetric := FreeCat_Symmetric S;

  (* [strict_is_monoidal (FreeCat_Strict S)] and
     [braided_is_monoidal (symmetric_is_braided (FreeCat_Symmetric S))]
     both reduce to the literal term [FreeCat_Monoidal S]. *)
  prop_monoidal_coherence := eq_refl;

  (* Objects of [FreeCat S] are literally the naturals. *)
  prop_of_nat := fun n : nat => n;

  (* [I] of [FreeCat_Monoidal S] is the literal [0]. *)
  prop_unit_zero := eq_refl;

  (* [fobj (FreeCat_Tensor S) (m, n)] reduces to [m + n]. *)
  prop_tensor_plus := fun m n => eq_refl
|}.

(** ** Side-condition instances for the interpretation files

    The hom-setoid equivalence of [FreeCat S] is [TermEq S] by
    delta/beta reduction of [Term_Setoid], and [TermEq S] is already
    [Prop]-valued, so the [Prop] reflection is the identity in both
    directions. *)

#[export] Instance FreeCat_HomEqProp : HomEqProp (FreeCat S) :=
  Build_HomEqProp (FreeCat S)
    (fun m n : nat => @TermEq S m n)
    (fun _ _ _ _ H => H)
    (fun _ _ _ _ H => H).

(** Objects of [FreeCat S] are [nat], whose equality is decidable. *)

#[export] Instance FreeCat_ObjDecEq : ObjDecEq (FreeCat S) := Nat.eq_dec.

(** ** Machine-checked sanity

    Each [Example] holds by [eq_refl], witnessing that the
    corresponding field of [FreePROP] is definitional. *)

(** The coherence between the strict and symmetric [Monoidal] paths is
    the reflexivity proof itself — the "known limitation" discussed in
    [Construction/PROP.v] does not bite on the free PROP. *)
Example FreePROP_coherence_is_refl :
  @prop_monoidal_coherence FreePROP = eq_refl := eq_refl.

(** The object correspondence is the identity on [nat]. *)
Example FreePROP_of_nat_id (n : nat) :
  @prop_of_nat FreePROP n = n := eq_refl.

(** The monoidal unit is the literal object [0]. *)
Example FreePROP_I :
  @I _ (@strict_is_monoidal _ (@prop_strict FreePROP)) = 0%nat := eq_refl.

(** Tensor-on-objects is literally addition, with [eq_refl] proof. *)
Example FreePROP_tensor_plus_is_refl (m n : nat) :
  @prop_tensor_plus FreePROP m n = eq_refl := eq_refl.

(** [PROP.v]'s successor decomposition [⟦S n⟧ = ⟦1⟧ ⨂ ⟦n⟧] applies to
    [FreePROP]; whichever [Monoidal] path its statement was elaborated
    through, conversion closes the gap here, because both paths project
    the one shared record. *)
Example FreePROP_of_nat_S_smoke (n : nat) :
  @prop_of_nat FreePROP (Datatypes.S n)
  = ((@prop_of_nat FreePROP 1)
       ⨂[@strict_is_monoidal _ (@prop_strict FreePROP)]
     (@prop_of_nat FreePROP n))%object :=
  prop_of_nat_S FreePROP n.

End FreePROP.

Arguments FreePROP S : assert.
