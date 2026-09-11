Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Comp.

Generalizable All Variables.

(** * The category of algebras of a variety *)

(* nLab:      https://ncatlab.org/nlab/show/variety+of+algebras
   nLab:      https://ncatlab.org/nlab/show/algebraic+theory
   Wikipedia: https://en.wikipedia.org/wiki/Variety_(universal_algebra)

   Mac Lane §V.6, book p. 124 (PDF p. 133); Awodey §9.8, printed p. 256
   (PDF p. 265).

   The algebras of a given type that satisfy a set of identities — groups,
   rings, abelian groups, lattices — together with their operation-preserving
   maps form a category, the VARIETY or equational class of that
   presentation.  Mac Lane needs it as the setting for the free-algebra
   adjunction; Awodey defines the theory, its algebras and the forgetful
   functor to sets as the setting for the free-algebra theorem.

   ** What was missing, measured

   Instance/Comp.v has the whole syntactic apparatus and stops one step
   short of the category.  [OpSignature] (:45), [OpAlgebra] (:54) and
   [AlgHom] (:64) give operations, interpretations and homomorphisms;
   [EqSignature] (:240) gives laws with their naturality conditions; and
   [Algebra S E] (:268) is the TYPE of algebras satisfying them.  But
   [Algs] (:151) is the category of algebras of an OPERATION signature —
   the equations are dropped — and [Group := Algebra GroupOp GroupEq]
   (:382) is a type, not a category.  So ⟨Ω,E⟩-Alg was nowhere formed, and
   Instance/Roster.v:604 records exactly that gap in prose: "there is no
   category of Groups there … the variety is recorded here as the type it
   is".  This file forms it.

   ** How, and why this way

   [Variety] is the FULL SUBCATEGORY of [Algs] cut out by satisfaction of
   the laws, built with Construction/Subcategory.v's [Sub] in exactly the
   shape Theory/Lawvere/Model.v:68 uses for [Models_sub]: an [sobj] that
   selects, an [shom] that retains every morphism ([True]), and closure
   proofs that are therefore [I].

   Two alternatives were considered and lose.  A fresh [Category] record
   over a sigma type would duplicate [Alg_id], [Alg_comp], [AlgHom_Setoid]
   and the four laws that [Sub] supplies for nothing; it would give up
   [Incl] and [Incl_Faithful]; and it would make fullness something to
   prove rather than the one-liner [fun _ _ _ _ _ => I].  The "[Models_sub]
   analogue" is not a third option — [Models] IS [Sub] of a subcategory, so
   that suggestion and this construction are the same one.

   The record presentation is not lost: [Variety_pack] and [Variety_unpack]
   are mutually inverse ON THE NOSE against Instance/Comp.v:268's
   [Algebra S E], each round trip an eta-expansion discharged by case
   analysis — the [Model_pack]/[Model_unpack] idiom of
   Theory/Lawvere/Model.v:85.

   Setoid discipline is inherited, not rebuilt: [Sub]'s hom-setoid is
   definitionally `≈` of first projections
   (Construction/Subcategory.v:58), so morphisms of [Variety] are compared
   with `≈`, and that `≈` is [Algs]' [AlgHom_Setoid], i.e. pointwise
   Leibniz [=] on carriers.  That is a property of the DONOR, which
   docs/INDEX.md's Instance/Ab.v bullet already flags, not a choice made
   here.

   ** The axiom boundary, stated up front

   [Variety] and its five satellites are closed under the global context.
   [GroupVariety] IS NOT, and cannot be: it reports
   [functional_extensionality_dep], inherited from Instance/Comp.v:358's
   [GroupEq], which is [Defined] with [functional_extensionality] at :370
   and :375.  That is structural rather than a proof-script accident.
   [EqSignature]'s [lhs_natural] and [rhs_natural] (:254, :257) ask for a
   LEIBNIZ equation between two [arity o → B] argument bundles that are
   only pointwise equal, and extensionality for functions out of a finite
   enumeration is not derivable in CIC — Test/ProbeVariety440.v's negative
   n1 records the refusal at the EMPTY arity, which is the root of every
   [functional_extensionality] in Instance/Comp.v.

   The boundary was measured on both sides.  A DEPTH-1 equation is
   axiom-free, because its naturality field IS [op_commute] with the
   argument bundle unchanged: [CommMagmaVariety] below is a commutative
   magma variety with [Print Assumptions] closed, and it is in this file
   precisely so that the obstruction is exhibited as a property of
   equation DEPTH and not of varieties.  An equation of depth ≥ 2, such as
   associativity, rebuilds the bundle and needs the axiom.

   Consequently [GroupVariety] is deliberately NOT in the
   [make print-assumptions] gate — gating it would make the axiom audit
   report a stdlib axiom — and docs/AXIOMS.md carries it instead, with
   this reason.  Every other constant here is gated.

   ** Not delivered

   No bridge to Theory/Lawvere/Model.v beyond a stated connection: see
   [variety_lawvere_connection] at the end of this file, which is a
   comment and not a theorem, and the follow-on issue it names.  No
   [GroupVariety ≅[Cat] Grp]: Instance/Variety/GroupComparison.v ships a fully
   faithful comparison functor instead and states why the isomorphism is
   not available.  No quotient of [Tree] by an equational congruence.  No
   removal of Instance/Comp.v's two commented-out instances at :189 and
   :223, which is an edit to that file and is surfaced rather than made. *)

(* Instance/Comp.v's record fields [carrier], [eq] and [map] would shadow
   the library's if this module were imported, so it is aliased and
   qualified throughout — the same decision, for the same reason, as
   Instance/Roster.v:588. *)
Module UA := Category.Instance.Comp.UniversalAlgebra.

Section Variety.

Context (S : UA.OpSignature).
Context (E : UA.EqSignature S).

(** ** Satisfaction, and the full subcategory it cuts out *)

(* [Subcategory]'s [sobj] lands in [Type], so satisfaction is stated as a
   [Type]-valued ∀ whose body is a Leibniz equation between two elements of
   the carrier.  It is DEFINITIONALLY the [equations] field of
   Instance/Comp.v:270, which is what makes the two presentations
   reflexivity-inverse below.

   Every coercion is written out.  Instance/Comp.v declares [eq :> Type]
   and [carrier :> Type] inside [Module UniversalAlgebra], and a module
   ALIAS does not activate coercions — only an [Import] would, which is
   the thing Instance/Roster.v:585 warns against because [eq], [carrier]
   and [map] would shadow the library's.  So [UA.eq S E] and
   [UA.carrier A] appear in full below wherever the coercion would
   otherwise fire. *)

Definition satisfies (A : UA.OpAlgebra S) : Type :=
  ∀ (e : UA.eq S E) (args : UA.eq_arity e → UA.carrier A),
    UA.lhs e args = UA.rhs e args.

Definition Variety_sub : Subcategory (@UA.Algs S) :=
  @Build_Subcategory (@UA.Algs S)
    satisfies
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition Variety : Category := Sub (@UA.Algs S) Variety_sub.

(* Full: every homomorphism between algebras that satisfy the laws is a
   morphism of the variety. *)
Definition Variety_Full : Full (@UA.Algs S) Variety_sub :=
  fun _ _ _ _ _ => I.

Definition Variety_Incl : Variety ⟶ @UA.Algs S := Incl (@UA.Algs S) Variety_sub.

Definition Variety_Incl_Faithful : Functor.Faithful Variety_Incl :=
  Incl_Faithful (@UA.Algs S) Variety_sub.

(** ** The record presentation, and its round trips *)

Definition Variety_pack (A : UA.Algebra S E) : Variety :=
  (UA.alg S E A; UA.equations S E A).

Definition Variety_unpack (x : Variety) : UA.Algebra S E :=
  {| UA.alg := `1 x ; UA.equations := `2 x |}.

(* Propositional [=] on the packed OBJECT data — the sanctioned case; no
   morphism equality is asserted. *)

Lemma Variety_unpack_pack (A : UA.Algebra S E) :
  Variety_unpack (Variety_pack A) = A.
Proof. destruct A; reflexivity. Qed.

Lemma Variety_pack_unpack (x : Variety) :
  Variety_pack (Variety_unpack x) = x.
Proof. destruct x; reflexivity. Qed.

(** ** The forgetful functor to Sets

    Awodey's §9.8 asks for the category AND its forgetful functor.  The
    carrier is a bare type, so it lands on the DISCRETE setoid
    (Lib/Setoid.v:65's [eq_Setoid]); the functor is faithful, which is the
    concreteness the free-algebra theorem consumes. *)

Program Definition Variety_Forget : Variety ⟶ Sets := {|
  fobj := fun A => {| carrier   := UA.carrier (`1 A)
                    ; is_setoid := eq_Setoid (UA.carrier (`1 A)) |};
  fmap := fun _ _ f => {| morphism := UA.map (`1 f) |}
|}.

Lemma Variety_Forget_Faithful : Functor.Faithful Variety_Forget.
Proof. construct; simpl in *; auto. Qed.

End Variety.

(* The signature is recoverable from the equation signature at every use
   site, so it is implicit throughout — [Variety E], not [Variety S E].
   [Arguments] here rather than inside the section, because a section's
   [Context] binders are explicit on the constants it closes over. *)
Arguments satisfies {_} _ _.
Arguments Variety_sub {_} _.
Arguments Variety {_} _.
Arguments Variety_Full {_} _.
Arguments Variety_Incl {_} _.
Arguments Variety_Incl_Faithful {_} _.
Arguments Variety_pack {_ _} _.
Arguments Variety_unpack {_ _} _.
Arguments Variety_unpack_pack {_ _} _.
Arguments Variety_pack_unpack {_ _} _.
Arguments Variety_Forget {_} _.
Arguments Variety_Forget_Faithful {_} _.

(** ** The group variety

    The instantiation Mac Lane's §V.6 and the issue ask for, under a name
    that does NOT collide with Instance/Grp.v's [Grp] — there is exactly
    one [Grp] in this tree and it is that one.

    THIS CONSTANT CARRIES [functional_extensionality_dep], for the reason
    given in the header: it mentions [GroupEq], which is [Defined] using
    the axiom.  It is not gated; docs/AXIOMS.md records it. *)

Definition GroupVariety : Category := Variety UA.GroupEq.

(* ℤ/2 under exclusive or, the witness Instance/Comp.v:405 already builds,
   as an OBJECT of the category rather than an inhabitant of a type. *)
Definition GroupVariety_Bool : GroupVariety := Variety_pack UA.Bool.

(** ** Where the axiom is not needed: a depth-1 variety

    Exhibited so that the obstruction above reads as a fact about equation
    DEPTH rather than about varieties.  One binary operation, one law
    (commutativity), whose two naturality fields are [op_commute] itself
    with the argument bundle passed through unchanged — so no bundle has to
    be rebuilt and no extensionality is needed.  [Print Assumptions] on
    every constant in this block says "Closed under the global context",
    and all of them are gated. *)

Inductive magma_op : Set := magma_mul.

Definition MagmaOp : UA.OpSignature :=
  {| UA.operation := magma_op ; UA.arity := fun _ => UA.binary |}.

Inductive comm_eq : Set := comm_law.

Definition comm_swap (i : UA.binary) : UA.binary :=
  match i with UA.Fst => UA.Snd | UA.Snd => UA.Fst end.

Definition CommEq : UA.EqSignature MagmaOp.
Proof.
  refine {| UA.eq       := comm_eq
          ; UA.eq_arity := fun _ => UA.binary
          ; UA.lhs      := fun (A : UA.OpAlgebra MagmaOp) _ args =>
                             UA.op A magma_mul args
          ; UA.rhs      := fun (A : UA.OpAlgebra MagmaOp) _ args =>
                             UA.op A magma_mul (fun i => args (comm_swap i))
         |}.
  - intros A B f [] args; exact (UA.op_commute A B f magma_mul args).
  - intros A B f [] args;
      exact (UA.op_commute A B f magma_mul (fun i => args (comm_swap i))).
Defined.

Definition CommMagmaVariety : Category := Variety CommEq.

(** ** The connection to Lawvere theories, stated and not proved

    Work item 3 of the issue asks that the connection to
    Theory/Lawvere/Model.v be RECORDED.  Here it is, as prose, because the
    proof is a separate development and is listed as not delivered.

    For a presentation ⟨S,E⟩ the associated Lawvere theory has [nat] for
    objects, the [E]-congruence classes of n-tuples of derived operators
    for morphisms m ~> n, and finite products given by addition; its
    [Models] in [Sets] (Theory/Lawvere/Model.v:77) ought to be equivalent
    to [Variety E].  Two things block the equivalence here and neither is
    incidental.  Building the theory needs the clone as a CATEGORY, with
    the congruence as its hom-setoid and the two propositional object
    equalities [law_zero_terminal] and [law_plus_product]
    (Theory/Lawvere.v:116).  And the comparison then meets the same wall as
    Instance/Variety/GroupComparison.v: [Models T Sets] has SETOID carriers where
    [Variety]'s are Leibniz types, so essential surjectivity needs
    quotients.  Instance/Variety/Clone.v supplies the derived operators and
    their substitution calculus, which is the first half of the first
    obstruction; the rest is filed as a follow-on. *)
