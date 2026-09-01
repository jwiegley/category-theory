(** * Translation endofunctors of a monoid, and their adjoints *)

From Coq Require Import Eqdep_dec.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Product.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Discrete.
Require Import Category.Construction.Comma.Special.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.

Generalizable All Variables.

(* nLab:      https://ncatlab.org/nlab/show/delooping
   nLab:      https://ncatlab.org/nlab/show/adjoint+functor
   nLab:      https://ncatlab.org/nlab/show/discrete+category
   nLab:      https://ncatlab.org/nlab/show/monoid
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, §IV.2, printed p. 90, Exercise 5

   THE EXERCISE.  Mac Lane's §IV.2 exercise regards a monoid M as a DISCRETE
   category — elements as OBJECTS, no non-identity arrows — and its
   multiplication as a bifunctor on that category.  The two partial
   applications of that bifunctor are the left and right translation
   endofunctors, x ↦ a·x and x ↦ x·a.  When M is a group, inversion supplies
   a right adjoint for each: translation by a⁻¹.  The exercise then asks
   whether the CONVERSE holds — whether a monoid all of whose translations
   have right adjoints must be a group.  (The wording of the exercise is
   taken from the catalogued item that commissioned this file rather than
   read off the page; the mathematics below stands on its own.)

   The converse DOES hold, and it is the substance of this file.  An
   adjunction L_a ⊣ R supplies, for every x and y, an INVERSE TRANSPOSE
   carrying hom(x, R y) to hom(a·x, y); in a discrete category those hom-sets
   are the identifications between a·x and y, and between x and R y.  Feeding
   the identity of R(1) to it at x := R 1, y := 1 yields a · R(1) ≈ 1 — a
   Leibniz `=` in the strict reading — so every element of M has a RIGHT
   inverse; and a monoid in which every element has a right inverse is a
   group.  That last step is [MonInverses_of_right_inverses] below, and it is
   reusable on its own.  Note how little of the adjunction is consumed: only
   the backward leg, at one pair of objects, applied to one identity.

   ** THE FORK: WHICH DISCRETE CATEGORY?

   "The discrete category on M" has two readings in a setoid library, and
   they are not interchangeable.  This file delivers BOTH and measures the
   difference rather than choosing silently.

   (a) [MonDiscrete M] — objects the carrier of M, a morphism x ~> y being a
       proof of the monoid's own `≈`.  This is Construction/Comma/Special.v's
       [DiscreteSetoidCat], reused rather than rebuilt, and it is the reading
       that file argues for at length (its lines 86-110): in a setoid library
       the identifications available between two elements are the inhabitants
       of `≈`, not of Rocq's `=`.  Over this category the development carries
       NO hypothesis on M beyond its being a monoid —
       [mon_group_iff_left_translation_adjoints] holds for an ARBITRARY
       [MonObject].

   (b) [MonDiscreteStrict M] — Instance/Discrete.v's [DiscreteCat] on the
       carrier, whose homs are proofs of Rocq's `=`.  This is the literal
       reading of "the category really is discrete (homs are equalities)".
       Over it the CONVERSE is still hypothesis-free
       ([strict_left_translation_adjoints_MonInverses]), because a Leibniz
       equality yields an `≈`; but the FORWARD direction is not, and the
       obstruction is exactly the one Construction/Comma/Special.v names.
       Building the transpose of a·x = y needs a⁻¹·(a·x) = x at LEIBNIZ
       equality, whereas the inverse laws give only `≈`.  The probe
       [probe_cancel_strict] pins that: [mon_inv_cancel_l] does not TYPE as
       the Leibniz statement, against the passing control [ctrl_cancel_equiv]
       at `≈`.  Read that probe precisely — it says conversion rejects the
       ascription at a VARIABLE monoid, NOT that no proof of the Leibniz form
       exists; for a monoid whose `≈` is `=` there of course is one, and
       [strict_cancel_l] instantiated at [Z3_MonStrict] is such a proof.

       So the forward direction is delivered under two explicit hypotheses,
       [MonStrict M] (`≈` implies `=`) and [MonUIP M] (uniqueness of identity
       proofs on the carrier), following the [HomStrict]/[HomUIP] pattern of
       Construction/Comma/Special.v.  [MonUIP] is needed because
       [DiscreteCat]'s hom-setoid is STRICT equality OF PROOFS, so both
       respectfulness proofs, both isomorphism laws and all four naturality
       clauses of [Adjunction] are equations between equality proofs.  Both
       hypotheses are free for a carrier with decidable equality
       ([MonUIP_dec], Hedberg via the stdlib's axiom-free [UIP_dec]).  THEY
       ARE SUFFICIENT AND ARE NOT SHOWN NECESSARY: no countermodel is offered
       and no forcing theorem is proved in either direction.

   The two categories are NOT convertible ([probe_categories_agree]) though
   they share their object type ([ctrl_objects_agree]); the passage
   [MonStrictToDiscrete] from (b) to (a) is hypothesis-free, while
   [MonDiscreteToStrict] the other way costs exactly [MonStrict] and
   [MonUIP] — the second of them because [fmap_id] there is an equation
   between two proofs of x = x.  No equivalence of categories is claimed.

   ** RELATION TO deloop_groupoid_iff — A DIFFERENT CATEGORIFICATION

   Structure/Groupoid.v:343 proves [deloop_groupoid_iff]: a monoid is a group
   exactly when its DELOOPING is a groupoid.  There the elements of M are the
   ARROWS of a one-object category.  Here they are the OBJECTS of a discrete
   category and the translations are ENDOFUNCTORS.  These are two different
   categorifications of one fact about M, and NEITHER is derived from the
   other below: no theorem below mentions the category [Deloop M], and
   Structure/Groupoid.v is required only for [MonInverses] with its
   accessors and [MonInverses_of], for [nat_plus_no_inverses], and for the
   [Z3] witnesses.  What
   the two share is their conclusion, [MonInverses M], which is deliberately
   NOT redefined here.

   ** WHAT IS DELIVERED

   - [MonDiscrete], the setoid-discrete category on a monoid, with objects
     and homs pinned by [eq_refl] and thinness recorded.
   - [MonMult], multiplication as a genuine BIFUNCTOR on it, and
     [LeftTranslation]/[RightTranslation] as endofunctors.
   - [left_translation_adjunction] : L_a ⊣ L_{a⁻¹} and
     [right_translation_adjunction] : R_a ⊣ R_{a⁻¹}, for an arbitrary monoid
     carrying [MonInverses].
   - [MonInverses_of_right_inverses] and [MonInverses_of_left_inverses]: a
     monoid with all right (resp. left) inverses is a group.
   - The biconditionals [mon_group_iff_left_translation_adjoints] and
     [mon_group_iff_right_translation_adjoints], which answer the exercise's
     question in the affirmative.
   - The LEFT-handed half of that again over [DiscreteCat], as
     [mon_group_iff_left_translation_adjoints_strict].
   - Witnesses: (ℕ, +) with a DIRECT refutation
     ([nat_translation_no_right_adjoint]) as well as the one through the
     biconditional; Z/3, whose inversion moves an element, so the left
     adjoint and the right adjoint are provably different functors.

   ** WHAT IS MEASURED RATHER THAN ASSERTED

   Strengths, tried strict-first:

     eq_refl   objects of [MonDiscrete M] are the carrier
     eq_refl   homs of [MonDiscrete M] are `≈`; of the strict one, `=`
     eq_refl   object types of the two discrete categories agree
     eq_refl   [fobj] and [fmap] of [LeftTranslation M a] and of
               [Partial_r (MonMult M) a] — BOTH data fields, so the
               translations ARE partial applications of the bifunctor on
               everything a consumer can observe
     eq_refl   likewise [RightTranslation] against [Partial_l]
     eq_refl   both comparison functors are the identity on objects
     eq_refl   the Z/3 and Z/2 computations
     REFUTED   the WHOLE-RECORD equality [LeftTranslation M a =
               Partial_r (MonMult M) a] ([probe_partial_record]).  [Functor]
               has primitive projections WITH eta, so record equality IS
               field equality; two of its five fields agree by [eq_refl] as
               above, and the remaining three are law fields built as
               separate opaque [Program] obligations on the two sides.  That
               localises the difference to those three.
     REFUTED   [MonDiscrete M = MonDiscreteStrict M]
     REFUTED   the homs of [MonDiscrete M] at a VARIABLE M are Rocq's `=`
               (they are at Z/3, whose `≈` IS `=`, which is why the probe is
               stated at a variable)
     REFUTED   the `≈`-cancellation law read as a Leibniz equation

   Which route was taken for the translations, and why: reading them off the
   bifunctor is CHEAPER — [Partial_r]/[Partial_l] discharge their three
   functor laws once and for all in Functor/Bifunctor/Partial.v, so the
   definition would cost no obligation at all, whereas the direct records
   below cost three apiece (each closed by [exact I], the hom-setoid of a
   thin category being trivially true).  The direct records are nevertheless
   what is shipped, so that the arrow action is legible in the source and so
   that Mac Lane's identification of the translations with the partial
   functors becomes a MEASURED fact rather than a definition; the four
   [*_partial_*] Examples in Block B are that measurement.

   Universes, read off BOTH the binder and the constraint block:

     [mon_group_iff_left_translation_adjoints@{u u0 u1 u2 u3 u4}] carries NO
     universe equation at all, and no `Set`; the monoid's three universes are
     only bounded.

     [MonDiscrete@{u u0 u1} : MonObject@{u u0 u1} -> Category@{u u0 u0}]
     IDENTIFIES the hom and proof universes — and the identification is in
     the BINDER while the block holds only two bounds, so reading the block
     alone gets it wrong.  It is INHERITED: [DiscreteSetoidCat@{u u0}] is
     declared with two universes and returns [Category@{u u0 u0}], its own
     constraint block being empty.  Nothing here adds to it and no repair is
     attempted (that file is not this file's to edit); it is NOT claimed
     unavoidable.

     [MonDiscreteStrict] carries explicit binders, and they are
     LOAD-BEARING: written unannotated, the same body minimizes so as to
     identify the hom and proof universes, whereas the annotated form leaves
     only the bound h <= p — [DiscreteCat@{o h p}] being properly annotated
     at its own declaration.  (Measured by compiling the same body twice,
     with and without binders; that measurement is NOT guarded in this
     file.)  But read what it buys: DOWNSTREAM the two levels minimize to
     the literal Set anyway — [LeftTranslationStrict] lands at
     Functor@{u Set Set u Set Set} — so the annotation buys freedom at
     [MonDiscreteStrict] itself and none at the strict headline.

     The strict headline's block contains `Set < _`, on an INTERNAL universe:
     [DiscreteCat]'s homs are Rocq's `eq`, hence `Prop`-valued, so the
     auxiliary [Sets] in which [Adjunction] states its hom-isomorphism
     minimizes its carrier universe to `Set`.  It does NOT restrict the
     monoid, and that is guarded rather than merely observed — the probe
     section at the end declares all three of a monoid's universes strictly
     above `Set` and both headlines still elaborate there.

     [DiscreteCat_Functor] (Instance/Discrete.v:59) is NOT used anywhere
     below: it is unannotated and pins its source at
     [DiscreteCat@{u Set Set}].  The functors out of the strict category are
     hand-written records instead.

   ** AUDIT

   104/104 constants closed under the global context — 66 source-declared
   heads plus 38 [Program] obligations that no source sweep sees, each
   queried by its fully qualified name.  The two enumerations reconcile
   exactly: nothing [Print Module] lists is missing from the source heads and
   nothing among the source heads is missing from [Print Module].  The file
   declares no [Record], [Class] or [Inductive], so there is no unlisted
   [Build_*].  Read the GRADE: that is a ONE-TIME measurement of all 104,
   not a standing gate.  The only stdlib import is [Eqdep_dec], for
   [UIP_dec], which is Hedberg's argument and carries no axiom.

   Name collisions were swept two ways over all 71 identifiers this file
   introduces (the 66 declared heads plus the 5 probe names, which declare
   nothing): by declaration head with the repository's usual regex, and — the
   stronger criterion — by WHOLE-WORD token occurrence ANYWHERE in ANY `.v`
   file of the worktree, this file excluded.  Zero hits under either
   criterion, at the revision this file was written against (reported as
   master e3ab9d22).  There are no record fields to sweep separately, no
   record being declared — which matters, since a record field is a global
   constant that a declaration-head sweep cannot see.

   Two names in the tree are near neighbours and are deliberately NOT
   shadowed, both verified at the lines given: [translation_functor]
   (Construction/Deloop/Functors.v:465) is a functor
   [Proset Z.le_preorder ⟶ Deloop Int_Plus] out of Awodey's cocycle
   construction, not a translation endofunctor; and [grp_translate]
   (Instance/Grp/Epi.v:467) is left translation as a setoid MAP on a coset
   space, not a functor at all.

   [make todo] grows by the five [Fail] lines below and by nothing else: no
   TODO, FIXME or jww is added.

   ** ENGINEERING FINDINGS

   Do not name a local variable [I] in a file whose obligation tactic is
   [exact I].  Measured both ways in this file's development: an obligation
   tactic set at top level still resolved [I] to [Logic.I] inside a section
   binding [I : MonInverses M], but the SAME tactic set INSIDE such a section
   resolved it to the section variable and every obligation failed with "the
   term I has type MonInverses M".  Every inverse witness below is therefore
   named [Inv].

   [Structure/Groupoid.v]'s [MonInverses] destructures as [minv]/[minv_l]/
   [minv_r]; [Construction/Deloop.v]'s [mon_inverse_unique] is what makes
   [MonInverses_of_right_inverses] two lines rather than a chase.

   ** NOT DELIVERED

   - No equivalence, and no isomorphism, between [MonDiscrete M] and
     [MonDiscreteStrict M] under any hypothesis; only the two comparison
     functors, and only their object actions are related.
   - No necessity result for [MonStrict] or [MonUIP], in either direction.
   - No strict-category analogue of [RightTranslation], hence no strict
     right-translation adjunction and no strict right-handed biconditional.
   - No unit or counit is named, and no triangle identity is stated; the
     adjunctions are delivered in the hom-set presentation only.  Over
     [MonDiscrete M] that costs little — the category is thin, so every
     component of a unit or counit is determined up to `≈` by its endpoints —
     but over [MonDiscreteStrict M] it is a genuine omission, that category
     being thin only under [MonUIP].
   - Nothing relates this to [deloop_groupoid_iff] beyond sharing
     [MonInverses]; in particular no functor between [Deloop M] and
     [MonDiscrete M] is built.
   - Nothing is said about monoid HOMOMORPHISMS, so there is no functor
     M ↦ [MonDiscrete M] and no naturality of any identification in M.
   - No [Instance] is registered: nothing here is meant for resolution.
   - The monoid record used is Construction/Deloop.v's [MonObject].  The tree
     carries several other notions of monoid (Structure/Monoid.v's
     [MonoidObject] over a monoidal base, Theory/Coq/Monoid.v's laws-free
     class, Instance/CMon.v's commutative [CMonObject], among others); none
     is related to this development here. *)

(** ** Block A: the discrete category on a monoid *)

(* The elements of M as objects, its own `≈` as the only identifications.
   [DiscreteSetoidCat] is Construction/Comma/Special.v:218, reused rather
   than rebuilt.  That file also explains why Instance/Proset.v's [Proset]
   was not the construction it wanted: [Proset] is stated over `Prop`-valued
   relations while `≈` is a `crelation`.  A `Prop`-squashed variant would in
   any case not obviously support the converse below, which reads an honest
   `≈` OUT of a hom-set — but that is an argument, not a measurement, and no
   squashed variant is built here. *)
Definition MonDiscrete (M : MonObject) : Category :=
  DiscreteSetoidCat (@is_setoid (mon_setoid M)).

Example mon_discrete_obj (M : MonObject) :
  obj[MonDiscrete M] = carrier M := eq_refl.

Example mon_discrete_hom (M : MonObject) (x y : carrier M) :
  (x ~{MonDiscrete M}~> y) = (x ≈ y) := eq_refl.

(* Thin: the hom-setoid identifies all parallel arrows.  This is what makes
   every law in Blocks B and D free — NOT those of the strict Block F, whose
   hom-setoid is strict equality of proofs — and it is [DiscreteSetoidCat]'s
   own property. *)
Lemma MonDiscrete_thin (M : MonObject) (x y : MonDiscrete M)
  (f g : x ~> y) : f ≈ g.
Proof. exact I. Qed.

(** ** Block B: multiplication as a bifunctor, and the translations *)

#[local] Obligation Tactic := repeat intro; exact I.

(* Mac Lane's "multiplication as a bifunctor": a functor from the product of
   the discrete category with itself.  Its arrow action IS [mon_op_respects],
   the field that makes multiplication respect `≈`. *)
Program Definition MonMult (M : MonObject) :
  MonDiscrete M ∏ MonDiscrete M ⟶ MonDiscrete M := {|
  fobj := fun p => mon_op (fst p) (snd p);
  fmap := fun x y f => mon_op_respects M _ _ (fst f) _ _ (snd f)
|}.

Program Definition LeftTranslation (M : MonObject) (a : carrier M) :
  MonDiscrete M ⟶ MonDiscrete M := {|
  fobj := fun x => mon_op a x;
  fmap := fun x y f => mon_op_respects M a a (reflexivity a) x y f
|}.

Program Definition RightTranslation (M : MonObject) (a : carrier M) :
  MonDiscrete M ⟶ MonDiscrete M := {|
  fobj := fun x => mon_op x a;
  fmap := fun x y f => mon_op_respects M x y f a a (reflexivity a)
|}.

Example left_translation_obj (M : MonObject) (a x : carrier M) :
  fobj[LeftTranslation M a] x = mon_op a x := eq_refl.

Example right_translation_obj (M : MonObject) (a x : carrier M) :
  fobj[RightTranslation M a] x = mon_op x a := eq_refl.

(* The translations ARE the partial applications of the bifunctor, on both
   data fields, by [eq_refl].  Note the handedness: [Partial_r F b] fixes the
   FIRST argument, so it is LEFT translation. *)
Example lt_partial_obj (M : MonObject) (a : carrier M) :
  fobj[LeftTranslation M a] = fobj[Partial_r (MonMult M) a] := eq_refl.

Example lt_partial_fmap (M : MonObject) (a : carrier M) :
  @fmap _ _ (LeftTranslation M a) = @fmap _ _ (Partial_r (MonMult M) a)
  := eq_refl.

Example rt_partial_obj (M : MonObject) (a : carrier M) :
  fobj[RightTranslation M a] = fobj[Partial_l (MonMult M) a] := eq_refl.

Example rt_partial_fmap (M : MonObject) (a : carrier M) :
  @fmap _ _ (RightTranslation M a) = @fmap _ _ (Partial_l (MonMult M) a)
  := eq_refl.

(** ** Block C: the cancellation calculus of a chosen inverse *)

Section Cancel.
Context (M : MonObject) (Inv : MonInverses M) (a : carrier M).

Lemma mon_inv_cancel_l (x : carrier M) :
  mon_op (minv Inv a) (mon_op a x) ≈ x.
Proof.
  rewrite mon_op_assoc, (minv_l Inv a).
  apply mon_op_unit_l.
Qed.

Lemma mon_inv_cancel_l' (x : carrier M) :
  mon_op a (mon_op (minv Inv a) x) ≈ x.
Proof.
  rewrite mon_op_assoc, (minv_r Inv a).
  apply mon_op_unit_l.
Qed.

Lemma mon_inv_cancel_r (x : carrier M) :
  mon_op (mon_op x a) (minv Inv a) ≈ x.
Proof.
  rewrite <- mon_op_assoc, (minv_r Inv a).
  apply mon_op_unit_r.
Qed.

Lemma mon_inv_cancel_r' (x : carrier M) :
  mon_op (mon_op x (minv Inv a)) a ≈ x.
Proof.
  rewrite <- mon_op_assoc, (minv_l Inv a).
  apply mon_op_unit_r.
Qed.

End Cancel.

(** ** Block D: inversion supplies the right adjoints *)

Section Adjoints.
Context (M : MonObject) (Inv : MonInverses M) (a : carrier M).

(* hom(a·x, y) → hom(x, a⁻¹·y). *)
Definition left_transpose (x y : carrier M) (p : mon_op a x ≈ y) :
  x ≈ mon_op (minv Inv a) y.
Proof.
  rewrite <- (mon_inv_cancel_l M Inv a x).
  now rewrite p.
Defined.

Definition left_untranspose (x y : carrier M)
  (q : x ≈ mon_op (minv Inv a) y) : mon_op a x ≈ y.
Proof.
  rewrite q.
  apply mon_inv_cancel_l'.
Defined.

(* Every remaining field of [Adjunction] — both isomorphism laws, both
   respectfulness proofs and all four naturality clauses — is an equation in
   a hom-setoid of [MonDiscrete M], hence trivially true; the obligation
   tactic in force discharges all eight. *)
Program Definition left_translation_adjunction :
  LeftTranslation M a ⊣ LeftTranslation M (minv Inv a) := {|
  adj := fun x y =>
    {| to   := {| morphism := left_transpose x y |}
     ; from := {| morphism := left_untranspose x y |} |}
|}.

(* hom(x·a, y) → hom(x, y·a⁻¹). *)
Definition right_transpose (x y : carrier M) (p : mon_op x a ≈ y) :
  x ≈ mon_op y (minv Inv a).
Proof.
  rewrite <- (mon_inv_cancel_r M Inv a x).
  now rewrite p.
Defined.

Definition right_untranspose (x y : carrier M)
  (q : x ≈ mon_op y (minv Inv a)) : mon_op x a ≈ y.
Proof.
  rewrite q.
  apply mon_inv_cancel_r'.
Defined.

Program Definition right_translation_adjunction :
  RightTranslation M a ⊣ RightTranslation M (minv Inv a) := {|
  adj := fun x y =>
    {| to   := {| morphism := right_transpose x y |}
     ; from := {| morphism := right_untranspose x y |} |}
|}.

End Adjoints.

(** ** Block E: the converse, and the biconditionals *)

(* The mathematical content of the converse, isolated: a monoid in which
   every element has a right inverse is a group.  With b := r a and
   c := r (r a) we have a·b ≈ 1 and b·c ≈ 1, so [mon_inverse_unique]
   (Construction/Deloop.v:159) gives a ≈ c, whence b·a ≈ b·c ≈ 1.

   Instance/Grp.v:208's [grp_mul_inv_r] is the MIRROR IMAGE of this — right
   inverses from left ones — but over that file's own [GrpObject] record, in
   which the inverse operation is a FIELD; it is a different statement over a
   different record, and no attempt is made here to derive either from the
   other. *)
Lemma MonInverses_of_right_inverses (M : MonObject)
  (r : carrier M → carrier M)
  (Hr : ∀ a : carrier M, mon_op a (r a) ≈ mon_unit) : MonInverses M.
Proof.
  refine {| minv := r ; minv_r := Hr |}.
  intro a.
  transitivity (mon_op (r a) (r (r a))).
  - apply mon_op_respects; [reflexivity |].
    exact (mon_inverse_unique M (r a) a (r (r a)) (Hr a) (Hr (r a))).
  - apply Hr.
Defined.

(* The mirror, for the right translations: all left inverses gives a group. *)
Lemma MonInverses_of_left_inverses (M : MonObject)
  (l : carrier M → carrier M)
  (Hl : ∀ a : carrier M, mon_op (l a) a ≈ mon_unit) : MonInverses M.
Proof.
  unshelve refine {| minv := l ; minv_l := Hl |}.
  intro a.
  transitivity (mon_op (l (l a)) (l a)).
  - apply mon_op_respects; [| reflexivity].
    symmetry.
    exact (mon_inverse_unique M (l a) (l (l a)) a (Hl (l a)) (Hl a)).
  - apply Hl.
Defined.

(* "Every left translation has a right adjoint", as DATA.  The library's ∃ is
   [sigT], so this is a function and no choice principle is consumed when the
   inverse operation is read off it. *)
Definition LeftTranslationAdjoints (M : MonObject) : Type :=
  ∀ a : carrier M,
    { R : MonDiscrete M ⟶ MonDiscrete M & LeftTranslation M a ⊣ R }.

Definition RightTranslationAdjoints (M : MonObject) : Type :=
  ∀ a : carrier M,
    { R : MonDiscrete M ⟶ MonDiscrete M & RightTranslation M a ⊣ R }.

(* The answer to the exercise's question, in the affirmative.  Forward:
   inversion supplies the adjoints.  Backward: the inverse transpose applied
   to the identity of R(1) is exactly a · R(1) ≈ 1. *)
Theorem mon_group_iff_left_translation_adjoints (M : MonObject) :
  MonInverses M ↔ LeftTranslationAdjoints M.
Proof.
  split.
  - intros Inv a.
    exists (LeftTranslation M (minv Inv a)).
    exact (left_translation_adjunction M Inv a).
  - intro H.
    unshelve refine (MonInverses_of_right_inverses M
      (fun a => fobj[projT1 (H a)] mon_unit) _).
    intro a.
    exact (from (@adj _ _ _ _ (projT2 (H a))
                  (fobj[projT1 (H a)] mon_unit) mon_unit)
             (reflexivity _)).
Defined.

Theorem mon_group_iff_right_translation_adjoints (M : MonObject) :
  MonInverses M ↔ RightTranslationAdjoints M.
Proof.
  split.
  - intros Inv a.
    exists (RightTranslation M (minv Inv a)).
    exact (right_translation_adjunction M Inv a).
  - intro H.
    unshelve refine (MonInverses_of_left_inverses M
      (fun a => fobj[projT1 (H a)] mon_unit) _).
    intro a.
    exact (from (@adj _ _ _ _ (projT2 (H a))
                  (fobj[projT1 (H a)] mon_unit) mon_unit)
             (reflexivity _)).
Defined.

(** ** Block F: the same over [DiscreteCat], where homs are Rocq's `=` *)

(* The two hypotheses, in the shape of Construction/Comma/Special.v:395-398's
   [HomStrict] and [HomUIP].  Sufficient for the forward direction below; NOT
   shown necessary. *)
Definition MonStrict (M : MonObject) : Type :=
  ∀ x y : carrier M, x ≈ y → x = y.

Definition MonUIP (M : MonObject) : Type :=
  ∀ (x y : carrier M) (p q : x = y), p = q.

(* Hedberg, via the stdlib's axiom-free [UIP_dec]. *)
Definition MonUIP_dec (M : MonObject)
  (dec : ∀ x y : carrier M, {x = y} + {x <> y}) : MonUIP M := UIP_dec dec.

(* The explicit binders are load-bearing: unannotated, this body minimizes so
   as to identify the hom and proof universes of the result. *)
Definition MonDiscreteStrict@{o h p m1 m2} (M : MonObject@{o m1 m2}) :
  Category@{o h p} := DiscreteCat@{o h p} (carrier M).

Example mon_discrete_strict_hom (M : MonObject) (x y : carrier M) :
  (x ~{MonDiscreteStrict M}~> y) = (x = y) := eq_refl.

(* Left translation on the strict category needs NO hypothesis: the arrow
   action is [f_equal], and both remaining functor laws close by destructing
   equality proofs.  There are only TWO obligations: the third field,
   [fmap_respects], is filled by instance resolution with
   [CMorphisms.reflexive_proper], the hom-setoid there being strict
   equality. *)
#[local] Obligation Tactic := idtac.

Program Definition LeftTranslationStrict (M : MonObject) (a : carrier M) :
  MonDiscreteStrict M ⟶ MonDiscreteStrict M := {|
  fobj := fun x => mon_op a x;
  fmap := fun x y (p : x = y) => f_equal (mon_op a) p
|}.
Next Obligation. intros M a x; reflexivity. Qed.
Next Obligation. intros M a x y z p q; now destruct p, q. Qed.

Section StrictAdjoint.
Context (M : MonObject) (HS : MonStrict M) (HU : MonUIP M).
Context (Inv : MonInverses M) (a : carrier M).

(* Where [MonStrict] is spent.  Within this section it occurs exactly twice,
   in the two definitions immediately below; everything after them goes
   through [strict_cancel_l]/[strict_cancel_r] and never mentions [HS].  It
   is spent once more elsewhere in the file, at [MonDiscreteToStrict] in
   Block G. *)
Definition strict_cancel_l (x : carrier M) :
  mon_op (minv Inv a) (mon_op a x) = x := HS _ _ (mon_inv_cancel_l M Inv a x).

Definition strict_cancel_r (y : carrier M) :
  mon_op a (mon_op (minv Inv a) y) = y := HS _ _ (mon_inv_cancel_l' M Inv a y).

Definition left_transpose_strict (x y : carrier M) (p : mon_op a x = y) :
  x = mon_op (minv Inv a) y :=
  eq_trans (eq_sym (strict_cancel_l x)) (f_equal (mon_op (minv Inv a)) p).

Definition left_untranspose_strict (x y : carrier M)
  (q : x = mon_op (minv Inv a) y) : mon_op a x = y :=
  eq_trans (f_equal (mon_op a) q) (strict_cancel_r y).

(* And this is where [MonUIP] is spent: every remaining field is an equation
   between two equality proofs. *)
#[local] Obligation Tactic := repeat intro; now apply HU.

Program Definition left_translation_strict_adjunction :
  LeftTranslationStrict M a ⊣ LeftTranslationStrict M (minv Inv a) := {|
  adj := fun x y =>
    {| to   := {| morphism := left_transpose_strict x y |}
     ; from := {| morphism := left_untranspose_strict x y |} |}
|}.

End StrictAdjoint.

Definition LeftTranslationAdjointsStrict (M : MonObject) : Type :=
  ∀ a : carrier M,
    { R : MonDiscreteStrict M ⟶ MonDiscreteStrict M &
      LeftTranslationStrict M a ⊣ R }.

(* The converse over the strict category needs NO hypothesis, because a
   Leibniz equality yields an `≈` outright.  The asymmetry with the forward
   direction is the whole content of the fork described in the header. *)
Definition strict_left_translation_adjoints_MonInverses (M : MonObject)
  (H : LeftTranslationAdjointsStrict M) : MonInverses M.
Proof.
  unshelve refine (MonInverses_of_right_inverses M
    (fun a => fobj[projT1 (H a)] mon_unit) _).
  intro a.
  refine (_ (from (@adj _ _ _ _ (projT2 (H a))
                     (fobj[projT1 (H a)] mon_unit) mon_unit) eq_refl)).
  intro e; simpl in e.
  now rewrite e.
Defined.

Theorem mon_group_iff_left_translation_adjoints_strict (M : MonObject)
  (HS : MonStrict M) (HU : MonUIP M) :
  MonInverses M ↔ LeftTranslationAdjointsStrict M.
Proof.
  split.
  - intros Inv a.
    exists (LeftTranslationStrict M (minv Inv a)).
    exact (left_translation_strict_adjunction M HS HU Inv a).
  - exact (strict_left_translation_adjoints_MonInverses M).
Defined.

(** ** Block G: comparing the two discrete categories *)

#[local] Obligation Tactic := repeat intro; exact I.

(* One way is free. *)
Program Definition MonStrictToDiscrete (M : MonObject) :
  MonDiscreteStrict M ⟶ MonDiscrete M := {|
  fobj := fun x => x;
  fmap := fun x y (p : x = y) =>
            match p with eq_refl => @id (MonDiscrete M) x end
|}.

Section Compare.
Context (M : MonObject) (HS : MonStrict M) (HU : MonUIP M).

(* The other costs exactly the two hypotheses: [MonStrict] for the arrow
   action, [MonUIP] for all three functor laws, each of which is an equation
   between equality proofs here.  (Three obligations, against two for
   [MonStrictToDiscrete], whose target is thin.) *)
#[local] Obligation Tactic := repeat intro; now apply HU.

Program Definition MonDiscreteToStrict :
  MonDiscrete M ⟶ MonDiscreteStrict M := {|
  fobj := fun x => x;
  fmap := fun x y f => HS x y f
|}.

End Compare.

Example mon_strict_to_discrete_obj (M : MonObject) (x : carrier M) :
  fobj[MonStrictToDiscrete M] x = x := eq_refl.

Example mon_discrete_to_strict_obj (M : MonObject) (HS : MonStrict M)
  (HU : MonUIP M) (x : carrier M) :
  fobj[MonDiscreteToStrict M HS HU] x = x := eq_refl.

(** ** Block H: witnesses *)

(* The discrete category on a monoid is not trivial: Z/3 gives two distinct
   objects with an EMPTY hom-set between them.  (This has to be checked at a
   concrete monoid: for a general M the hom x ~> y IS the type x ≈ y, which
   may perfectly well be inhabited for distinct x and y.) *)
Lemma Z3_two_objects : (Z3_0 : MonDiscrete Z3_Mon) <> Z3_1.
Proof. discriminate. Qed.

Lemma Z3_hom_empty : (Z3_0 ~{MonDiscrete Z3_Mon}~> Z3_1) → False.
Proof. intro p; discriminate. Qed.

(* (ℕ, +) is not a group, so by the biconditional its left translations
   cannot all have right adjoints.  The direct refutation is sharper: ONE
   translation suffices, and the contradiction is a computation.  From
   L_1 ⊣ R, the inverse transpose at the identity of R(0) reads
   1 + R(0) ≈ 0, that is S (R 0) = 0. *)
Lemma nat_translation_no_right_adjoint
  (R : MonDiscrete Nat_Plus ⟶ MonDiscrete Nat_Plus)
  (A : LeftTranslation Nat_Plus 1%nat ⊣ R) : False.
Proof.
  pose proof (from (@adj _ _ _ _ A (fobj[R] 0%nat) 0%nat) (reflexivity _))
    as e.
  simpl in e.
  discriminate.
Qed.

Corollary nat_no_right_adjoints : LeftTranslationAdjoints Nat_Plus → False.
Proof.
  intro H.
  exact (nat_plus_no_inverses
           (snd (mon_group_iff_left_translation_adjoints Nat_Plus) H)).
Qed.

(* The group witness.  Z/2 would be DEGENERATE here: every element is its own
   inverse ([bool_xor_self_adjoint]), so each left translation would be its
   own right adjoint and the adjunction would say nothing about inversion.
   Z/3 is the smallest group whose inversion moves an element
   (Structure/Groupoid.v's [Z3_inv_moves]), so over it the left adjoint and
   the right adjoint are provably different functors. *)
Definition Bool_Xor_Inverses : MonInverses Bool_Xor :=
  MonInverses_of Bool_Xor_Grp.

Example bool_xor_self_adjoint (b : carrier Bool_Xor) :
  minv Bool_Xor_Inverses b = b := eq_refl.

Definition Z3_Inverses : MonInverses Z3_Mon := MonInverses_of Z3_Grp.

Definition Z3_left_adjunction (a : carrier Z3_Mon) :
  LeftTranslation Z3_Mon a ⊣ LeftTranslation Z3_Mon (minv Z3_Inverses a) :=
  left_translation_adjunction Z3_Mon Z3_Inverses a.

Example Z3_left_adjoint_at :
  fobj[LeftTranslation Z3_Mon Z3_1] Z3_0 = Z3_1 := eq_refl.

Example Z3_right_adjoint_at :
  fobj[LeftTranslation Z3_Mon (minv Z3_Inverses Z3_1)] Z3_0 = Z3_2 := eq_refl.

Lemma Z3_adjoints_differ :
  fobj[LeftTranslation Z3_Mon Z3_1] Z3_0
    <> fobj[LeftTranslation Z3_Mon (minv Z3_Inverses Z3_1)] Z3_0.
Proof. discriminate. Qed.

(* Z/3's carrier setoid is Leibniz equality on [Z3] (Structure/Groupoid.v),
   so it also witnesses the strict reading, with both hypotheses discharged:
   [MonStrict] by the identity function, [MonUIP] by Hedberg. *)
Definition Z3_MonStrict : MonStrict Z3_Mon := fun _ _ p => p.

Definition Z3_dec (x y : Z3) : {x = y} + {x <> y}.
Proof.
  destruct x, y; solve [ left; reflexivity | right; discriminate ].
Defined.

Definition Z3_MonUIP : MonUIP Z3_Mon := MonUIP_dec Z3_Mon Z3_dec.

Definition Z3_strict_adjunction (a : carrier Z3_Mon) :
  LeftTranslationStrict Z3_Mon a
    ⊣ LeftTranslationStrict Z3_Mon (minv Z3_Inverses a) :=
  left_translation_strict_adjunction Z3_Mon Z3_MonStrict Z3_MonUIP
    Z3_Inverses a.

(** ** Block I: probes *)

(* FOUR negatives of TWO KINDS, plus a separate instrument check.  Each of
   the five was stripped of its [Fail] and compiled alone.
   [mon_probe_instrument], [probe_partial_record],
   [probe_categories_agree] and [probe_hom_is_eq] report `cannot unify`
   between two terms of one type (CONVERSION); [probe_cancel_strict] reports
   a plain type mismatch with NO `cannot unify` clause (TYPING).  Every
   negative is stated at a VARIABLE monoid, which matters for
   [probe_hom_is_eq]: at Z/3, whose `≈` IS `=`, that statement HOLDS, so a
   probe at a concrete monoid would have measured nothing.

   No constant a negative names, other than the negative's own name, is
   absent from a command that must SUCCEED (measured mechanically over the
   token sets, zero exceptions), so no guard here is vacuous. *)
Section Probes.
Context (M : MonObject) (Inv : MonInverses M) (a x y : carrier M).

(* Instrument check: [Fail] itself is doing something. *)
Fail Definition mon_probe_instrument : True = False := eq_refl.

Fail Definition probe_partial_record :
  LeftTranslation M a = Partial_r (MonMult M) a := eq_refl.

Fail Definition probe_categories_agree :
  MonDiscrete M = MonDiscreteStrict M := eq_refl.

Definition ctrl_objects_agree :
  obj[MonDiscrete M] = obj[MonDiscreteStrict M] := eq_refl.

Fail Definition probe_hom_is_eq :
  (x ~{MonDiscrete M}~> y) = (x = y) := eq_refl.

Definition ctrl_hom_is_equiv :
  (x ~{MonDiscrete M}~> y) = (x ≈ y) := eq_refl.

Definition ctrl_strict_hom_is_eq :
  (x ~{MonDiscreteStrict M}~> y) = (x = y) := eq_refl.

Fail Definition probe_cancel_strict :
  mon_op (minv Inv a) (mon_op a x) = x := mon_inv_cancel_l M Inv a x.

Definition ctrl_cancel_equiv :
  mon_op (minv Inv a) (mon_op a x) ≈ x := mon_inv_cancel_l M Inv a x.

End Probes.

(* The `Set` in the strict headline's constraint block sits on an internal
   universe — the auxiliary [Sets] in which [Adjunction] states its
   hom-isomorphism, whose carrier universe minimizes to `Set` because
   [DiscreteCat]'s homs are Rocq's `eq`, hence `Prop`-valued.  It does not
   restrict the monoid, and this section is the guard rather than a remark:
   all three of a monoid's universes are declared strictly above `Set` and
   both headlines still elaborate. *)
Section UniverseProbe.
Universe mo mh mp.
Constraint Set < mo.
Constraint Set < mh.
Constraint Set < mp.
Context (Mu : MonObject@{mo mh mp}).

Check (mon_group_iff_left_translation_adjoints Mu).
Check (mon_group_iff_left_translation_adjoints_strict Mu).
Check (MonDiscrete Mu).
Check (MonDiscreteStrict Mu).

End UniverseProbe.
