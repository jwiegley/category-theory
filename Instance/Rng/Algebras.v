(* [Coq.QArith.QArith] must be required BEFORE [Category.Lib]: it exports its
   own [equiv], which shadows [Setoid]'s, and the anonymous record
   [{| equiv := _ |}] used below is then rejected with the error
   "equiv: Not a projection".  Instance/FdVect.v records the same
   import-order gotcha. *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.QArith.QArith.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Slice.
Require Import Category.Construction.Subcategory.
Require Import Category.Functor.Diagonal.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Rng.

Generalizable All Variables.

#[local] Set Transparent Obligations.

(** * Commutative K-algebras as the coslice of commutative rings

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §II.6
    Exercise 1 (printed p. 47) [maclane:II.6:ex1].  The catalog's
    paraphrase of the exercise — its wording, not the book's — reads:
    "For a commutative ring K, show the comma category (K ↓ CRng) is the
    usual category of all small commutative K-algebras."  The comma
    category in question is §II.6's [maclane:II.6:def3], the category of
    objects S-under b for S the identity functor: objects are the arrows
    f : K ~> A of CRng, arrows ⟨f, A⟩ → ⟨f', A'⟩ are the CRng-arrows
    h : A ~> A' with h ∘ f = f'.
    nLab: https://ncatlab.org/nlab/show/category
    nLab: https://ncatlab.org/nlab/show/under+category
    nLab: https://ncatlab.org/nlab/show/associative+algebra
    Wikipedia: https://en.wikipedia.org/wiki/Associative_algebra

    WHAT IS ALREADY IN TREE.  The exercise's first half — the category
    [CRng] of commutative rings — is Instance/Rng.v's, not this file's:
    [CRng_Sub] (Instance/Rng.v:381) selects the commutative [RingObject]s
    and retains every [Rng]-morphism between them, [CRng] (:388) is
    [Sub Rng CRng_Sub], [CRng_Full] (:390) records the fullness, and
    [Int_CRng] (:398) is the witness ℤ.  Consequently an object of [CRng]
    is a dependent pair (R; proof that R is commutative) and a morphism of
    [CRng] is a pair (a [RigHom]; a trivially-true membership witness) —
    [Sub]'s shape, Construction/Subcategory.v:57.  [Coslice]
    (Construction/Slice.v:169) and its comma reading [Comma_Coslice]
    (Construction/Slice.v:181) are likewise pre-existing.

    WHAT THIS FILE ADDS.  The category of commutative K-algebras defined
    DIRECTLY — [KAlgObject]/[KAlgHom]/[KAlg] below — and the proof that it
    agrees with the coslice.  The definition is deliberately given in the
    ELEMENTARY spelling: a [KAlgObject K] is a bare [RingObject] together
    with a commutativity proof and a [RigHom] out of K's underlying ring,
    NOT a [CRng] object together with a [CRng] morphism.  The alternative
    spelling would make [KAlgObject K] literally the coslice's object type
    and the comparison a near-identity; the elementary one keeps a real
    (if small) repackaging on both sides — a [Sub] membership witness and
    two dependent pairs have to be assembled and taken apart — which is
    what the exercise is actually asking one to check.  What it costs is
    that the algebra's ring is not, on the nose, an object of [CRng]; what
    it buys is that the comparison functors below have content, and that
    the exact strength of the agreement can be measured rather than
    asserted.

    STRENGTH, MEASURED.  Two statements are delivered, and they are not
    the same statement:

      [KAlg_Coslice_strict_iso]  KAlg K ≅[StrictCat] Coslice CRng K
      [KAlg_Coslice_iso]         KAlg K ≅[Cat]       Coslice CRng K

    In this library [≅[Cat]] is EQUIVALENCE of categories, since [Cat]'s
    hom-setoid is [Functor_Setoid] (Instance/Cat.v:145), which identifies
    functors up to natural isomorphism.  The stronger [≅[StrictCat]] is
    the on-the-nose isomorphism: [StrictCat]'s hom-setoid is
    [Functor_StrictEq_Setoid] (Theory/Functor.v:606), which asks for
    F x = G x at Leibniz equality on objects together with the
    transported agreement of the morphism actions.  The strict reading
    DOES close here, so [KAlg_Coslice_iso] is DERIVED from it
    ([strict_equiv_implies_fun_equiv], Instance/StrictCat/ToCat.v:57) and
    is the weaker of the two; it carries the name the issue pins, which is
    also the form most of the library's consumers take.

    The two directions are not symmetric, and the asymmetry was measured,
    not guessed:

      * [KAlg_Coslice_round_obj] — going KAlg → Coslice → KAlg returns the
        object DEFINITIONALLY: it is proved by [eq_refl], and is stated as
        an [Example] so the claim is machine-checked rather than asserted.
        [KAlgObject] is a [Record] and primitive projections are in force
        (inherited from Lib/Setoid.v and Lib/Datatypes.v; [About kalg_ring]
        reports "is a primitive projection of KAlgObject"), so records have
        definitional eta and reassembling an algebra from its three
        projections is the algebra.

      * [Coslice_KAlg_round_obj] — going Coslice → KAlg → Coslice returns
        the object only up to a [destruct]-provable Leibniz equality.
        [eq_refl] is REJECTED for it; that was measured, by writing the
        statement out with [eq_refl] as its proof term and reading the
        error ("cannot unify ... and x"), not inferred.  The obstruction is
        that a coslice object over [CRng] is built from [sigT] (twice) and
        from the [True] of [CRng_Sub]'s [shom], and none of those has
        definitional eta in Coq — unlike the [Record] above; the proof
        therefore case-splits and only then closes by [reflexivity].  This
        is the usual record-eta culprit, and here it bites on exactly one
        side.

    Both morphism actions ARE definitional: each comparison functor leaves
    the underlying ring homomorphism untouched, so the two hom-level round
    trips ([KAlg_Coslice_round_hom], [Coslice_KAlg_round_hom]) close by
    [reflexivity] — on the [KAlg] side after one [intro], which only
    unfolds the hom-setoid to the pointwise form [Rng] gives it, since
    setoid [reflexivity] unifies the two sides of the RELATION and the
    relation there is still folded.

    THE COMMA READING.  [KAlg_Comma_iso] composes the above with
    [Comma_Coslice] to land at (=(K) ↓ Id), the shape Mac Lane's
    [maclane:II.6:def3] writes; it is at [Cat] strength, since
    [Comma_Coslice] is stated there.

    UNIVERSES, measured on all 35 NAMED constants of this file with
    [About] under [Set Printing Universes] (the file's four [Program
    Definition]s contribute twelve further obligation constants, each
    also measured for assumptions — 47 in all — but they are transparent
    and carry no universe content of their own).  Every one of them is universe
    polymorphic (the flag is inherited from Lib/Setoid.v).  Three things
    are worth naming, and the first two are the DONORS' doing, not this
    file's:

      * [KAlg K : Category@{o h h}] identifies the hom and proof
        universes.  That is [Rng]'s own shape — [Rng@{u u0} :
        Category@{u u0 u0}] (Instance/Rng.v:80), which comes from
        [RigHom_Setoid : Setoid@{h h}] (Theory/Algebra/Rig.v:184) — and
        [CRng] carries it through [Sub].  Nothing here narrows it.

      * Six constants print a literal [Set] as a universe instance
        argument: [Q_KAlg], [Int_to_Q_KAlg], [Int_to_Q_triangle],
        [Q_KAlg_in_Coslice], [Z_KAlg], [Z_KAlg_unit_unique].  In each case
        the donor is already pinned: [ZtoQ] is typed
        [hom Int_Ring@{Set Set Set} Q_Ring@{Set Set Set}]
        (Instance/Rng.v:461), and [rng_from_Z] takes
        [R : RingObject@{Set Set Set}] (Instance/Rng.v:332).  Three
        further constants ([Q_KAlg_unit_computes],
        [Q_KAlg_unit_not_surjective], [Q_KAlg_is_canonical]) mention
        [Q_KAlg] and inherit the same instance without printing it.  The [KAlg] spine and both isomorphisms carry no [Set]
        instance, and [Int_KAlg] is fully polymorphic.

      * At either isomorphism three of [KAlg]'s four universe parameters
        collapse to one.  That is what stating an [Isomorphism] in ANY
        category of categories costs — both categories must be objects of
        one and the same instance — and it is NOT specific to [Cat]: the
        collapse is already present at [KAlg_Coslice_strict_iso], since
        [StrictCat] has the same [obj := Category].  Taking the strict form
        does not keep the universes apart (audit-corrected).

    These statements are scoped to the constants of this file, each
    measured individually; nothing is claimed about the donors' other
    constants.

    WHERE COMMUTATIVITY ENTERS.  [kalg_comm] is not decoration: it is
    literally [CRng_Sub]'s membership predicate, recorded by
    [kalg_comm_is_CRng_membership], whose proof term is the field itself
    ([:= kalg_comm A], no tactic).  It is what lets the comparison land in
    [Coslice CRng K] rather than [Coslice Rng (`1 K)] — drop it and the
    coslice one gets is the category of (not necessarily commutative)
    rings under K, which is NOT the category of commutative K-algebras.
    K's own commutativity is carried by K : CRng and is never used below;
    the exercise supplies it because without it "K-algebra" in the usual
    sense is not the right notion.

    WHAT THIS DOES NOT SAY, deferred and disclosed.

      * Non-commutative K-algebras are not treated.  The same coslice
        taken in [Rng] would give rings under K, which is a different and
        larger notion than a K-algebra in the non-commutative sense (there
        the structure map is required to land in the CENTRE, a condition
        that is automatic exactly when the target is commutative).  No
        centre-valued variant is built here.

      * The MODULE-THEORETIC definition is not connected up.  The usual
        textbook definition of a K-algebra is a K-module (Instance/Mod.v's
        [RModObject]) carrying a bilinear multiplication, i.e. a ring plus
        a module structure plus a compatibility law.  The coslice
        definition SIDESTEPS that: for a COMMUTATIVE K the structure map
        K ~> A determines the module action by k · a := f(k)·a, and
        conversely, so the two definitions agree — but that agreement is a
        theorem about [RModObject] and is not proved here.  This file
        proves only the comparison the exercise asks for, between the
        direct definition and the coslice.  Nothing below mentions
        [RModObject], and no claim is made that [KAlg] is equivalent to a
        category of modules.

      * "Small" in the exercise's statement is not formalized as a size
        condition; the library's [Theory/Size.v] vocabulary is not
        invoked, and the categories here sit wherever their universe
        parameters put them. *)

(** ** The direct definition *)

(* A commutative K-algebra: a commutative ring together with a
   homomorphism out of K.  The three fields are, in order, the underlying
   ring, its commutativity, and the structure map. *)
Record KAlgObject (K : CRng) := {
  kalg_ring : RingObject;
  kalg_comm : ∀ a b, rig_mul kalg_ring a b ≈ rig_mul kalg_ring b a;
  kalg_unit : `1 K ~{Rng}~> kalg_ring
}.

Arguments kalg_ring {K} _.
Arguments kalg_comm {K} _ _ _.
Arguments kalg_unit {K} _.

(* A morphism of K-algebras is a ring homomorphism commuting with the two
   structure maps.  The orientation of the triangle is [Coslice]'s
   (Construction/Slice.v:171, `2 y ≈ f ∘ `2 x), so that the comparison
   below needs no transposition. *)
Definition KAlgHom {K : CRng} (A B : KAlgObject K) : Type :=
  ∃ f : kalg_ring A ~{Rng}~> kalg_ring B, kalg_unit B ≈ f ∘ kalg_unit A.

(* Two K-algebra morphisms are equal when their underlying ring
   homomorphisms are; the triangle proof is irrelevant.  This matches
   [Coslice]'s convention (Construction/Slice.v:172). *)
Program Definition KAlgHom_Setoid {K : CRng} (A B : KAlgObject K) :
  Setoid (KAlgHom A B) := {|
  equiv := fun f g => `1 f ≈ `1 g
|}.
Next Obligation.
  constructor.
  - intros f a; reflexivity.
  - intros f g Hfg a; symmetry; apply Hfg.
  - intros f g h Hfg Hgh a; transitivity (`1 g a); [ apply Hfg | apply Hgh ].
Defined.

Lemma kalg_id_triangle {K : CRng} (A : KAlgObject K) :
  kalg_unit A ≈ id ∘ kalg_unit A.
Proof. now rewrite id_left. Defined.

Lemma kalg_comp_triangle {K : CRng} {A B C : KAlgObject K}
      (f : KAlgHom B C) (g : KAlgHom A B) :
  kalg_unit C ≈ (`1 f ∘ `1 g) ∘ kalg_unit A.
Proof.
  rewrite <- comp_assoc.
  rewrite <- (`2 g).
  exact (`2 f).
Defined.

Program Definition KAlg (K : CRng) : Category := {|
  obj     := KAlgObject K;
  hom     := @KAlgHom K;
  homset  := @KAlgHom_Setoid K;
  id      := fun A => (id; kalg_id_triangle A);
  compose := fun _ _ _ f g => (`1 f ∘ `1 g; kalg_comp_triangle f g)
|}.
Next Obligation.
  intros f1 f2 Hf g1 g2 Hg a.
  transitivity (rig_map (`1 f1) (rig_map (`1 g2) a)).
  - apply (proper_morphism (rig_map (`1 f1))), Hg.
  - apply Hf.
Defined.

(* The commutativity field IS [CRng_Sub]'s membership predicate: this term
   typechecks with the field handed over verbatim.  That is what makes the
   comparison below land in a coslice over [CRng]. *)
Example kalg_comm_is_CRng_membership (K : CRng) (A : KAlgObject K) :
  sobj Rng CRng_Sub (kalg_ring A) := kalg_comm A.

(** ** The comparison *)

(* An algebra becomes an object under K: package the ring with its
   commutativity to get an object of [CRng], and the structure map with
   [CRng_Sub]'s trivial membership witness to get a morphism of [CRng].
   On morphisms, the triangle carries over verbatim — `2 f is handed to
   the coslice unchanged. *)
Program Definition KAlg_to_Coslice (K : CRng) : KAlg K ⟶ Coslice CRng K := {|
  fobj := fun A => ((kalg_ring A; kalg_comm A); (kalg_unit A; I));
  fmap := fun A B f => ((`1 f; I); `2 f)
|}.

(* ...and back: forget the packaging. *)
Program Definition Coslice_to_KAlg (K : CRng) : Coslice CRng K ⟶ KAlg K := {|
  fobj := fun x => {| kalg_ring := `1 (`1 x);
                      kalg_comm := `2 (`1 x);
                      kalg_unit := `1 (`2 x) |};
  fmap := fun x y g => (`1 (`1 g); `2 g)
|}.

(** ** The round trips *)

(* KAlg → Coslice → KAlg is the identity on objects DEFINITIONALLY: the
   round trip rebuilds the record from its three projections, and records
   have eta here. *)
Example KAlg_Coslice_round_obj (K : CRng) (A : KAlg K) :
  fobj[Coslice_to_KAlg K] (fobj[KAlg_to_Coslice K] A) = A := eq_refl.

(* Coslice → KAlg → Coslice is the identity on objects only up to a
   [destruct]-provable equality: [sigT] (twice) and the [True] of
   [CRng_Sub]'s [shom] have no definitional eta, so [eq_refl] does not
   typecheck here and the proof must case-split first. *)
Lemma Coslice_KAlg_round_obj (K : CRng) (x : Coslice CRng K) :
  fobj[KAlg_to_Coslice K] (fobj[Coslice_to_KAlg K] x) = x.
Proof.
  destruct x as [[R comm] [u t]]; destruct t; reflexivity.
Defined.

(* Both morphism actions leave the underlying ring homomorphism alone, so
   both hom-level round trips are [reflexivity].  On the coslice side the
   two objects are only propositionally equal, so the statement is made at
   the underlying [Rng]-morphism — which is exactly what either category's
   hom-setoid compares. *)
Lemma KAlg_Coslice_round_hom (K : CRng) (A B : KAlg K) (f : A ~> B) :
  fmap[Coslice_to_KAlg K] (fmap[KAlg_to_Coslice K] f) ≈ f.
Proof. intro a; reflexivity. Qed.

Lemma Coslice_KAlg_round_hom (K : CRng) (x y : Coslice CRng K) (g : x ~> y) :
  `1 (`1 (fmap[KAlg_to_Coslice K] (fmap[Coslice_to_KAlg K] g))) ≈ `1 (`1 g).
Proof. reflexivity. Qed.

(** ** The isomorphism *)

(* Mac Lane's exercise at on-the-nose strength: an isomorphism of
   categories, not merely an equivalence.  Its two components say that the
   composites are strictly equal to the identity functors.  On the coslice
   side the object component is [Coslice_KAlg_round_obj], which reduces to
   [eq_refl] once its argument is a literal pair — which is why the
   coherence goal is discharged by case-splitting on the two objects before
   appealing to reflexivity; on the algebra side the object component is
   [eq_refl] outright. *)
Definition KAlg_Coslice_strict_iso (K : CRng) :
  KAlg K ≅[StrictCat] Coslice CRng K.
Proof.
  unshelve refine (@Build_Isomorphism StrictCat (KAlg K) (Coslice CRng K)
    (KAlg_to_Coslice K) (Coslice_to_KAlg K) _ _).
  - (* to ∘ from ≈ id, on the coslice *)
    exists (Coslice_KAlg_round_obj K).
    intros x y f.
    destruct x as [[Rx cx] [ux tx]], y as [[Ry cy] [uy ty]].
    destruct tx, ty.
    simpl.
    reflexivity.
  - (* from ∘ to ≈ id, on the algebras; the object component is [eq_refl] *)
    exists (fun _ => eq_refl).
    intros A B f; simpl.
    reflexivity.
Defined.

(* The two composites, named: each is strictly equal to an identity
   functor.  These are the round trips at FUNCTOR level, the object- and
   hom-level statements above being their components. *)
Definition KAlg_Coslice_to_from (K : CRng) :
  @equiv _ (@homset StrictCat (Coslice CRng K) (Coslice CRng K))
    (@compose StrictCat _ _ _ (KAlg_to_Coslice K) (Coslice_to_KAlg K))
    (@id StrictCat (Coslice CRng K)) :=
  iso_to_from (KAlg_Coslice_strict_iso K).

Definition KAlg_Coslice_from_to (K : CRng) :
  @equiv _ (@homset StrictCat (KAlg K) (KAlg K))
    (@compose StrictCat _ _ _ (Coslice_to_KAlg K) (KAlg_to_Coslice K))
    (@id StrictCat (KAlg K)) :=
  iso_from_to (KAlg_Coslice_strict_iso K).

(* The same statement read in [Cat], where functors are compared up to
   natural isomorphism.  This is the WEAKER reading — [≅[Cat]] in this
   library is equivalence of categories — and is recorded because it is
   the form most consumers take. *)
Definition KAlg_Coslice_iso (K : CRng) : KAlg K ≅[Cat] Coslice CRng K :=
  @Build_Isomorphism Cat (KAlg K) (Coslice CRng K)
    (KAlg_to_Coslice K) (Coslice_to_KAlg K)
    (strict_equiv_implies_fun_equiv _ _ (KAlg_Coslice_to_from K))
    (strict_equiv_implies_fun_equiv _ _ (KAlg_Coslice_from_to K)).

(* The comma reading, Mac Lane's own shape (K ↓ CRng): compose with
   [Comma_Coslice] (Construction/Slice.v:181).  At [Cat] strength, because
   that is where [Comma_Coslice] is stated. *)
Definition KAlg_Comma_iso (K : CRng) : KAlg K ≅[Cat] (=(K) ↓ Id) :=
  iso_compose (Comma_Coslice CRng K) (KAlg_Coslice_iso K).

(** ** Witnesses *)

(* ℤ is a ℤ-algebra by way of the identity structure map. *)
Definition Int_KAlg : KAlgObject Int_CRng :=
  Build_KAlgObject Int_CRng Int_Ring Int_Ring_commutative (@id Rng Int_Ring).

Example Int_KAlg_unit_computes :
  rig_map (kalg_unit Int_KAlg) 3%Z = 3%Z := eq_refl.

(* ℚ is commutative, hence an object of [CRng]... *)
Lemma Q_Ring_commutative : ∀ a b, rig_mul Q_Ring a b ≈ rig_mul Q_Ring b a.
Proof. intros a b; simpl; apply Qmult_comm. Qed.

Definition Q_CRng : CRng := (Q_Ring; Q_Ring_commutative).

(* ...and a ℤ-algebra by the inclusion ℤ → ℚ, a genuinely non-identity
   structure map: Instance/Rng.v's [ZtoQ_not_surjective] shows it misses
   1/2, so this algebra is not its own base ring in disguise. *)
Definition Q_KAlg : KAlgObject Int_CRng :=
  Build_KAlgObject Int_CRng Q_Ring Q_Ring_commutative ZtoQ.

Example Q_KAlg_unit_computes :
  rig_map (kalg_unit Q_KAlg) 3%Z = inject_Z 3 := eq_refl.

Corollary Q_KAlg_unit_not_surjective :
  (∀ q : Q, exists z : Z, rig_map (kalg_unit Q_KAlg) z == q)%Q → False.
Proof. exact ZtoQ_not_surjective. Qed.

(* A non-identity morphism of ℤ-algebras: the inclusion itself. *)
Lemma Int_to_Q_triangle : kalg_unit Q_KAlg ≈ ZtoQ ∘ kalg_unit Int_KAlg.
Proof. now rewrite id_right. Qed.

Definition Int_to_Q_KAlg : Int_KAlg ~{KAlg Int_CRng}~> Q_KAlg :=
  (ZtoQ; Int_to_Q_triangle).

(* More generally, EVERY commutative ring is a ℤ-algebra, canonically:
   [Rng_Initial_Z] (Instance/Rng.v:369) makes ℤ initial in [Rng], so the
   structure map is not a choice.  This is the general reason the coslice
   under ℤ is the whole of [CRng] again — a statement not made here. *)
Definition Z_KAlg (A : CRng) : KAlgObject Int_CRng :=
  Build_KAlgObject Int_CRng (`1 A) (`2 A) (rng_from_Z (`1 A)).

(* ...and canonically means uniquely: any structure map out of ℤ on any
   ℤ-algebra agrees with the canonical one, by [rng_from_Z_unique]. *)
Lemma Z_KAlg_unit_unique (A : KAlgObject Int_CRng) (z : Z) :
  rig_map (kalg_unit A) z ≈ rig_map (kalg_unit (Z_KAlg (kalg_ring A; kalg_comm A))) z.
Proof. apply rng_from_Z_unique. Qed.

(* In particular the ℚ witness's chosen structure map IS the canonical one:
   the two descriptions of ℚ as a ℤ-algebra agree.  This is also where
   [Q_CRng] is exercised — [(kalg_ring Q_KAlg; kalg_comm Q_KAlg)] and
   [Q_CRng] are the same pair, so [Z_KAlg_unit_unique] applies at it
   directly. *)
Example Q_KAlg_is_canonical (z : Z) :
  rig_map (kalg_unit Q_KAlg) z ≈ rig_map (kalg_unit (Z_KAlg Q_CRng)) z.
Proof. exact (Z_KAlg_unit_unique Q_KAlg z). Qed.

(* The witnesses transport across the comparison, so the coslice is
   inhabited too, on the nose. *)
Example Q_KAlg_in_Coslice :
  fobj[KAlg_to_Coslice Int_CRng] Q_KAlg = ((Q_Ring; Q_Ring_commutative); (ZtoQ; I))
  := eq_refl.
