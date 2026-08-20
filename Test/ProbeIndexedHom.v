(** * Boundary probes for the indexed hom-set bijections

    Companion to Structure/Limit/Indexed/Hom.v (issue #320; Mac Lane §III.3
    def 2, Riehl §3.1 Remark 3.1.27 clauses (i) and (ii)).  **If the [Fail]
    commands below stop failing, this file breaks the build.**

    THE TWO KINDS OF NEGATIVE ARE NOT THE SAME AND ARE NOT DESCRIBED WITH
    ONE WORD.

    (1) FORMABILITY.  Five [Fail Check]s, in two groups, both about
    universes.

    Group (1a), three negatives.  The comparison map
    [iprod_hom_transform] — and everything built on it — requires the INDEX
    universe to sit at or below the ambient category's HOM universe.  The
    reason is that its source is the hom-functor [Curried_CoHom C q], whose
    objects ARE the hom-setoids of [C]; a [SetoidObject] carries its
    [Setoid] as a field, and neither record is cumulative in this library
    (measured: lifting a [Setoid@{a a}] to a [Setoid@{b b}] with [a < b] is
    rejected, and likewise for [SetoidObject]), so the target [Sets]'
    carrier universe is forced EQUAL to [C]'s hom universe rather than
    merely above it.  The bound on the index follows.
    The bound is NOT inherited: the target functor [iprod_hom_functor]
    alone tolerates a strictly larger index (its object action builds a
    fresh dependent-function type through [Sets_iprod_obj], which lifts),
    and so does the hom-functor alone, so the two positive controls of this
    group locate the rejection at the [Transform] that puts them in ONE
    functor category, not at either functor.

    Group (1b), two negatives.  The two LIMIT-shaped bridges
    [limit_hom_iso] and [colimit_hom_iso] are stated with [{A : Set}], and
    that binder is the COMBINATION of a donor restriction with the group
    (1a) bound — neither alone forces it.  [Structure/Limit/Product.v]'s
    [iprod] is over [C : Category@{u Set Set}] (the [DiscreteCat] hom-setoid
    is strict equality), with its INDEX universe free; the two controls here
    show [Limit (DiscreteCat_Functor f)] and [iprod f L] are both formable
    at a large index over such a [C].  Adding the group (1a) bound at
    [C]'s hom universe, which is [Set] here, is what cuts the index down to
    [Set].

    Scope these two negatives precisely: they fail because the bridges are
    DECLARED [{A : Set}], so they would fail for that reason whatever the
    universe situation, and they cannot by themselves detect that the binder
    is forced rather than stylistic.  The separating power comes from the two
    controls plus [iprod_hom_transform]'s own signature, and NOT from these
    two negatives alone.  The half they do not measure was checked outside
    the tree and holds: writing either bridge with [{A : Type}] is rejected
    ("cannot ensure that [Type@{u}] is a subtype of [Set]"), so the binder is
    forced.  That variant is not landed here as a sixth negative; it is the
    one that would notice if the pin ever stopped being necessary.

    (2) CONVERSION.  Two claims of Leibniz equality are rejected because
    the round trip through the mediator is not definitional — it is what the
    universal property's uniqueness clause proves.  These are [Fail
    Definition ... := eq_refl] and not [Fail Example ... : T.]: a failing
    type ascription would guard only the statement, whereas what is claimed
    is convertibility of the two terms.  Five controls across the two
    sections are the strict readings that DO hold, so the rejection is
    attributable
    to the round trip and not to the [transform]/[morphism] projections
    being stuck; at [Sets] a further control shows the agreement holding one
    level in, at the underlying map, which locates the rejection precisely at
    the [proper_morphism] certificate.

    COUNTS.  Seven negatives — five formability, two conversion — and ten
    positive controls.  This is not a one-to-one pairing: the controls of
    each group serve that group's negatives jointly.  The instrument itself
    was checked — wrapping [Fail] around a succeeding command reports "The
    command has not failed!" and aborts compilation — and every negative was
    compiled once with the [Fail] stripped, to confirm the error is the
    intended one:

      - group (1a), three reports of "universe inconsistency: Cannot
        enforce ua <= uh because uh < ua", naming the declared universes;
      - group (1b), two reports of "universe inconsistency: Cannot enforce
        ub <= Set";
      - group (2), two "cannot unify" conversion errors.

    The import list is the target file's own, in the target file's order,
    plus the target file itself. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.
Require Import Category.Instance.Discrete.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Indexed.Hom.

Generalizable All Variables.

(** ** (1a) An index universe strictly above the ambient hom universe *)

Section IndexAboveHoms.

Universes uo uh ua.
Constraint uh < ua.

Context (C : Category@{uo uh uh}) (A : Type@{ua}) (f : A -> C).

(* Positive control 1: the TARGET functor alone accepts the large index —
   its object action is a fresh dependent-function setoid, which lifts. *)
Check (iprod_hom_functor f).

(* Positive control 2: the coproduct-side target functor likewise. *)
Check (icoprod_hom_functor f).

(* Positive control 3: the SOURCE functor is formable at this category, so
   neither half of the comparison is what gets rejected. *)
Check (fun q : C => fobj[Curried_CoHom C] q).

(* Negative 1: the comparison map itself is not formable — the two functors
   have to live in ONE [Sets], and the hom-functor pins that [Sets]' carrier
   universe to [C]'s hom universe. *)
Fail Check (fun (q : C) (proj : forall a : A, q ~> f a) =>
              @iprod_hom_transform C A f q proj).

(* Negative 2: hence neither is the isomorphism. *)
Fail Check (fun (q : C) (proj : forall a : A, q ~> f a)
                (H : @IsIndexedProduct C A f q proj) =>
              @iprod_hom_iso C A f q proj H).

(* Negative 3: the coproduct side is the same statement at [C^op] and
   inherits the same bound. *)
Fail Check (fun (p : C) (inj : forall a : A, f a ~> p) =>
              @icoprod_hom_transform C A f p inj).

End IndexAboveHoms.

(** ** (1b) The limit-shaped bridges, and why they carry [{A : Set}] *)

Section LimitShapeIndex.

Universes uo ub.
Constraint Set < ub.

(* [DiscreteCat]'s hom-setoid is strict equality, so [Limit
   (DiscreteCat_Functor f)] pins [C]'s hom and proof universes to [Set];
   that much is the donor's, and it leaves the INDEX free. *)
Context (C : Category@{uo Set Set}) (A : Type@{ub}) (f : A -> C).

(* Positive control 4: the limit shape IS formable at this large index. *)
Check (Limit (DiscreteCat_Functor f)).

(* Positive control 5: so is the product object read off it. *)
Check (fun L : Limit (DiscreteCat_Functor f) => @iprod C A f L).

(* Negative 4: the hom-set bijection at that limit is not — the group (1a)
   bound now reads "index at or below [Set]". *)
Fail Check (fun L : Limit (DiscreteCat_Functor f) => @limit_hom_iso C A f L).

(* Negative 5: dually. *)
Fail Check (fun L : Limit (@DiscreteCat_Functor A (C^op) f) =>
              @colimit_hom_iso C A f L).

End LimitShapeIndex.

(** ** (2) The round trip is not definitional *)

Section Conversion.

Context {C : Category}.
Context {A : Type}.
Context {f : A -> C}.
Context {q : C}.
Context {proj : forall a : A, q ~> f a}.
Context (H : IsIndexedProduct f q proj).
Context (c : C).
Context (u : c ~> q).
Context (fam : forall a : A, c ~> f a).

(* Positive control 6: the forward leg IS the comparison map, on the nose. *)
Definition probe_to_control :
  to (iprod_hom_iso H) = iprod_hom_transform f q proj := eq_refl.

(* Positive control 7: the backward leg's value IS the mediator named by the
   pre-existing [∃!] accessor, on the nose. *)
Definition probe_from_control :
  transform (from (iprod_hom_iso H)) c fam = unique_obj (iprod_desc H fam)
  := eq_refl.

(* Positive control 8: and the forward leg computes to restriction along the
   projections. *)
Definition probe_transform_control :
  transform (to (iprod_hom_iso H)) c u = fun a : A => proj a ∘ u := eq_refl.

(* Negative 6: but the round trip does NOT compute.  Recovering [u] from the
   family it restricts to is exactly the uniqueness clause of [iprod_desc],
   a [≈]-level fact with no definitional content; [iso_from_to] is where it
   is discharged. *)
Fail Definition probe_roundtrip :
  transform (from (iprod_hom_iso H)) c
    (transform (to (iprod_hom_iso H)) c u) = u := eq_refl.

End Conversion.

Section ConversionSets.

Context {A : Type}.
Context (F : A -> obj[Sets]).
Context (c : obj[Sets]).
Context (fam : forall a : A, c ~{Sets}~> F a).
Context (u : c ~{Sets}~> Sets_iprod_obj F).

(* Positive control 9: at [Sets] the backward leg computes to the tupling
   map of Instance/Sets/Products.v. *)
Definition probe_sets_from_control :
  transform (from (Sets_iprod_hom_iso F)) c fam = Sets_iprod_tuple F c fam
  := eq_refl.

(* Negative 7: the round trip still does not compute, even at the concrete
   [Sets] product where both legs reduce.  [SetoidMorphism] has primitive
   projections with eta conversion, so the comparison descends to the two
   fields, and it is the [proper_morphism] field that differs: the tupling
   rebuilds it as its own obligation.  Control 10, just below, is exactly
   that diagnosis — the [morphism] field DOES agree, on the nose. *)
Fail Definition probe_sets_roundtrip :
  transform (from (Sets_iprod_hom_iso F)) c
    (transform (to (Sets_iprod_hom_iso F)) c u) = u := eq_refl.

(* Positive control 10: the agreement holds one level further in, at the
   underlying map, so the rejection above is about the certificate field and
   not about either leg being stuck. *)
Definition probe_sets_roundtrip_value_control (x : c) :
  transform (from (Sets_iprod_hom_iso F)) c
    (transform (to (Sets_iprod_hom_iso F)) c u) x = u x := eq_refl.

End ConversionSets.
