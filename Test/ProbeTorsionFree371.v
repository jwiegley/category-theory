(** * Boundary probe for Instance/Ab/TorsionFree.v (issue #371)

    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    §IV.3, printed p. 92, Exercise 2.

    Every rejection the target's header MEASURES is pinned here rather
    than in the target itself, for the reason this tree records
    elsewhere: an in-file [Fail] renames in lockstep with the constant
    it guards, so it cannot detect a rename.  This file mirrors the
    target's FULL [Require] list plus the target — a short prefix is
    what makes a probe pass for a reason it never measured.

    SEVEN [Fail] commands: SIX negatives of THREE KINDS kept lexically
    apart, plus one scope-free instrument check.

      - CONVERSION (3): each reports "cannot unify" between two terms of
        ONE type.
      - TYPING (1): a plain "has type ... while it is expected to have
        type ...", with NO "cannot unify" and no universe clause.
      - FORMABILITY (2): each ends "universe inconsistency: Cannot
        enforce up = uh because uh < up".

    Each negative was stripped ONE AT A TIME (the others left as
    [Fail]), compiled alone, and its WHOLE error read; a [Fail] that
    succeeds prints NOTHING under this coqc, which is why stripping is
    the only way to see what fired.  Every constant a negative names is
    also named OUTSIDE a [Fail] below, so that renaming any of them
    breaks this file at a control rather than turning a guard silently
    green. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Coproduct.
Require Import Category.Instance.Ab.Monoidal.
Require Import Category.Instance.Ab.DirectedColimit.
Require Import Category.Instance.Ab.Character.Finite.
Require Import Category.Adjunction.Unitalization.
Require Import Category.Instance.Ab.TorsionFree.
Require Import Coq.ZArith.ZArith.

(** ** Instrument check

    Scope-free: it names nothing, so it stays red however the target is
    renamed, and it shows [Fail] is doing its job in this file. *)

Fail Check probe_371_no_such_reference.

(** ** CONVERSION 1 — the unit is the projection POINTWISE, not as a
       morphism record

    [AdjunctionFromUniversalArrows] builds ⌊−⌋ as
    [fun g => fmap[U] g ∘ arrow], so the class unit is
    [fmap[Incl] id ∘ ab_quot_proj …].  Applied to an ELEMENT that
    composite reduces to the element itself, which is the target's
    [torsion_unit_is_proj]; as a whole [CMonHom] record it does not,
    and the `≈` form is the target's [torsion_unit_is_proj_hom]. *)

Fail Example probe_unit_is_proj_strict (A : AbObject) :
  torsion_unit A = ab_quot_proj (torsion_incl A) := eq_refl.

Example probe_unit_is_proj_pointwise (A : AbObject) (a : carrier A) :
  cmon_map (torsion_unit A) a
    = cmon_map (ab_quot_proj (torsion_incl A)) a := eq_refl.

(** ** CONVERSION 2 — the scalar action at a VARIABLE scalar

    [AbQuotient] reuses [A]'s own zero and addition, so those two fields
    ARE [A]'s on the nose (controls below) and [nat_smul] agrees at every
    CLOSED scalar.  At a variable [k] the [Fixpoint] is stuck, so
    conversion is left comparing the two [AbObject]s themselves, which
    differ in their setoid field — the whole point of the quotient — and
    in every law field; one differing law field alone already blocks
    it (measured in the target's header).  The target proves the
    agreement by induction ([nat_smul_quot]). *)

Fail Example probe_nat_smul_quot_strict
  (A : AbObject) (k : nat) (x : carrier A) :
  nat_smul (AbModTorsion A) k x = nat_smul A k x := eq_refl.

Example probe_nat_smul_quot_closed (A : AbObject) (x : carrier A) :
  nat_smul (AbModTorsion A) 2 x = nat_smul A 2 x := eq_refl.

Example probe_quot_zero_strict (A : AbObject) :
  cmon_zero (AbModTorsion A) = cmon_zero A := eq_refl.

Example probe_quot_plus_strict (A : AbObject) (x y : carrier A) :
  cmon_plus (AbModTorsion A) x y = cmon_plus A x y := eq_refl.

Lemma probe_nat_smul_quot_lemma
  (A : AbObject) (k : nat) (x : carrier A) :
  nat_smul (AbModTorsion A) k x = nat_smul A k x.
Proof. apply nat_smul_quot. Qed.

(** ** CONVERSION 3 — ℤ/T(ℤ) is not ℤ, though it is isomorphic to it

    ℤ is torsion-free, so its torsion subgroup is trivial and the
    reflector returns it up to isomorphism ([ZAb_reflect_iso], the
    counit isomorphism instantiated).  The two objects are nevertheless
    distinct: [AbModTorsion ZAb] carries the coarsened setoid. *)

Fail Example probe_quot_ZAb_strict : AbModTorsion ZAb = ZAb := eq_refl.

Definition probe_ZAb_iso :
  fobj[TorsionFree_reflector] (Incl Ab TorsionFree_Sub ZAb_TF)
    ≅[Sub Ab TorsionFree_Sub] ZAb_TF := ZAb_reflect_iso.

(** ** TYPING — [Reflective] is a record, not an adjunction

    Mac Lane's phrase "full reflective subcategory" is the RECORD:
    fullness, a reflector, and the adjunction.  The adjunction alone is
    strictly less, and the mismatch is a plain typing error — no
    "cannot unify", no universe clause. *)

Fail Definition probe_reflective_is_adjunction
  : TorsionFree_reflector ⊣ Incl Ab TorsionFree_Sub :=
  TorsionFree_Reflective.

Definition probe_reflective_adj
  : TorsionFree_reflector ⊣ Incl Ab TorsionFree_Sub :=
  reflective_adj TorsionFree_Reflective.

Definition probe_reflective_record : Reflective TorsionFree_Sub :=
  TorsionFree_Reflective.

(** ** FORMABILITY — the donors identify hom with proof

    [Subcategory] is declared over [Category@{u u0 u0}] and [Reflective]
    over [Category@{u3 u5 u5}].  At a category whose hom and proof
    universes are declared strictly apart, naming a hom-set and an
    identity is fine while [Subcategory] is refused.  The second
    rejection below names [Reflective], but it fires at the
    [Subcategory] ARGUMENT with the identical message -- [Reflective]
    takes a [Subcategory] and cannot be tested apart from it (the trap
    Test/ProbeRingLattice340.v records for [MonoidObject]) -- so it
    separates nothing, and whether [Reflective] identifies anything OF
    ITS OWN is not measured here.  The identification is the DONORS'
    and is inherited by everything in the target; nothing there adds to
    it, and no constraint block of any constant of the target carries a
    universe equation at all. *)

Section ProbeTorsionUniverses.

Universes uo uh up.
Constraint uh < up.

Context (Cu : Category@{uo uh up}).
Context (xu yu : obj[Cu]).

Check (xu ~{Cu}~> yu).
Check (@id Cu xu).

Fail Check (@Subcategory Cu).

Fail Check (fun S : @Subcategory Cu => @Reflective Cu S).

End ProbeTorsionUniverses.

(** ** Controls naming every constant the negatives mention *)

Check @torsion_unit.
Check @torsion_incl.
Check @ab_quot_proj.
Check @nat_smul.
Check @AbModTorsion.
Check @AbObject.
Check @carrier.
Check @TorsionFree_reflector.
Check @TorsionFree_Sub.
Check @TorsionFree_Reflective.
Check @TorsionFree_Full.
Check @Incl.
Check @Ab.
Check @ZAb.
Check @ZAb_TF.
Check @ZAb_reflect_iso.
Check @Subcategory.
Check @Reflective.
Check @Sub.
Check @nat_smul_quot.
Check @cmon_map.
Check @cmon_zero.
Check @cmon_plus.
