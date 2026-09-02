(** * Boundary probe for Instance/Top/Kolmogorov.v (issue #372, part b)

    Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
    §IV.3, printed p. 92, Exercise 4(b).

    Every rejection the target's header MEASURES is pinned here rather
    than in the target itself, for the reason this tree records
    elsewhere: an in-file [Fail] renames in lockstep with the constant
    it guards, so it cannot detect a rename.  This file mirrors the
    target's FULL [Require] list plus the target -- a short prefix is
    what makes a probe pass for a reason it never measured.

    SEVEN [Fail] commands: SIX negatives of THREE KINDS kept lexically
    apart, plus one scope-free instrument check.

      - CONVERSION (3): each reports "cannot unify" between two terms
        of ONE type.
      - TYPING (1): a plain "has type ... while it is expected to have
        type ...", with NO "cannot unify" and no universe clause.
      - FORMABILITY (2): each ends "universe inconsistency: Cannot
        enforce ...".  The first is this development's own headline
        measurement -- the unrestricted indistinguishability relation
        is one universe too big to be a space's `≈`; the second is the
        donor identification [Subcategory] carries.

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
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Kolmogorov.

(** ** Instrument check

    Scope-free: it names nothing, so it stays red however the target is
    renamed, and it shows [Fail] is doing its job in this file. *)

Fail Check probe_372b_no_such_reference.

(** ** FORMABILITY 1 -- the headline: the unrestricted relation is one
       universe too big to be a space's `≈`

    [TopSpace@{o}] carries [top_carrier :> SetoidObject@{o o}], so a
    space's own `≈` is valued in [Type@{o}], while [IsOpen] quantifies
    over predicates [X → Type@{o}] and so a relation quantifying over
    ALL of them lands at a level strictly above [o].  The control shows the
    level-restricted [SameOpens] DOES land at [Type@{o}] at the very
    same declared levels, and [kq_setoid] builds the coarsened
    [SetoidObject] out of it; the negative shows [SameOpensAll] does
    not.  That is the whole reason the target's quotient tests against
    the opens valued at a level strictly below the space's own. *)

Section ProbeKolmogorovLevels.

Universes s o.
Constraint s < o.

Context (Xu : TopSpace@{o}).

Definition k372_probe_small_at_o (x y : Xu) : Type@{o} :=
  SameOpens@{s o} Xu x y.

Definition k372_probe_kq_setoid_at_o : SetoidObject@{o o} :=
  kq_setoid@{s o} Xu.

Fail Definition k372_probe_all_at_o (x y : Xu) : Type@{o} :=
  SameOpensAll Xu x y.

End ProbeKolmogorovLevels.

(** ** FORMABILITY 2 -- the donor identifies hom with proof

    [Subcategory] is declared over [Category@{u u0 u0}].  At a category
    whose hom and proof universes are declared strictly apart, naming a
    hom-set and an identity is fine while [Subcategory] is refused.
    The identification is the DONOR's and is inherited by
    [T0_Subcategory], [T0Spaces] and [T0_Reflective_in_Top]; nothing in
    the target adds to it, and no constraint block of any constant of
    the target carries a universe equation at all.

    Only ONE such negative is stated.  [Reflective] takes a
    [Subcategory] and cannot be tested apart from it, so a negative
    naming [Reflective] would fire at its [Subcategory] argument with
    the identical message and separate nothing (the trap
    Test/ProbeRingLattice340.v records for [MonoidObject]). *)

Section ProbeKolmogorovDonor.

Universes uo uh up.
Constraint uh < up.

Context (Cu : Category@{uo uh up}).
Context (xu yu : obj[Cu]).

Check (xu ~{Cu}~> yu).
Check (@id Cu xu).

Fail Check (@Subcategory Cu).

End ProbeKolmogorovDonor.

(** ** CONVERSION 1 -- the unit is the projection POINTWISE, not as a
       morphism record

    [AdjunctionFromUniversalArrows] builds the forward transpose as
    [fun g => fmap[U] g ∘ arrow], so the class unit is
    [fmap[Incl] id ∘ kolmogorov_proj X].  Applied to a POINT that
    composite reduces to the point itself, which is the target's
    [t0_unit_is_proj]; as a whole [ContinuousMorphism] record it does
    not, and the `≈` form is the target's [t0_unit_is_proj_hom]. *)

Fail Example k372_probe_unit_is_proj_strict (X : TopSpace) :
  t0_unit X = kolmogorov_proj X := eq_refl.

Example k372_probe_unit_is_proj_pointwise (X : TopSpace) (x : X) :
  continuous_map (t0_unit X) x
    = continuous_map (kolmogorov_proj X) x := eq_refl.

Lemma k372_probe_unit_is_proj_hom (X : TopSpace) :
  t0_unit X ≈ kolmogorov_proj X.
Proof. apply t0_unit_is_proj_hom. Qed.

(** ** CONVERSION 2 -- the quotient's opens are NOT the base space's

    [KolmogorovQuotient X] keeps X's carrier ([kq_carrier_strict]) and
    coarsens its `≈` to [SameOpens X] ([kq_equiv_strict]), but its
    opens are the pairs of an open of X with a proof that the open
    respects that relation -- which is [kq_open], and is what makes
    [open_proper] available for the coarser `≈`.  So the two [IsOpen]
    fields are different terms.  The one-directional passage is the
    target's [small_open_is_kq_open]. *)

Fail Example k372_probe_kq_isopen_strict (X : TopSpace) (U : X → Type) :
  IsOpen (KolmogorovQuotient X) U = IsOpen X U := eq_refl.

Example k372_probe_kq_isopen_is_kq_open (X : TopSpace) (U : X → Type) :
  IsOpen (KolmogorovQuotient X) U = kq_open X U := eq_refl.

Example k372_probe_kq_carrier (X : TopSpace) :
  carrier (top_carrier (KolmogorovQuotient X))
    = carrier (top_carrier X) := eq_refl.

(** ** CONVERSION 3 -- a T0 space is not EQUAL to its own quotient

    [Bool_Discrete] is T0, so the reflector returns it up to
    isomorphism ([bool_reflect_iso], the counit isomorphism
    instantiated).  The two spaces are nevertheless distinct:
    [Discrete_Top]'s opens are the `≈`-respecting predicates and the
    quotient's are the respecting ones in the sense above, and the
    setoid field and every law field are separately built. *)

Fail Example k372_probe_quot_bool_strict :
  KolmogorovQuotient Bool_Discrete = Bool_Discrete := eq_refl.

Definition k372_probe_bool_iso :
  fobj[T0_reflector] (Incl Top T0_Subcategory Bool_Discrete_T0Space)
    ≅[T0Spaces] Bool_Discrete_T0Space := bool_reflect_iso.

(** ** TYPING -- [Reflective] is a record, not an adjunction

    Mac Lane's phrase "full reflective subcategory" is the RECORD:
    fullness, a reflector, and the adjunction.  The adjunction alone is
    strictly less, and the mismatch is a plain typing error -- no
    "cannot unify", no universe clause. *)

Fail Definition k372_probe_reflective_is_adjunction
  : T0_reflector ⊣ Incl Top T0_Subcategory :=
  T0_Reflective_in_Top.

Definition k372_probe_reflective_adj
  : T0_reflector ⊣ Incl Top T0_Subcategory :=
  reflective_adj T0_Reflective_in_Top.

Definition k372_probe_reflective_record : Reflective T0_Subcategory :=
  T0_Reflective_in_Top.

Definition k372_probe_reflective_full :
  Category.Construction.Subcategory.Full Top T0_Subcategory :=
  reflective_full T0_Reflective_in_Top.

(** ** Controls naming every constant the negatives mention *)

Check @SameOpens.
Check @SameOpensAll.
Check @SameOpensAll_SameOpens.
Check @IsT0.
Check @kq_setoid.
Check @kq_open.
Check @small_open_is_kq_open.
Check @KolmogorovQuotient.
Check @KolmogorovQuotient_T0.
Check @KolmogorovT0.
Check @kolmogorov_proj.
Check @kolmogorov_med.
Check @kolmogorov_universal.
Check @kolmogorov_universal_arrow.
Check @t0_unit.
Check @t0_unit_is_proj_hom.
Check @t0_reflect_iso.
Check @T0_reflector.
Check @T0_adj.
Check @T0_Subcategory.
Check @T0Spaces.
Check @T0_Full.
Check @T0_Incl_Full.
Check @T0_Incl_Faithful.
Check @T0_Reflective_in_Top.
Check @Bool_Discrete_T0.
Check @Bool_Discrete_T0Space.
Check @bool_reflect_iso.
Check @TwoPoint_Indiscrete_not_T0.
Check @Hausdorff_T0_nn.
Check @Tri_Top.
Check @Tri_Top_not_T0.
Check @tri_point_apart.
Check @tri_quot_keeps_point_apart.
Check @Tri_T0.
Check @Subcategory.
Check @Reflective.
Check @Sub.
Check @Incl.
Check @Top.
Check @TopSpace.
Check @IsOpen.
Check @Bool_Discrete.
Check @continuous_map.
Check @carrier.
Check @top_carrier.
Check @SetoidObject.
