Require Import Coq.ZArith.ZArith.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Construction.Deloop.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Matr.GL.
Require Import Category.Instance.Rng.MonoidRing.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * The integral group ring, and the unit-group functor

    Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          GTM 5, §III.1, printed p. 59, Exercise 1 — the integral group
          ring ℤ[G] as a universal arrow to the unit-group functor
          (maclane:III.1:ex1)
    nLab:      https://ncatlab.org/nlab/show/group+algebra
    Wikipedia: https://en.wikipedia.org/wiki/Group_ring

    MAC LANE'S OWN PHRASING, RECOVERED.  Instance/Rng/MonoidRing.v builds
    R[M] for a monoid M and exhibits ℤ[M] as a universal arrow to the
    MULTIPLICATIVE-MONOID functor.  The exercise as Mac Lane states it is
    about a GROUP G and the functor sending a ring to its GROUP OF UNITS,
    and this file supplies exactly that reading, on top of the monoid ring
    rather than beside it: [GrpRing G] is by definition
    [ZMonRing (Grp_MonSets G)], the same object, and no second
    construction is made.

    THE ONE MATHEMATICAL STEP, and it is a theorem rather than a
    convenience: a homomorphism of MONOIDS out of the underlying monoid of
    a GROUP, into the multiplicative monoid of a ring, automatically lands
    in the units — the image of g⁻¹ is a two-sided inverse of the image of
    g.  That is [monoid_hom_to_units], and it is what makes the
    unit-group reading equivalent to the multiplicative-monoid reading at
    a group.  The two passages [units_hom_of_monoid_hom] and
    [monoid_hom_of_units_hom] are mutually inverse ON THE UNDERLYING MAP
    by [eq_refl] in both directions; no claim is made that they are
    inverse on the whole records, because the unit-side records carry
    inverse data that the monoid side does not.

    THREE FUNCTORS, ONE OF THEM NEW.  [Rng_Units : Rng ⟶ Grp] is the
    group-of-units functor over ALL unital rings.  Instance/Matr/GL.v
    already has [Units_Functor], but over [CRng] only — its objects are
    commutative rings, and ℤ[G] is not commutative when G is not — so
    this file states the same construction over [Rng].  The two are built
    from the same donors ([UnitsOf], [Ring_mul_mon], [mul_MonHom],
    [UnitsOf_map]), and nothing is re-proved.  [Grp_MonSets : Grp ⟶
    MonSets] forgets the inverses of a group; it is new, since the tree
    had a monoid-object bridge for rings ([rig_mult_monoid]) but none for
    groups.

    BOTH SETOID-MONOID RECORDS APPEAR IN THIS FILE, and they never meet.
    Instance/Matr/GL.v's [UnitsOf] is stated over Construction/Deloop.v's
    [MonObject], so [Rng_Units] uses that record — but only through
    [Ring_mul_mon], on the multiplicative monoid of a ring.  Everything
    else here, and the whole of Instance/Rng/MonoidRing.v, uses
    Theory/Algebra/Monoid/Hom.v's [Mon Sets].  No bridge between the two
    records is built or needed: no definition below applies a [Mon Sets]
    construction to a [MonObject] or the reverse.  Recording it because
    the two drifting apart is a real hazard — Instance/Rep.v had to build
    [grp_mon] for the analogous situation with two [GrpObject] records —
    and because a reader who sees [MonSets] and [MonObject] in one file
    should be told that the separation is deliberate.

    THE UNIVERSE RESTRICTION IS INHERITED, and is disclosed in
    Instance/Rng/MonoidRing.v in full: [Rig_Forget_Mon] is instantiable
    only at rigs whose carrier and [≈] live in [Set], which is the
    donor's own limitation and not one introduced here, so everything
    below is likewise a statement about [Set]-carrier rings — and,
    through [Grp_MonSets], about [Set]-carrier groups.  Test/ProbeAlgebras.v
    pins the boundary with a positive control at [Int_Ring@{Set Set Set}]
    and a rejected instance one universe up.

    WHAT IS DELIVERED.

      - [Rng_Units : Rng ⟶ Grp] and [Grp_MonSets : Grp ⟶ MonSets];
      - [monoid_hom_to_units] with the two passages and their round trips
        on the underlying map;
      - [GrpRing G] with [grp_ring_insert : G ~{Grp}~> Rng_Units (GrpRing G)];
      - [grp_ring_universal_arrow : UniversalArrow G Rng_Units] and
        [grp_ring_auniversal_arrow], Mac Lane's Exercise 1 in his own
        vocabulary, with the left-adjoint reading [GroupRingFunctor] and
        [grp_ring_adjunction : GroupRingFunctor ⊣ Rng_Units];
      - [grp_ring_insert_inverse]: the insertion's chosen inverse is the
        generator of the inverse group element, on the nose.

    WHAT IS NOT DELIVERED.  No augmentation map ℤ[G] → ℤ and hence no
    augmentation ideal.  No identification of ℤ[G] with the free
    ℤ-module on G.  No group-algebra representation theory: this file
    does not connect ℤ[G]-modules with Instance/Rep.v's linear
    representations, and no such comparison is claimed.  No statement
    about when ℤ[G] is commutative, and no non-degeneracy results of its
    own — those live with the monoid ring, which is the same object. *)

(** ** The group of units of an arbitrary unital ring

    Instance/Matr/GL.v's [Units_Functor] is this construction over [CRng].
    The objects here are all unital rings, because the group ring of a
    non-commutative group is not commutative. *)

Program Definition Rng_Units : Rng ⟶ Grp := {|
  fobj := fun R : RingObject => UnitsOf (Ring_mul_mon R);
  fmap := fun R S f => UnitsOf_map (mul_MonHom f)
|}.
Next Obligation. intros R S f g Hfg x; simpl; exact (Hfg _). Qed.
Next Obligation. intros R x; simpl; reflexivity. Qed.
Next Obligation. intros R S T f g x; simpl; reflexivity. Qed.

Example rng_units_element (R : Rng) (x : carrier (grp_setoid (Rng_Units R))) :
  carrier (rig_setoid R) := `1 x.

(** ** The underlying monoid of a group

    The group-side counterpart of Theory/Algebra/Rig.v's
    [rig_mult_monoid], built the same way: the multiplication uncurried
    over the product setoid, the unit selected from the terminal
    setoid. *)

Program Definition grp_monoid (G : GrpObject)
  : @Monoid Sets Sets_Product_Monoidal (grp_setoid G) := {|
  mu := {| morphism := fun p => grp_mul G (fst p) (snd p) |};
  eta := {| morphism := fun _ => grp_unit G |}
|}.
Next Obligation.
  intros G p q [Hp Hq]; simpl.
  now rewrite Hp, Hq.
Qed.
Next Obligation.
  intros G [[a b] c]; simpl.
  apply grp_mul_assoc.
Qed.
Next Obligation.
  intros G [u a]; simpl.
  apply grp_mul_unit_l.
Qed.
Next Obligation.
  intros G [a u]; simpl.
  apply grp_mul_unit_r.
Qed.

Program Definition Grp_MonSets : Grp ⟶ MonSets := {|
  fobj := fun G => (grp_setoid G : obj[Sets]; grp_monoid G);
  fmap := fun G H f => (grp_map f; _)
|}.
Next Obligation.
  intros G H f.
  unshelve econstructor.
  - intros [a b]; simpl.
    apply grp_map_mul.
  - intros []; simpl.
    apply grp_map_unit.
Qed.
Next Obligation. intros G H f g Hfg a; exact (Hfg a). Qed.
Next Obligation. intros G a; simpl; reflexivity. Qed.
Next Obligation. intros G H K f g a; simpl; reflexivity. Qed.

(* The element-level readings, on the nose. *)
Example grp_monsets_carrier (G : Grp) :
  mcar (Grp_MonSets G) = grp_setoid G := eq_refl.
Example grp_monsets_op (G : Grp) (a b : carrier (grp_setoid G)) :
  mop (Grp_MonSets G) a b = grp_mul G a b := eq_refl.
Example grp_monsets_one (G : Grp) :
  mone (Grp_MonSets G) = grp_unit G := eq_refl.

(** ** Monoid homomorphisms out of a group land in the units

    The image of g⁻¹ is a two-sided inverse of the image of g, so any
    monoid homomorphism out of [Grp_MonSets G] into the multiplicative
    monoid of a ring factors through the group of units.  This is the step
    that makes Mac Lane's unit-group phrasing and the
    multiplicative-monoid phrasing agree at a group. *)

Lemma monoid_hom_to_units (G : Grp) (S : Rng)
  (psi : Grp_MonSets G ~{MonSets}~> Rng_Forget_Mon S)
  (g : carrier (grp_setoid G)) :
  (rig_mul S (mmap psi g) (mmap psi (grp_inv G g)) ≈ rig_one S)
  * (rig_mul S (mmap psi (grp_inv G g)) (mmap psi g) ≈ rig_one S).
Proof.
  split.
  - rewrite <- (mmap_op psi g (grp_inv G g)).
    rewrite (proper_morphism (mmap psi : SetoidMorphism _ _) _ _
               (grp_mul_inv_r G g)).
    exact (mmap_one psi).
  - rewrite <- (mmap_op psi (grp_inv G g) g).
    rewrite (proper_morphism (mmap psi : SetoidMorphism _ _) _ _
               (grp_mul_inv_l G g)).
    exact (mmap_one psi).
Qed.

Program Definition units_hom_of_monoid_hom (G : Grp) (S : Rng)
  (psi : Grp_MonSets G ~{MonSets}~> Rng_Forget_Mon S)
  : G ~{Grp}~> Rng_Units S := {|
  grp_map := {| morphism := fun g =>
    (mmap psi g;
     (mmap psi (grp_inv G g);
      (fst (monoid_hom_to_units G S psi g),
       snd (monoid_hom_to_units G S psi g)))) |}
|}.
Next Obligation.
  intros G S psi a b Hab; simpl.
  exact (proper_morphism (mmap psi : SetoidMorphism _ _) _ _ Hab).
Qed.
Next Obligation. intros G S psi; simpl; exact (mmap_one psi). Qed.
Next Obligation. intros G S psi a b; simpl; exact (mmap_op psi a b). Qed.

Definition monoid_hom_of_units_hom (G : Grp) (S : Rng)
  (h : G ~{Grp}~> Rng_Units S)
  : Grp_MonSets G ~{MonSets}~> Rng_Forget_Mon S :=
  @mhom (Grp_MonSets G) (Rng_Forget_Mon S)
    (fun g => `1 (grp_map h g))
    (fun a b Hab => proper_morphism (grp_map h) a b Hab)
    (fun a b => grp_map_mul h a b)
    (grp_map_unit h).

(* Both passages leave the underlying map alone, on the nose. *)
Example units_hom_round (G : Grp) (S : Rng)
  (psi : Grp_MonSets G ~{MonSets}~> Rng_Forget_Mon S)
  (g : carrier (grp_setoid G)) :
  mmap (monoid_hom_of_units_hom G S (units_hom_of_monoid_hom G S psi)) g
    = mmap psi g := eq_refl.

Example monoid_hom_round (G : Grp) (S : Rng) (h : G ~{Grp}~> Rng_Units S)
  (g : carrier (grp_setoid G)) :
  `1 (grp_map (units_hom_of_monoid_hom G S
                 (monoid_hom_of_units_hom G S h)) g)
    = `1 (grp_map h g) := eq_refl.

(** * ℤ[G] and Mac Lane's Exercise 1 *)

Definition GrpRing (G : Grp) : Rng := ZMonRing (Grp_MonSets G).

(** The insertion of the group: the generator, with the generator of the
    inverse as its chosen two-sided inverse. *)
Definition grp_ring_insert (G : Grp) : G ~{Grp}~> Rng_Units (GrpRing G) :=
  units_hom_of_monoid_hom G (GrpRing G) (zmring_insert (Grp_MonSets G)).

Example grp_ring_insert_computes (G : Grp) (g : carrier (grp_setoid G)) :
  `1 (grp_map (grp_ring_insert G) g) = @mr_gen Int_Ring (Grp_MonSets G) g
  := eq_refl.

Example grp_ring_insert_inverse (G : Grp) (g : carrier (grp_setoid G)) :
  `1 (`2 (grp_map (grp_ring_insert G) g))
    = @mr_gen Int_Ring (Grp_MonSets G) (grp_inv G g) := eq_refl.

(** The universal property: a homomorphism from G to the units of S is the
    same thing as a ring homomorphism from ℤ[G] to S.  The forward
    direction is the monoid ring's own extension, applied to the monoid
    homomorphism underlying the given group homomorphism; uniqueness is
    the monoid ring's uniqueness, since the two agree on generators. *)
Lemma grp_ring_universal (G : Grp) (S : Rng) (h : G ~{Grp}~> Rng_Units S) :
  ∃! k : GrpRing G ~{Rng}~> S,
    h ≈ fmap[Rng_Units] k ∘ grp_ring_insert G.
Proof.
  unshelve eexists.
  - exact (zmring_eval (Grp_MonSets G) S (monoid_hom_of_units_hom G S h)).
  - intro g; simpl; reflexivity.
  - intros k Hk t; simpl.
    symmetry.
    apply (mring_extend_unique (rng_from_Z S)
             (monoid_hom_of_units_hom G S h) k).
    + intro z; exact (zmring_hom_scal (Grp_MonSets G) S k z).
    + intro g; symmetry; exact (Hk g).
Qed.

Definition grp_ring_universal_arrow (G : Grp)
  : UniversalArrow G Rng_Units :=
  universal_arrow_from_UMP G Rng_Units (GrpRing G) (grp_ring_insert G)
    (grp_ring_universal G).

Program Definition grp_ring_auniversal_arrow (G : Grp)
  : AUniversalArrow G Rng_Units (GrpRing G) := {|
  universal_arrow := grp_ring_insert G
|}.
Next Obligation.
  intros G S h.
  unshelve eexists.
  - exact (zmring_eval (Grp_MonSets G) S (monoid_hom_of_units_hom G S h)).
  - intro g; simpl; reflexivity.
  - intros k Hk t; simpl.
    symmetry.
    apply (mring_extend_unique (rng_from_Z S)
             (monoid_hom_of_units_hom G S h) k).
    + intro z; exact (zmring_hom_scal (Grp_MonSets G) S k z).
    + intro g; exact (Hk g).
Qed.

(** The left-adjoint reading: the integral group ring is left adjoint to
    the group-of-units functor. *)
Definition GroupRingFunctor : Grp ⟶ Rng :=
  LeftAdjointFunctorFromUniversalArrows Rng_Units grp_ring_universal_arrow.

Definition grp_ring_adjunction : GroupRingFunctor ⊣ Rng_Units :=
  AdjunctionFromUniversalArrows Rng_Units grp_ring_universal_arrow.

Example GroupRingFunctor_obj (G : Grp) :
  fobj[GroupRingFunctor] G = GrpRing G := eq_refl.

Example grp_ring_arrow_is_insert (G : Grp) :
  @arrow _ _ G Rng_Units (grp_ring_universal_arrow G) = grp_ring_insert G
  := eq_refl.

Definition grp_ring_unit (G : Grp)
  : G ~{Grp}~> Rng_Units (fobj[GroupRingFunctor] G) :=
  @Category.Theory.Adjunction.unit _ _ _ _ grp_ring_adjunction G.

Example grp_ring_unit_is_gen (G : Grp) (g : carrier (grp_setoid G)) :
  `1 (grp_map (grp_ring_unit G) g) = @mr_gen Int_Ring (Grp_MonSets G) g
  := eq_refl.
