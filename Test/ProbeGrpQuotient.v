(** * Boundary probes for the quotient group and the isomorphism theorems

    Companion to Instance/Grp/Quotient.v, Instance/Grp/Quotient/Isomorphism.v
    and Instance/Grp/Quotient/Colimit.v (issue #313, Mac Lane §III.1
    construction 5 and Exercise 4; Awodey §4.2 Theorem 4.4 and
    Corollary 4.5; Riehl §3.1 Example 3.1.25).  Those files make four
    strength claims whose negative side is a conversion or a universe
    boundary.  A measurement made outside the tree would not be noticed by
    a refactor, so it is pinned here.  **If the [Fail] commands below stop
    being rejected, this file breaks the build.**

    Each negative is paired with a positive control that must SUCCEED, for
    the reason Test/ProbeQuiverConstructions.v gives: a [Fail] alone
    passes just as happily when a name has been renamed out from under it.
    The instrument itself was checked — wrapping [Fail] around a
    succeeding command aborts compilation with "The command has not
    failed!" — and that check was not hypothetical here: an earlier draft
    wrote the three conversion negatives as [Fail Example ... : T.], which
    guards only the STATEMENT and not the proof, and the build reported
    that message at the first of them.  They are written as
    [Fail Definition ... := eq_refl] below, so that what is rejected is
    the elaboration of the term.  Each negative was also compiled once
    with the [Fail] stripped, to confirm the rejection is the intended one
    and not a syntax, scope or resolution error: three "Unable to unify"
    conversion errors, and one genuine universe inconsistency naming the
    declared universe, "Cannot enforce Set = big".

    The import list below is the union of the three target files' own
    lists, in their order.  That matters: a short prefix would leave the
    coercions and instances unresolved and the negatives would then be
    reported as illegal applications rather than as the conversion errors
    they are, which is a probe that passes for the wrong reason.

    THE FOUR BOUNDARIES.

    (1) THE KERNEL SUBGROUP IS NOT THE PRE-EXISTING KERNEL GROUP.
    Instance/Grp/Quotient.v's [KernelNS_carrier_is_Grp_kernel] records
    that [SubgroupGrp (KernelNS h)] and Instance/Grp.v:729's [Grp_kernel h]
    have the same CARRIER by [eq_refl].  The whole records are NOT
    convertible, the group-law fields being different proof terms
    ([SubgroupGrp] is [Program]-built, [Grp_kernel] is built by
    [unshelve notypeclasses refine]).  Negative 1 pins that, so the
    carrier-level claim is not silently read as a record-level one.

    (2) THE MEDIATOR'S TRIANGLE IS `≈`, NOT LEIBNIZ.
    [quot_med_commutes] states [quot_med N x ∘ quot_proj N ≈ `1 x] and
    proves it pointwise by [reflexivity] — the projection being the
    identity function, the two homomorphisms agree at every element.  They
    are nevertheless distinct RECORDS: the composite rebuilds the
    unit-preservation and multiplication-preservation fields.  Negative 2
    pins the distinction, which is exactly the `≈`/`=` discipline the
    house rules ask for.

    (3) THE IMAGE'S CLOSURE WITNESSES DO NOT REDUCE.
    Instance/Grp/Epi.v's [GrpImage_unit], [GrpImage_mul] and
    [GrpImage_inv] are [Qed]-opaque, so the preimage carried by the group
    operations of [ImageGrp] is not accessible to computation.  That is
    why Isomorphism.v's [image_med] discharges its unit and product laws
    through [image_med_wd] — comparing h-images — rather than by
    unfolding.  Negative 3 pins the opacity; if those lemmas were ever
    made transparent this probe would break and the comment in
    [image_med_wd] would need revisiting.

    (4) ZERO MORPHISMS IN [Grp] ARE CONFINED TO [Set].
    [Grp_trivial] (Instance/Grp.v:522) elaborates at [GrpObject@{u Set u}]
    and hence [Grp_Zero] at [ZeroObject@{u Set} Grp@{u Set}], even though
    the donor [unit_setoid@{t u}] (Lib/Setoid.v:59) is polymorphic in
    exactly the pinned argument.  So every [IsCokernel] and every
    coequalizer-against-zero statement about [Grp] — the whole of
    Instance/Grp/Quotient/Colimit.v — holds only for groups whose carriers
    live in [Set].  THE PIN IS THE DONOR'S, not this development's, and it
    is not shown unavoidable; it has the shape of the
    [Build_Quiver_Standard_Eq] erratum that issue #300 lifted.  Negative 4
    is the guard: if a later change to Instance/Grp.v lifts it, this probe
    breaks and Colimit.v's disclosure should be deleted.

    WHAT IS DELIBERATELY *NOT* PROBED.  The positive controls in
    section [Positive] include the two strict identifications that DO
    hold — the isomorphism of the first isomorphism theorem has the two
    mediators as its legs, by [eq_refl] — because those are the claims a
    refactor is most likely to break silently. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Quotient.Isomorphism.
Require Import Category.Theory.Universal.Element.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Regular.
Require Import Category.Structure.Kernel.
Require Import Category.Instance.Grp.Quotient.Colimit.

Generalizable All Variables.

(** ** Negative 1: the kernel subgroup group is not [Grp_kernel] *)

(* POSITIVE CONTROL: the carriers ARE convertible. *)
Example control_kernel_carrier {G K : GrpObject} (h : G ~{Grp}~> K) :
  carrier (SubgroupGrp (KernelNS h)) = carrier (Grp_kernel h).
Proof. reflexivity. Qed.

(* NEGATIVE: the whole records are not. *)
Fail Definition negative_kernel_record {G K : GrpObject} (h : G ~{Grp}~> K) :
  SubgroupGrp (KernelNS h) = Grp_kernel h := eq_refl.

(** ** Negative 2: the mediator triangle is `≈` and not Leibniz *)

(* POSITIVE CONTROL: the `≈` form holds, pointwise by reflexivity. *)
Example control_med_triangle {G K : GrpObject} (N : NormalSubgroup G)
  (x : Kills N K) : quot_med N x ∘ quot_proj N ≈ `1 x.
Proof. exact (quot_med_commutes N x). Qed.

(* NEGATIVE: the Leibniz form does not. *)
Fail Definition negative_med_triangle {G K : GrpObject} (N : NormalSubgroup G)
  (x : Kills N K) : quot_med N x ∘ quot_proj N = `1 x := eq_refl.

(** ** Negative 3: [GrpImage_unit] is opaque *)

(* POSITIVE CONTROL: the equation the opaque lemma carries IS accessible,
   which is what [image_med] uses instead of the witness. *)
Example control_image_unit_equation {G K : GrpObject} (h : G ~{Grp}~> K) :
  grp_map h (`1 (GrpImage_unit h)) ≈ grp_unit K.
Proof. exact (`2 (GrpImage_unit h)). Qed.

(* NEGATIVE: the witness itself does not reduce to the unit. *)
Fail Definition negative_image_unit_witness {G K : GrpObject}
  (h : G ~{Grp}~> K) : `1 (GrpImage_unit h) = grp_unit G := eq_refl.

(** ** Negative 4: zero morphisms in [Grp] pin the hom universe to [Set] *)

Monomorphic Universe big.
Monomorphic Constraint Set < big.

(* POSITIVE CONTROL: the quotient machinery itself carries no such pin --
   [QuotientGrp] and its universal element are formable at a group whose
   universes are declared strictly above [Set].  This is the half that
   says the pin belongs to [Grp_Zero] and not to this development. *)
Section BigCarrier.

Context {G : GrpObject@{big big big}}.
Context (N : NormalSubgroup@{big big big big} G).

Definition control_big_quotient : GrpObject@{big big big} := QuotientGrp N.

Definition control_big_projection : G ~{Grp}~> control_big_quotient :=
  quot_proj N.

Definition control_big_universal :
  AUniversalElement (KillsFunctor N) (QuotientGrp N) :=
  quot_universal_element N.

Definition control_big_kernel {K : GrpObject@{big big big}}
  (h : G ~{Grp}~> K) : NormalSubgroup G := KernelNS h.

Definition control_big_first_iso {K : GrpObject@{big big big}}
  (h : G ~{Grp}~> K) :
  QuotientGrp (KernelNS h) ≅[Grp] ImageGrp h :=
  first_isomorphism_theorem h.

End BigCarrier.

(* NEGATIVE: the zero morphism is not, at the same universes. *)
Section BigZero.

Context {G K : GrpObject@{big big big}}.

Fail Definition negative_big_zero : G ~{Grp}~> K := @zero_mor Grp Grp_Zero G K.

End BigZero.

(** ** Positive controls for the strict identifications that DO hold *)

Section Positive.

(* The comparison isomorphism of the first isomorphism theorem has the two
   mediators as its legs, by convertibility: the universal-element
   machinery of Theory/Universal/Element.v rebuilds neither. *)
Example positive_first_iso_to {G K : GrpObject} (h : G ~{Grp}~> K) :
  to (first_isomorphism_theorem h) = quot_med (KernelNS h) (image_elem h).
Proof. reflexivity. Qed.

Example positive_first_iso_from {G K : GrpObject} (h : G ~{Grp}~> K) :
  from (first_isomorphism_theorem h) = image_med h (quot_elem (KernelNS h)).
Proof. reflexivity. Qed.

(* The universal element's underlying homomorphism IS the projection. *)
Example positive_universal_elem {G : GrpObject} (N : NormalSubgroup G) :
  `1 (@aue_elem _ (KillsFunctor N) (QuotientGrp N) (quot_universal_element N))
    = quot_proj N.
Proof. reflexivity. Qed.

End Positive.
