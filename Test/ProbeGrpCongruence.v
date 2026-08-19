(** * Boundary probes for group congruences and normal subgroups

    Companion to Instance/Grp/Congruence.v (issue #301, Mac Lane §II.8
    Exercise 2; Awodey §4.2 and §4.5 Exercise 1).  That file makes six
    strength claims whose negative side is a conversion boundary.  A
    measurement made outside the tree would not be noticed by a refactor,
    so it is pinned here.  **If the [Fail] commands below stop being
    rejected, this file breaks the build.**

    Each negative is paired with a positive control that must SUCCEED, for
    the reason Test/ProbeQuiverConstructions.v and Test/ProbeGrpQuotient.v
    give: a [Fail] alone passes just as happily when a name has been
    renamed out from under it.  The instrument itself was checked --
    wrapping [Fail] around a succeeding command aborts compilation with
    "The command has not failed!" -- and every negative below was compiled
    once with the [Fail] stripped, to confirm the rejection is the
    intended one and not a syntax, scope or resolution error.  All six
    report a conversion error ("The term ... has type ... while it is
    expected to have type ...", followed by "cannot unify X and Y").

    The import list below is Instance/Grp/Congruence.v's own, in its
    order, INCLUDING the deliberate placement of the [Instance.Grp]
    satellites last.  That matters twice over: a short prefix would leave
    coercions unresolved and the negatives would then be reported as
    illegal applications rather than as the conversion errors they are;
    and a different order would make the unqualified [GrpObject]
    Construction/Deloop.v's rather than Instance/Grp.v's, so the
    statements would be about a different record.

    THE SIX BOUNDARIES.

    (1) THE TWO GROUPOID WITNESSES ARE NOT THE SAME TERM.
    [deloop_GrpObject_agrees] shows that the record conversion
    [grp_deloop_GrpObject] deloops to Instance/Grp/Free.v's [grp_deloop]
    by [eq_refl], and [grp_deloop_ginv] that the chosen inverse is the
    group inverse.  What does NOT follow is that
    [Deloop_IsGroupoid (grp_deloop_GrpObject H)] and
    [grp_deloop_IsGroupoid H] are one term: the first routes through
    Construction/Deloop.v's [Deloop_group_invertible], a [Program
    Instance] whose two obligations are [Qed]-opaque, the second names
    Instance/Grp.v's [grp_mul_inv_r] and [grp_mul_inv_l] directly.  The
    DATA agree (control), the records do not (negative 1).

    (2) THE MEMBERSHIP ROUND TRIP IS A BICONDITIONAL, NOT A CONVERSION.
    [ns_of_cong_of_ns] says the members of [cong_ns (ns_rel N)] are the
    members of N, and it is [quot_rel_unit_iff] applied.  It is an [iff]
    and not an equality of types because the recovered membership unfolds
    to "a * e⁻¹ lies in N", not to "a lies in N"; the control shows
    exactly what it DOES convert to, so the negative is located rather
    than merely observed.

    (3) THE QUOTIENT CATEGORY IS NOT LEIBNIZ-EQUAL TO THE DELOOPING OF THE
    QUOTIENT GROUP.  [deloop_quotient_iso] is stated at [≅[StrictCat]],
    the genuine isomorphism of categories.  Exactly FOUR of the ten
    fields a [Category] record literal supplies are convertible -- [obj],
    [hom], [id] and [compose] (the class's [uhom], [dom] and [cod] are
    [:=] definitions derived from them, not data either construction
    chooses) -- and the three controls below exhibit the last three
    ([obj] is [poly_unit] on both sides by inspection).  The other six are
    built twice: [homset], whose two [Equivalence] witnesses are
    [Quotient_equivalence] and [QuotientGrp]'s own [Program] obligation,
    both [Qed]; and with it [compose_respects], [id_left], [id_right],
    [comp_assoc] and [comp_assoc_sym], which [Quotient] assembles from
    [cong_comp]/[cong_incl] and [Deloop] from the monoid's law fields.  So
    the whole records are not convertible (negative 3).  Without this
    probe "isomorphism of categories" could drift into being read as
    "equal".

    (4) THE TWO MEDIATORS AGREE ON THE MAP, NOT AS RECORDS.
    [cat_med_is_quot_med] is [eq_refl] on the underlying map: the
    categorical route through [QuotientLift] lands on #313's [quot_med].
    The [GrpHom] records are not convertible, their unit- and
    product-preservation fields being separately built (one by
    [Build_GrpHom'] from [fmap_comp], the other by [Program]).

    (5) THE CATEGORICAL KERNEL IS COEXTENSIVE WITH [KernelNS], NOT EQUAL.
    [kernel_ns] is obtained with no group-level obligation, from
    [FunctorKernel_Congruence] and [cong_ns].  Its members are the a with
    h a ≈ h e; #313's [KernelNS] collects the a with h a ≈ e.
    [grp_map_unit h] is the one step between them, and it is a proof, not
    a conversion.  The control shows what the categorical membership IS.

    (6) THE PROJECTION FUNCTORS AGREE ON ARROWS, NOT ON OBJECTS.
    [deloop_proj_fmap] is [eq_refl]; [deloop_proj_fobj] needs a [destruct].
    The reason is Construction/Deloop/Transform.v:282-289's, quoted in the
    target file: [poly_unit] is an ordinary inductive with no definitional
    eta, so the constant function at [ttt] and the identity on a
    one-element type are different terms.  This probe pins that the
    difference is real and not an artifact of how the lemma was written.

    WHAT IS DELIBERATELY *NOT* PROBED.  The [≅[Cat]] reading derived from
    [deloop_quotient_iso] carries no conversion claim at all, and the
    setoid isomorphism [ns_cong_iso] is a statement about setoids whose
    equivalences are logical, so neither has a strict side to pin. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Deloop.
Require Import Category.Construction.Deloop.Transform.
Require Import Category.Structure.Groupoid.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Free.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Congruence.

Generalizable All Variables.

(** ** Negative 1: the two groupoid witnesses are not the same term *)

(* POSITIVE CONTROL: the record conversion deloops to the tree's own
   delooping, and the chosen inverses agree, both by [eq_refl]. *)
Example control_deloop_agrees (H : GrpObject) :
  Deloop (grp_deloop_GrpObject H) = grp_deloop H := eq_refl.

Example control_ginv_agrees (H : GrpObject) (a : carrier H) :
  ginv (grp_deloop_IsGroupoid' H) (x:=ttt) (y:=ttt) a = grp_inv H a := eq_refl.

(* ...and for the OTHER witness too, so that "the data agree" is about
   both of the terms the negative separates and not just one of them. *)
Example control_ginv_agrees_Free (H : GrpObject) (a : carrier H) :
  ginv (grp_deloop_IsGroupoid H) (x:=ttt) (y:=ttt) a = grp_inv H a := eq_refl.

(* NEGATIVE: the whole [IsGroupoid] structures are not convertible. *)
Fail Definition negative_isgroupoid_record (H : GrpObject) :
  grp_deloop_IsGroupoid' H = grp_deloop_IsGroupoid H := eq_refl.

(** ** Negative 2: the membership round trip is a biconditional *)

(* POSITIVE CONTROL: what the recovered membership DOES convert to. *)
Example control_round_unfolds {G : GrpObject} (N : NormalSubgroup G)
  (a : carrier G) :
  sub_mem (@cong_ns G (ns_rel N) (ns_congruence N)) a
    = quot_rel N a (grp_unit G) := eq_refl.

(* NEGATIVE: it is not membership in N on the nose. *)
Fail Definition negative_round_strict {G : GrpObject} (N : NormalSubgroup G)
  (a : carrier G) :
  sub_mem (@cong_ns G (ns_rel N) (ns_congruence N)) a = sub_mem N a := eq_refl.

(** ** Negative 3: the quotient category is not the delooping, on the nose *)

(* POSITIVE CONTROLS: hom type and identity agree by [eq_refl]. *)
Example control_quotient_hom {G : GrpObject} (N : NormalSubgroup G) :
  (ttt ~{deloop_quotient N}~> ttt)
    = (ttt ~{grp_deloop (QuotientGrp N)}~> ttt) := eq_refl.

Example control_quotient_id {G : GrpObject} (N : NormalSubgroup G) :
  @id (deloop_quotient N) ttt = @id (grp_deloop (QuotientGrp N)) ttt := eq_refl.

Example control_quotient_compose {G : GrpObject} (N : NormalSubgroup G)
  (f g : carrier G) :
  @compose (deloop_quotient N) ttt ttt ttt f g
    = @compose (grp_deloop (QuotientGrp N)) ttt ttt ttt f g := eq_refl.

(* NEGATIVE: the whole categories are not convertible. *)
Fail Definition negative_quotient_category {G : GrpObject}
  (N : NormalSubgroup G) :
  deloop_quotient N = grp_deloop (QuotientGrp N) := eq_refl.

(** ** Negative 4: the two mediators agree on the map, not as records *)

(* POSITIVE CONTROL: the underlying maps are the same term. *)
Example control_med_map {G K : GrpObject} (N : NormalSubgroup G)
  (p : Kills N K) (a : carrier (QuotientGrp N)) :
  grp_map (cat_med N p) a = grp_map (quot_med N p) a := eq_refl.

(* NEGATIVE: the homomorphism records are not. *)
Fail Definition negative_med_record {G K : GrpObject} (N : NormalSubgroup G)
  (p : Kills N K) : cat_med N p = quot_med N p := eq_refl.

(** ** Negative 5: the categorical kernel is coextensive, not equal *)

(* POSITIVE CONTROL: what the categorical kernel's membership IS. *)
Example control_kernel_unfolds {G K : GrpObject} (h : G ~{Grp}~> K)
  (a : carrier G) :
  sub_mem (kernel_ns h) a = (grp_map h a ≈ grp_map h (grp_unit G)) := eq_refl.

(* NEGATIVE: it is not #313's kernel membership on the nose. *)
Fail Definition negative_kernel_strict {G K : GrpObject} (h : G ~{Grp}~> K)
  (a : carrier G) :
  sub_mem (kernel_ns h) a = sub_mem (KernelNS h) a := eq_refl.

(** ** Negative 6: the projection functors agree on arrows, not on objects *)

(* POSITIVE CONTROL: the arrow actions are the same term. *)
Example control_proj_fmap {G : GrpObject} (N : NormalSubgroup G)
  (a : carrier G) :
  @fmap _ _ (quot_to_deloop N ◯ deloop_quotient_proj N) ttt ttt a
    = @fmap _ _ (deloop_hom (quot_proj N)) ttt ttt a := eq_refl.

(* NEGATIVE: the object actions are not. *)
Fail Definition negative_proj_fobj {G : GrpObject} (N : NormalSubgroup G)
  (x : grp_deloop G) :
  fobj[quot_to_deloop N ◯ deloop_quotient_proj N] x
    = fobj[deloop_hom (quot_proj N)] x := eq_refl.
