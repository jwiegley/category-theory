Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Quotient.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Epi.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Quotient.Isomorphism.

Generalizable All Variables.

(** * Mac Lane's group illustration: the quotient objects of G are the
      G/N *)

(* nLab:      https://ncatlab.org/nlab/show/quotient+object
   nLab:      https://ncatlab.org/nlab/show/quotient+group
   Wikipedia: https://en.wikipedia.org/wiki/Quotient_group

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.7, book p. 126 (PDF p. 135), Definition 3, illustrates quotient
   objects with groups: a quotient object of a group G is a quotient
   G/N by a normal subgroup.  Issue #446 recorded that illustration as
   absent "the library having no group theory of that kind".  That was
   STALE when written: Instance/Grp/Quotient.v already carried
   [Subgroup] (:156), [NormalSubgroup] (:178), [QuotientGrp] (:360), the
   projection (:395) with its epicness (:421) and [KernelNS] (:620), and
   Instance/Grp/Quotient/Isomorphism.v already carried the first
   isomorphism theorem (:297) with its triangle (:305).  This file spends
   those donors; it adds no group theory.

   WHAT IS DELIVERED.  One direction is a line: [grp_quot_of_normal N] is
   [mk_quot (quot_proj N) (quot_proj_epic N)].  The order comes with it:
   [grp_quot_le_of_included] says that a LARGER normal subgroup gives a
   SMALLER quotient object -- N ⊆ N' implies G/N' ≤ G/N in the
   factorization preorder, the coarser quotient being the lower one --
   with the identity function as mediator, its respectfulness clause
   being exactly the inclusion of members.

   The CONVERSE is where the constructive cost sits, and the type says
   so.  [grp_quot_is_quot_by_kernel] takes a quotient object whose epi is
   SURJECTIVE ([GrpSurjective], Instance/Grp/Epi.v:333) and produces
   q ≈ grp_quot_of_normal (KernelNS (quot_epi q)): the first isomorphism
   theorem gives G/ker e ≅ im e, [surjective_image_iso]
   (Instance/Grp/Quotient/Isomorphism.v:173) gives im e ≅ Q, and the
   composite carries the projection to e ([grp_quot_kernel_triangle],
   through :305 and :156), which is what makes it an equivalence OF
   QUOTIENT OBJECTS rather than a bare isomorphism of codomains.
   Surjectivity is NOT available from [Epic] alone in this tree: in [Grp]
   "surjective implies epic" is unconditional (Instance/Grp/Epi.v:1080)
   but the converse is the double-negation elimination that file's own
   header sets out -- the unconditional theorem is :1072's
   [grp_epic_image_dense], "no element can be SHOWN to miss the image" --
   and recovering a preimage needs :1094's [GrpImageStable].  So the
   [Epic]-only reading is stated separately and conditionally, as
   [grp_quot_is_quot_by_kernel_stable] through
   [grp_quot_surjective_of_stable] (:1108's [grp_epic_is_surjective]).
   Instance/Grp/Epi.v:1127 onwards also shows that for an epimorphism
   that hypothesis IS the conclusion restated (:1137,
   [surjective_gives_stable]), so the conditional form is
   honest about buying nothing for free.  This is precisely the clause
   that Instance/FinSet/QuotObj.v does NOT need, the finite search there
   being decidable.

   Non-vacuity is checked rather than assumed: A3 inside S3
   (Instance/Grp/Quotient.v:745) is a proper nontrivial normal subgroup
   of a nonabelian group, so [grp_quot_S3_A3] is a quotient object that
   is neither the top nor the bottom of the order, and
   [grp_quot_S3_trivial_le_A3] inhabits the order lemma at it.

   STRENGTH.  Everything is at ≈ on [QuotObj G].  [QuotObj] inherits
   [SubObj]'s setoid (Theory/Subobject.v:33) and has no Leibniz
   antisymmetry, so no statement here is or could be an [eq_refl]
   readback.

   THE GENERAL LEMMA IT NEEDS.  [quot_equiv_of_cod_iso] -- an
   isomorphism of codomains carrying one epi to the other gives ≈ of
   quotient objects -- is not about groups.  It was first proved in this
   file during the parallel build (as [grp_quot_equiv_of_cod_iso]) and
   was lifted into Theory/Subobject/Quotient.v at integration as a
   corollary of that file's [quot_equiv_iff_iso]; this file consumes it
   and no longer carries its own copy.

   MEASUREMENTS, each re-runnable.  10 constants (.glob heads; a first
   draft had 11, the eleventh being the general lemma since lifted), no
   [Program] so no obligations in the .vo, and all 10 report "Closed
   under the global context" under [Print Assumptions] -- including the
   ones routed through the S3 witness, whose carrier is
   [rot * bool] with decidable equality and needs no axiom.  1 [Defined]
   and 5 [Qed] (a first draft had 2 [Defined], the other being the lifted
   lemma); the [Defined] recompiles green as [Qed] (measured by
   flipping and rebuilding), and it is kept [Defined]
   because [quot_le] and `≈` on [QuotObj] are data that a consumer may
   want to read.  The requirement closure is 94 files (iterated over
   .Makefile.coq.d).  No name introduced here occurs anywhere else in the
   tree (swept over all .glob files with
   '^[a-z]+ [0-9:]+ [^ ]* NAME$', instrument-checked on [sub_le]).
   Universes, by [About], RE-MEASURED after the PR "algebraic carriers are
   sets" (2026-09-17): [grp_quot_of_normal@{u u0 u1}] binds
   [GrpObject@{u0 u0 u0}] and [Grp] as [Category@{u u0}] -- hom level
   identified with proof level, which is what [SubObj] demands and which
   [Grp] satisfies on the nose; the identification is INHERITED from
   Theory/Subobject.v:15 and is not introduced here.  An earlier revision
   wrote [@{u u0}] for the constant and [Category@{u u0 u0}] for [Grp], and
   said "No [Set] pin".  The constant now carries three universes (the
   [NormalSubgroup] argument's own level became visible) and its block
   gained [Set < u] -- a strict LOWER bound, entering with [Prop]'s sort
   through [PropEquiv], and NOT an identification: nothing is pinned AT
   [Set], which is what that sentence was about.

   NOT DELIVERED.  No correspondence theorem: that [quot_le] between two
   G/N is EQUIVALENT to inclusion of the normal subgroups is not stated,
   only the one direction that is cheap; the converse would need the
   mediator's action on members recovered from the factorization.  No
   lattice: the meet of two quotient objects of a group is the pushout of
   the two projections, [Grp] has pushouts (Instance/Grp/Pushout.v), and
   nothing here identifies that pushout with the quotient by the join of
   the two normal subgroups.  No coimages in [Grp^op]: the image
   factorization is in tree (Instance/Grp/Quotient/Isomorphism.v:349's
   [factorization]) but is not packaged as an [ImageOf] at [Grp^op], as
   it is for [Sets] and [FinSet].  No enumeration of the quotient objects
   of any finite group.  No [Print Assumptions] claim about the donors:
   the eleven verdicts below cover the constants of THIS file, and
   docs/AXIOMS.md is where the library-wide picture lives. *)

(** ** Mac Lane's illustration: the quotient objects of a group *)

(* The general lemma this file needs -- two quotient objects are
   equivalent when an isomorphism of their codomains carries one epi to
   the other -- is Theory/Subobject/Quotient.v's [quot_equiv_of_cod_iso].
   It was first proved HERE during the parallel build (as
   [grp_quot_equiv_of_cod_iso], directly by [Isomorphism_Opposite
   (iso_sym i)]) and was lifted into that file at integration as a
   corollary of [quot_equiv_iff_iso]; this file now consumes it.  The
   orientation is still the trap: [SubObj_Setoid] at [C^op] asks for an
   isomorphism IN [C^op], whose [to] is a [C]-arrow the other way round,
   so the [C]-isomorphism handed in goes from the codomain of r to the
   codomain of q. *)

(* Instance/Grp/Quotient.v:360's [QuotientGrp N] with its projection
   (:395), which is epic (:421) because it is the identity function on
   the carrier.  This is the whole of Mac Lane's example in one line. *)
Definition grp_quot_of_normal {G : GrpObject} (N : NormalSubgroup G) :
  @QuotObj Grp G :=
  mk_quot (quot_proj N) (quot_proj_epic N).

(* The order, in the direction the factorization preorder gives it: a
   LARGER normal subgroup gives a SMALLER (coarser) quotient object.
   The mediating arrow is the identity function, and its respectfulness
   clause is exactly the inclusion of members. *)
Lemma grp_quot_le_of_included {G : GrpObject} (N N' : NormalSubgroup G)
  (H : ∀ a : carrier G, sub_mem N a → sub_mem N' a) :
  @quot_le Grp G (grp_quot_of_normal N') (grp_quot_of_normal N).
Proof.
  unshelve eexists.
  - unshelve refine {| grp_map := {| morphism :=
      fun a : carrier (QuotientGrp N) => a : carrier (QuotientGrp N') |} |}.
    (* The quotient's `≈` is the truncation of [quot_rel] since the PR
       "algebraic carriers are sets" (2026-09-17): the inclusion is applied
       under it, [Prop] to [Prop]. *)
    + intros a b Hab.
      change (inhabited (quot_rel N a b)) in Hab.
      change (inhabited (quot_rel N' a b)).
      destruct Hab as [Hab]; exact (inhabits (H _ Hab)).
    + simpl; constructor; apply quot_rel_refl.
    + intros a b; simpl; constructor; apply quot_rel_refl.
  - intro a; simpl; constructor; apply quot_rel_refl.
Defined.

(** ** The converse, and the hypothesis it costs *)

Section Converse.

Context {G : GrpObject}.

(* In [Grp] a surjection is epic unconditionally
   (Instance/Grp/Epi.v:1080) but the converse is not available
   constructively: [grp_epic_image_dense] (:1072) gives only that no
   element can be SHOWN to miss the image, and Instance/Grp/Epi.v's
   header sets out why -- recovering a preimage from an epimorphism is
   the double-negation elimination its [GrpImageStable] (:1094) names.
   So the theorem below is stated for a quotient object whose epi is
   surjective, and the [Epic]-only form is recorded separately as the
   conditional [grp_quot_is_quot_by_kernel_stable]. *)
Definition grp_quot_surjective_of_stable (q : @QuotObj Grp G)
  (Hst : @GrpImageStable G (quot_cod q) (quot_epi q)) :
  GrpSurjective (quot_epi q) :=
  grp_epic_is_surjective (quot_epi q) Hst (quot_is_epic q).

(* The comparison: G/ker e ≅ im e ≅ Q, the first isomorphism theorem
   (Instance/Grp/Quotient/Isomorphism.v:297) followed by the
   identification of the image with the codomain of a surjection (:173). *)
Definition grp_quot_kernel_iso (q : @QuotObj Grp G)
  (Hs : GrpSurjective (quot_epi q)) :
  QuotientGrp (KernelNS (quot_epi q)) ≅[Grp] quot_cod q :=
  iso_compose (surjective_image_iso (quot_epi q) Hs)
              (first_isomorphism_theorem (quot_epi q)).

(* ... and it carries the projection to the quotient epi, which is what
   makes it an equivalence OF QUOTIENT OBJECTS and not merely an
   isomorphism of codomains.  The two triangles are :305's
   [first_isomorphism_triangle] and :156's [image_factors]. *)
Lemma grp_quot_kernel_triangle (q : @QuotObj Grp G)
  (Hs : GrpSurjective (quot_epi q)) :
  to (grp_quot_kernel_iso q Hs) ∘ quot_proj (KernelNS (quot_epi q))
    ≈ quot_epi q.
Proof.
  change (to (surjective_image_iso (quot_epi q) Hs)
            ∘ to (first_isomorphism_theorem (quot_epi q))
            ∘ quot_proj (KernelNS (quot_epi q)) ≈ quot_epi q).
  rewrite <- comp_assoc.
  rewrite (first_isomorphism_triangle (quot_epi q)).
  exact (image_factors (quot_epi q)).
Qed.

(* Mac Lane §V.7: the quotient objects of a group ARE the G/N.  Stated
   at ≈ on [QuotObj G], which is the strongest relation available --
   [QuotObj] inherits [SubObj]'s setoid and has no Leibniz
   antisymmetry. *)
Theorem grp_quot_is_quot_by_kernel (q : @QuotObj Grp G)
  (Hs : GrpSurjective (quot_epi q)) :
  q ≈ grp_quot_of_normal (KernelNS (quot_epi q)).
Proof.
  exact (quot_equiv_of_cod_iso q
           (grp_quot_of_normal (KernelNS (quot_epi q)))
           (grp_quot_kernel_iso q Hs) (grp_quot_kernel_triangle q Hs)).
Qed.

(* The same statement with the stability hypothesis in place of
   surjectivity, so that the cost of the classical reading is visible in
   the type rather than hidden in a side condition. *)
Theorem grp_quot_is_quot_by_kernel_stable (q : @QuotObj Grp G)
  (Hst : @GrpImageStable G (quot_cod q) (quot_epi q)) :
  q ≈ grp_quot_of_normal (KernelNS (quot_epi q)).
Proof.
  exact (grp_quot_is_quot_by_kernel q (grp_quot_surjective_of_stable q Hst)).
Qed.

End Converse.

(** ** Non-vacuity *)

(* The correspondence is inhabited at a nondegenerate pair: A3 inside S3
   (Instance/Grp/Quotient.v:745) is a proper nontrivial normal subgroup
   of a nonabelian group, so [grp_quot_of_normal A3] is a quotient object
   of S3 that is neither the top nor the bottom of the order.  The two
   separations are Instance/Grp/Quotient.v's [S3_mod_A3_not_collapsed]
   and [quot_proj_A3_not_injective]; [grp_quot_S3_A3_not_collapsed]
   below is a verbatim RE-EXPORT of the first under a name that says
   what it is used for, and proves nothing new -- the constant that
   carries new content here is [grp_quot_S3_A3] itself and the order
   inhabitant [grp_quot_S3_trivial_le_A3]. *)
Definition grp_quot_S3_A3 : @QuotObj Grp S3 := grp_quot_of_normal A3.

Lemma grp_quot_S3_A3_not_collapsed :
  quot_rel A3 S3_s s3_unit → False.
Proof. exact (S3_mod_A3_not_collapsed). Qed.

(* The trivial normal subgroup sits below A3, so the identity quotient is
   above it in the factorization order -- the order lemma, inhabited. *)
Lemma grp_quot_S3_trivial_le_A3 :
  @quot_le Grp S3 (grp_quot_of_normal A3) (grp_quot_of_normal (TrivialNS S3)).
Proof. exact (grp_quot_le_of_included (TrivialNS S3) A3 trivial_in_A3). Qed.
