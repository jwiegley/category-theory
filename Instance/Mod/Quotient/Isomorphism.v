Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.Subtract.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Instance.Mod.Quotient.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Theory.Universal.Element.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * The module isomorphism theorems, from the universal property

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §III.1
    Exercise 5 (printed p. 59, PDF p. 68) [maclane:III.1:ex5].
    nLab: https://ncatlab.org/nlab/show/isomorphism+theorem
    Wikipedia: https://en.wikipedia.org/wiki/Isomorphism_theorems

    Mac Lane's point at §III.1 is that the isomorphism theorems follow
    from the universality of the projection ALONE, without a second look
    at cosets.  This file takes that seriously, and the honest accounting
    of how far it goes is the first thing below, because "derived from
    universality" is a claim about the SHAPE of a proof and is easy to
    assert falsely.  The grading is the same as
    Instance/Grp/Quotient/Isomorphism.v's and is repeated rather than
    cited, because the proofs here are not that file's proofs.

    HOW EACH THEOREM IS ACTUALLY OBTAINED.

    The comparisons for the FIRST and THIRD are produced by ONE
    mechanism: [universal_element_iso] (Theory/Universal/Element.v:766),
    which turns two universal elements of the SAME functor into an
    isomorphism of their carriers, together with its uniqueness clause
    [universal_element_iso_unique]; neither is built by exhibiting
    mutually inverse maps and checking round trips.  The SECOND is not of
    that form and this header does not pretend otherwise.  What differs
    between the three is the cost of exhibiting the SECOND universal
    element:

      - THIRD ([mod_third_isomorphism_theorem], (M/S)/(T/S) ≅ M/T).  A pure
        universal-property chase, and the cleanest of the three:
        [mquot_universal_T_over_S] derives the second universal element
        from [mquot_universal_element T] and [mquot_proj_epic S] by
        composing and cancelling [mquot_proj S] on the right.  THE STEPS
        THAT CARRY ELEMENTWISE CONTENT -- not every step that MENTIONS
        an element, since several obligations bind an element variable
        and then never inspect it -- and none of them destructures one: [mquot_step_kills] and
        [mod_third_precompose_kills], which say respectively that the
        comparison kills T/S and that k ∘ p_S kills T -- both are
        [mquot_rel_zero_iff] or the given killing hypothesis applied at
        a variable, and both are unavoidable in any formulation, since
        "kills" is an elementwise predicate BY DEFINITION -- and the
        `≈`-saturation obligation of [TmodS], which is the only one that
        COMPUTES with elements and which is a prerequisite to STATING
        the theorem rather than a step in proving it.  No coset is
        manipulated and no representative is chosen.

      - FIRST ([mod_first_isomorphism_theorem], M/ker f ≅ im f).  The second
        universal element ([mod_image_universal_element]) is exhibited
        directly, and the mediator [mod_image_med] READS A PREIMAGE out
        of the image-membership witness -- [mod_image_med_wd] being what
        makes that well defined.  The witness is DATA ([ImageSubmod]'s
        membership is a sigma), so nothing is chosen, but an element IS
        destructured, which is the honest difference from the third.
        It is fair to call this a
        universal-property derivation of the ISOMORPHISM whose input is
        an elementwise construction of the comparison universal element.
        Nothing shortens that input: the image is DEFINED elementwise, as
        a submodule of the codomain, so any map out of it must consume a
        membership witness.

      - SECOND ([mod_second_isomorphism_theorem], S/(S ∩ T) ≅ (S + T)/T).  A
        COROLLARY of the first, in the textbook manner: the composite
        S ↪ S + T ↠ (S + T)/T is surjective with kernel S ∩ T.  Its two
        elementwise inputs are named and proved separately
        ([mod_psi_kernel_is_meet], [mod_psi_surjective]).  Downstream of those
        two the argument is again universality -- BUT read the
        composition honestly: this theorem is
        [mod_first_isomorphism_theorem mod_psi] composed with
        [mod_surjective_image_iso], and THAT one IS built as an inverse pair
        with two round trips, as is [mquot_congr]
        (Instance/Mod/Quotient.v) which the literal form composes with.
        Both are degenerate as inverse pairs -- every leg the identity on
        underlying elements, every round trip [reflexivity] or
        [mquot_rel_refl] -- but they are not instances of
        [universal_element_iso], and the claim above is scoped to the
        comparisons, not to every isomorphism this file names.

    So: one theorem is a pure chase, one has an elementwise construction
    of its comparison object, and one is a corollary of that plus two
    identity-carrier repackagings.  NONE of them manipulates cosets, for
    the structural reason that the setoid quotient of
    Instance/Mod/Quotient.v forms no coset object at all -- but that is a
    property of the PRESENTATION, and the elementwise steps above would
    still be elementwise in any presentation.

    WHERE THE MODULE CASE IS GENUINELY CHEAPER THAN THE GROUP CASE, and
    it is not a matter of degree.  Instance/Grp/Quotient/Isomorphism.v
    needs [product_shuffle] and [inverse_shuffle] -- two normality
    manipulations, associativity chains of four and five rewrites
    respectively -- to make [SubgroupProduct] closed under product and
    inverse, and it must require its second argument to be a NORMAL
    subgroup for the product to be a subgroup at all.  Here
    [SubmoduleSum] takes TWO arbitrary submodules, closure under
    addition is one commutativity shuffle, closure under negation is
    not even a field, and the SUM is symmetric in its two arguments
    ([SubmoduleSum_comm], at the level of membership) in a way the
    group product cannot be.  Nothing in this file conjugates
    anything.

    WHAT IS DELIVERED.  The image of a homomorphism as an object with its
    corestriction; the first isomorphism theorem with its uniqueness
    clause and the epi-mono mod_factorization; the third with its uniqueness
    clause; the second over an explicit [SubmoduleSum]; and non-vacuity
    witnesses at ℤ for all three.

    WHAT IS NOT DELIVERED.  No fourth ("correspondence"/lattice) theorem;
    no modular law; no butterfly lemma; no exact sequences; and no
    naturality of the isomorphisms in f, S or T.  The second theorem's
    two universal elements are not compared by a uniqueness clause, it
    being a composite of three isomorphisms rather than a single
    comparison. *)

(** ** The image of a homomorphism, as an object of [RMod R] *)

Definition ImageMod {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : RModObject R := SubmoduleMod (ImageSubmod f).

(* The corestriction of f to its image: the same map, carrying its own
   witness. *)
Program Definition mod_image_cores {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : M ~{RMod R}~> ImageMod f := {|
  rm_hom := {| cmon_map := {| morphism := fun a : carrier (cmon_setoid M) =>
      existT _ (cmon_map (rm_hom f) a) (existT _ a (reflexivity _)) |} |}
|}.
Next Obligation. intros R M N f a b Hab; simpl; now rewrite Hab. Qed.
Next Obligation.
  intros R M N f; simpl; apply (cmon_map_zero (rm_hom f)).
Qed.
Next Obligation.
  intros R M N f a b; simpl; apply (cmon_map_plus (rm_hom f)).
Qed.
Next Obligation. intros R M N f r a; simpl; apply (rm_map_smul f). Qed.

(* The inclusion of the image recovers f: the triangle
   f = (im f ↪ N) ∘ (M ↠ im f) holds pointwise by reflexivity, the
   corestriction changing no element. *)
Lemma mod_image_factors {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) :
  smod_incl (ImageSubmod f) ∘ mod_image_cores f ≈ f.
Proof. intro a; simpl; reflexivity. Qed.

Lemma mod_image_cores_surjective {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : RModSurjective (mod_image_cores f).
Proof.
  intro p; simpl.
  exists (`1 (`2 p)); simpl.
  exact (`2 (`2 p)).
Qed.

(* A surjective homomorphism identifies its image with its codomain.  The
   inverse map sends b to b together with its preimage witness, which is
   DATA, so nothing is chosen. *)
Program Definition mod_surjective_image_iso {R : RingObject}
  {M N : RModObject R} (f : M ~{RMod R}~> N) (Hs : RModSurjective f) :
  ImageMod f ≅[RMod R] N := {|
  to := smod_incl (ImageSubmod f);
  from := {| rm_hom := {| cmon_map :=
    {| morphism := fun b : carrier (cmon_setoid N) =>
         existT _ b (Hs b) |} |} |}
|}.
Next Obligation. intros R M N f Hs a b Hab; exact Hab. Qed.
Next Obligation. intros R M N f Hs; simpl; reflexivity. Qed.
Next Obligation. intros R M N f Hs a b; simpl; reflexivity. Qed.
Next Obligation. intros R M N f Hs r a; simpl; reflexivity. Qed.
Next Obligation. intros R M N f Hs a; simpl; reflexivity. Qed.
Next Obligation. intros R M N f Hs a; simpl; reflexivity. Qed.

(** ** The image carries the second universal element *)

Section ImageUniversal.

Context {R : RingObject}.
Context {M N : RModObject R}.
Context (f : M ~{RMod R}~> N).

Lemma mod_image_cores_kills (a : carrier (cmon_setoid M)) :
  smod_mem (KernelSub f) a →
  cmon_map (rm_hom (mod_image_cores f)) a ≈ cmon_zero (ImageMod f).
Proof. intro Ha; simpl in *; exact Ha. Qed.

Definition mod_image_elem : MKills (KernelSub f) (ImageMod f) :=
  existT _ (mod_image_cores f) mod_image_cores_kills.

Section ImageMediator.

Context {K : RModObject R}.
Context (x : MKills (KernelSub f) K).

(* Well-definedness, isolated as one lemma: elements with the same image
   under f have the same image under the given map, because they differ
   by an element of ker f, which that map kills.  This is the ONE place
   an element is inspected, and everything the mediator owes is
   discharged from it.

   Isolating it is not tidiness -- it is what makes the construction
   independent of whether [ImageSubmod]'s closure obligations are
   transparent.  They are [Program] obligations and hence [Qed]-opaque,
   so the preimage witness that [ImageMod]'s operations carry does NOT
   reduce, and the zero, addition and scalar laws below cannot be closed
   by computation; they are closed by comparing f-images instead. *)
Lemma mod_image_med_wd (a b : carrier (cmon_setoid M)) :
  cmon_map (rm_hom f) a ≈ cmon_map (rm_hom f) b →
  cmon_map (rm_hom (`1 x)) a ≈ cmon_map (rm_hom (`1 x)) b.
Proof.
  intro Hab.
  apply (mkills_descends (KernelSub f) x).
  unfold mquot_rel; simpl.
  rewrite (ab_map_sub (rm_hom f) a b), Hab.
  apply ab_sub_self.
Qed.

Program Definition mod_image_med : ImageMod f ~{RMod R}~> K := {|
  rm_hom := {| cmon_map :=
    {| morphism := fun p : carrier (cmon_setoid (ImageMod f)) =>
         cmon_map (rm_hom (`1 x)) (`1 (`2 p)) |} |}
|}.
Next Obligation.
  intros p q Hpq; simpl in *.
  apply mod_image_med_wd.
  rewrite (`2 (`2 p)), (`2 (`2 q)).
  exact Hpq.
Qed.
Next Obligation.
  simpl.
  transitivity (cmon_map (rm_hom (`1 x)) (cmon_zero M)).
  - apply mod_image_med_wd.
    rewrite (`2 (`2 (cmon_zero (ImageMod f)))); simpl.
    symmetry; apply (cmon_map_zero (rm_hom f)).
  - apply (cmon_map_zero (rm_hom (`1 x))).
Qed.
Next Obligation.
  intros p q; simpl.
  transitivity (cmon_map (rm_hom (`1 x))
                  (cmon_plus M (`1 (`2 p)) (`1 (`2 q)))).
  - apply mod_image_med_wd.
    rewrite (`2 (`2 (cmon_plus (ImageMod f) p q))).
    rewrite (cmon_map_plus (rm_hom f)).
    now rewrite (`2 (`2 p)), (`2 (`2 q)).
  - apply (cmon_map_plus (rm_hom (`1 x))).
Qed.
Next Obligation.
  intros r p; simpl.
  transitivity (cmon_map (rm_hom (`1 x)) (rm_smul M r (`1 (`2 p)))).
  - apply mod_image_med_wd.
    rewrite (`2 (`2 (rm_smul (ImageMod f) r p))).
    rewrite (rm_map_smul f).
    now rewrite (`2 (`2 p)).
  - apply (rm_map_smul (`1 x)).
Qed.

Lemma mod_image_med_commutes : mod_image_med ∘ mod_image_cores f ≈ `1 x.
Proof. intro a; simpl; reflexivity. Qed.

Lemma mod_image_med_unique (v : ImageMod f ~{RMod R}~> K)
  (Hv : v ∘ mod_image_cores f ≈ `1 x) : mod_image_med ≈ v.
Proof.
  intro p; simpl.
  transitivity (cmon_map (rm_hom v)
                  (cmon_map (rm_hom (mod_image_cores f)) (`1 (`2 p)))).
  - symmetry; exact (Hv (`1 (`2 p))).
  - apply proper_morphism; simpl.
    exact (`2 (`2 p)).
Qed.

End ImageMediator.

(* ⟨im f, corestriction⟩ is a universal element of the SAME functor of
   which ⟨M/ker f, projection⟩ is one. *)
Program Definition mod_image_universal_element :
  AUniversalElement (MKillsFunctor (KernelSub f)) (ImageMod f) := {|
  aue_elem := mod_image_elem
|}.
Next Obligation.
  intros K x.
  unshelve refine {| unique_obj := mod_image_med x |}.
  - exact (mod_image_med_commutes x).
  - intros v Hv; simpl in *.
    exact (mod_image_med_unique x v Hv).
Defined.

End ImageUniversal.

(** ** The first isomorphism theorem *)

(* Two universal elements of one functor: [universal_element_iso] does
   the rest.  Nothing here builds a map or checks a round trip. *)
Definition mod_first_isomorphism_theorem {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) :
  QuotientMod (KernelSub f) ≅[RMod R] ImageMod f :=
  universal_element_iso (mquot_universal_element (KernelSub f))
                        (mod_image_universal_element f).

Lemma mod_first_isomorphism_triangle {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) :
  to (mod_first_isomorphism_theorem f) ∘ mquot_proj (KernelSub f)
    ≈ mod_image_cores f.
Proof.
  exact (ue_med_commutes (mquot_universal_element (KernelSub f))
                         (mod_image_universal_element f)).
Qed.

(* BOTH LEGS ARE THE TWO MEDIATORS, by convertibility -- the [eq_refl]
   exception to the `≈` discipline.  [ue_med] is
   [unique_obj (aue_universal U1 (aue_elem U2))]
   (Theory/Universal/Element.v:728), and since both universal elements
   above were built with their mediators as [unique_obj], the generic
   machinery rebuilds neither map.  The strict form was tried FIRST and
   holds; the boundary that does NOT hold strictly is the mediator's
   triangle, which is `≈` and not Leibniz (pinned in
   Test/ProbeModQuotient.v). *)
Example mod_first_isomorphism_to_is_mquot_med {R : RingObject}
  {M N : RModObject R} (f : M ~{RMod R}~> N) :
  to (mod_first_isomorphism_theorem f)
    = mquot_med (KernelSub f) (mod_image_elem f).
Proof. reflexivity. Qed.

Example mod_first_isomorphism_from_is_image_med {R : RingObject}
  {M N : RModObject R} (f : M ~{RMod R}~> N) :
  from (mod_first_isomorphism_theorem f)
    = mod_image_med f (mquot_elem (KernelSub f)).
Proof. reflexivity. Qed.

(* UNIQUENESS, proved rather than cited: any isomorphism carrying the
   projection to the corestriction IS this one. *)
Theorem mod_first_isomorphism_unique {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N)
  (v : QuotientMod (KernelSub f) ≅[RMod R] ImageMod f)
  (Hv : to v ∘ mquot_proj (KernelSub f) ≈ mod_image_cores f) :
  mod_first_isomorphism_theorem f ≈ v.
Proof.
  exact (universal_element_iso_unique
           (mquot_universal_element (KernelSub f))
           (mod_image_universal_element f) v Hv).
Qed.

(** ** The epi-mono mod_factorization *)

Theorem mod_factorization {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) :
  smod_incl (ImageSubmod f)
    ∘ to (mod_first_isomorphism_theorem f)
    ∘ mquot_proj (KernelSub f)
  ≈ f.
Proof.
  rewrite <- comp_assoc.
  rewrite (mod_first_isomorphism_triangle f).
  apply mod_image_factors.
Qed.

Theorem mod_factorization_epi {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Epic (mquot_proj (KernelSub f)).
Proof. apply mquot_proj_epic. Qed.

Theorem mod_factorization_mono {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Monic (smod_incl (ImageSubmod f)).
Proof. apply smod_incl_monic. Qed.

(* f is injective exactly when its kernel is trivial. *)
Theorem mod_injective_iff_kernel_trivial {R : RingObject}
  {M N : RModObject R} (f : M ~{RMod R}~> N) :
  RModInjective f
    ↔ (∀ a : carrier (cmon_setoid M), smod_mem (KernelSub f) a →
         a ≈ cmon_zero M).
Proof.
  split.
  - intros Hinj a Ha; simpl in Ha.
    apply Hinj.
    rewrite Ha.
    symmetry; apply (cmon_map_zero (rm_hom f)).
  - intros Htriv a b Hab.
    apply (fst (ab_sub_eq_zero_iff M a b)).
    apply Htriv; simpl.
    rewrite (ab_map_sub (rm_hom f) a b), Hab.
    apply ab_sub_self.
Qed.

Theorem mod_monic_iff_kernel_trivial {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) :
  Monic f ↔ (∀ a : carrier (cmon_setoid M), smod_mem (KernelSub f) a →
               a ≈ cmon_zero M).
Proof.
  split.
  - intro Hm.
    apply (fst (mod_injective_iff_kernel_trivial f)).
    exact (fst (rmod_monic_iff_injective f) Hm).
  - intro Ht.
    apply (snd (rmod_monic_iff_injective f)).
    exact (snd (mod_injective_iff_kernel_trivial f) Ht).
Qed.

(** ** The third isomorphism theorem *)

Section Third.

Context {R : RingObject}.
Context {M : RModObject R}.
Context (S T : Submodule M).
Context (Hsub : ∀ a : carrier (cmon_setoid M), smod_mem S a → smod_mem T a).

(* T read as a submodule of M/S.  The membership predicate is UNCHANGED;
   only the saturation law is new, since M/S's `≈` is coarser than M's.
   The other three laws are the very terms T carries, because M/S's zero,
   addition and action ARE M's. *)
Program Definition TmodS : Submodule (QuotientMod S) := {|
  smod_mem := fun a : carrier (cmon_setoid (QuotientMod S)) => smod_mem T a
|}.
Next Obligation.
  intros a b Hab Ha; simpl in *.
  (* b ≈ a - (a - b), and both a and a - b lie in T *)
  apply (smod_at T (a := ab_sub M a (ab_sub M a b))).
  - unfold ab_sub.
    rewrite ab_neg_plus.
    rewrite (ab_neg_invol M b).
    rewrite <- cmon_plus_assoc.
    rewrite ab_neg_right.
    apply cmon_plus_zero_l.
  - exact (smod_sub T _ _ Ha (Hsub _ Hab)).
Qed.
Next Obligation. simpl; exact (smod_zero T). Qed.
Next Obligation.
  intros a b Ha Hb; simpl in *; exact (smod_plus T _ _ Ha Hb).
Qed.
Next Obligation.
  intros r a Ha; simpl in *; exact (smod_smul T _ _ Ha).
Qed.

(* The comparison M/S ↠ M/T: the identity function again, well defined
   because S ⊆ T. *)
Program Definition mquot_step : QuotientMod S ~{RMod R}~> QuotientMod T := {|
  rm_hom := {| cmon_map :=
    {| morphism := fun a : carrier (cmon_setoid (QuotientMod S)) => a |} |}
|}.
Next Obligation. intros a b Hab; exact (Hsub _ Hab). Qed.
Next Obligation. simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros a b; simpl; apply mquot_rel_refl. Qed.
Next Obligation. intros r a; simpl; apply mquot_rel_refl. Qed.

Lemma mquot_step_triangle : mquot_step ∘ mquot_proj S ≈ mquot_proj T.
Proof. intro a; simpl; apply mquot_rel_refl. Qed.

Lemma mquot_step_kills (a : carrier (cmon_setoid (QuotientMod S))) :
  smod_mem TmodS a →
  cmon_map (rm_hom mquot_step) a ≈ cmon_zero (QuotientMod T).
Proof.
  intro Ha; simpl in *.
  exact (snd (mquot_rel_zero_iff T a) Ha).
Qed.

Definition mquot_step_elem : MKills TmodS (QuotientMod T) :=
  existT _ mquot_step mquot_step_kills.

Section ThirdMediator.

Context {K : RModObject R}.
Context (x : MKills TmodS K).

(* ONE OF THE TWO ELEMENTWISE STEPS of this theorem, the other being
   [mquot_step_kills] as the header records: transferring the killing
   hypothesis across the projection.  A member of T is projected by p_S
   to a member of T/S -- definitionally, the membership predicates being
   the same and p_S the identity function -- so k ∘ p_S kills T. *)
Lemma mod_third_precompose_kills (a : carrier (cmon_setoid M)) :
  smod_mem T a →
  cmon_map (rm_hom (`1 x ∘ mquot_proj S)) a ≈ cmon_zero K.
Proof.
  intro Ha; simpl; unfold Basics.compose.
  exact (`2 x a Ha).
Qed.

Definition mod_third_precompose : MKills T K :=
  existT _ (`1 x ∘ mquot_proj S) mod_third_precompose_kills.

Definition mod_third_med : QuotientMod T ~{RMod R}~> K :=
  mquot_med T mod_third_precompose.

(* Its triangle against the comparison map, obtained by cancelling the
   epimorphism p_S on the right -- no element inspected. *)
Lemma mod_third_med_commutes : mod_third_med ∘ mquot_step ≈ `1 x.
Proof.
  apply (epic (Epic := mquot_proj_epic S)).
  rewrite <- comp_assoc.
  rewrite mquot_step_triangle.
  exact (mquot_med_commutes T mod_third_precompose).
Qed.

Lemma mod_third_med_unique (v : QuotientMod T ~{RMod R}~> K)
  (Hv : v ∘ mquot_step ≈ `1 x) : mod_third_med ≈ v.
Proof.
  apply (mquot_med_unique T mod_third_precompose).
  rewrite <- mquot_step_triangle.
  rewrite comp_assoc.
  now rewrite Hv.
Qed.

End ThirdMediator.

Program Definition mquot_universal_T_over_S :
  AUniversalElement (MKillsFunctor TmodS) (QuotientMod T) := {|
  aue_elem := mquot_step_elem
|}.
Next Obligation.
  intros K x.
  unshelve refine {| unique_obj := mod_third_med x |}.
  - exact (mod_third_med_commutes x).
  - intros v Hv; simpl in *.
    exact (mod_third_med_unique x v Hv).
Defined.

Definition mod_third_isomorphism_theorem :
  QuotientMod TmodS ≅[RMod R] QuotientMod T :=
  universal_element_iso (mquot_universal_element TmodS)
                        mquot_universal_T_over_S.

Lemma mod_third_isomorphism_triangle :
  to mod_third_isomorphism_theorem ∘ mquot_proj TmodS ≈ mquot_step.
Proof.
  exact (ue_med_commutes (mquot_universal_element TmodS)
                         mquot_universal_T_over_S).
Qed.

Theorem mod_third_isomorphism_unique
  (v : QuotientMod TmodS ≅[RMod R] QuotientMod T)
  (Hv : to v ∘ mquot_proj TmodS ≈ mquot_step) :
  mod_third_isomorphism_theorem ≈ v.
Proof.
  exact (universal_element_iso_unique (mquot_universal_element TmodS)
                                      mquot_universal_T_over_S v Hv).
Qed.

End Third.

Arguments TmodS {R M} S T Hsub.
Arguments mquot_step {R M} S T Hsub.
Arguments mod_third_isomorphism_theorem {R M} S T Hsub.
Arguments mod_third_isomorphism_unique {R M} S T Hsub.

(** ** The second isomorphism theorem *)

Section Second.

Context {R : RingObject}.
Context {M : RModObject R}.
Context (S T : Submodule M).

(* The sum S + T, as a submodule.  Membership carries the decomposition
   as DATA, so the elementwise steps below read it back out with nothing
   chosen.  NOTE what is NOT here: the group case
   (Instance/Grp/Quotient/Isomorphism.v's [SubgroupProduct]) needs its
   second argument NORMAL and spends [product_shuffle] and
   [inverse_shuffle]; here both arguments are arbitrary submodules and
   closure is [ab_sub_plus]-style commutativity plus the derived
   [smod_neg]. *)
Definition in_sum (x : carrier (cmon_setoid M)) : Type :=
  { s : carrier (cmon_setoid M) & { t : carrier (cmon_setoid M) &
      ((smod_mem S s * smod_mem T t) * (x ≈ cmon_plus M s t))%type } }.

Program Definition SubmoduleSum : Submodule M := {|
  smod_mem := in_sum
|}.
Next Obligation.
  intros a b Hab [s [t [Hst Ha]]].
  exists s, t; split; [ exact Hst | now rewrite <- Hab ].
Qed.
Next Obligation.
  exists (cmon_zero M), (cmon_zero M).
  split; [ split; [ exact (smod_zero S) | exact (smod_zero T) ] | ].
  symmetry; apply cmon_plus_zero_l.
Qed.
Next Obligation.
  intros a b [s [t [[Hs Ht] Ha]]] [s' [t' [[Hs' Ht'] Hb]]].
  exists (cmon_plus M s s'), (cmon_plus M t t').
  split.
  - split.
    + exact (smod_plus S _ _ Hs Hs').
    + exact (smod_plus T _ _ Ht Ht').
  - rewrite Ha, Hb.
    (* (s + t) + (s' + t') ≈ (s + s') + (t + t'): commutativity, and
       nothing else. *)
    rewrite !cmon_plus_assoc.
    apply cmon_plus_respects; [ reflexivity |].
    rewrite <- !cmon_plus_assoc.
    apply cmon_plus_respects; [| reflexivity ].
    apply cmon_plus_comm.
Qed.
Next Obligation.
  intros r a [s [t [[Hs Ht] Ha]]].
  exists (rm_smul M r s), (rm_smul M r t).
  split.
  - split.
    + exact (smod_smul S _ _ Hs).
    + exact (smod_smul T _ _ Ht).
  - rewrite Ha.
    apply rm_smul_distr_l.
Qed.

Lemma T_in_sum (t : carrier (cmon_setoid M)) :
  smod_mem T t → smod_mem SubmoduleSum t.
Proof.
  intro Ht.
  exists (cmon_zero M), t.
  split; [ split; [ exact (smod_zero S) | exact Ht ] | ].
  symmetry; apply cmon_plus_zero_l.
Qed.

(* T, read as a submodule of S + T. *)
Program Definition TinSum : Submodule (SubmoduleMod SubmoduleSum) := {|
  smod_mem := fun p : carrier (cmon_setoid (SubmoduleMod SubmoduleSum)) =>
                smod_mem T (`1 p)
|}.
Next Obligation.
  intros a b Hab Ha; simpl in *; exact (smod_resp T _ _ Hab Ha).
Qed.
Next Obligation. simpl; exact (smod_zero T). Qed.
Next Obligation.
  intros a b Ha Hb; simpl in *; exact (smod_plus T _ _ Ha Hb).
Qed.
Next Obligation.
  intros r a Ha; simpl in *; exact (smod_smul T _ _ Ha).
Qed.

(* S, as a submodule of S + T -- the inclusion S ↪ S + T. *)
Program Definition S_into_Sum :
  SubmoduleMod S ~{RMod R}~> SubmoduleMod SubmoduleSum := {|
  rm_hom := {| cmon_map := {| morphism :=
    fun p : carrier (cmon_setoid (SubmoduleMod S)) =>
      existT _ (`1 p)
        (existT _ (`1 p) (existT _ (cmon_zero M)
           (pair (pair (`2 p) (smod_zero T))
                 (symmetry (cmon_plus_zero_r M (`1 p)))))) |} |}
|}.
Next Obligation. intros p q Hpq; exact Hpq. Qed.
Next Obligation. simpl; reflexivity. Qed.
Next Obligation. intros p q; simpl; reflexivity. Qed.
Next Obligation. intros r p; simpl; reflexivity. Qed.

(* The composite S ↪ S + T ↠ (S + T)/T. *)
Definition mod_psi : SubmoduleMod S ~{RMod R}~> QuotientMod TinSum :=
  mquot_proj TinSum ∘ S_into_Sum.

(* ELEMENTWISE INPUT ONE: the kernel of ψ is S ∩ T -- as a biconditional
   on membership, not merely an inclusion. *)
Lemma mod_psi_kernel_is_meet (p : carrier (cmon_setoid (SubmoduleMod S))) :
  smod_mem (KernelSub mod_psi) p ↔ smod_mem T (`1 p).
Proof.
  split.
  - intro Hp; simpl in Hp.
    apply (smod_at T (a := ab_sub M (`1 p) (cmon_zero M))).
    + apply ab_sub_zero_r.
    + exact Hp.
  - intro Hp; simpl.
    apply (smod_at T (a := `1 p)).
    + symmetry; apply ab_sub_zero_r.
    + exact Hp.
Qed.

(* ELEMENTWISE INPUT TWO: ψ is surjective.  Every member of S + T is
   s + t for data s ∈ S, t ∈ T, and s + t is congruent to s modulo T
   because s - (s + t) ≈ -t lies in T.  The group case needs one
   normality computation here; this needs none. *)
Lemma mod_psi_surjective : RModSurjective mod_psi.
Proof.
  intro q.
  destruct (`2 q) as [s [t [[Hs Ht] Hq]]].
  exists (existT _ s Hs).
  simpl.
  unfold mquot_rel; simpl.
  apply (smod_at T (a := ab_neg M t)).
  - rewrite Hq.
    unfold ab_sub.
    rewrite ab_neg_plus.
    rewrite <- cmon_plus_assoc.
    rewrite ab_neg_right.
    symmetry; apply cmon_plus_zero_l.
  - exact (smod_neg T _ Ht).
Qed.

(* Mac Lane §III.1 Exercise 5, second isomorphism theorem, as a corollary
   of the first: S/(S ∩ T) is S/ker ψ, which the first theorem identifies
   with im ψ, which surjectivity identifies with (S + T)/T. *)
Definition mod_second_isomorphism_theorem :
  QuotientMod (KernelSub mod_psi) ≅[RMod R] QuotientMod TinSum :=
  iso_compose (mod_surjective_image_iso mod_psi mod_psi_surjective)
              (mod_first_isomorphism_theorem mod_psi).

(* S ∩ T, as a submodule of S: membership in T, read on elements of S.
   This is the literal left-hand side of the theorem. *)
Program Definition MeetSub : Submodule (SubmoduleMod S) := {|
  smod_mem := fun p : carrier (cmon_setoid (SubmoduleMod S)) =>
                smod_mem T (`1 p)
|}.
Next Obligation.
  intros a b Hab Ha; simpl in *; exact (smod_resp T _ _ Hab Ha).
Qed.
Next Obligation. simpl; exact (smod_zero T). Qed.
Next Obligation.
  intros a b Ha Hb; simpl in *; exact (smod_plus T _ _ Ha Hb).
Qed.
Next Obligation.
  intros r a Ha; simpl in *; exact (smod_smul T _ _ Ha).
Qed.

Definition mod_second_isomorphism_theorem_literal :
  QuotientMod MeetSub ≅[RMod R] QuotientMod TinSum :=
  iso_compose mod_second_isomorphism_theorem
    (mquot_congr MeetSub (KernelSub mod_psi)
       (fun p Hp => snd (mod_psi_kernel_is_meet p) Hp)
       (fun p Hp => fst (mod_psi_kernel_is_meet p) Hp)).

End Second.

Arguments SubmoduleSum {R M} S T.
Arguments TinSum {R M} S T.
Arguments MeetSub {R M} S T.
Arguments mod_psi {R M} S T.
Arguments mod_second_isomorphism_theorem {R M} S T.
Arguments mod_second_isomorphism_theorem_literal {R M} S T.

(* The sum is SYMMETRIC in its two arguments, which the group-level
   [SubgroupProduct] cannot be (there the second argument must be
   normal).  Both directions, at the level of membership. *)
Lemma SubmoduleSum_comm {R : RingObject} {M : RModObject R}
  (S T : Submodule M) (x : carrier (cmon_setoid M)) :
  smod_mem (SubmoduleSum S T) x → smod_mem (SubmoduleSum T S) x.
Proof.
  intros [s [t [[Hs Ht] Hx]]].
  exists t, s.
  split; [ split; assumption |].
  rewrite Hx; apply cmon_plus_comm.
Qed.

(** ** Non-vacuity at ℤ

    All three theorems above hold for every module, so nothing yet shows
    any of them is about a nondegenerate situation.  Instance/Mod.v's
    [Int_RMod] with the even integers (Instance/Mod/Quotient.v's
    [EvenSub]) supplies witnesses for each, and ℤ's setoid is Leibniz
    equality, so every check is a computation.  The multiples of 4 give
    the strictly smaller submodule the third theorem needs, and the
    multiples of 3 give a second submodule whose sum with [EvenSub] is
    everything -- so the second theorem is instantiated at a pair whose
    sum is NOT either summand. *)

Definition FourSub_mem (a : Z) : Type := { k : Z & a = (4 * k)%Z }.

Program Definition FourSub : Submodule Int_RMod := {|
  smod_mem := FourSub_mem
|}.
Next Obligation.
  intros a b Hab [k Hk]; simpl in *.
  exists k; now subst.
Qed.
Next Obligation. exists 0%Z; reflexivity. Qed.
Next Obligation.
  intros a b [k Hk] [l Hl].
  rewrite int_plus_is_add, Hk, Hl.
  exists (k + l)%Z; ring.
Qed.
Next Obligation.
  intros r a [k Hk].
  rewrite int_smul_is_mul, Hk.
  exists (r * k)%Z; ring.
Qed.

Lemma four_in_even (a : Z) : smod_mem FourSub a → smod_mem EvenSub a.
Proof.
  intros [k Hk]; exists (2 * k)%Z; lia.
Qed.

(* 4ℤ is STRICTLY smaller than 2ℤ, so the third theorem is applied to a
   proper inclusion. *)
Theorem four_in_even_strict : smod_mem FourSub 2%Z → False.
Proof. intros [k Hk]; lia. Qed.

Definition ThreeSub_mem (a : Z) : Type := { k : Z & a = (3 * k)%Z }.

Program Definition ThreeSub : Submodule Int_RMod := {|
  smod_mem := ThreeSub_mem
|}.
Next Obligation.
  intros a b Hab [k Hk]; simpl in *.
  exists k; now subst.
Qed.
Next Obligation. exists 0%Z; reflexivity. Qed.
Next Obligation.
  intros a b [k Hk] [l Hl].
  rewrite int_plus_is_add, Hk, Hl.
  exists (k + l)%Z; ring.
Qed.
Next Obligation.
  intros r a [k Hk].
  rewrite int_smul_is_mul, Hk.
  exists (r * k)%Z; ring.
Qed.

(* *** The first theorem at ℤ *)

Definition Z_first_iso :
  QuotientMod (KernelSub (mquot_proj EvenSub))
    ≅[RMod Int_Ring] ImageMod (mquot_proj EvenSub) :=
  mod_first_isomorphism_theorem (mquot_proj EvenSub).

(* The kernel of the projection is exactly 2ℤ, in both directions, so
   the left-hand side really is ℤ/2ℤ. *)
Lemma Z_proj_kernel_is_EvenSub (a : Z) :
  smod_mem (KernelSub (mquot_proj EvenSub)) a ↔ smod_mem EvenSub a.
Proof. exact (mquot_proj_kernel EvenSub a). Qed.

(* Nondegenerate: the image of the projection has two elements apart in
   its own setoid. *)
Theorem Z_first_iso_nondegenerate :
  cmon_map (rm_hom (mod_image_cores (mquot_proj EvenSub))) 1%Z
    ≈ cmon_map (rm_hom (mod_image_cores (mquot_proj EvenSub))) 0%Z → False.
Proof.
  intro H.
  exact (Z_mod_2Z_not_collapsed H).
Qed.

(* *** The third theorem at ℤ: (ℤ/4ℤ)/(2ℤ/4ℤ) ≅ ℤ/2ℤ *)

Definition Z_third_iso :
  QuotientMod (TmodS FourSub EvenSub four_in_even)
    ≅[RMod Int_Ring] QuotientMod EvenSub :=
  mod_third_isomorphism_theorem FourSub EvenSub four_in_even.

(* Nondegenerate on the left: 1 is still apart from 0 in
   (ℤ/4ℤ)/(2ℤ/4ℤ). *)
Theorem Z_third_iso_nondegenerate :
  mquot_rel (TmodS FourSub EvenSub four_in_even) 1%Z 0%Z → False.
Proof.
  (* The membership equation is CONVERTIBLE to one about plain ℤ -- the
     [eq_refl] exception again -- and [exact] is what performs the
     conversion.  [rewrite] cannot: the subtraction here is taken in
     [QuotientMod FourSub] rather than in [Int_RMod], and although the
     two agree on every projection they are not the same term. *)
  intros [k Hk].
  assert (Hz : (1 = 2 * k)%Z) by exact Hk.
  lia.
Qed.

(* And the middle quotient is not the whole of ℤ/4ℤ either: 1 is not in
   2ℤ/4ℤ, while 2 is -- so the theorem is not being applied at a
   degenerate inclusion. *)
Theorem Z_third_middle_proper :
  smod_mem (TmodS FourSub EvenSub four_in_even) 1%Z → False.
Proof.
  intros [k Hk].
  assert (Hz : (1 = 2 * k)%Z) by exact Hk.
  lia.
Qed.

Theorem Z_third_middle_nontrivial :
  smod_mem (TmodS FourSub EvenSub four_in_even) 2%Z.
Proof. exists 1%Z; reflexivity. Qed.

(* *** The second theorem at ℤ: 2ℤ/(2ℤ ∩ 3ℤ) ≅ (2ℤ + 3ℤ)/3ℤ *)

Definition Z_second_iso :
  QuotientMod (KernelSub (mod_psi EvenSub ThreeSub))
    ≅[RMod Int_Ring] QuotientMod (TinSum EvenSub ThreeSub) :=
  mod_second_isomorphism_theorem EvenSub ThreeSub.

Definition Z_second_iso_literal :
  QuotientMod (MeetSub EvenSub ThreeSub)
    ≅[RMod Int_Ring] QuotientMod (TinSum EvenSub ThreeSub) :=
  mod_second_isomorphism_theorem_literal EvenSub ThreeSub.

(* The pair is nondegenerate in the way the theorem's hypotheses ask
   for.  NEITHER submodule contains the other: 2 is even and not a
   multiple of 3, 3 is a multiple of 3 and not even.  So the sum is
   strictly larger than both. *)
Theorem EvenSub_not_in_ThreeSub : smod_mem ThreeSub 2%Z → False.
Proof. intros [k Hk]; lia. Qed.

Theorem ThreeSub_not_in_EvenSub : smod_mem EvenSub 3%Z → False.
Proof. intros [k Hk]; lia. Qed.

(* 1 lies in 2ℤ + 3ℤ (as 3 + (-2)), so the sum is all of ℤ and is
   strictly larger than either summand. *)
Theorem one_in_sum : smod_mem (SubmoduleSum EvenSub ThreeSub) 1%Z.
Proof.
  exists (-2)%Z, 3%Z.
  split.
  - split.
    + exists (-1)%Z; reflexivity.
    + exists 1%Z; reflexivity.
  - reflexivity.
Qed.

(* Nondegenerate on the left: 2ℤ ∩ 3ℤ is 6ℤ, so 2 stays apart from 0 in
   2ℤ/(2ℤ ∩ 3ℤ). *)
Theorem Z_second_iso_nondegenerate :
  mquot_rel (MeetSub EvenSub ThreeSub)
    (existT _ 2%Z (existT (fun k : Z => 2%Z = (2 * k)%Z) 1%Z eq_refl))
    (cmon_zero (SubmoduleMod EvenSub))
  → False.
Proof.
  intros [k Hk].
  assert (Hz : (2 = 3 * k)%Z) by exact Hk.
  lia.
Qed.

(* And on the RIGHT: 1, read as an element of 2ℤ + 3ℤ, stays apart from
   0 in (2ℤ + 3ℤ)/3ℤ.  So both sides have at least two elements. *)
Definition Z_one_in_sum :
  carrier (cmon_setoid (SubmoduleMod (SubmoduleSum EvenSub ThreeSub))) :=
  existT _ 1%Z one_in_sum.

Theorem Z_second_iso_codomain_nondegenerate :
  mquot_rel (TinSum EvenSub ThreeSub) Z_one_in_sum
    (cmon_zero (SubmoduleMod (SubmoduleSum EvenSub ThreeSub)))
  → False.
Proof.
  intros [k Hk].
  assert (Hz : (1 = 3 * k)%Z) by exact Hk.
  lia.
Qed.
