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
Require Import Category.Theory.Universal.Element.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * The isomorphism theorems, from the universal property

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §III.1
    Exercise 4 (printed p. 59) [maclane:III.1:ex4]; Awodey, "Category
    Theory", 2nd ed., §4.2 Corollary 4.5 (printed p. 85)
    [awodey:4.2:cor5].
    nLab: https://ncatlab.org/nlab/show/isomorphism+theorem
    Wikipedia: https://en.wikipedia.org/wiki/Isomorphism_theorems

    Mac Lane's point at §III.1 is that the isomorphism theorems follow
    from the universality of the projection ALONE, without a second look
    at cosets.  This file takes that seriously, and the honest accounting
    of how far it goes is the first thing below, because "derived from
    universality" is a claim about the SHAPE of a proof and is easy to
    assert falsely.

    HOW EACH THEOREM IS ACTUALLY OBTAINED, stated before the theorems so
    that no reader has to reverse-engineer it.

    The comparisons for the FIRST and THIRD are produced by ONE
    mechanism: [universal_element_iso] (Theory/Universal/Element.v:766),
    which turns two universal elements of the SAME functor into an
    isomorphism of their carriers, together with its uniqueness clause
    [universal_element_iso_unique]; neither of those two is built by
    exhibiting mutually inverse maps and checking round trips.  The
    SECOND is not of that form and this header does not pretend
    otherwise: it is the FIRST's comparison composed with two
    identity-carrier inverse pairs ([surjective_image_iso] below, and
    [quot_congr] in Instance/Grp/Quotient.v), each hand-built with
    explicit [to] and [from] and their round trips discharged.  Both are
    degenerate — every leg the identity on elements, every round trip
    reflexivity — but degenerate is not the same as absent, and the
    paragraphs below grade all three accordingly.  What differs between
    the three theorems is the cost of exhibiting the SECOND universal
    element:

      - THIRD ([third_isomorphism_theorem], (G/M)/(N/M) ≅ G/N).  A pure
        universal-property chase, and the cleanest of the three:
        [quot_universal_N_over_M] derives the second universal element
        from [quot_universal_element N] and [quot_proj_epic M] by
        composing and cancelling [quot_proj M] on the right, and inspects
        no element of any group.  Elementwise steps, exhaustively: the
        `≈`-saturation obligation of [NmodM], which is a prerequisite to
        STATING the theorem rather than a step in proving it, and
        [third_precompose_kills], which transfers the hypothesis "k kills
        N/M" to "k ∘ p_M kills N" and is unavoidable in any formulation,
        since "kills" is an elementwise predicate by definition.  No coset
        is manipulated and no representative is chosen.

      - FIRST ([first_isomorphism_theorem], G/ker h ≅ im h).  The second
        universal element ([image_universal_element]) is exhibited
        directly, and its descent step ([image_med_wd]) reads a preimage
        out of the image-membership witness.  That witness is DATA --
        Epi.v's [GrpImage] is a sigma -- so nothing is chosen, but an
        element IS inspected.  This is NOT a coset argument: no coset
        object exists anywhere in the construction, and the mediator's
        uniqueness is still the universal property's.  It is fair to call
        it a universal-property derivation of the ISOMORPHISM whose input
        is an elementwise construction of the comparison universal
        element.  Nothing shortens that input: the image is DEFINED
        elementwise, as a subgroup of the codomain, so any map out of it
        must consume a membership witness.

      - SECOND ([second_isomorphism_theorem], SN/N ≅ S/(S ∩ N)).  A
        COROLLARY of the first, in the textbook manner: the composite
        S ↪ SN ↠ SN/N is surjective with kernel S ∩ N.  Its two
        elementwise inputs are named and proved separately
        ([psi_kernel_is_meet], [psi_surjective]), and each is a single
        normality computation.  Downstream of those two lemmas the
        argument is again universality -- BUT read the composition
        honestly: this theorem is [first_isomorphism_theorem psi]
        composed with [surjective_image_iso], and THAT one IS built as an
        inverse pair with two round trips, as is [quot_congr]
        (Instance/Grp/Quotient.v) which the literal form
        [second_isomorphism_theorem_literal] composes with.  Both are
        degenerate as inverse pairs -- every leg is the identity on
        underlying elements and every round trip closes by [reflexivity]
        or [quot_rel_refl] -- but they are not instances of
        [universal_element_iso] and the claim above is scoped to the
        comparisons, not to every isomorphism this file names.

    So: one theorem is a pure chase, one has an elementwise construction
    of its comparison object, and one is a corollary of that plus two
    identity-carrier repackagings.  NONE of them manipulates cosets, for
    the structural reason that the setoid quotient of
    Instance/Grp/Quotient.v forms no coset object at all -- but the reader
    should note that this is a property of the PRESENTATION, and that the
    elementwise steps above would still be elementwise in any
    presentation.

    WHAT IS DELIVERED.  The image of a homomorphism as a subgroup of the
    codomain with its corestriction; the first isomorphism theorem
    together with Awodey's Corollary 4.5 (the factorization
    G ↠ G/ker h ≅ im h ↪ K, and h monic iff its kernel is trivial); the
    third; the second, over an explicit [SubgroupProduct]; and non-vacuity
    witnesses at S3 for all three.

    UNIQUENESS is proved, not merely available: [first_isomorphism_unique]
    and [third_isomorphism_unique] say that any isomorphism carrying the
    one universal element to the other IS the comparison.  The second
    theorem has no such clause, being a composite of three isomorphisms
    rather than a single comparison.

    WHAT IS NOT DELIVERED.  No fourth ("correspondence"/lattice) theorem;
    no Zassenhaus, Schreier or Jordan-Hölder; no butterfly lemma; and no
    naturality of the isomorphisms in h, S or N.  The second theorem is
    stated as S/(S ∩ N) ≅ SN/N ([second_isomorphism_theorem_literal]),
    the mirror of the orientation the issue writes; isomorphism being
    symmetric, no separate statement is given for the other reading. *)

(** ** The image of a homomorphism, as a subgroup of the codomain *)

(* [GrpImage] and its four closure lemmas are Instance/Grp/Epi.v:322-372;
   they are exactly the four [Subgroup] laws, so this record is assembled
   rather than proved. *)
Definition ImageSub {G K : GrpObject} (h : G ~{Grp}~> K) : Subgroup K :=
  {| sub_mem := GrpImage h
   ; sub_resp := GrpImage_respects h
   ; sub_unit := GrpImage_unit h
   ; sub_mul := GrpImage_mul h
   ; sub_inv := GrpImage_inv h |}.

Definition ImageGrp {G K : GrpObject} (h : G ~{Grp}~> K) : GrpObject :=
  SubgroupGrp (ImageSub h).

(* The corestriction of h to its image: the same map, carrying its own
   witness. *)
Program Definition image_cores {G K : GrpObject} (h : G ~{Grp}~> K) :
  G ~{Grp}~> ImageGrp h := {|
  grp_map := {| morphism := fun a : carrier G =>
                  existT _ (grp_map h a) (existT _ a (reflexivity _)) |}
|}.
Next Obligation. intros G K h a b Hab; simpl; now rewrite Hab. Qed.
Next Obligation. intros G K h; simpl; apply (grp_map_unit h). Qed.
Next Obligation. intros G K h a b; simpl; apply (grp_map_mul h). Qed.

(* The inclusion of the image recovers h: the triangle
   h = (im h ↪ K) ∘ (G ↠ im h) holds pointwise by reflexivity, the
   corestriction changing no element. *)
Lemma image_factors {G K : GrpObject} (h : G ~{Grp}~> K) :
  sub_incl (ImageSub h) ∘ image_cores h ≈ h.
Proof. intro a; simpl; reflexivity. Qed.

(* The corestriction is surjective, by construction. *)
Lemma image_cores_surjective {G K : GrpObject} (h : G ~{Grp}~> K) :
  GrpSurjective (image_cores h).
Proof.
  intro p; simpl.
  exists (`1 (`2 p)).
  simpl.
  exact (`2 (`2 p)).
Qed.

(* A surjective homomorphism identifies its image with its codomain.  The
   inverse map sends b to b together with its preimage witness, which is
   DATA (Epi.v's [GrpImage] is a sigma), so nothing is chosen. *)
Program Definition surjective_image_iso {G K : GrpObject} (h : G ~{Grp}~> K)
  (Hs : GrpSurjective h) : ImageGrp h ≅[Grp] K := {|
  to := sub_incl (ImageSub h);
  from := {| grp_map := {| morphism := fun b : carrier K =>
               existT _ b (Hs b) |} |}
|}.
Next Obligation. intros G K h Hs a b Hab; exact Hab. Qed.
Next Obligation. intros G K h Hs; simpl; reflexivity. Qed.
Next Obligation. intros G K h Hs a b; simpl; reflexivity. Qed.
Next Obligation. intros G K h Hs a; simpl; reflexivity. Qed.
Next Obligation. intros G K h Hs a; simpl; reflexivity. Qed.

(** ** The image carries the second universal element *)

Section ImageUniversal.

Context {G K : GrpObject}.
Context (h : G ~{Grp}~> K).

(* The corestriction kills the kernel of h. *)
Lemma image_cores_kills (a : carrier G) :
  sub_mem (KernelNS h) a →
  grp_map (image_cores h) a ≈ grp_unit (ImageGrp h).
Proof. intro Ha; simpl in *; exact Ha. Qed.

Definition image_elem : Kills (KernelNS h) (ImageGrp h) :=
  existT _ (image_cores h) image_cores_kills.

Section ImageMediator.

Context {K' : GrpObject}.
Context (x : Kills (KernelNS h) K').

(* Well-definedness, isolated as one lemma: elements with the same image
   under h have the same image under the given map, because they differ by
   an element of ker h, which that map kills.  This is the ONE place an
   element is inspected, and everything the mediator owes is discharged
   from it.

   Isolating it is not tidiness -- it is what makes the construction
   independent of whether Instance/Grp/Epi.v's closure lemmas are
   transparent.  [GrpImage_unit], [GrpImage_mul] and [GrpImage_inv] are
   [Qed]-opaque there, so the preimage witness the group operations of
   [ImageGrp] carry does NOT reduce, and the unit and product laws below
   cannot be closed by computation; they are closed by comparing h-images
   instead. *)
Lemma image_med_wd (a b : carrier G) :
  grp_map h a ≈ grp_map h b → grp_map (`1 x) a ≈ grp_map (`1 x) b.
Proof.
  intro Hab.
  apply (kills_descends (KernelNS h) x).
  unfold quot_rel; simpl.
  rewrite (grp_map_mul h), (grp_map_inv h), Hab.
  apply (grp_mul_inv_r K).
Qed.

(* The mediator out of the image: read the preimage out of the membership
   witness and apply the given map to it. *)
Program Definition image_med : ImageGrp h ~{Grp}~> K' := {|
  grp_map := {| morphism := fun p : carrier (ImageGrp h) =>
                  grp_map (`1 x) (`1 (`2 p)) |}
|}.
Next Obligation.
  intros p q Hpq; simpl in *.
  apply image_med_wd.
  rewrite (`2 (`2 p)), (`2 (`2 q)).
  exact Hpq.
Qed.
Next Obligation.
  simpl.
  transitivity (grp_map (`1 x) (grp_unit G)).
  - apply image_med_wd.
    rewrite (`2 (`2 (grp_unit (ImageGrp h)))).
    simpl.
    symmetry; apply (grp_map_unit h).
  - apply (grp_map_unit (`1 x)).
Qed.
Next Obligation.
  intros p q; simpl.
  transitivity (grp_map (`1 x)
                  (grp_mul G (`1 (`2 p)) (`1 (`2 q)))).
  - apply image_med_wd.
    rewrite (`2 (`2 (grp_mul (ImageGrp h) p q))).
    rewrite (grp_map_mul h).
    rewrite (`2 (`2 p)), (`2 (`2 q)).
    reflexivity.
  - apply (grp_map_mul (`1 x)).
Qed.

Lemma image_med_commutes : image_med ∘ image_cores h ≈ `1 x.
Proof. intro a; simpl; reflexivity. Qed.

Lemma image_med_unique (v : ImageGrp h ~{Grp}~> K')
  (Hv : v ∘ image_cores h ≈ `1 x) : image_med ≈ v.
Proof.
  intro p; simpl.
  transitivity (grp_map v (grp_map (image_cores h) (`1 (`2 p)))).
  - symmetry; exact (Hv (`1 (`2 p))).
  - apply proper_morphism; simpl.
    exact (`2 (`2 p)).
Qed.

End ImageMediator.

(* ⟨im h, corestriction⟩ is a universal element of the SAME functor of
   which ⟨G/ker h, projection⟩ is one. *)
Program Definition image_universal_element :
  AUniversalElement (KillsFunctor (KernelNS h)) (ImageGrp h) := {|
  aue_elem := image_elem
|}.
Next Obligation.
  intros K' x.
  unshelve refine {| unique_obj := image_med x |}.
  - exact (image_med_commutes x).
  - intros v Hv; simpl in *.
    exact (image_med_unique x v Hv).
Defined.

End ImageUniversal.

(** ** The first isomorphism theorem *)

(* Two universal elements of one functor: [universal_element_iso] does the
   rest.  Nothing here builds a map or checks a round trip. *)
Definition first_isomorphism_theorem {G K : GrpObject} (h : G ~{Grp}~> K) :
  QuotientGrp (KernelNS h) ≅[Grp] ImageGrp h :=
  universal_element_iso (quot_universal_element (KernelNS h))
                        (image_universal_element h).

(* The comparison carries the projection to the corestriction, which is
   the triangle the reader wants and is [ue_med_commutes] read at these
   two universal elements. *)
Lemma first_isomorphism_triangle {G K : GrpObject} (h : G ~{Grp}~> K) :
  to (first_isomorphism_theorem h) ∘ quot_proj (KernelNS h)
    ≈ image_cores h.
Proof.
  exact (ue_med_commutes (quot_universal_element (KernelNS h))
                         (image_universal_element h)).
Qed.

(* BOTH LEGS ARE THE TWO MEDIATORS, by convertibility -- the [eq_refl]
   exception to the `≈` discipline.  [ue_med] is
   [unique_obj (aue_universal U1 (aue_elem U2))]
   (Theory/Universal/Element.v:728), and since both universal elements
   above were built with their mediators as [unique_obj], the generic
   machinery rebuilds neither map.  The strict form was tried FIRST and
   holds; the boundary that does NOT hold strictly is the mediator's
   triangle, which is `≈` and not Leibniz (pinned in
   Test/ProbeGrpQuotient.v). *)
Example first_isomorphism_to_is_quot_med {G K : GrpObject}
  (h : G ~{Grp}~> K) :
  to (first_isomorphism_theorem h) = quot_med (KernelNS h) (image_elem h).
Proof. reflexivity. Qed.

Example first_isomorphism_from_is_image_med {G K : GrpObject}
  (h : G ~{Grp}~> K) :
  from (first_isomorphism_theorem h) = image_med h (quot_elem (KernelNS h)).
Proof. reflexivity. Qed.

(* UNIQUENESS, proved rather than cited: any isomorphism carrying the
   projection to the corestriction IS this one.  This is
   [universal_element_iso_unique] at the two universal elements, and it is
   what makes the comparison canonical rather than merely existent. *)
Theorem first_isomorphism_unique {G K : GrpObject} (h : G ~{Grp}~> K)
  (v : QuotientGrp (KernelNS h) ≅[Grp] ImageGrp h)
  (Hv : to v ∘ quot_proj (KernelNS h) ≈ image_cores h) :
  first_isomorphism_theorem h ≈ v.
Proof.
  exact (universal_element_iso_unique (quot_universal_element (KernelNS h))
                                      (image_universal_element h) v Hv).
Qed.

(** ** Awodey Corollary 4.5: the epi-mono factorization *)

(* h = (im h ↪ K) ∘ (comparison) ∘ (G ↠ G/ker h), the middle map an
   isomorphism.  The proof composes the two triangles above. *)
Theorem factorization {G K : GrpObject} (h : G ~{Grp}~> K) :
  sub_incl (ImageSub h)
    ∘ to (first_isomorphism_theorem h)
    ∘ quot_proj (KernelNS h)
  ≈ h.
Proof.
  rewrite <- comp_assoc.
  rewrite (first_isomorphism_triangle h).
  apply image_factors.
Qed.

(* The left leg is epic and the right leg monic, so this is an epi-mono
   factorization in the literal sense. *)
Theorem factorization_epi {G K : GrpObject} (h : G ~{Grp}~> K) :
  Epic (quot_proj (KernelNS h)).
Proof. apply quot_proj_epic. Qed.

Theorem factorization_mono {G K : GrpObject} (h : G ~{Grp}~> K) :
  Monic (sub_incl (ImageSub h)).
Proof. apply sub_incl_monic. Qed.

(* Awodey's corollary proper: h is injective exactly when its kernel is
   trivial.  Both directions are elementary; the forward one is the
   observation that the unit is already in the kernel. *)
Theorem injective_iff_kernel_trivial {G K : GrpObject} (h : G ~{Grp}~> K) :
  (∀ a b : carrier G, grp_map h a ≈ grp_map h b → a ≈ b)
    ↔ (∀ a : carrier G, sub_mem (KernelNS h) a → a ≈ grp_unit G).
Proof.
  split.
  - intros Hinj a Ha; simpl in Ha.
    apply Hinj.
    rewrite Ha.
    symmetry; apply (grp_map_unit h).
  - intros Htriv a b Hab.
    apply (grp_cancel_r G (grp_inv G b)).
    rewrite (grp_mul_inv_r G b).
    apply Htriv; simpl.
    rewrite (grp_map_mul h), (grp_map_inv h), Hab.
    apply (grp_mul_inv_r K).
Qed.

(* And the same statement with [Monic], through Instance/Grp.v's
   biconditional. *)
Theorem monic_iff_kernel_trivial {G K : GrpObject} (h : G ~{Grp}~> K) :
  Monic h ↔ (∀ a : carrier G, sub_mem (KernelNS h) a → a ≈ grp_unit G).
Proof.
  split.
  - intro Hm.
    apply (fst (injective_iff_kernel_trivial h)).
    exact (snd (Grp_injectivity_is_monic h) Hm).
  - intro Ht.
    apply (fst (Grp_injectivity_is_monic h)).
    exact (snd (injective_iff_kernel_trivial h) Ht).
Qed.

(** ** The third isomorphism theorem *)

Section Third.

Context {G : GrpObject}.
Context (M N : NormalSubgroup G).
Context (Hsub : ∀ a : carrier G, sub_mem M a → sub_mem N a).

(* N read as a normal subgroup of G/M.  The membership predicate is
   UNCHANGED; only the saturation law is new, since G/M's `≈` is coarser
   than G's.  The other four laws are the very terms N carries, because
   G/M's unit, product and inverse ARE G's. *)
Program Definition NmodM : NormalSubgroup (QuotientGrp M) := {|
  ns_sub := {| sub_mem := fun a : carrier (QuotientGrp M) => sub_mem N a |}
|}.
Next Obligation.
  intros a b Hab Ha; simpl in *.
  (* b ≈ (a * b⁻¹)⁻¹ * a, and both factors lie in N *)
  apply (sub_at N (a := grp_mul G (grp_inv G (grp_mul G a (grp_inv G b))) a)).
  - rewrite (grp_inv_mul G a (grp_inv G b)).
    rewrite (grp_inv_inv G b).
    rewrite (grp_mul_assoc G b (grp_inv G a) a).
    rewrite (grp_mul_inv_l G a).
    apply (grp_mul_unit_r G).
  - exact (sub_mul N _ _ (sub_inv N _ (Hsub _ Hab)) Ha).
Qed.
Next Obligation. simpl; exact (sub_unit N). Qed.
Next Obligation. intros a b Ha Hb; simpl in *; exact (sub_mul N _ _ Ha Hb). Qed.
Next Obligation. intros a Ha; simpl in *; exact (sub_inv N _ Ha). Qed.
Next Obligation. intros t a Ha; simpl in *; exact (ns_conj N t _ Ha). Qed.

(* The comparison G/M ↠ G/N: the identity function again, well defined
   because M ⊆ N. *)
Program Definition quot_step : QuotientGrp M ~{Grp}~> QuotientGrp N := {|
  grp_map := {| morphism := fun a : carrier (QuotientGrp M) => a |}
|}.
Next Obligation. intros a b Hab; exact (Hsub _ Hab). Qed.
Next Obligation. simpl; apply quot_rel_refl. Qed.
Next Obligation. intros a b; simpl; apply quot_rel_refl. Qed.

(* The triangle relating the three projections. *)
Lemma quot_step_triangle : quot_step ∘ quot_proj M ≈ quot_proj N.
Proof. intro a; simpl; apply quot_rel_refl. Qed.

(* The comparison kills N/M. *)
Lemma quot_step_kills (a : carrier (QuotientGrp M)) :
  sub_mem NmodM a → grp_map quot_step a ≈ grp_unit (QuotientGrp N).
Proof.
  intro Ha; simpl in *.
  exact (snd (quot_rel_unit_iff N a) Ha).
Qed.

Definition quot_step_elem : Kills NmodM (QuotientGrp N) :=
  existT _ quot_step quot_step_kills.

Section ThirdMediator.

Context {K : GrpObject}.
Context (x : Kills NmodM K).

(* THE ONE ELEMENTWISE STEP of this theorem: transferring the killing
   hypothesis across the projection.  A member of N is projected by p_M to
   a member of N/M -- definitionally, the membership predicates being the
   same and p_M the identity function -- so k ∘ p_M kills N. *)
Lemma third_precompose_kills (a : carrier G) :
  sub_mem N a → grp_map (`1 x ∘ quot_proj M) a ≈ grp_unit K.
Proof.
  intro Ha; simpl; unfold Basics.compose.
  exact (`2 x a Ha).
Qed.

Definition third_precompose : Kills N K :=
  existT _ (`1 x ∘ quot_proj M) third_precompose_kills.

(* From here the argument is a chase.  The mediator is the one G/N's
   universal property produces for k ∘ p_M. *)
Definition third_med : QuotientGrp N ~{Grp}~> K := quot_med N third_precompose.

(* Its triangle against the comparison map, obtained by cancelling the
   epimorphism p_M on the right -- no element inspected. *)
Lemma third_med_commutes : third_med ∘ quot_step ≈ `1 x.
Proof.
  apply (epic (Epic := quot_proj_epic M)).
  rewrite <- comp_assoc.
  rewrite quot_step_triangle.
  exact (quot_med_commutes N third_precompose).
Qed.

Lemma third_med_unique (v : QuotientGrp N ~{Grp}~> K)
  (Hv : v ∘ quot_step ≈ `1 x) : third_med ≈ v.
Proof.
  apply (quot_med_unique N third_precompose).
  rewrite <- quot_step_triangle.
  rewrite comp_assoc.
  rewrite Hv.
  reflexivity.
Qed.

End ThirdMediator.

(* ⟨G/N, comparison⟩ is a universal element of the kills-(N/M) functor on
   G/M.  Every step above used only [quot_universal_element N], the
   epimorphism [quot_proj_epic M], and the triangle. *)
Program Definition quot_universal_N_over_M :
  AUniversalElement (KillsFunctor NmodM) (QuotientGrp N) := {|
  aue_elem := quot_step_elem
|}.
Next Obligation.
  intros K x.
  unshelve refine {| unique_obj := third_med x |}.
  - exact (third_med_commutes x).
  - intros v Hv; simpl in *.
    exact (third_med_unique x v Hv).
Defined.

(* Mac Lane §III.1 Exercise 4, third isomorphism theorem. *)
Definition third_isomorphism_theorem :
  QuotientGrp NmodM ≅[Grp] QuotientGrp N :=
  universal_element_iso (quot_universal_element NmodM) quot_universal_N_over_M.

Lemma third_isomorphism_triangle :
  to third_isomorphism_theorem ∘ quot_proj NmodM ≈ quot_step.
Proof.
  exact (ue_med_commutes (quot_universal_element NmodM)
                         quot_universal_N_over_M).
Qed.

(* Uniqueness, as for the first theorem. *)
Theorem third_isomorphism_unique
  (v : QuotientGrp NmodM ≅[Grp] QuotientGrp N)
  (Hv : to v ∘ quot_proj NmodM ≈ quot_step) :
  third_isomorphism_theorem ≈ v.
Proof.
  exact (universal_element_iso_unique (quot_universal_element NmodM)
                                      quot_universal_N_over_M v Hv).
Qed.

End Third.

Arguments NmodM {G} M N Hsub.
Arguments quot_step {G} M N Hsub.
Arguments third_isomorphism_theorem {G} M N Hsub.
Arguments third_isomorphism_unique {G} M N Hsub.

(** ** The second isomorphism theorem *)

(* Two shuffles, isolated so that the subgroup laws below are one-liners.
   Both are the standard normality manipulations, and both are proved by
   right-associating everything and cancelling one inverse pair. *)
Lemma product_shuffle (G : GrpObject) (s n s' n' : carrier G) :
  grp_mul G (grp_mul G s n) (grp_mul G s' n')
  ≈ grp_mul G (grp_mul G s s')
      (grp_mul G (grp_mul G (grp_mul G (grp_inv G s') n) s') n').
Proof.
  rewrite !grp_mul_assoc.
  rewrite <- (grp_mul_assoc G s' (grp_inv G s')
                (grp_mul G n (grp_mul G s' n'))).
  rewrite (grp_mul_inv_r G s').
  rewrite (grp_mul_unit_l G).
  reflexivity.
Qed.

Lemma inverse_shuffle (G : GrpObject) (s n : carrier G) :
  grp_inv G (grp_mul G s n)
  ≈ grp_mul G (grp_inv G s)
      (grp_mul G (grp_mul G s (grp_inv G n)) (grp_inv G s)).
Proof.
  rewrite (grp_inv_mul G s n).
  rewrite !grp_mul_assoc.
  rewrite <- (grp_mul_assoc G (grp_inv G s) s
                (grp_mul G (grp_inv G n) (grp_inv G s))).
  rewrite (grp_mul_inv_l G s).
  rewrite (grp_mul_unit_l G).
  reflexivity.
Qed.

Section Second.

Context {G : GrpObject}.
Context (S : Subgroup G).
Context (N : NormalSubgroup G).

(* The product set SN, as a subgroup.  Membership carries the
   decomposition as DATA, so the second isomorphism theorem's elementwise
   steps read it back out with nothing chosen.  Closure under product and
   inverse is where normality is spent:
       (s n)(s' n') = (s s') ((s'⁻¹ n s') n')   and
       (s n)⁻¹      = s⁻¹ (s n⁻¹ s⁻¹). *)
Definition in_product (x : carrier G) : Type :=
  { s : carrier G & { n : carrier G &
      ((sub_mem S s * sub_mem N n) * (x ≈ grp_mul G s n))%type } }.

Program Definition SubgroupProduct : Subgroup G := {|
  sub_mem := in_product
|}.
Next Obligation.
  intros a b Hab [s [n [Hsn Ha]]].
  exists s, n; split; [ exact Hsn | now rewrite <- Hab ].
Qed.
Next Obligation.
  exists (grp_unit G), (grp_unit G).
  split; [ split; [ exact (sub_unit S) | exact (sub_unit N) ] | ].
  symmetry; apply (grp_mul_unit_l G).
Qed.
Next Obligation.
  intros a b [s [n [[Hs Hn] Ha]]] [s' [n' [[Hs' Hn'] Hb]]].
  exists (grp_mul G s s').
  exists (grp_mul G
            (grp_mul G (grp_mul G (grp_inv G s') n) (grp_inv G (grp_inv G s')))
            n').
  split.
  - split.
    + exact (sub_mul S _ _ Hs Hs').
    + exact (sub_mul N _ _ (ns_conj N (grp_inv G s') _ Hn) Hn').
  - rewrite Ha, Hb.
    rewrite (grp_inv_inv G s').
    apply product_shuffle.
Qed.
Next Obligation.
  intros a [s [n [[Hs Hn] Ha]]].
  exists (grp_inv G s).
  exists (grp_mul G (grp_mul G s (grp_inv G n)) (grp_inv G s)).
  split.
  - split.
    + exact (sub_inv S _ Hs).
    + exact (ns_conj N s _ (sub_inv N _ Hn)).
  - rewrite Ha.
    apply inverse_shuffle.
Qed.

(* N sits inside SN, and is normal there. *)
Lemma N_in_product (n : carrier G) : sub_mem N n → sub_mem SubgroupProduct n.
Proof.
  intro Hn.
  exists (grp_unit G), n.
  split; [ split; [ exact (sub_unit S) | exact Hn ] | ].
  symmetry; apply (grp_mul_unit_l G).
Qed.

Program Definition NinSN : NormalSubgroup (SubgroupGrp SubgroupProduct) := {|
  ns_sub := {| sub_mem := fun p : carrier (SubgroupGrp SubgroupProduct) =>
                            sub_mem N (`1 p) |}
|}.
Next Obligation.
  intros a b Hab Ha; simpl in *.
  exact (sub_resp N _ _ Hab Ha).
Qed.
Next Obligation. simpl; exact (sub_unit N). Qed.
Next Obligation. intros a b Ha Hb; simpl in *; exact (sub_mul N _ _ Ha Hb). Qed.
Next Obligation. intros a Ha; simpl in *; exact (sub_inv N _ Ha). Qed.
Next Obligation. intros t a Ha; simpl in *; exact (ns_conj N _ _ Ha). Qed.

(* S sits inside SN too, as a homomorphism of groups. *)
Program Definition S_into_SN :
  SubgroupGrp S ~{Grp}~> SubgroupGrp SubgroupProduct := {|
  grp_map := {| morphism := fun p : carrier (SubgroupGrp S) =>
     existT _ (`1 p)
       (existT _ (`1 p) (existT _ (grp_unit G)
          (pair (pair (`2 p) (sub_unit N))
                (symmetry (grp_mul_unit_r G (`1 p)))))) |}
|}.
Next Obligation. intros p q Hpq; exact Hpq. Qed.
Next Obligation. simpl; reflexivity. Qed.
Next Obligation. intros p q; simpl; reflexivity. Qed.

(* The composite S ↪ SN ↠ SN/N, whose kernel is S ∩ N and which is
   surjective. *)
Definition psi : SubgroupGrp S ~{Grp}~> QuotientGrp NinSN :=
  quot_proj NinSN ∘ S_into_SN.

(* ELEMENTWISE INPUT ONE: the kernel of ψ is S ∩ N -- as a biconditional
   on membership, not merely an inclusion. *)
Lemma psi_kernel_is_meet (p : carrier (SubgroupGrp S)) :
  sub_mem (KernelNS psi) p ↔ sub_mem N (`1 p).
Proof.
  split.
  - intro Hp; simpl in Hp.
    apply (sub_at N (a := grp_mul G (`1 p) (grp_inv G (grp_unit G)))).
    + rewrite (grp_inv_unit G); apply (grp_mul_unit_r G).
    + exact Hp.
  - intro Hp; simpl.
    apply (sub_at N (a := `1 p)).
    + rewrite (grp_inv_unit G); symmetry; apply (grp_mul_unit_r G).
    + exact Hp.
Qed.

(* ELEMENTWISE INPUT TWO: ψ is surjective.  Every member of SN is s·n for
   data s ∈ S, n ∈ N, and s·n is congruent to s modulo N because
   (s n) s⁻¹ lies in N -- one normality computation. *)
Lemma psi_surjective : GrpSurjective psi.
Proof.
  intro q.
  destruct (`2 q) as [s [n [[Hs Hn] Hq]]].
  exists (existT _ s Hs).
  simpl.
  unfold quot_rel; simpl.
  (* s * (s n)⁻¹ lies in N *)
  apply (sub_at N (a := grp_mul G (grp_mul G s (grp_inv G n)) (grp_inv G s))).
  - rewrite Hq.
    rewrite (grp_inv_mul G s n).
    rewrite (grp_mul_assoc G s (grp_inv G n) (grp_inv G s)).
    reflexivity.
  - exact (ns_conj N s _ (sub_inv N _ Hn)).
Qed.

(* Mac Lane §III.1 Exercise 4, second isomorphism theorem, as a corollary
   of the first: S/(S ∩ N) is S/ker ψ, which the first theorem identifies
   with im ψ, which surjectivity identifies with SN/N. *)
Definition second_isomorphism_theorem :
  QuotientGrp (KernelNS psi) ≅[Grp] QuotientGrp NinSN :=
  iso_compose (surjective_image_iso psi psi_surjective)
              (first_isomorphism_theorem psi).

(* S ∩ N, as a normal subgroup of S: membership in N, read on elements of
   S.  This is the literal left-hand side of the theorem, and the
   statement below is the literal one -- [second_isomorphism_theorem]
   above says S/ker ψ, which is the same group only because
   [psi_kernel_is_meet] says the two memberships coincide, and
   [quot_congr] is what turns that coincidence into an isomorphism. *)
Program Definition MeetNS : NormalSubgroup (SubgroupGrp S) := {|
  ns_sub := {| sub_mem := fun p : carrier (SubgroupGrp S) =>
                            sub_mem N (`1 p) |}
|}.
Next Obligation.
  intros a b Hab Ha; simpl in *; exact (sub_resp N _ _ Hab Ha).
Qed.
Next Obligation. simpl; exact (sub_unit N). Qed.
Next Obligation. intros a b Ha Hb; simpl in *; exact (sub_mul N _ _ Ha Hb). Qed.
Next Obligation. intros a Ha; simpl in *; exact (sub_inv N _ Ha). Qed.
Next Obligation. intros t a Ha; simpl in *; exact (ns_conj N _ _ Ha). Qed.

Definition second_isomorphism_theorem_literal :
  QuotientGrp MeetNS ≅[Grp] QuotientGrp NinSN :=
  iso_compose second_isomorphism_theorem
    (quot_congr MeetNS (KernelNS psi)
       (fun p Hp => snd (psi_kernel_is_meet p) Hp)
       (fun p Hp => fst (psi_kernel_is_meet p) Hp)).

End Second.

Arguments SubgroupProduct {G} S N.
Arguments MeetNS {G} S N.
Arguments NinSN {G} S N.
Arguments psi {G} S N.
Arguments second_isomorphism_theorem {G} S N.
Arguments second_isomorphism_theorem_literal {G} S N.

(** ** Non-vacuity at S3

    All three theorems above hold for every group, so nothing yet shows
    any of them is about a nondegenerate situation.  S3 with its rotation
    subgroup A3 (Instance/Grp/Quotient.v) supplies witnesses for each, and
    the degeneracies are excluded by proof: S3 is nonabelian, A3 is a
    PROPER NONTRIVIAL normal subgroup, and the quotient does not
    collapse. *)

(* The projection S3 ↠ S3/A3 has kernel A3, in both directions.  Together
   with [S3_mod_A3_not_collapsed] this makes the first isomorphism theorem
   at this map a statement about a two-element quotient of a six-element
   group, not about a degenerate one. *)
Lemma S3_proj_kernel_is_A3 (a : carrier S3) :
  sub_mem (KernelNS (quot_proj A3)) a ↔ sub_mem A3 a.
Proof. exact (quot_proj_kernel A3 a). Qed.

(* The first isomorphism theorem instantiated: S3/ker(p) ≅ im(p). *)
Definition S3_first_iso :
  QuotientGrp (KernelNS (quot_proj A3)) ≅[Grp] ImageGrp (quot_proj A3) :=
  first_isomorphism_theorem (quot_proj A3).

(* And it is nondegenerate: the image of the projection has two elements
   apart in its own setoid. *)
Theorem S3_first_iso_nondegenerate :
  grp_map (image_cores (quot_proj A3)) S3_s
    ≈ grp_map (image_cores (quot_proj A3)) s3_unit → False.
Proof. simpl; discriminate. Qed.

(* The third isomorphism theorem at M = trivial, N = A3: (S3/1)/(A3/1) ≅
   S3/A3.  The inclusion hypothesis is that everything ≈-equal to the unit
   is a rotation. *)
Lemma trivial_in_A3 (a : carrier S3) : sub_mem (TrivialNS S3) a → sub_mem A3 a.
Proof. intro Ha; simpl in *; now subst. Qed.

Definition S3_third_iso :
  QuotientGrp (NmodM (TrivialNS S3) A3 trivial_in_A3)
    ≅[Grp] QuotientGrp A3 :=
  third_isomorphism_theorem (TrivialNS S3) A3 trivial_in_A3.

(* Nondegenerate: the reflection is still apart from the unit on the left
   of the isomorphism. *)
Theorem S3_third_iso_nondegenerate :
  quot_rel (NmodM (TrivialNS S3) A3 trivial_in_A3) S3_s s3_unit → False.
Proof. simpl; discriminate. Qed.

(* The second isomorphism theorem is instantiated at S = the two-element
   reflection subgroup and N = A3.  That pair is nondegenerate in the way
   the theorem's hypotheses ask for: S is a plain [Subgroup] and is
   provably NOT normal (Instance/Grp/Quotient.v's [S3_refl_sub_not_normal]),
   so the statement is not being applied in a case where the
   plain-subgroup generality is idle. *)

Definition S3_second_iso :
  QuotientGrp (KernelNS (psi S3_refl_sub A3))
    ≅[Grp] QuotientGrp (NinSN S3_refl_sub A3) :=
  second_isomorphism_theorem S3_refl_sub A3.

(* Nondegenerate on the left: S ∩ N is trivial here (a rotation-free
   element that is a rotation is the unit), so S/(S ∩ N) still separates
   the reflection from the unit. *)
Theorem S3_second_iso_nondegenerate :
  quot_rel (KernelNS (psi S3_refl_sub A3))
    (existT _ S3_s (eq_refl : fst S3_s = rot0))
    (grp_unit (SubgroupGrp S3_refl_sub))
  → False.
Proof. simpl; discriminate. Qed.

(* The literal form, whose left-hand side is S/(S ∩ N) rather than
   S/ker ψ. *)
Definition S3_second_iso_literal :
  QuotientGrp (MeetNS S3_refl_sub A3)
    ≅[Grp] QuotientGrp (NinSN S3_refl_sub A3) :=
  second_isomorphism_theorem_literal S3_refl_sub A3.

Theorem S3_second_iso_literal_nondegenerate :
  quot_rel (MeetNS S3_refl_sub A3)
    (existT _ S3_s (eq_refl : fst S3_s = rot0))
    (grp_unit (SubgroupGrp S3_refl_sub))
  → False.
Proof. simpl; discriminate. Qed.

(* And nondegenerate on the RIGHT as well: the reflection, read as an
   element of SN via the decomposition s = s · e, stays apart from the
   unit in SN/N.  So both sides of the second isomorphism have at least
   two elements and the theorem is not identifying two collapsed
   groups. *)
Definition S3_s_in_SN : carrier (SubgroupGrp (SubgroupProduct S3_refl_sub A3)).
Proof.
  refine (existT _ S3_s _).
  exists S3_s, s3_unit.
  split; [ split | ].
  - exact (eq_refl : fst S3_s = rot0).
  - exact (eq_refl : snd s3_unit = false).
  - vm_compute; reflexivity.
Defined.

Theorem S3_second_iso_codomain_nondegenerate :
  quot_rel (NinSN S3_refl_sub A3) S3_s_in_SN
    (grp_unit (SubgroupGrp (SubgroupProduct S3_refl_sub A3)))
  → False.
Proof. simpl; discriminate. Qed.
