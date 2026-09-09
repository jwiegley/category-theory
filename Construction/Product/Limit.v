Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cartesian.Product.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Construction.Product.Indexed.
Require Import Category.Functor.Opposite.

Generalizable All Variables.

(** * Limits in a product of categories are computed componentwise *)

(* Book:  Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
          §V.2 Exercise 2, printed p. 114 (PDF p. 123) — maclane:V.2:ex2
   Book:  Riehl, "Category Theory in Context", 2nd ed., §3.4 Exercise
          3.4.v, printed p. 108 (PDF p. 128) — riehl:3.4:exv
   nLab:  https://ncatlab.org/nlab/show/product+category
   nLab:  https://ncatlab.org/nlab/show/complete+category

   Mac Lane's exercise: a product of complete categories is complete, and
   dually for cocompleteness — limits in [C ∏ D] are computed one factor
   at a time.  Riehl's exercise says the same thing more precisely, for a
   product [∏_{i ∈ I} C_i] of categories: (i) each projection preserves
   limits; (ii) the projections JOINTLY CREATE limits — if every component
   diagram has a limit then those limits are the components of a limit of
   the whole diagram; and (iii) a product of categories has a given class
   of limits or colimits if and only if each factor does.

   WHAT IS DELIVERED, AND AT WHICH STRENGTH.

   For the binary product [C ∏ D] of Construction/Product.v, over a
   diagram [K : J ⟶ C ∏ D]:

     - [prod_cone] pairs a cone over [Fst ◯ K] with a cone over [Snd ◯ K]
       into a cone over [K]; the apex is the pair of apexes and every leg
       the pair of legs, on the nose ([prod_cone_apex], [prod_cone_leg]).
     - [prod_IsLimitCone]: the pairing of two limiting cones is limiting,
       and its mediator IS the pair of the two mediators, on the nose
       ([prod_IsLimitCone_med]).  This is Riehl's clause (ii), existence
       half, and the engine of everything below.
     - [Fst_PreservesLimitCone], [Snd_PreservesLimitCone]: Riehl's clause
       (i), UNCONDITIONALLY — no limit is assumed to exist in either
       factor.  The argument splices a competing cone in [C] with the
       [D]-image of the given limiting cone, reads the [C]-component of
       the mediator, and gets uniqueness by observing that [(v, id)] is a
       mediator for the spliced cone.
     - [prod_reflect]: a cone over [K] both of whose projections are
       limiting is limiting — Riehl's clause (ii), reflection half — by
       transporting [prod_IsLimitCone] across the cone isomorphism
       [prod_cone_iso : prod_cone (FCone Fst N) (FCone Snd N) ≅ N], whose
       apex isomorphism is [(id, id)].
     - [Product_JointlyCreateLimit]: the two projections, packaged as the
       [bool]-indexed family [ProdProj], inhabit Structure/Limit/Creation.v's
       [JointlyCreateLimit] — the creation reading of the exercise.
     - [Product_Limit], [Product_Complete], [Product_Cocomplete] —
       Mac Lane's statement and its dual.  The dual costs NOTHING: the
       opposite of a product is the product of the opposites BY
       CONVERSION ([Product_Opposite], Construction/Product.v:185, closes
       by [reflexivity]), so [Product_Cocomplete] is [Product_Complete] at
       [C^op] and [D^op] applied to [K^op], with [Complete_op_of_Cocomplete]
       the one-line passage that [Cocomplete C] IS [Complete (C^op)] up to
       the definitional [(G^op)^op = G].
     - Riehl's clause (iii), the "only if" direction, under an EXPLICIT
       POINT of the other factor: [Product_Limit_Fst : Limit (pair_const d G)
       → Limit G] and [Product_Complete_Fst : Complete (C ∏ D) → D →
       Complete C], with the [Snd] mirrors.  The point is needed to form a
       diagram in the product from a diagram in one factor (the constant
       diagram at [d] fills the other slot), and it is what the exercise
       silently assumes: with [D] empty, [C ∏ D] is empty and has no
       terminal object, so it is not complete whatever [C] is.  Deriving
       the point from completeness itself would go through the limit of
       the empty diagram, i.e. through Instance/Zero.v's [_0], whose
       hom and proof universes are pinned to [Set]; the explicit hypothesis
       keeps the statement universe-clean.
     - The componentwise [Product_Terminal], [Product_Initial] and
       [Product_Cocartesian] the verifier's survey found missing beside the
       pre-existing [Product_Cartesian] (Structure/Cartesian/Product.v).
       The two duals are the primal instances at the opposite categories,
       again by the conversion [Product_Opposite]; they are plain
       [Definition]s rather than registered instances, since a
       resolution goal [Terminal ((C ∏ D)^op)] does not syntactically
       match [Terminal (?C ∏ ?D)].

   For the [I]-indexed product [PiCat D] of Construction/Product/Indexed.v:

     - [pi_cone], [pi_IsLimitCone] (mediator the family of mediators, on
       the nose), [pi_cone_iso], [pi_reflect], [PiCat_JointlyCreateLimit],
       [PiCat_Limit], [PiCat_Complete] — Riehl's clause (ii) at arbitrary
       index, and the completeness half of (iii).  [PiCat] is consumed as
       the tree's [I]-indexed product of categories; the QA note on the
       issue points at a [Cat_HasIndexedProducts] that does not yet exist,
       and nothing here depends on how that construction will relate to
       [PiCat].

   NOT DELIVERED, AND WHY.

     - Riehl's clause (i) at arbitrary index: that EACH [PiCat_Proj D i]
       preserves limits.  The binary argument splices a competing cone in
       one factor with the image of the limiting cone in the OTHER; at an
       arbitrary index type that splice must decide, for every [j], whether
       [j = i], and so needs decidable equality on [I] together with a
       transport of the spliced component — neither of which the binary
       case, where the two factors are told apart by the type checker,
       has to pay.  It is stated at [bool] (through [ProdProj]) and left
       open at a general [I].
     - [PiCat_Cocomplete].  [(PiCat D)^op] and [PiCat (fun i => (D i)^op)]
       agree on objects, homs, identities and composition but NOT as
       records: [PiCat]'s law fields are [Program] obligations, so the two
       are refused at [eq_refl] (pinned in Test/ProbeProductLimit418.v)
       and the free duality route of the binary case is unavailable.  A
       direct cocone development, or a transport of [Complete] along the
       identity-on-everything equivalence, would supply it; neither is
       attempted here.
     - Clause (iii)'s "only if" at arbitrary index, for the same
       point-of-the-other-factors reason as the binary case plus the
       splicing above.
     - Any comparison of [Product_Limit] at a discrete shape with
       [Product_Cartesian], or of the empty-shape limit with
       [Product_Terminal]: both would route through Instance/Discrete.v's
       universe-unannotated [DiscreteCat_Functor], which pins the ambient
       hom and proof universes to [Set] (the measurement recorded at
       Structure/Limit/Product/Finite.v and Functor/Hom/Limit.v).

   STRICTNESS, MEASURED STRICT FIRST.  Fifteen readbacks close by
   [eq_refl] and ship as [Example]s: the paired apex and legs, the
   [Fst]/[Snd] images of a paired cone leg by leg, the paired mediator,
   the pairing functor's object action, the recovered limit's apex, the
   terminal, initial and coproduct objects, and the family apex, projected
   legs, mediator and limit apex on the [PiCat] side.  The WHOLE-RECORD
   identifications do not — [FCone Fst (prod_cone N1 N2)] is not [N1]
   because the coherence field is a rebuilt proof and [≈] is Type-valued,
   and [prod_cone (FCone Fst N) (FCone Snd N)] is not [N] because a [prod]
   has no definitional eta — and are pinned as conversion negatives in
   Test/ProbeProductLimit418.v, with [prod_cone_iso] and [pi_cone_iso] the
   [≈]-level statements that do hold; on the [PiCat] side even the legs
   agree on the nose by function eta, which locates the whole-record
   refusal exactly in the coherence field.  Of the fifteen [Defined]
   tokens, exactly SIX are load-bearing — flipping any one of [prod_cone],
   [prod_IsLimitCone], [pair_const], [const_pair], [pi_cone] or
   [pi_IsLimitCone] alone to [Qed] breaks an [eq_refl] readback below it —
   and the other nine are [Defined] by the data convention only (measured
   by flipping each alone).

   UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK.  [Product] is fully
   polymorphic and [PiCat] bounds only by the index, but every constant
   here that mentions a composite [Fst ◯ K] or [PiCat_Proj D i ◯ K]
   identifies the SHAPE's hom level with every factor's and the product's,
   and hom with proof — [prod_cone]'s block carries [u0 = u2], [u0 = u4],
   [u0 = u6] over the binders [J : Category@{u u0 u0}],
   [C : Category@{u1 u2 u2}], [D : Category@{u3 u4 u4}] — and that is
   [Compose]'s doing, which is declared over three categories sharing ONE
   hom-and-proof level: at a shape whose homs are declared strictly below
   the factors' homs, the diagram [K : Ju ⟶ Cu ∏ Du] and a [Cone] over it
   are accepted while [Fst ◯ K] is refused (pinned in the probe with those
   two as controls).  The OBJECT universes of the shape, both factors and
   the product stay free of one another, only bounded.  The completeness
   statements additionally read [C] and [D] at one hom level in the
   BINDER with no block equation at all, [Complete]'s own shape; no
   word-bounded [Set] occurs in the binder or block of any of the 52
   constants.  All 52 — the 51 declared heads plus the single [Program]
   obligation [Product_Terminal_obligation_1], counted on [Print Module];
   the file declares no [Record]/[Class]/[Inductive], so there is no
   unlisted [Build_*] — are closed under the global context and gated in
   [make print-assumptions] fully qualified, as are the ten new constants
   of Structure/Limit/Creation.v; the transitive in-project closure is 29
   modules excluding this file (Construction/Product/Indexed alone is 18,
   Structure/Limit/Creation alone 24). *)

(** ** Cones over a diagram in a binary product *)

Section ProductCones.

Context {J C D : Category}.
Context (K : J ⟶ C ∏ D).

(* Pairing: a cone over each projected diagram assembles into a cone over
   [K], with the pair of apexes and the pairs of legs. *)

Definition prod_cone (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) : Cone K.
Proof.
  unshelve refine
    (@Build_Cone J (C ∏ D) K (vertex_obj[N1], vertex_obj[N2])
       (@Build_ACone J (C ∏ D) (vertex_obj[N1], vertex_obj[N2]) K
          (fun x => (cone_leg N1 x, cone_leg N2 x)) _)).
  intros x y f; split.
  - exact (cone_leg_coh N1 f).
  - exact (cone_leg_coh N2 f).
Defined.

Example prod_cone_apex (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) :
  vertex_obj[prod_cone N1 N2] = (vertex_obj[N1], vertex_obj[N2]) := eq_refl.

Example prod_cone_leg (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) (x : J) :
  cone_leg (prod_cone N1 N2) x = (cone_leg N1 x, cone_leg N2 x) := eq_refl.

(* Projecting the pairing returns each component leg by leg, on the nose;
   the whole cone records differ only in their rebuilt coherence proofs. *)

Example prod_cone_fst_leg (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) (x : J) :
  cone_leg (FCone Fst (prod_cone N1 N2)) x = cone_leg N1 x := eq_refl.

Example prod_cone_snd_leg (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) (x : J) :
  cone_leg (FCone Snd (prod_cone N1 N2)) x = cone_leg N2 x := eq_refl.

Definition prod_cone_fst_iso (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) :
  ConeIso (FCone Fst (prod_cone N1 N2)) N1.
Proof.
  exists iso_id.
  intro x; simpl; now rewrite id_right.
Defined.

Definition prod_cone_snd_iso (N1 : Cone (Fst ◯ K)) (N2 : Cone (Snd ◯ K)) :
  ConeIso (FCone Snd (prod_cone N1 N2)) N2.
Proof.
  exists iso_id.
  intro x; simpl; now rewrite id_right.
Defined.

(** ** The pairing of two limiting cones is limiting *)

(* The mediator out of a competing cone is the pair of the two mediators
   out of its projections; uniqueness is uniqueness in each factor. *)

Definition prod_IsLimitCone {N1 : Cone (Fst ◯ K)} {N2 : Cone (Snd ◯ K)}
  (H1 : IsLimitCone N1) (H2 : IsLimitCone N2) :
  IsLimitCone (prod_cone N1 N2).
Proof.
  intro M.
  unshelve refine
    {| unique_obj := (unique_obj (H1 (FCone Fst M)),
                      unique_obj (H2 (FCone Snd M))) |}.
  - intro x; split.
    + exact (unique_property (H1 (FCone Fst M)) x).
    + exact (unique_property (H2 (FCone Snd M)) x).
  - intros [v1 v2] Hv; split.
    + apply (uniqueness (H1 (FCone Fst M))).
      intro x; exact (fst (Hv x)).
    + apply (uniqueness (H2 (FCone Snd M))).
      intro x; exact (snd (Hv x)).
Defined.

Example prod_IsLimitCone_med {N1 : Cone (Fst ◯ K)} {N2 : Cone (Snd ◯ K)}
  (H1 : IsLimitCone N1) (H2 : IsLimitCone N2) (M : Cone K) :
  unique_obj (prod_IsLimitCone H1 H2 M)
    = (unique_obj (H1 (FCone Fst M)), unique_obj (H2 (FCone Snd M)))
  := eq_refl.

(** ** Each projection preserves limits, unconditionally (Riehl (i)) *)

(* Given a limiting cone [N] over [K] and a competing cone [M] over
   [Fst ◯ K], splice [M] with the [D]-image of [N] into a cone over [K];
   the [C]-component of its mediator into [N] is the wanted arrow.  For
   uniqueness, any [v] commuting with the [C]-legs makes [(v, id)] a
   mediator for the spliced cone, so [v] is that component. *)

Definition Fst_PreservesLimitCone : PreservesLimitCone K Fst.
Proof.
  intros N HN M.
  pose (P := prod_cone M (FCone Snd N)).
  unshelve refine {| unique_obj := fst (unique_obj (HN P)) |}.
  - intro x; exact (fst (unique_property (HN P) x)).
  - intros v Hv.
    refine (fst (uniqueness (HN P) (v, id) _)).
    intro x; split.
    + exact (Hv x).
    + simpl; now rewrite id_right.
Defined.

Definition Snd_PreservesLimitCone : PreservesLimitCone K Snd.
Proof.
  intros N HN M.
  pose (P := prod_cone (FCone Fst N) M).
  unshelve refine {| unique_obj := snd (unique_obj (HN P)) |}.
  - intro x; exact (snd (unique_property (HN P) x)).
  - intros v Hv.
    refine (snd (uniqueness (HN P) (id, v) _)).
    intro x; split.
    + simpl; now rewrite id_right.
    + exact (Hv x).
Defined.

(** ** A cone is limiting when both its projections are (Riehl (ii)) *)

(* A cone over [K] is isomorphic to the pairing of its two projections; the
   apex isomorphism is [(id, id) : (fst n, snd n) ≅ n], which is not the
   identity only because [prod] has no definitional eta. *)

Definition prod_cone_iso (N : Cone K) :
  ConeIso (prod_cone (FCone Fst N) (FCone Snd N)) N.
Proof.
  unshelve refine ((_; _)).
  - unshelve refine (@Build_Isomorphism (C ∏ D)
        (vertex_obj[prod_cone (FCone Fst N) (FCone Snd N)]) (vertex_obj[N])
        (id, id) (id, id) _ _).
    + split; simpl; apply id_left.
    + split; simpl; apply id_left.
  - intro x; split; simpl; apply id_right.
Defined.

Definition prod_reflect (N : Cone K)
  (H1 : IsLimitCone (FCone Fst N)) (H2 : IsLimitCone (FCone Snd N)) :
  IsLimitCone N :=
  limitcone_transport (prod_cone_iso N) (prod_IsLimitCone H1 H2).

(** ** The projections jointly create limits *)

(* The two projections as a [bool]-indexed family, so that the creation
   vocabulary of Structure/Limit/Creation.v applies verbatim. *)

Definition ProdFactor (b : bool) : Category := if b then C else D.

Definition ProdProj (b : bool) : C ∏ D ⟶ ProdFactor b :=
  match b as b0 return C ∏ D ⟶ ProdFactor b0 with
  | true  => Fst
  | false => Snd
  end.

Definition Product_JointlyCreateLimit : JointlyCreateLimit K ProdProj.
Proof.
  unshelve refine
    {| jcreates_lift := fun N HN => prod_cone (N true) (N false) |}.
  - intros N HN b.
    destruct b.
    + exact (prod_cone_fst_iso (N true) (N false)).
    + exact (prod_cone_snd_iso (N true) (N false)).
  - intros M H.
    exact (prod_reflect M (H true) (H false)).
Defined.

(** ** Limits of the projected diagrams give a limit of the diagram *)

Definition Product_Limit (L1 : Limit (Fst ◯ K)) (L2 : Limit (Snd ◯ K)) :
  Limit K :=
  limitcone_limit _ (prod_IsLimitCone (limit_limitcone L1) (limit_limitcone L2)).

Example Product_Limit_apex (L1 : Limit (Fst ◯ K)) (L2 : Limit (Snd ◯ K)) :
  vertex_obj[Product_Limit L1 L2] = (vertex_obj[L1], vertex_obj[L2])
  := eq_refl.

End ProductCones.

(** ** Mac Lane §V.2 Exercise 2: a product of complete categories is
       complete, and dually *)

Definition Product_Complete {C D : Category}
  (HC : @Complete C) (HD : @Complete D) : @Complete (C ∏ D) :=
  fun J K => Product_Limit K (HC J (Fst ◯ K)) (HD J (Snd ◯ K)).

(* [Cocomplete C] is [Complete (C^op)] up to the definitional involutions
   [(J^op)^op = J] and [(G^op)^op = G]; no cone is repackaged. *)

Definition Complete_op_of_Cocomplete {E : Category} (H : @Cocomplete E) :
  @Complete (E^op) :=
  fun J G => H (Opposite J) (Opposite_Functor G).

(* The dual, through the conversion [(C ∏ D)^op = C^op ∏ D^op]. *)

Definition Product_Cocomplete {C D : Category}
  (HC : @Cocomplete C) (HD : @Cocomplete D) : @Cocomplete (C ∏ D) :=
  fun J K =>
    @Product_Complete (Opposite C) (Opposite D)
      (Complete_op_of_Cocomplete HC) (Complete_op_of_Cocomplete HD)
      (Opposite J) (Opposite_Functor K).

(** ** The "only if" direction, at an explicit point of the other factor *)

Section ProductOnlyIf.

Context {C D : Category}.

(* The diagram in [C ∏ D] whose [C]-component is [G] and whose
   [D]-component is constant at [d]. *)

Definition pair_const (d : D) {J : Category} (G : J ⟶ C) : J ⟶ C ∏ D.
Proof.
  unshelve refine
    (@Build_Functor J (C ∏ D) (fun x => (G x, d))
       (fun _ _ f => (fmap[G] f, id)) _ _ _).
  - repeat intro; split; simpl; [ now apply fmap_respects | reflexivity ].
  - intro x; split; simpl; [ apply fmap_id | reflexivity ].
  - intros x y z f g; split; simpl;
      [ apply fmap_comp | symmetry; apply id_left ].
Defined.

Definition const_pair (c : C) {J : Category} (G : J ⟶ D) : J ⟶ C ∏ D.
Proof.
  unshelve refine
    (@Build_Functor J (C ∏ D) (fun x => (c, G x))
       (fun _ _ f => (id, fmap[G] f)) _ _ _).
  - repeat intro; split; simpl; [ reflexivity | now apply fmap_respects ].
  - intro x; split; simpl; [ reflexivity | apply fmap_id ].
  - intros x y z f g; split; simpl;
      [ symmetry; apply id_left | apply fmap_comp ].
Defined.

Example pair_const_obj (d : D) {J : Category} (G : J ⟶ C) (x : J) :
  fobj[pair_const d G] x = (G x, d) := eq_refl.

(* A cone over [Fst ◯ pair_const d G] IS a cone over [G]: the two functors
   agree on objects and arrows by conversion, so the repackaging carries
   the same apex and the same legs, and the two readings of "limiting"
   are convertible. *)

Definition repack_fst {d : D} {J : Category} {G : J ⟶ C}
  (N : Cone (Fst ◯ pair_const d G)) : Cone G :=
  @Build_Cone J C G (vertex_obj[N])
    (@Build_ACone J C (vertex_obj[N]) G (fun x => cone_leg N x)
       (fun x y f => cone_leg_coh N f)).

Definition repack_fst_inv {d : D} {J : Category} {G : J ⟶ C}
  (M : Cone G) : Cone (Fst ◯ pair_const d G) :=
  @Build_Cone J C (Fst ◯ pair_const d G) (vertex_obj[M])
    (@Build_ACone J C (vertex_obj[M]) (Fst ◯ pair_const d G)
       (fun x => cone_leg M x) (fun x y f => cone_leg_coh M f)).

Definition Product_Limit_Fst (d : D) {J : Category} (G : J ⟶ C)
  (L : Limit (pair_const d G)) : Limit G :=
  limitcone_limit (repack_fst (FCone Fst (@limit_cone _ _ _ L)))
    (fun M => Fst_PreservesLimitCone (pair_const d G)
                (@limit_cone _ _ _ L) (limit_limitcone L) (repack_fst_inv M)).

Definition repack_snd {c : C} {J : Category} {G : J ⟶ D}
  (N : Cone (Snd ◯ const_pair c G)) : Cone G :=
  @Build_Cone J D G (vertex_obj[N])
    (@Build_ACone J D (vertex_obj[N]) G (fun x => cone_leg N x)
       (fun x y f => cone_leg_coh N f)).

Definition repack_snd_inv {c : C} {J : Category} {G : J ⟶ D}
  (M : Cone G) : Cone (Snd ◯ const_pair c G) :=
  @Build_Cone J D (Snd ◯ const_pair c G) (vertex_obj[M])
    (@Build_ACone J D (vertex_obj[M]) (Snd ◯ const_pair c G)
       (fun x => cone_leg M x) (fun x y f => cone_leg_coh M f)).

Definition Product_Limit_Snd (c : C) {J : Category} (G : J ⟶ D)
  (L : Limit (const_pair c G)) : Limit G :=
  limitcone_limit (repack_snd (FCone Snd (@limit_cone _ _ _ L)))
    (fun M => Snd_PreservesLimitCone (const_pair c G)
                (@limit_cone _ _ _ L) (limit_limitcone L) (repack_snd_inv M)).

Definition Product_Complete_Fst (H : @Complete (C ∏ D)) (d : D) :
  @Complete C :=
  fun J G => Product_Limit_Fst d G (H J (pair_const d G)).

Definition Product_Complete_Snd (H : @Complete (C ∏ D)) (c : C) :
  @Complete D :=
  fun J G => Product_Limit_Snd c G (H J (const_pair c G)).

(* The recovered limit sits on the [C]-component of the product limit's
   apex, on the nose. *)

Example Product_Limit_Fst_apex (d : D) {J : Category} (G : J ⟶ C)
  (L : Limit (pair_const d G)) :
  vertex_obj[Product_Limit_Fst d G L] = fst (vertex_obj[L]) := eq_refl.

End ProductOnlyIf.

(** ** Componentwise terminal and initial objects, and coproducts *)

Section ProductTerminal.

Context {C D : Category}.

#[export]
Program Instance Product_Terminal `{@Terminal C} `{@Terminal D} :
  @Terminal (C ∏ D) := {
  terminal_obj := (1, 1);
  one := fun _ => (one, one)
}.
Next Obligation. split; apply one_unique. Qed.

Example Product_Terminal_obj `{@Terminal C} `{@Terminal D} :
  @terminal_obj (C ∏ D) Product_Terminal = (@terminal_obj C _, @terminal_obj D _)
  := eq_refl.

End ProductTerminal.

(* The duals are the primal instances at the opposite categories, through
   the conversion [Product_Opposite]; not registered for resolution. *)

Definition Product_Initial {C D : Category}
  (HC : @Initial C) (HD : @Initial D) : @Initial (C ∏ D) :=
  @Product_Terminal (C^op) (D^op) HC HD.

Definition Product_Cocartesian {C D : Category}
  (HC : @Cocartesian C) (HD : @Cocartesian D) : @Cocartesian (C ∏ D) :=
  @Product_Cartesian (C^op) (D^op) HC HD.

Example Product_Initial_obj {C D : Category}
  (HC : @Initial C) (HD : @Initial D) :
  @initial_obj (C ∏ D) (Product_Initial HC HD)
    = (@initial_obj C HC, @initial_obj D HD)
  := eq_refl.

Example Product_Cocartesian_obj {C D : Category}
  (HC : @Cocartesian C) (HD : @Cocartesian D) (x y : C ∏ D) :
  @Coprod (C ∏ D) (Product_Cocartesian HC HD) x y
    = (@Coprod C HC (fst x) (fst y), @Coprod D HD (snd x) (snd y))
  := eq_refl.

(** ** The set-indexed product: Riehl's clause (ii) at arbitrary index *)

Section PiCatCones.

Context {I : Type} {D : I → Category} {J : Category}.
Context (K : J ⟶ PiCat D).

Definition pi_cone (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K)) : Cone K.
Proof.
  unshelve refine
    (@Build_Cone J (PiCat D) K (fun i => vertex_obj[N i])
       (@Build_ACone J (PiCat D) (fun i => vertex_obj[N i]) K
          (fun x i => cone_leg (N i) x) _)).
  intros x y f i.
  exact (cone_leg_coh (N i) f).
Defined.

Example pi_cone_apex (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K)) :
  vertex_obj[pi_cone N] = fun i => vertex_obj[N i] := eq_refl.

Example pi_cone_proj_leg (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K))
  (i : I) (x : J) :
  cone_leg (FCone (PiCat_Proj D i) (pi_cone N)) x = cone_leg (N i) x
  := eq_refl.

Definition pi_cone_proj_iso (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K)) (i : I) :
  ConeIso (FCone (PiCat_Proj D i) (pi_cone N)) (N i).
Proof.
  exists iso_id.
  intro x; simpl; now rewrite id_right.
Defined.

Definition pi_IsLimitCone (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K))
  (HN : ∀ i : I, IsLimitCone (N i)) : IsLimitCone (pi_cone N).
Proof.
  intro M.
  unshelve refine
    {| unique_obj := fun i => unique_obj (HN i (FCone (PiCat_Proj D i) M)) |}.
  - intros x i.
    exact (unique_property (HN i (FCone (PiCat_Proj D i) M)) x).
  - intros v Hv i.
    apply (uniqueness (HN i (FCone (PiCat_Proj D i) M))).
    intro x; exact (Hv x i).
Defined.

Example pi_IsLimitCone_med (N : ∀ i : I, Cone (PiCat_Proj D i ◯ K))
  (HN : ∀ i : I, IsLimitCone (N i)) (M : Cone K) :
  unique_obj (pi_IsLimitCone N HN M)
    = fun i => unique_obj (HN i (FCone (PiCat_Proj D i) M))
  := eq_refl.

(* Here the apex isomorphism IS [iso_id]: a function has definitional eta
   where a pair does not, so the two apexes are the same object. *)

Definition pi_cone_iso (N : Cone K) :
  ConeIso (pi_cone (fun i => FCone (PiCat_Proj D i) N)) N.
Proof.
  exists iso_id.
  intros x i; simpl; apply id_right.
Defined.

Definition pi_reflect (N : Cone K)
  (H : ∀ i : I, IsLimitCone (FCone (PiCat_Proj D i) N)) : IsLimitCone N :=
  limitcone_transport (pi_cone_iso N)
    (pi_IsLimitCone (fun i => FCone (PiCat_Proj D i) N) H).

Definition PiCat_JointlyCreateLimit : JointlyCreateLimit K (PiCat_Proj D).
Proof.
  unshelve refine {| jcreates_lift := fun N HN => pi_cone N |}.
  - intros N HN i; exact (pi_cone_proj_iso N i).
  - exact pi_reflect.
Defined.

Definition PiCat_Limit (L : ∀ i : I, Limit (PiCat_Proj D i ◯ K)) : Limit K :=
  limitcone_limit _
    (pi_IsLimitCone (fun i => @limit_cone _ _ _ (L i))
       (fun i => limit_limitcone (L i))).

Example PiCat_Limit_apex (L : ∀ i : I, Limit (PiCat_Proj D i ◯ K)) :
  vertex_obj[PiCat_Limit L] = fun i => vertex_obj[L i] := eq_refl.

End PiCatCones.

Definition PiCat_Complete {I : Type} {D : I → Category}
  (HD : ∀ i : I, @Complete (D i)) : @Complete (PiCat D) :=
  fun J K => PiCat_Limit K (fun i => HD i J (PiCat_Proj D i ◯ K)).
