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

Generalizable All Variables.

(** * The hom-set form of the indexed product and coproduct *)

(* nLab:      https://ncatlab.org/nlab/show/product
   nLab:      https://ncatlab.org/nlab/show/coproduct
   Wikipedia: https://en.wikipedia.org/wiki/Coproduct

   Sources, cited BY LOCATION; the descriptions are transcribed from the
   catalog entries of issue #320 rather than from the printed books:

     - Mac Lane, "Categories for the Working Mathematician", 2nd ed.
       (Springer GTM 5), section III.3, printed p. 64 (PDF p. 73), item
       [maclane:III.3:def2]: for a set X read as a discrete category, the
       X-fold coproduct of a family {a_x} is an object with injections
       through which every family of arrows out factors uniquely --
       "equivalently, a bijection C(⊔_x a_x, c) ≅ ∏_x C(a_x, c) natural in
       c".  It is that "equivalently" which this file supplies.
     - Riehl, "Category Theory in Context", 2nd ed., section 3.1, printed
       pp. 90-91 (PDF pp. 110-111), item [riehl:3.1:remark27], clauses (i)
       and (ii): morphisms out of an I-indexed coproduct correspond
       naturally and bijectively to I-indexed families,
       C(∐_i A_i, X) ≅ ∏_i C(A_i, X), the i-th component being restriction
       along the inclusion; dually C(X, ∏_j B_j) ≅ ∏_j C(X, B_j).
       Clause (iii), the (I × J)-matrix, is issue #336 and is NOT here.

   WHAT WAS ALREADY IN THE TREE, AND WHAT THIS FILE ADDS

   The two universal properties themselves are Structure/Limit/Product.v
   ([IsIndexedProduct]:51, [iprod]:93, [HasIndexedProducts]:128) and
   Structure/Limit/Coproduct.v (its definitional dual at [C^op]), and both
   are inhabited at [Sets] (Instance/Sets/Products.v:302, :387).  What
   neither file states is the hom-set bijection: as of this commit,

     rg -n '≅\[Sets\]|@Isomorphism|hom_iso' \
        Structure/Limit/Product.v Structure/Limit/Coproduct.v

   returns nothing, and so does [rg -c 'Isomorphism'] over the same two
   files.  [iprod_desc] and [icoprod_desc] give UNIQUE EXISTENCE -- ∃! u,
   ∀ a, proj a ∘ u ≈ pi a -- with no naturality anywhere.  This file
   upgrades both to an [Isomorphism] in a functor category over [Sets],
   natural in the varying object, and relates each back to the pre-existing
   [∃!] accessor so the two presentations cannot drift.

   WHY A NEW FILE RATHER THAN AN EXTENSION IN PLACE

   Not taste: a cycle.  The right-hand side ∏_a C(c, f a) is the
   dependent-function setoid [Sets_iprod_obj], and the statement lives in
   [Sets]; but Instance/Sets/Products.v already Requires
   Structure/Limit/Product.v AND Structure/Limit/Coproduct.v, so neither of
   those two can Require it back.  Structure/Limit/Weighted.v is the
   in-tree precedent for a Structure/Limit/ file that Requires
   Instance/Sets and builds a [J ⟶ Sets] functor out of hom-setoids.

   WHICH DISCRETE-DIAGRAM SHAPE THIS IS STATED AGAINST -- NEITHER

   Structure/Limit/Coproduct.v's header records a real obstruction: its
   [icoprod] reads a [Limit] of the discrete diagram taken IN [C^op],
   namely [Limit (@DiscreteCat_Functor A (C^op) f)], and NOT a [Colimit] in
   the sense of Structure/Limit.v:158, which sets [Colimit F := Limit (F^op)]
   and so indexes over [(DiscreteCat A)^op]; the two categories are not
   identified, and no translation between them exists in the tree.

   This file states everything against the ELEMENTARY records
   [IsIndexedProduct] and [IsIndexedCoproduct], which mention no discrete
   diagram at all, so the question does not arise and no translation is
   needed or supplied.  That choice is not merely evasive -- it is what
   makes the result compose with every presentation the tree carries
   ACCESSORS for, and all four compositions are exhibited rather than
   asserted:

     [limit_hom_iso]             through [limit_is_indexed_product]
     [colimit_hom_iso]           through [colimit_is_indexed_coproduct]
     [indexed_product_hom_iso]   through [indexed_product_ump]   (the class)
     [indexed_coproduct_hom_iso] through [indexed_coproduct_ump] (the class)

   Read "every presentation the tree carries accessors for" strictly: it is
   NOT every expressible shape.  [Colimit (@DiscreteCat_Functor A C f)] --
   the form Structure/Limit.v:158 defines, indexing over [(DiscreteCat A)^op]
   -- is formable and is a genuine in-tree presentation, and
   [colimit_hom_iso] does NOT accept it: a term of that type is rejected
   against the expected [Limit (@DiscreteCat_Functor A (C^op) f)].  That is
   the same non-identification recorded above and in NOT DELIVERED below, and
   it is the one shape these four compositions leave out of reach.  Nothing
   here narrows it; the translation remains open.

   THE COPRODUCT SIDE COSTS NOTHING, AND THAT IS THE POINT OF THE SYMMETRY

   Every coproduct-side constant is its product-side counterpart applied at
   [C^op], supplied by [:=] with no tactic and no obligation -- the
   discipline Structure/Limit/Coproduct.v already follows.  Two conversions
   make it work and both were measured outside the tree, then relied on
   here: [(C^op)^op = C] and [@Curried_CoHom (C^op) p = @Curried_Hom C p],
   each by [eq_refl].  (They are not landed as [Example]s, and the reason is
   NOT the [make todo] scan: that scan greps for a fixed list of
   proof-hole and TODO keywords, none of which a positive [eq_refl]
   contains, so landing them would cost nothing there.  They are guarded
   implicitly instead, by the coproduct section below typechecking at all.
   Do not quote that keyword list in a source file: one of its entries is
   also what the separate proof-hole gate counts, so quoting it raises that
   count and breaks the build.  Note too that the two gates use DIFFERENT
   patterns -- the Makefile's is word-bounded and lefthook's is not, so
   lefthook also counts that keyword as a substring of longer words.  Both
   were measured the hard way, in that order.)  The second holds because [Curried_CoHom D] IS
   [Curried_Hom D^op] by Definition (Functor/Hom.v:146).  So the two clauses
   of Riehl's Remark 3.1.27 are symmetric BY CONSTRUCTION here, not by a
   parallel development; [icoprod_hom_functor_is_op] records the reading.

   WHAT IS PROVED, AND AT WHICH STRENGTH

   For an arbitrary family [f : A → C] and an arbitrary candidate cone:

     [iprod_hom_functor f : C^op ⟶ Sets]   is  c ↦ ∏_a C(c, f a)
     [icoprod_hom_functor f : C ⟶ Sets]    is  c ↦ ∏_a C(f a, c)

   and [iprod_hom_transform f q proj] is the comparison natural
   transformation [Hom ─,q] ⟹ ∏_a [Hom ─,f a], u ↦ (proj a ∘ u)_a.  It is
   defined for ANY family [proj], with NO universal property assumed: its
   naturality is associativity and nothing else.  The content is therefore
   entirely in INVERTIBILITY, and that is delivered as a biconditional --

     [iprod_iff_hom_iso]   : IsIndexedProduct f q proj
                             ↔ IsIsomorphism (iprod_hom_transform f q proj)
     [icoprod_iff_hom_iso] : the same at [C^op]

   -- whose two legs are [iprod_hom_iso] (which packages the isomorphism in
   [[C^op, Sets]] proper) and [iprod_of_hom_iso].  The [↔] is [Lib]'s
   Type-valued [iffT], and the pairing is transparent, so projecting it
   returns the named leg by conversion -- machine-checked by
   [iprod_iff_hom_iso_fst]/[_snd] and their coproduct duals, at Leibniz [=].

   STRICT-FIRST MEASUREMENT.  The following hold at Leibniz [=] by
   [eq_refl], and are recorded as [Example]s so the claims are
   machine-checked rather than inferred:

     - the forward leg of the isomorphism IS the comparison map, and the
       backward leg IS [iprod_hom_inverse] ([iprod_hom_iso_to],
       [iprod_hom_iso_from], and [icoprod_hom_iso_to]);
     - the backward leg's VALUE is the mediator named by the pre-existing
       [∃!] accessor -- [iprod_hom_iso_from_is_desc] and
       [icoprod_hom_iso_from_is_desc] are the "does not drift" guarantee at
       its strongest available form;
     - the forward leg computes to restriction along the projections
       ([iprod_hom_transform_computes]) and, on the coproduct side, to
       [u ∘ inj a] ([icoprod_hom_transform_computes]);
     - the right-hand side IS the tree's own indexed product read in [Sets]
       ([iprod_hom_functor_is_indexed_product] and its dual);
     - at [Sets] the backward leg computes to the tupling and case maps of
       Instance/Sets/Products.v ([Sets_iprod_hom_from_computes],
       [Sets_icoprod_hom_from_computes]), and the class-derived isomorphism
       is the SAME TERM as the one read straight off [Sets_IsIndexedProduct]
       ([Sets_iprod_hom_iso_is_class] and its dual).

   TWO STRICT ATTEMPTS WERE MADE AND REFUTED, both pinned as [Fail]
   probes in Test/ProbeIndexedHom.v with positive controls: the ROUND TRIP
   does not compute, neither at an abstract product nor at the concrete
   [Sets] one.  Recovering [u] from the family it restricts to is exactly
   the uniqueness clause of [iprod_desc], a [≈]-level fact.  At [Sets] the
   diagnosis is sharper and is itself pinned by a control: [SetoidMorphism]
   has primitive projections with eta, the [morphism] fields DO agree on the
   nose, and what differs is the [proper_morphism] certificate, which the
   tupling rebuilds as its own obligation.

   UNIVERSES, MEASURED IN THE CONSTRAINT BLOCKS

   Reproduce with [Set Printing Universes.] and [About].  Reading the
   binder alone gets this wrong; the constraint block is the authority.

   [iprod_hom_functor@{u u0 u1 u2 u3 u4}] takes [C : Category@{u3 u4 u4}]
   and [A : Type@{u}] with [u <= u2] and [u4 <= u2] -- the index universe
   and [C]'s hom universe are each bounded by the TARGET [Sets]' carrier
   universe [u2] and are unrelated to each other.  So the target functor
   alone tolerates an index strictly larger than [C]'s homs.

   The COMPARISON MAP does not, and the cause is worth knowing.  Its source
   is the hom-functor, whose objects ARE the hom-setoids of [C]; a
   [SetoidObject] carries its [Setoid] as a field, and neither record is
   cumulative here (measured: lifting a [Setoid@{a a}] to a [Setoid@{b b}]
   with [a < b] is rejected, and likewise for [SetoidObject]), so the [Sets]
   in which the comparison lives has its carrier universe forced EQUAL to
   [C]'s hom universe rather than merely above it -- an annotated variant
   declaring the two apart was attempted and reports "Cannot enforce
   uh = us because uh < us".  The index bound follows.  This is pinned in Test/ProbeIndexedHom.v
   as a formability negative with the exact message "Cannot enforce
   ua <= uh because uh < ua", against two controls showing that neither
   functor alone is what gets rejected.  In practice the bound costs
   nothing that cumulativity does not already give: an index at or below
   [C]'s hom universe lifts, and this is the same smallness side condition
   Instance/Sets/Products.v's header analyses at [Sets].

   The two LIMIT-shaped bridges carry [{A : Set}], and that binder is a
   COMBINATION of two facts rather than one, which the probe file
   separates.  [Structure/Limit/Product.v]'s [iprod] is over
   [C : Category@{u Set Set}] -- [DiscreteCat]'s hom-setoid is strict
   equality -- with its own index universe FREE; the probe's controls show
   [Limit (DiscreteCat_Functor f)] and [iprod f L] are both formable over
   such a [C] at an index strictly above [Set].  Adding this file's bound at
   [C]'s hom universe, which is [Set] there, is what cuts the index to
   [Set].  The class-shaped bridges [indexed_product_hom_iso] and
   [indexed_coproduct_hom_iso] carry no such pin, mentioning no discrete
   diagram.

   NON-VACUITY, IN BOTH DIRECTIONS

   The conditional is instantiated at the tree's only inhabitants:
   [Sets_iprod_hom_iso] and [Sets_icoprod_hom_iso] over
   Instance/Sets/Products.v, with both backward legs computing.  And the
   INVERTIBILITY hypothesis is proved not to be vacuous, which the
   instantiations alone would not show: [Sets_bad_not_iprod] and
   [Sets_bad_not_icoprod] exhibit a candidate cone in [Sets] -- the
   two-element setoid with the constantly-true map for its single
   projection -- whose comparison map is not invertible, and conclude
   through the biconditional's forward leg that it is not an indexed
   (co)product.  So [iprod_of_hom_iso]'s hypothesis genuinely selects.

   WHAT IS NOT DELIVERED

   No (I × J)-matrix form (Riehl clause (iii), issue #336).  No translation
   between [(DiscreteCat A)^op] and [DiscreteCat A]: the question is
   side-stepped rather than settled, exactly as before this file.  No
   naturality in the FAMILY [f] or in the index [A], only in the varying
   object.  No [Representable] instance for either functor, and no
   universal-element packaging.  Nothing is claimed about a category
   without the relevant (co)product: the comparison map exists there, but
   this file exhibits no such category.

   STATUS: axiom-free.  All 59 constants -- 47 named plus 12 [Program]
   obligations, enumerated by [Print Module] per the docs/AXIOMS.md
   methodology -- report "Closed under the global context"; the Makefile's
   [print-assumptions] target audits the headline ones.  Nothing here
   appeals to funext, choice, or UIP.  The concrete [Sets] witness of a
   small coproduct is issue #254's, in Instance/Sets/Products.v, and is not
   duplicated; issue #729 consumes Structure/Limit/Coproduct.v and is not
   affected by this file. *)

#[local] Obligation Tactic := idtac.

(** ** The indexed hom presheaf [c ↦ ∏ₐ C(c, f a)] *)

Definition iprod_hom_fam {C : Category} {A : Type} (f : A → C) (c : C) :
  A → obj[Sets] :=
  fun a => {| carrier := @hom C c (f a); is_setoid := @homset C c (f a) |}.

Program Definition iprod_hom_functor {C : Category} {A : Type} (f : A → C) :
  C^op ⟶ Sets := {|
  fobj := fun c => Sets_iprod_obj (iprod_hom_fam f c);
  fmap := fun c c' (h : c ~{C^op}~> c') =>
            {| morphism := fun fam => fun a : A => fam a ∘[C] h |}
|}.
Next Obligation.
  intros C A f c c' h fam fam' Hfam a; simpl in *; now rewrite (Hfam a).
Qed.
Next Obligation.
  intros C A f c c' h h' Hh fam a; simpl in *; now rewrite Hh.
Qed.
Next Obligation.
  intros C A f c fam a; simpl; apply id_right.
Qed.
Next Obligation.
  intros C A f x y z h k fam a; simpl; apply comp_assoc.
Qed.

(** ** The comparison map: restriction along the projections *)

Program Definition iprod_hom_transform {C : Category} {A : Type} (f : A → C)
  (q : C) (proj : ∀ a : A, q ~> f a) :
  @Transform (C^op) Sets (@Curried_CoHom C q) (iprod_hom_functor f) := {|
  transform := fun c => {| morphism := fun u => fun a : A => proj a ∘ u |}
|}.
Next Obligation.
  intros C A f q proj c u v Huv a; simpl in *; now rewrite Huv.
Qed.
Next Obligation.
  intros C A f q proj x y h u a; simpl; apply comp_assoc_sym.
Qed.
Next Obligation.
  intros C A f q proj x y h u a; simpl; apply comp_assoc.
Qed.

(** ** The inverse, supplied by the universal property *)

Program Definition iprod_hom_inverse {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj) :
  @Transform (C^op) Sets (iprod_hom_functor f) (@Curried_CoHom C q) := {|
  transform := fun c => {| morphism := fun fam => unique_obj (iprod_desc H fam) |}
|}.
Next Obligation.
  intros C A f q proj H c fam fam' Hfam; simpl in *.
  symmetry.
  apply (uniqueness (iprod_desc H fam')).
  intros a.
  rewrite (unique_property (iprod_desc H fam) a).
  now rewrite (Hfam a).
Qed.
Next Obligation.
  intros C A f q proj H x y h fam; simpl in *.
  symmetry.
  apply (uniqueness (iprod_desc H (fun a => fam a ∘ h))).
  intros a.
  rewrite comp_assoc.
  now rewrite (unique_property (iprod_desc H fam) a).
Qed.
Next Obligation.
  intros C A f q proj H x y h fam; simpl in *.
  apply (uniqueness (iprod_desc H (fun a => fam a ∘ h))).
  intros a.
  rewrite comp_assoc.
  now rewrite (unique_property (iprod_desc H fam) a).
Qed.

Program Definition iprod_hom_iso {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj) :
  @Isomorphism ([C^op, Sets]) (@Curried_CoHom C q) (iprod_hom_functor f) := {|
  to   := iprod_hom_transform f q proj;
  from := iprod_hom_inverse H
|}.
Next Obligation.
  intros C A f q proj H c fam a; simpl.
  rewrite id_right.
  apply (unique_property (iprod_desc H fam) a).
Qed.
Next Obligation.
  intros C A f q proj H c u; simpl.
  rewrite id_right.
  apply (uniqueness (iprod_desc H (fun a => proj a ∘ u))).
  intros a; reflexivity.
Qed.

(** ** The converse: an invertible comparison map is a universal property *)

Definition iprod_of_hom_iso {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a}
  (I : @IsIsomorphism ([C^op, Sets]) (@Curried_CoHom C q)
                      (iprod_hom_functor f) (iprod_hom_transform f q proj)) :
  IsIndexedProduct f q proj.
Proof.
  apply (@Build_IsIndexedProduct C A f q proj).
  intros c pi.
  unshelve eapply Build_Unique.
  - exact (transform (@two_sided_inverse _ _ _ _ I) c pi).
  - intros a.
    pose proof (@is_right_inverse _ _ _ _ I c pi a) as Hr; simpl in Hr.
    now rewrite id_right in Hr.
  - intros v Hv.
    pose proof (@is_left_inverse _ _ _ _ I c v) as Hl; simpl in Hl.
    rewrite id_right in Hl.
    transitivity (transform (@two_sided_inverse _ _ _ _ I) c
                    (fun a => proj a ∘ v)).
    + apply (proper_morphism (transform (@two_sided_inverse _ _ _ _ I) c)).
      intros a; symmetry; exact (Hv a).
    + exact Hl.
Defined.

Definition iprod_hom_IsIsomorphism {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj) :
  @IsIsomorphism ([C^op, Sets]) (@Curried_CoHom C q) (iprod_hom_functor f)
                 (iprod_hom_transform f q proj).
Proof.
  exact (@Build_IsIsomorphism ([C^op, Sets])
           (@Curried_CoHom C q) (iprod_hom_functor f)
           (iprod_hom_transform f q proj) (iprod_hom_inverse H)
           (iso_to_from (iprod_hom_iso H)) (iso_from_to (iprod_hom_iso H))).
Defined.

Definition iprod_iff_hom_iso {C : Category} {A : Type} (f : A → C)
  (q : C) (proj : ∀ a : A, q ~> f a) :
  IsIndexedProduct f q proj ↔
  @IsIsomorphism ([C^op, Sets]) (@Curried_CoHom C q) (iprod_hom_functor f)
                 (iprod_hom_transform f q proj) :=
  (fun H => iprod_hom_IsIsomorphism H, fun I => iprod_of_hom_iso I).

(** ** Strict readings *)

Example iprod_hom_transform_computes {C : Category} {A : Type} (f : A → C)
  (q : C) (proj : ∀ a : A, q ~> f a) (c : C) (u : c ~> q) :
  transform (iprod_hom_transform f q proj) c u = fun a : A => proj a ∘ u
  := eq_refl.

Example iprod_hom_iso_to {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj) :
  to (iprod_hom_iso H) = iprod_hom_transform f q proj := eq_refl.

Example iprod_hom_iso_from {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj) :
  from (iprod_hom_iso H) = iprod_hom_inverse H := eq_refl.

Example iprod_hom_iso_from_is_desc {C : Category} {A : Type} {f : A → C}
  {q : C} {proj : ∀ a : A, q ~> f a} (H : IsIndexedProduct f q proj)
  (c : C) (fam : ∀ a : A, c ~> f a) :
  transform (from (iprod_hom_iso H)) c fam = unique_obj (iprod_desc H fam)
  := eq_refl.

(* The biconditional's pairing is transparent, so projecting it returns the
   named leg by conversion rather than merely proving the same thing. *)

Example iprod_iff_hom_iso_fst {C : Category} {A : Type} (f : A → C)
  (q : C) (proj : ∀ a : A, q ~> f a) :
  fst (iprod_iff_hom_iso f q proj)
  = fun H => @iprod_hom_IsIsomorphism C A f q proj H := eq_refl.

Example iprod_iff_hom_iso_snd {C : Category} {A : Type} (f : A → C)
  (q : C) (proj : ∀ a : A, q ~> f a) :
  snd (iprod_iff_hom_iso f q proj)
  = fun I => @iprod_of_hom_iso C A f q proj I := eq_refl.

(** ** The coproduct side, by definition at [C^op] *)

(* Every constant in this section is its product counterpart applied at
   [C^op], supplied by [:=] with no tactic; [icoprod_hom_functor_is_op]
   records that reading by [eq_refl]. *)

Definition icoprod_hom_fam {C : Category} {A : Type} (f : A → C) (c : C) :
  A → obj[Sets] :=
  @iprod_hom_fam (C^op) A f c.

Definition icoprod_hom_functor {C : Category} {A : Type} (f : A → C) :
  C ⟶ Sets :=
  @iprod_hom_functor (C^op) A f.

Definition icoprod_hom_transform {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) :
  @Transform C Sets (@Curried_Hom C p) (icoprod_hom_functor f) :=
  @iprod_hom_transform (C^op) A f p inj.

Definition icoprod_hom_inverse {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj) :
  @Transform C Sets (icoprod_hom_functor f) (@Curried_Hom C p) :=
  @iprod_hom_inverse (C^op) A f p inj H.

Definition icoprod_hom_iso {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj) :
  @Isomorphism ([C, Sets]) (@Curried_Hom C p) (icoprod_hom_functor f) :=
  @iprod_hom_iso (C^op) A f p inj H.

Definition icoprod_hom_IsIsomorphism {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj) :
  @IsIsomorphism ([C, Sets]) (@Curried_Hom C p) (icoprod_hom_functor f)
                 (icoprod_hom_transform f p inj) :=
  @iprod_hom_IsIsomorphism (C^op) A f p inj H.

Definition icoprod_of_hom_iso {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p}
  (I : @IsIsomorphism ([C, Sets]) (@Curried_Hom C p) (icoprod_hom_functor f)
                      (icoprod_hom_transform f p inj)) :
  IsIndexedCoproduct f p inj :=
  @iprod_of_hom_iso (C^op) A f p inj I.

Definition icoprod_iff_hom_iso {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) :
  IsIndexedCoproduct f p inj ↔
  @IsIsomorphism ([C, Sets]) (@Curried_Hom C p) (icoprod_hom_functor f)
                 (icoprod_hom_transform f p inj) :=
  @iprod_iff_hom_iso (C^op) A f p inj.

Example icoprod_hom_transform_computes {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) (c : C) (u : p ~> c) :
  transform (icoprod_hom_transform f p inj) c u = fun a : A => u ∘ inj a
  := eq_refl.

Example icoprod_iff_hom_iso_fst {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) :
  fst (icoprod_iff_hom_iso f p inj)
  = fun H => @icoprod_hom_IsIsomorphism C A f p inj H := eq_refl.

Example icoprod_iff_hom_iso_snd {C : Category} {A : Type} (f : A → C)
  (p : C) (inj : ∀ a : A, f a ~> p) :
  snd (icoprod_iff_hom_iso f p inj)
  = fun I => @icoprod_of_hom_iso C A f p inj I := eq_refl.

Example icoprod_hom_iso_to {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj) :
  to (icoprod_hom_iso H) = icoprod_hom_transform f p inj := eq_refl.

Example icoprod_hom_iso_from_is_desc {C : Category} {A : Type} {f : A → C}
  {p : C} {inj : ∀ a : A, f a ~> p} (H : IsIndexedCoproduct f p inj)
  (c : C) (fam : ∀ a : A, f a ~> c) :
  transform (from (icoprod_hom_iso H)) c fam = unique_obj (icoprod_desc H fam)
  := eq_refl.

(** ** The three presentations of an indexed (co)product all compose *)

Definition limit_hom_iso {C : Category} {A : Set} (f : A → C)
  (L : Limit (DiscreteCat_Functor f)) :
  @Isomorphism ([C^op, Sets]) (@Curried_CoHom C (iprod f L))
               (iprod_hom_functor f) :=
  iprod_hom_iso (limit_is_indexed_product f L).

Definition colimit_hom_iso {C : Category} {A : Set} (f : A → C)
  (L : Limit (@DiscreteCat_Functor A (C^op) f)) :
  @Isomorphism ([C, Sets]) (@Curried_Hom C (icoprod f L))
               (icoprod_hom_functor f) :=
  icoprod_hom_iso (colimit_is_indexed_coproduct f L).

Definition indexed_product_hom_iso {C : Category}
  {HP : @HasIndexedProducts C} {A : Type} (f : A → C) :
  @Isomorphism ([C^op, Sets]) (@Curried_CoHom C (indexed_product f))
               (iprod_hom_functor f) :=
  iprod_hom_iso (indexed_product_ump f).

Definition indexed_coproduct_hom_iso {C : Category}
  {HC : @HasIndexedCoproducts C} {A : Type} (f : A → C) :
  @Isomorphism ([C, Sets]) (@Curried_Hom C (indexed_coproduct f))
               (icoprod_hom_functor f) :=
  icoprod_hom_iso (indexed_coproduct_ump f).

(** ** The right-hand side is the tree's own indexed product, at [Sets] *)

Example iprod_hom_functor_is_indexed_product {C : Category} {A : Type}
  (f : A → C) (c : C) :
  fobj[iprod_hom_functor f] c = indexed_product (iprod_hom_fam f c) := eq_refl.

Example icoprod_hom_functor_is_indexed_product {C : Category} {A : Type}
  (f : A → C) (c : C) :
  fobj[icoprod_hom_functor f] c = indexed_product (icoprod_hom_fam f c)
  := eq_refl.

Example icoprod_hom_functor_is_op {C : Category} {A : Type} (f : A → C) :
  icoprod_hom_functor f = @iprod_hom_functor (C^op) A f := eq_refl.

(** ** Non-vacuity: the in-tree indexed (co)products of [Sets] *)

Definition Sets_iprod_hom_iso {A : Type} (F : A → obj[Sets]) :
  @Isomorphism ([Sets^op, Sets]) (@Curried_CoHom Sets (Sets_iprod_obj F))
               (iprod_hom_functor F) :=
  iprod_hom_iso (Sets_IsIndexedProduct F).

Definition Sets_icoprod_hom_iso {A : Type} (F : A → obj[Sets]) :
  @Isomorphism ([Sets, Sets]) (@Curried_Hom Sets (Sets_icoprod_obj F))
               (icoprod_hom_functor F) :=
  icoprod_hom_iso (Sets_IsIndexedCoproduct F).

Example Sets_iprod_hom_from_computes {A : Type} (F : A → obj[Sets])
  (c : obj[Sets]) (fam : ∀ a : A, c ~{Sets}~> F a) :
  transform (from (Sets_iprod_hom_iso F)) c fam = Sets_iprod_tuple F c fam
  := eq_refl.

Example Sets_icoprod_hom_from_computes {A : Type} (F : A → obj[Sets])
  (c : obj[Sets]) (fam : ∀ a : A, F a ~{Sets}~> c) :
  transform (from (Sets_icoprod_hom_iso F)) c fam = Sets_icoprod_case F c fam
  := eq_refl.

(** ** The invertibility hypothesis is not vacuous *)

Definition Sets_const_true : Sets_bool ~{Sets}~> Sets_bool.
Proof.
  unshelve refine {| morphism := fun _ => true |}.
  all: intros x y Hxy; reflexivity.
Defined.

Definition Sets_bad_proj (a : poly_unit) :
  Sets_bool ~{Sets}~> (fun _ : poly_unit => Sets_bool) a := Sets_const_true.

Lemma Sets_bad_transform_not_iso :
  @IsIsomorphism ([Sets^op, Sets])
    (@Curried_CoHom Sets Sets_bool)
    (iprod_hom_functor (fun _ : poly_unit => Sets_bool))
    (iprod_hom_transform (fun _ : poly_unit => Sets_bool)
                         Sets_bool Sets_bad_proj) → False.
Proof.
  intros I.
  pose proof (@is_left_inverse _ _ _ _ I Sets_bool
                (@id Sets Sets_bool)) as H0.
  pose proof (@is_left_inverse _ _ _ _ I Sets_bool Sets_const_true) as H1.
  simpl in H0, H1.
  assert (Heq : transform (@two_sided_inverse _ _ _ _ I) Sets_bool
                  (fun _ : poly_unit => Sets_const_true ∘ @id Sets Sets_bool)
                ≈ transform (@two_sided_inverse _ _ _ _ I) Sets_bool
                  (fun _ : poly_unit => Sets_const_true ∘ Sets_const_true)).
  { apply (proper_morphism
             (transform (@two_sided_inverse _ _ _ _ I) Sets_bool)).
    intros a x; reflexivity. }
  specialize (Heq false).
  rewrite H0, H1 in Heq.
  simpl in Heq.
  discriminate Heq.
Qed.

Definition Sets_bad_not_iprod :
  IsIndexedProduct (fun _ : poly_unit => Sets_bool) Sets_bool Sets_bad_proj
  → False :=
  fun H => Sets_bad_transform_not_iso (fst (iprod_iff_hom_iso _ _ _) H).

Definition Sets_bad_inj (a : poly_unit) :
  (fun _ : poly_unit => Sets_bool) a ~{Sets}~> Sets_bool := Sets_const_true.

Lemma Sets_bad_transform_not_iso_co :
  @IsIsomorphism ([Sets, Sets])
    (@Curried_Hom Sets Sets_bool)
    (icoprod_hom_functor (fun _ : poly_unit => Sets_bool))
    (icoprod_hom_transform (fun _ : poly_unit => Sets_bool)
                           Sets_bool Sets_bad_inj) → False.
Proof.
  intros I.
  pose proof (@is_left_inverse _ _ _ _ I Sets_bool
                (@id Sets Sets_bool)) as H0.
  pose proof (@is_left_inverse _ _ _ _ I Sets_bool Sets_const_true) as H1.
  simpl in H0, H1.
  assert (Heq : transform (@two_sided_inverse _ _ _ _ I) Sets_bool
                  (fun _ : poly_unit => @id Sets Sets_bool ∘ Sets_const_true)
                ≈ transform (@two_sided_inverse _ _ _ _ I) Sets_bool
                  (fun _ : poly_unit => Sets_const_true ∘ Sets_const_true)).
  { apply (proper_morphism
             (transform (@two_sided_inverse _ _ _ _ I) Sets_bool)).
    intros a x; reflexivity. }
  specialize (Heq false).
  rewrite H0, H1 in Heq.
  simpl in Heq.
  discriminate Heq.
Qed.

Definition Sets_bad_not_icoprod :
  IsIndexedCoproduct (fun _ : poly_unit => Sets_bool) Sets_bool Sets_bad_inj
  → False :=
  fun H => Sets_bad_transform_not_iso_co (fst (icoprod_iff_hom_iso _ _ _) H).

(* The class-derived comparison and the one read straight off
   [Sets_IsIndexedProduct] are the SAME TERM, not merely isomorphic: the
   class projection reduces by iota to the field it was built from. *)

Example Sets_iprod_hom_iso_is_class {A : Type} (F : A → obj[Sets]) :
  @indexed_product_hom_iso Sets Sets_HasIndexedProducts A F
  = Sets_iprod_hom_iso F := eq_refl.

Example Sets_icoprod_hom_iso_is_class {A : Type} (F : A → obj[Sets]) :
  @indexed_coproduct_hom_iso Sets Sets_HasIndexedCoproducts A F
  = Sets_icoprod_hom_iso F := eq_refl.
