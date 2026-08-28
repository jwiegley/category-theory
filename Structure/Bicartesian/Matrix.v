Require Import Coq.Vectors.Fin.
Require Import Coq.Logic.Eqdep_dec.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Bicartesian.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.Semiadditive.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Coproduct.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(* Every lemma below sits in a section whose hypotheses ([inj]/[proj],
   [HQ]/[HP], [dec]) frequently do not appear in the statement, so the file
   opts into the [Default Proof Using "All"] discipline of
   Theory/EckmannHilton.v rather than annotating each proof.  Definitions are
   unaffected: they abstract only the section variables they actually use, so
   e.g. [matrix_row] takes [HP] alone while [matrix_mor] takes both. *)
#[local] Set Default Proof Using "All".

(** * Matrices of morphisms between finite coproducts and products *)

(* nLab:      https://ncatlab.org/nlab/show/biproduct
   nLab:      https://ncatlab.org/nlab/show/matrix+calculus
   Wikipedia: https://en.wikipedia.org/wiki/Biproduct

   Mac Lane, CWM 2nd ed. §III.5 (pp. 73-74), records that a morphism out of
   an m-fold coproduct and into an n-fold product is *exactly* an m x n
   matrix of morphisms: the coproduct UMP splits it into m rows, the product
   UMP splits each row into n entries, and nothing else about it is free.
   With a zero object in play the identity matrix -- identities down the
   diagonal, zero morphisms elsewhere -- names a canonical comparison from
   the coproduct to the product, whose invertibility is what "the finite
   coproduct and the finite product coincide" means.  Riehl, CTiC 2nd ed.
   §3.1, states the same correspondence (Remark 3.1.27 clause (iii)) and uses
   it to define direct sums; her Exercise 3.1.ix is the small consequence
   that in the presence of a zero object the coproduct injections split.

   This file proves the correspondence over the *indexed* (co)product
   vocabulary of Structure/Limit/{Product,Coproduct}.v -- so the row and
   column index types are arbitrary, not merely finite -- and then reads it
   off at the n-ary folds [fin_coprod]/[fin_prod] and at the classes
   [HasFiniteCoproducts]/[HasFiniteProducts] of
   Structure/Limit/Product/Finite.v.

   ** What is proved

   (1) DETERMINATION AND CONSTRUCTION.  For a coproduct (q, inj) of a family
       [g : J -> C] and a product (p, proj) of a family [fam : K -> C],
       [mat_entry inj proj u j k := proj k ∘ u ∘ inj j] is the (j,k) entry of
       [u : q ~> p].  Then [matrix_ext] says two such morphisms agreeing in
       every entry are equal, [matrix_determined] packages that as a
       biconditional (Lib's [↔] is the Type-valued [iffT], so both legs are
       data), [matrix_mor] builds the morphism with prescribed
       entries, [matrix_entry] computes its entries back, and [matrix_ump]
       bundles both halves as the unique existence
       [∃! u, ∀ j k, mat_entry inj proj u j k ≈ e j k].
       [matrix_mor_entry] is the other round trip.  No finiteness, no
       decidability, no zero object, and no [Cartesian]/[Cocartesian]
       instance: the two universal properties are the entire input.

   (2) THE IDENTITY MATRIX.  Over a single family, a decidable index
       equality and a [ZeroObject], [kron] is the Kronecker delta
       (an identity on the diagonal, [zero_mor] off it -- the diagonal case
       is a transport [eq_rect] along the index equality, and the decider is
       what makes the two cases separable), and [can_matrix] is the induced
       comparison from the coproduct to the product.  [can_matrix_diag] and
       [can_matrix_off] read its entries; [can_matrix_unique] and
       [can_matrix_ump] say it is the only morphism with those entries.
       Specialized at the folds this is [fin_can] and at the classes
       [finite_can].  That this generalizes the binary [can_comparison] of
       Structure/Semiadditive.v:289 is not asserted but *proved*:
       [binary_IsIndexedProduct] and [binary_IsIndexedCoproduct] exhibit the
       ordinary binary product and coproduct as indexed ones over
       [fin2fam x y], and [binary_can_is_can_comparison] shows the identity
       matrix there IS [can_comparison x y] -- at [≈]; the [eq_refl] reading
       is refuted and located below.  The four matrix-entry
       lemmas [exl_can_inl], [exr_can_inl], [exl_can_inr], [exr_can_inr]
       (Structure/Semiadditive.v:300-322) are exactly the four entries that
       proof consumes.

   (3) RIEHL EXERCISE 3.1.ix.  With a zero object the coproduct injections
       are split monic, hence monic, and this needs *no* [Cartesian]
       structure: [inl_Section] and [inr_Section] exhibit the retractions
       [id ▽ zero_mor] and [zero_mor ▽ id], whose defining equations are
       literally instances of [inl_merge] / [inr_merge]
       (Structure/Cocartesian.v:175,182), and [inl_Monic] / [inr_Monic]
       follow through [sections_are_monic] (Theory/Morphisms.v:182).
       [indexed_inj_Section] and [indexed_inj_Monic] are the n-ary form, the
       retraction being the cotuple of a column of the Kronecker delta --
       note the asymmetry, that the *binary* statement needs no decidable
       index equality (the two summands are distinguished syntactically)
       while the indexed one does, since without a decider [kron] cannot
       even be written.

   ** Prior art for (3), scoped

   The census is a search over the whole tree for the SHAPE "an equation
   whose left side composes something with [inl] and whose right side is
   [id]", plus a search for [Section]/[SplitMono]/[Monic] applied to a
   coproduct injection.  It returns three things, none of them this
   statement.  (i) Structure/Semiadditive.v:300's [exl_can_inl] is the only
   in-tree DERIVED retraction for a [Cocartesian] [inl]; it additionally
   assumes [Cartesian] and routes through [can_comparison].  (ii)
   Structure/Biproduct.v:51's [bi_exl_inl] is a FIELD of the [Biproduct]
   record -- assumed data about that record's own [bi_inl], not about
   [inl], and no [Cocartesian] structure is in sight.  (iii)
   Instance/Grp/Pushout.v:644,653 prove the free-product injections of
   [Grp] split and are monic, but concretely and from a FACTORIZATION
   hypothesis ([am_inj1_Section_of_factor]) rather than from a zero object.
   Adjacent but not subsuming: Structure/Pushout/Split.v:191's
   [pushout_both_Monic] derives monic injections from split legs of a
   pushout, and a binary coproduct is a pushout over the initial object --
   but that identification is issue #862's and is not in tree, so the
   generic "zero object + binary coproducts ⟹ the injections split" is
   stated here for the first time.

   ** Without a zero object the injections need not be monic

   Structure/Cocartesian.v:75 makes this point in prose, citing the nLab.
   It is RECORDED here and not proved: no in-tree category is exhibited
   whose coproduct injections fail to be monic, and no impossibility is
   claimed either.  What the file does establish is where the hypothesis is
   spent -- the retraction [id ▽ zero_mor] cannot be written without
   [zero_mor], and [zero_mor] cannot be written without a zero object.

   ** Riehl's abelian-category footnote is not pursued, and cannot be

   Riehl remarks that the identity matrix is invertible in any abelian
   category.  As this library is arranged that is not a theorem waiting to
   be proved but a statement with no content: Structure/Abelian.v:137-138
   carries [abelian_additive : Additive C] and Structure/Additive.v:37,40
   carries [additive_biproducts : HasBiproducts] as DATA, so an in-tree
   abelian category HAS biproducts by hypothesis and there is nothing left
   to derive.  The remark is therefore stated here and left alone.

   ** Strengths measured, strict first

   These are measurements, not expectations.  What HOLDS at [eq_refl]:

     - [mat_entry_unfold]: an entry IS [proj k ∘ u ∘ inj j], by definition.
     - [matrix_row_at_fold]: the j-th row of a matrix built over the product
       fold IS [fin_tuple n fs (gs j) (e j)] -- the fold's own tupling, on
       the nose.  This works because [fin_prod_ump] is [Defined] and
       [IsIndexedProduct] has primitive projections, so [unique_obj] of the
       descent datum reduces.
     - [matrix_mor_at_fold]: correspondingly the whole matrix morphism IS
       [fin_cotuple] of those rows.
     - [finite_matrix_is_fin_matrix] and [finite_can_is_fin_can]: at the
       instances [Cartesian_Terminal_HasFiniteProducts] and
       [Cocartesian_Initial_HasFiniteCoproducts] the class-level
       constructions ARE the fold-level ones.
     - [kron_off_computes]: at two closed, distinct [Fin.t 2] indices the
       Kronecker delta reduces to [zero_mor] over [Fin.eq_dec].
     - [coq_matrix_computes] and [coq_matrix_computes_right]: over [Coq] a
       2x2 matrix of successors sends [inl 3] to [(4, (4, tt))] and
       [inr (inl 7)] to [(8, (8, tt))].  ([Category.Instance.Coq] is
       required directly for these, and adds nothing to the dependency
       closure: Structure/Limit/Product/Finite.v already requires it for
       its own computing examples.)

   What is REFUTED at [eq_refl] (measured during development; pinned in the
   companion probe), each a genuine conversion failure reported as
   "cannot unify":

     - [kron fam Fin.eq_dec Fin.F1 Fin.F1 = id].  The failure is located
       precisely: the branch selection DOES reduce -- [Fin.eq_dec] applied to
       two closed indices exposes [Specif.left]/[Specif.right], which is why
       [kron_off_computes] above succeeds -- but the equality proof it
       returns is not [eq_refl], so the [eq_rect] transport in the diagonal
       branch is stuck.  This is a property of the DECIDER, not of [kron]:
       the sections are parametric in [dec], and a decider returning
       [eq_refl] on the diagonal would collapse it.  No such decider is
       built here.
     - [binary_can x y = can_comparison x y].  The two are proved equal at
       [≈] ([binary_can_is_can_comparison]) and are not convertible: the
       former is a cotuple of tuples produced by two descent data, the
       latter the hand-written [(id △ zero_mor) ▽ (zero_mor △ id)].

   ** Universes, read off the constraint blocks

   [mat_entry] is declared with explicit universe binders and its constraint
   block is [uh <= up] alone: the two index universes are free of the
   category's, and the category's hom and proof universes are kept APART.
   That annotation is load-bearing and the fact was measured, not assumed --
   written unannotated, [mat_entry] elaborates at [Category@{uo uh uh}] with
   an EMPTY constraint block, and a probe at a section declaring
   [Constraint uh < up] then rejects it while accepting bare [~>] and [∘]
   at that same setting, and accepting the SHIPPED, annotated [mat_entry]
   applied at those levels.  (An earlier draft of this sentence described
   that control as a re-derivation of the body under explicit binders; the
   probe applies the shipped constant instead.  The conclusion is the same
   either way, but the method described was not the method shipped.)
   So the identification was minimization, not
   content, and explicit binders lift it; the probes are pinned in the
   companion probe file.

   Everything downstream nevertheless identifies the category's hom and
   proof universes, and that is the DONORS' doing rather than this file's,
   measured on their own constraint blocks: [IsIndexedProduct@{u u0 u1 u2}]
   is stated over [Category@{u1 u2 u2}], [IsIndexedCoproduct] over
   [Category@{u2 u3 u3}], and [ZeroObject@{u u0}] over [Category@{u u0 u0}].
   Read that roster as EXHIBITING donors, not as exhausting them -- an
   earlier draft presented it as a full account and it is not.  At least
   two more identify the same levels: [Cartesian@{u u0}] is itself over
   [Category@{u u0 u0}] and is what identifies them across the binary half
   ([inl_Section], [inl_Monic], [binary_can]), and [fin2_colegs@{u u0}] is
   over [Category@{u u0 u0}] while using NONE of the three named above --
   its donors are Structure/Limit/Product/Finite.v's [fin2_legs] and
   [fin2fam] plus Construction/Opposite.v's [Opposite].  The claim that
   the identification is the DONORS' doing and not this file's survives
   unchanged; only the completeness of the list was wrong.
   No attempt is made to lift any of them.  Within that, the
   constraint blocks are
   BOUNDS and not identifications: [matrix_ext] carries seven [<=] relations
   and no equation, with the row and column index universes [u1], [u2]
   bounded above by the two records' universes and unrelated to each other;
   [kron]'s entire constraint block is [u0 <= eq_rect.u0] and
   [u1 <= eq_rect.u1], i.e. the transport's, and nothing else; and
   [inl_Monic]'s constraint block is EMPTY.

   ** Axioms

   62/62 constants report "Closed under the global context".  The count is
   the file's [def] plus [prf] glob entries, and it is exact rather than a
   floor: the file contains no [Program], no [Record]/[Class]/[Inductive]
   and no [Instance], so there are no obligation constants, constructors or
   instance names for a glob sweep to miss -- 24 [Definition] + 19
   [Theorem] + 10 [Lemma] + 8 [Example] + 1 [Corollary] = 62 independently.
   [UIP_dec] (Hedberg) is the only nontrivial stdlib import and is
   axiom-free.

   ** Relation to #320, which hosts the other two clauses

   Structure/Limit/Indexed/Hom.v delivers Riehl 3.1.27 clauses (i) and
   (ii) over the SAME arbitrary-index API, as NATURAL ISOMORPHISMS
   ([iprod_hom_iso], [icoprod_hom_iso]); its header points forward twice
   (:41, :234) saying clause (iii) "is issue #336 and is NOT here".  This
   file supplies clause (iii), so the back pointer belongs here and an
   earlier draft omitted it entirely.  Two honest notes rather than one
   convenient one.  First, clause (iii) is NOT derived from (i) and (ii)
   here; whether it follows by composing them is not investigated.
   Second, it lands one strength LOWER than its siblings: they are
   isomorphisms in a functor category, whereas this is [∃!] plus mutually
   inverse maps at [≈], with no [≅[Sets]] object anywhere.  #336's own
   body says an implementer "should read #320 before starting the
   arbitrary-index box"; that was done, and the two are related by
   citation only.

   ** Citations corrected against the issue

   Five of #336's own line numbers are stale and are silently corrected
   above; recording them so the correction is visible.  The issue cites
   Structure/Semiadditive.v:288 ([can_comparison], really :289) and :299
   ([exl_can_inl], really :300); Structure/Biproduct.v:52 ([bi_exl_inl],
   really :51); Theory/Morphisms.v:179 ([sections_are_monic], really
   :182); and Structure/Additive.v:34,37 ([additive_biproducts], really
   :37,40).  Each corrected number was checked by reading the line.

   ** NOT delivered

   The general matrix composition formula -- that composing two matrices
   multiplies them, entry (j,l) of [v ∘ u] being the sum over k of
   (entry (k,l) of v) ∘ (entry (j,k) of u) -- is NOT proved here.  It is
   OWNED by issue #536, whose QA correction on #336 says to "cite it
   rather than re-proving", so it is cross-referenced and nothing below
   depends on it.

   THE SECOND DEFERRAL IS NOT THE SAME KIND, and an earlier draft of this
   header wrongly said "both are owned by issue #536".  #336's remaining
   Riehl box asks that the identity-matrix comparison BE AN ISOMORPHISM
   for finite index, with the direct sum [⊕] as the common value.  Only
   the OBJECT is #536's -- its QA correction says the object "is #536's
   first Work item; consume it" -- while the box's own text says "the
   n-ary case is genuine new work".  So that box is #336's OWN work,
   BLOCKED on #536's [⊕], and DEFERRED here; it is not owned elsewhere.
   #336 states that it "cannot close while [these boxes] are unproved",
   so this commit ADVANCES #336 rather than closing it: the other box of
   that pair, the arbitrary-index matrix determination, IS delivered
   above, and both of its halves are.  Also absent: no invertibility criterion
   for [can_matrix] and so no n-ary semiadditivity (the binary version is
   Structure/Semiadditive.v's [E] hypothesis); no functoriality of
   [matrix_mor] in the two families; no naturality; no transpose or duality
   statement relating the J-indexed and K-indexed sides; no concrete
   category with a zero object is instantiated IN THIS FILE, so
   [can_matrix], [fin_can], [finite_can] and the Exercise 3.1.ix results
   are conditionals here (the [Coq] examples witness only (1), [Coq]
   having no zero object -- its initial object is [False] and its terminal
   [unit], asserted rather than proved, though the tree proves the
   analogue twice at Instance/Top.v:505 and for [Rng]).  READ THAT AS A
   CHOICE, NOT AN UNAVAILABILITY: an earlier draft of this paragraph
   explained the gap by the witness category alone, which misleads.  The
   tree carries SIX registered [ZeroObject] instances -- [Grp_Zero]
   (Instance/Grp.v:600), [Ab_Zero] (Instance/Ab.v:276), [CMon_Zero]
   (Instance/CMon/Biproduct.v:160), [RMod_Zero] (Instance/Mod.v:389),
   [Rel_Zero] (Instance/Rel/Dagger.v:191), [PointedSets_Zero]
   (Instance/Sets/Pointed.v:302) -- and [Ab] supplies BOTH hypotheses as
   exported instances, [Ab_Cocartesian] being Instance/Ab/Coproduct.v:228.
   The Exercise 3.1.ix witness is therefore two lines of pure
   instantiation, and it IS shipped, in Test/ProbeMatrix336.v.  It is kept
   out of THIS file for a measured reason: [Instance/Ab] is not in this
   file's dependency closure (0 of 19 modules), while
   Instance/Ab/Coproduct.v's own closure is 17, so importing it here would
   nearly double a [Structure/] file's footprint for two [Example]s.  What
   remains genuinely unwitnessed is the [can_matrix] family, which needs a
   zero object AND a decidable index AND both indexed structures; and
   nothing is said about when the comparison is an isomorphism in any
   particular category. *)

(** ** Entries *)

(* The (j,k) entry of a morphism out of a coproduct and into a product:
   restrict along the j-th injection, then project onto the k-th factor.
   Explicit universe binders keep the category's hom and proof universes
   apart; see the header. *)
Definition mat_entry@{uo uh up uj uk} {C : Category@{uo uh up}}
  {J : Type@{uj}} {K : Type@{uk}} {g : J → C} {fam : K → C} {q p : C}
  (inj : ∀ j : J, g j ~> q) (proj : ∀ k : K, p ~> fam k)
  (u : q ~> p) (j : J) (k : K) : g j ~> fam k :=
  proj k ∘ u ∘ inj j.

Example mat_entry_unfold {C : Category} {J K : Type} {g : J → C}
  {fam : K → C} {q p : C} (inj : ∀ j : J, g j ~> q)
  (proj : ∀ k : K, p ~> fam k) (u : q ~> p) (j : J) (k : K) :
  mat_entry inj proj u j k = proj k ∘ u ∘ inj j := eq_refl.

(** ** The m x n determination (Mac Lane §III.5) *)

Section Matrix.

Context {C : Category}.
Context {J K : Type}.
Context {g : J → C}.
Context {fam : K → C}.
Context {q : C}.
Context {inj : ∀ j : J, g j ~> q}.
Context {p : C}.
Context {proj : ∀ k : K, p ~> fam k}.
Context (HQ : IsIndexedCoproduct g q inj).
Context (HP : IsIndexedProduct fam p proj).

(* Two morphisms into the product agree when all their projections do: both
   factor the same family through the universal one. *)
Lemma iprod_ext {c : C} (a b : c ~> p) :
  (∀ k : K, proj k ∘ a ≈ proj k ∘ b) → a ≈ b.
Proof.
  intro H.
  pose proof (iprod_desc HP (fun k => proj k ∘ a)) as D.
  transitivity (unique_obj D).
  - symmetry.
    apply (uniqueness D).
    intro k; reflexivity.
  - apply (uniqueness D).
    intro k; symmetry; apply H.
Qed.

(* Dually for morphisms out of the coproduct. *)
Lemma icoprod_ext {c : C} (a b : q ~> c) :
  (∀ j : J, a ∘ inj j ≈ b ∘ inj j) → a ≈ b.
Proof.
  intro H.
  pose proof (icoprod_desc HQ (fun j => a ∘ inj j)) as D.
  transitivity (unique_obj D).
  - symmetry.
    apply (uniqueness D).
    intro j; reflexivity.
  - apply (uniqueness D).
    intro j; symmetry; apply H.
Qed.

(* Mac Lane's determination: a morphism from the coproduct to the product is
   fixed by its m x n matrix of entries.  Restricting along the injections
   uses the coproduct UMP, projecting onto the factors the product UMP; the
   only other step is reassociation. *)
Theorem matrix_ext (u v : q ~> p) :
  (∀ (j : J) (k : K),
     mat_entry inj proj u j k ≈ mat_entry inj proj v j k) → u ≈ v.
Proof.
  intro H.
  apply icoprod_ext; intro j.
  apply iprod_ext; intro k.
  rewrite !comp_assoc.
  exact (H j k).
Qed.

Corollary matrix_determined (u v : q ~> p) :
  u ≈ v ↔ (∀ (j : J) (k : K),
             mat_entry inj proj u j k ≈ mat_entry inj proj v j k).
Proof.
  split.
  - intros Huv j k.
    unfold mat_entry.
    now rewrite Huv.
  - apply matrix_ext.
Qed.

(* The j-th row of a prescribed matrix: the tuple of its entries. *)
Definition matrix_row (e : ∀ (j : J) (k : K), g j ~> fam k) (j : J) :
  g j ~> p := unique_obj (iprod_desc HP (e j)).

Lemma matrix_row_commutes (e : ∀ (j : J) (k : K), g j ~> fam k)
  (j : J) (k : K) : proj k ∘ matrix_row e j ≈ e j k.
Proof. exact (unique_property (iprod_desc HP (e j)) k). Qed.

(* The morphism with prescribed entries: the cotuple of the rows. *)
Definition matrix_mor (e : ∀ (j : J) (k : K), g j ~> fam k) : q ~> p :=
  unique_obj (icoprod_desc HQ (matrix_row e)).

Lemma matrix_mor_inj (e : ∀ (j : J) (k : K), g j ~> fam k) (j : J) :
  matrix_mor e ∘ inj j ≈ matrix_row e j.
Proof. exact (unique_property (icoprod_desc HQ (matrix_row e)) j). Qed.

Theorem matrix_entry (e : ∀ (j : J) (k : K), g j ~> fam k)
  (j : J) (k : K) : mat_entry inj proj (matrix_mor e) j k ≈ e j k.
Proof.
  unfold mat_entry.
  rewrite <- comp_assoc.
  rewrite matrix_mor_inj.
  apply matrix_row_commutes.
Qed.

(* The correspondence in one statement: matrices are morphisms. *)
Theorem matrix_ump (e : ∀ (j : J) (k : K), g j ~> fam k) :
  ∃! u : q ~> p, ∀ (j : J) (k : K), mat_entry inj proj u j k ≈ e j k.
Proof.
  unshelve eapply Build_Unique.
  - exact (matrix_mor e).
  - exact (matrix_entry e).
  - intros v Hv.
    apply matrix_ext; intros j k.
    rewrite matrix_entry.
    symmetry; apply Hv.
Defined.

(* The other round trip: reading a morphism's entries and rebuilding it
   returns it (up to ≈; see the header for what is refuted strictly). *)
Theorem matrix_mor_entry (u : q ~> p) :
  matrix_mor (mat_entry inj proj u) ≈ u.
Proof. apply matrix_ext; intros j k; apply matrix_entry. Qed.

End Matrix.

(** ** The Kronecker delta *)

Section KroneckerDelta.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context {A : Type}.
Context (fam : A → C).
Context (dec : ∀ a b : A, {a = b} + {a <> b}).

(* An identity on the diagonal, a zero morphism off it.  The diagonal branch
   must transport the identity along the index equality, which is why a
   decider is needed to write this down at all: [Specif.left] carries the
   proof [e : j = k] that [eq_rect] consumes. *)
Definition kron (j k : A) : fam j ~> fam k :=
  match dec j k with
  | Specif.left e  => eq_rect j (fun k' : A => fam j ~> fam k') id k e
  | Specif.right _ => zero_mor
  end.

(* Uniqueness of identity proofs on a type with decidable equality is
   Hedberg's theorem, [UIP_dec], which is axiom-free. *)
Lemma kron_diag (j : A) : kron j j ≈ id.
Proof.
  unfold kron.
  destruct (dec j j) as [e|ne].
  - now rewrite (UIP_dec dec e eq_refl).
  - now contradiction ne.
Qed.

Lemma kron_off (j k : A) : j <> k → kron j k ≈ zero_mor.
Proof.
  intro Hne.
  unfold kron.
  destruct (dec j k) as [e|ne].
  - contradiction.
  - reflexivity.
Qed.

End KroneckerDelta.

(* Off the diagonal the delta COMPUTES over [Fin.eq_dec] at closed indices:
   the decider exposes [Specif.right], and that branch carries no transport.
   The diagonal case does not; see the header. *)
Example kron_off_computes {C : Category} `{Z : @ZeroObject C}
  (fam : Fin.t 2 → C) :
  kron fam Fin.eq_dec Fin.F1 (Fin.FS Fin.F1) = zero_mor := eq_refl.

(** ** The identity matrix as the canonical comparison *)

Section IdentityMatrix.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context {A : Type}.
Context (fam : A → C).
Context (dec : ∀ a b : A, {a = b} + {a <> b}).
Context {q : C}.
Context {inj : ∀ a : A, fam a ~> q}.
Context {p : C}.
Context {proj : ∀ a : A, p ~> fam a}.
Context (HQ : IsIndexedCoproduct fam q inj).
Context (HP : IsIndexedProduct fam p proj).

Definition can_matrix : q ~> p := matrix_mor HQ HP (kron fam dec).

Theorem can_matrix_diag (j : A) : mat_entry inj proj can_matrix j j ≈ id.
Proof.
  unfold can_matrix.
  rewrite matrix_entry.
  apply kron_diag.
Qed.

Theorem can_matrix_off (j k : A) :
  j <> k → mat_entry inj proj can_matrix j k ≈ zero_mor.
Proof.
  intro Hne.
  unfold can_matrix.
  rewrite matrix_entry.
  now apply kron_off.
Qed.

(* The identity matrix determines the comparison: any morphism with those
   entries is it. *)
Theorem can_matrix_unique (u : q ~> p) :
  (∀ j : A, mat_entry inj proj u j j ≈ id) →
  (∀ j k : A, j <> k → mat_entry inj proj u j k ≈ zero_mor) →
  u ≈ can_matrix.
Proof.
  intros Hd Ho.
  apply (matrix_ext HQ HP); intros j k.
  destruct (dec j k) as [e|ne].
  - destruct e.
    rewrite can_matrix_diag.
    apply Hd.
  - rewrite (can_matrix_off _ _ ne).
    now apply Ho.
Qed.

Theorem can_matrix_ump :
  ∃! u : q ~> p,
    (∀ j : A, mat_entry inj proj u j j ≈ id) *
    (∀ j k : A, j <> k → mat_entry inj proj u j k ≈ zero_mor).
Proof.
  unshelve eapply Build_Unique.
  - exact can_matrix.
  - exact (can_matrix_diag, can_matrix_off).
  - intros v [Hd Ho].
    symmetry.
    now apply can_matrix_unique.
Defined.

End IdentityMatrix.

(** ** Riehl Exercise 3.1.ix, indexed form *)

Section IndexedInjections.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context {A : Type}.
Context (fam : A → C).
Context (dec : ∀ a b : A, {a = b} + {a <> b}).
Context {q : C}.
Context {inj : ∀ a : A, fam a ~> q}.
Context (HQ : IsIndexedCoproduct fam q inj).

(* The retraction of the j-th injection is the cotuple of the j-th COLUMN of
   the Kronecker delta.  Note that only the coproduct is used: no product,
   no [Cartesian], no [Terminal]. *)
Definition inj_retract (j : A) : q ~> fam j :=
  unique_obj (icoprod_desc HQ (fun k => kron fam dec k j)).

Lemma inj_retract_commutes (j k : A) :
  inj_retract j ∘ inj k ≈ kron fam dec k j.
Proof.
  exact (unique_property
           (icoprod_desc HQ (fun k => kron fam dec k j)) k).
Qed.

Lemma inj_retract_id (j : A) : inj_retract j ∘ inj j ≈ id.
Proof.
  rewrite inj_retract_commutes.
  apply kron_diag.
Qed.

Definition indexed_inj_Section (j : A) : Section (inj j) :=
  {| section := inj_retract j; section_comp := inj_retract_id j |}.

Definition indexed_inj_SplitMono (j : A) : SplitMono (inj j) :=
  indexed_inj_Section j.

Definition indexed_inj_Monic (j : A) : Monic (inj j) :=
  sections_are_monic _ _ _ (indexed_inj_Section j).

End IndexedInjections.

(** ** Riehl Exercise 3.1.ix, binary form *)

Section CoproductInjections.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{CC : @Cocartesian C}.
Context (x y : C).

(* Minimal hypotheses: a zero object and binary coproducts.  There is no
   [Cartesian] instance in this section, and the defining equations are
   nothing but [inl_merge] and [inr_merge] read at [id] and [zero_mor].
   Unlike the indexed form above this needs no decidable index equality,
   the two summands being distinguished syntactically. *)
Definition inl_Section : Section (@inl C CC x y) :=
  {| section := id ▽ zero_mor; section_comp := inl_merge id zero_mor |}.

Definition inr_Section : Section (@inr C CC x y) :=
  {| section := zero_mor ▽ id; section_comp := inr_merge zero_mor id |}.

Definition inl_SplitMono : SplitMono (@inl C CC x y) := inl_Section.
Definition inr_SplitMono : SplitMono (@inr C CC x y) := inr_Section.

Definition inl_Monic : Monic (@inl C CC x y) :=
  sections_are_monic _ _ _ inl_Section.

Definition inr_Monic : Monic (@inr C CC x y) :=
  sections_are_monic _ _ _ inr_Section.

End CoproductInjections.

(** ** The binary product and coproduct as indexed ones *)

(* The dual of [fin2_legs]: a pair of morphisms INTO a common target,
   indexed over [Fin.t 2].  It is [fin2_legs] read in C^op, which is why the
   binary coproduct instance below is a one-line instantiation. *)
Definition fin2_colegs {C : Category} {a x y : C} (f : x ~> a) (g : y ~> a) :
  ∀ i : Fin.t 2, fin2fam x y i ~> a :=
  @fin2_legs (C^op) a x y f g.

Definition binary_IsIndexedProduct {C : Category}
  (CP : @Cartesian C) (x y : C) :
  IsIndexedProduct (fin2fam x y) (x × y)%object (fin2_legs exl exr).
Proof.
  apply Build_IsIndexedProduct.
  intros c pi.
  unshelve eapply Build_Unique.
  - exact (pi Fin.F1 △ pi (Fin.FS Fin.F1)).
  - intro i.
    pattern i; apply (Fin.caseS' i); simpl.
    + apply exl_fork.
    + intro j.
      pattern j; apply (Fin.caseS' j); simpl.
      * apply exr_fork.
      * intro k; apply (Fin.case0 (fun _ => _) k).
  - intros v Hv.
    symmetry.
    apply (snd (ump_products _ _ _)).
    split.
    + exact (Hv Fin.F1).
    + exact (Hv (Fin.FS Fin.F1)).
Defined.

Definition binary_IsIndexedCoproduct {C : Category}
  (CC : @Cocartesian C) (x y : C) :
  IsIndexedCoproduct (fin2fam x y) (x + y)%object (fin2_colegs inl inr) :=
  @binary_IsIndexedProduct (C^op) CC x y.

(** ** The identity matrix at n = 2 IS Semiadditive's [can_comparison] *)

Section BinaryComparison.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{CP : @Cartesian C}.
Context `{CC : @Cocartesian C}.
Context (x y : C).

Definition binary_can : (x + y)%object ~> (x × y)%object :=
  can_matrix (fin2fam x y) Fin.eq_dec
    (binary_IsIndexedCoproduct CC x y) (binary_IsIndexedProduct CP x y).

(* The two diagonal entries are [exl_can_inl] and [exr_can_inr]. *)
Lemma binary_entry_diag (j : Fin.t 2) :
  mat_entry (fin2_colegs inl inr) (fin2_legs exl exr)
    (can_comparison x y) j j ≈ id.
Proof.
  pattern j; apply fin2fam_rect; unfold mat_entry; simpl.
  - apply exl_can_inl.
  - apply exr_can_inr.
Qed.

(* The two off-diagonal entries are [exr_can_inl] and [exl_can_inr]. *)
Lemma binary_entry_off (j k : Fin.t 2) :
  j <> k →
  mat_entry (fin2_colegs inl inr) (fin2_legs exl exr)
    (can_comparison x y) j k ≈ zero_mor.
Proof.
  revert k.
  pattern j; apply fin2fam_rect; intro k; pattern k; apply fin2fam_rect;
  intro Hne; unfold mat_entry; simpl.
  - now contradiction Hne.
  - apply exr_can_inl.
  - apply exl_can_inr.
  - now contradiction Hne.
Qed.

Theorem binary_can_is_can_comparison : can_comparison x y ≈ binary_can.
Proof.
  apply (can_matrix_unique (fin2fam x y) Fin.eq_dec
           (binary_IsIndexedCoproduct CC x y)
           (binary_IsIndexedProduct CP x y)).
  - exact binary_entry_diag.
  - exact binary_entry_off.
Qed.

End BinaryComparison.

(** ** At the n-ary folds of Structure/Limit/Product/Finite.v *)

Section FiniteMatrix.

Context {C : Category}.
Context `{CP : @Cartesian C}.
Context `{T : @Terminal C}.
Context (CC : @Cocartesian C).
Context (I : @Initial C).

Definition fin_matrix {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k) :
  fin_coprod CC I m gs ~> fin_prod n fs :=
  matrix_mor (fin_IsIndexedCoproduct CC I m gs) (fin_IsIndexedProduct n fs) e.

Theorem fin_matrix_entry {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k)
  (j : Fin.t m) (k : Fin.t n) :
  mat_entry (fin_inj CC I m gs) (fin_proj n fs)
    (fin_matrix gs fs e) j k ≈ e j k.
Proof. apply matrix_entry. Qed.

Theorem fin_matrix_ext {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (u v : fin_coprod CC I m gs ~> fin_prod n fs) :
  (∀ (j : Fin.t m) (k : Fin.t n),
     mat_entry (fin_inj CC I m gs) (fin_proj n fs) u j k
       ≈ mat_entry (fin_inj CC I m gs) (fin_proj n fs) v j k) → u ≈ v.
Proof.
  apply (matrix_ext (fin_IsIndexedCoproduct CC I m gs)
                    (fin_IsIndexedProduct n fs)).
Qed.

(* Strict: the rows and the whole matrix ARE the fold's own tupling and
   cotupling.  [fin_prod_ump] is [Defined] and [IsIndexedProduct] has
   primitive projections, so the descent datum reduces. *)
Example matrix_row_at_fold {J : Type} {gs : J → C} {n : nat}
  (fs : Fin.t n → C) (e : ∀ (j : J) (k : Fin.t n), gs j ~> fs k) (j : J) :
  matrix_row (fin_IsIndexedProduct n fs) e j = fin_tuple n fs (gs j) (e j) :=
  eq_refl.

Example matrix_mor_at_fold {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k) :
  fin_matrix gs fs e
    = fin_cotuple CC I m gs (fin_prod n fs)
        (fun j => fin_tuple n fs (gs j) (e j)) := eq_refl.

End FiniteMatrix.

Section FiniteComparison.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context `{CP : @Cartesian C}.
Context `{T : @Terminal C}.
Context (CC : @Cocartesian C).
Context (I : @Initial C).

(* [T] and [I] are taken as separate hypotheses rather than read off [Z].
   That is not a stronger assumption -- [zero_terminal] and [zero_initial]
   inhabit them -- and it keeps the fold's chosen unit independent of the
   zero object used for [zero_mor]. *)
Definition fin_can {n : nat} (fs : Fin.t n → C) :
  fin_coprod CC I n fs ~> fin_prod n fs :=
  can_matrix fs Fin.eq_dec
    (fin_IsIndexedCoproduct CC I n fs) (fin_IsIndexedProduct n fs).

Theorem fin_can_diag {n : nat} (fs : Fin.t n → C) (j : Fin.t n) :
  mat_entry (fin_inj CC I n fs) (fin_proj n fs) (fin_can fs) j j ≈ id.
Proof. apply can_matrix_diag. Qed.

Theorem fin_can_off {n : nat} (fs : Fin.t n → C) (j k : Fin.t n) :
  j <> k →
  mat_entry (fin_inj CC I n fs) (fin_proj n fs) (fin_can fs) j k
    ≈ zero_mor.
Proof. apply can_matrix_off. Qed.

Theorem fin_can_unique {n : nat} (fs : Fin.t n → C)
  (u : fin_coprod CC I n fs ~> fin_prod n fs) :
  (∀ j : Fin.t n,
     mat_entry (fin_inj CC I n fs) (fin_proj n fs) u j j ≈ id) →
  (∀ j k : Fin.t n, j <> k →
     mat_entry (fin_inj CC I n fs) (fin_proj n fs) u j k ≈ zero_mor) →
  u ≈ fin_can fs.
Proof. apply can_matrix_unique. Qed.

End FiniteComparison.

(** ** At the classes [HasFiniteCoproducts] / [HasFiniteProducts] *)

Section FiniteClassMatrix.

Context {C : Category}.
Context {HFP : HasFiniteProducts C}.
Context {HFC : HasFiniteCoproducts C}.

Definition finite_matrix {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k) :
  finite_coproduct gs ~> finite_product fs :=
  matrix_mor (finite_coproduct_ump gs) (finite_product_ump fs) e.

Theorem finite_matrix_entry {m n : nat} (gs : Fin.t m → C)
  (fs : Fin.t n → C) (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k)
  (j : Fin.t m) (k : Fin.t n) :
  mat_entry (finite_coproduct_inj gs) (finite_product_proj fs)
    (finite_matrix gs fs e) j k ≈ e j k.
Proof. apply matrix_entry. Qed.

Theorem finite_matrix_ext {m n : nat} (gs : Fin.t m → C)
  (fs : Fin.t n → C) (u v : finite_coproduct gs ~> finite_product fs) :
  (∀ (j : Fin.t m) (k : Fin.t n),
     mat_entry (finite_coproduct_inj gs) (finite_product_proj fs) u j k
       ≈ mat_entry (finite_coproduct_inj gs) (finite_product_proj fs)
           v j k) → u ≈ v.
Proof.
  apply (matrix_ext (finite_coproduct_ump gs) (finite_product_ump fs)).
Qed.

End FiniteClassMatrix.

Section FiniteClassComparison.

Context {C : Category}.
Context `{Z : @ZeroObject C}.
Context {HFP : HasFiniteProducts C}.
Context {HFC : HasFiniteCoproducts C}.

Definition finite_can {n : nat} (fs : Fin.t n → C) :
  finite_coproduct fs ~> finite_product fs :=
  can_matrix fs Fin.eq_dec
    (finite_coproduct_ump fs) (finite_product_ump fs).

Theorem finite_can_diag {n : nat} (fs : Fin.t n → C) (j : Fin.t n) :
  mat_entry (finite_coproduct_inj fs) (finite_product_proj fs)
    (finite_can fs) j j ≈ id.
Proof. apply can_matrix_diag. Qed.

Theorem finite_can_off {n : nat} (fs : Fin.t n → C) (j k : Fin.t n) :
  j <> k →
  mat_entry (finite_coproduct_inj fs) (finite_product_proj fs)
    (finite_can fs) j k ≈ zero_mor.
Proof. apply can_matrix_off. Qed.

Theorem finite_can_unique {n : nat} (fs : Fin.t n → C)
  (u : finite_coproduct fs ~> finite_product fs) :
  (∀ j : Fin.t n,
     mat_entry (finite_coproduct_inj fs) (finite_product_proj fs) u j j
       ≈ id) →
  (∀ j k : Fin.t n, j <> k →
     mat_entry (finite_coproduct_inj fs) (finite_product_proj fs) u j k
       ≈ zero_mor) →
  u ≈ finite_can fs.
Proof. apply can_matrix_unique. Qed.

End FiniteClassComparison.

(* Strict: at the instances built from [Cartesian]+[Terminal] and
   [Cocartesian]+[Initial], the class-level constructions ARE the
   fold-level ones. *)
Example finite_matrix_is_fin_matrix {C : Category} (CP : @Cartesian C)
  (T : @Terminal C) (CC : @Cocartesian C) (I : @Initial C)
  {m n : nat} (gs : Fin.t m → C) (fs : Fin.t n → C)
  (e : ∀ (j : Fin.t m) (k : Fin.t n), gs j ~> fs k) :
  @finite_matrix C (Cartesian_Terminal_HasFiniteProducts CP T)
    (Cocartesian_Initial_HasFiniteCoproducts CC I) m n gs fs e
  = @fin_matrix C CP T CC I m n gs fs e := eq_refl.

Example finite_can_is_fin_can {C : Category} `{Z : @ZeroObject C}
  (CP : @Cartesian C) (T : @Terminal C) (CC : @Cocartesian C)
  (I : @Initial C) {n : nat} (fs : Fin.t n → C) :
  @finite_can C Z (Cartesian_Terminal_HasFiniteProducts CP T)
    (Cocartesian_Initial_HasFiniteCoproducts CC I) n fs
  = @fin_can C Z CP T CC I n fs := eq_refl.

(** ** Non-vacuity: the matrix construction computes *)

(* [Coq] has finite products and coproducts but no zero object (its initial
   object is [False] and its terminal [unit]), so it witnesses the m x n
   determination and nothing about the identity matrix. *)

Definition coq_succ_matrix :
  ∀ (j k : Fin.t 2), (fun _ : Fin.t 2 => nat : Coq) j
                       ~> (fun _ : Fin.t 2 => nat : Coq) k :=
  fun _ _ => fun x => S x.

Example coq_matrix_computes :
  fin_matrix Coq_Cocartesian Coq_Initial
    (fun _ : Fin.t 2 => nat : Coq) (fun _ : Fin.t 2 => nat : Coq)
    coq_succ_matrix (Datatypes.inl 3%nat) = (4%nat, (4%nat, tt)) := eq_refl.

Example coq_matrix_computes_right :
  fin_matrix Coq_Cocartesian Coq_Initial
    (fun _ : Fin.t 2 => nat : Coq) (fun _ : Fin.t 2 => nat : Coq)
    coq_succ_matrix (Datatypes.inr (Datatypes.inl 7%nat))
      = (8%nat, (8%nat, tt)) := eq_refl.
