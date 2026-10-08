Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Absolute.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Mon.Coproduct.
Require Import Category.Instance.Mon.Free.
Require Import Category.Instance.Mon.Word.

Generalizable All Variables.

(** * Every monoid is a coequalizer of free monoids *)

(* Book:   Awodey, "Category Theory", 1st ed., Carnegie Mellon pre-print,
           September 2005, §3.4, Proposition 3.22 and its proof, printed
           pp. 74-75 (PDF pp. 83-84), item awodey:3.4:prop22; §3.5,
           Exercise 3, printed p. 76 (PDF p. 85), item awodey:3:ex3;
           read from the page images
   nLab:   https://ncatlab.org/nlab/show/monadic+functor
   nLab:   https://ncatlab.org/nlab/show/split+coequalizer
   Wikipedia: https://en.wikipedia.org/wiki/Free_monoid

   WHAT THE BOOK SAYS.  Proposition 3.22: "For every monoid M there are
   sets G and R and a coequalizer diagram, F(R) ⇉ F(G) → M, with F(G)
   and F(R) free, thus M ≅ F(G)/(r₁ = r₂)."  The proof writes
   TN = M(|N|) and π : TN → N, π(x₁, …, xₙ) = x₁ · … · xₙ, and takes
   T²M ⇉ TM → M with the arrows ε and μ = Tπ: "ε uses the multiplication
   in TM and μ uses that in M"; for h : TM → N with hε = hμ it defines
   h̄ = h ∘ i, i : |M| → |TM| the insertion of generators, and leaves "an
   easy exercise for the reader to show that h̄ is a homomorphism".
   Exercise 3: "Show that coequalizers of this particular form are
   preserved by the forgetful functor Mon → Sets."

   NAMES.  T is F U for Instance/Mon/Free.v's free monoid [FreeMonSets]
   and [Mon_Forget] at Theory/Algebra/Monoid/Hom.v's [Mon] at
   (Sets, ×), through the hom-set form of the adjunction,
   [free_mon_sets_adjunction_hom], whose counit is the fold at
   [eq_refl].  Awodey's π is the counit at M, [Mon_evaluate]; his ε is
   the counit at TM, [Mon_flatten], concatenation; his μ is Tπ,
   [Mon_free_evaluate], evaluation of each inner word.  His μ is not the
   monad's multiplication: that one is U of his ε (Instance/Mon/Word.v's
   [W0_join_counit]), so the descriptive names are used.  His G and R
   are |M| and |TM|.

   WHAT IS HERE.
     - [Mon_canonical_presentation]: Proposition 3.22, in [Mon].  The
       cofork is counit naturality, Monad/Monadicity/Crude.v's
       [crude_unit_cofork]; the descent is h ∘ i, [Mon_canonical_desc],
       whose homomorphism laws are the cofork read at the words of words
       [[x, y]] and [[]] (the book's exercise); uniqueness on elements.
     - [Mon_presented_iso]: "thus M ≅ F(G)/(r₁ = r₂)": any coequalizer
       of the pair is isomorphic to M (Structure/Coequalizer.v's
       [coequalizer_unique]).
     - [Mon_canonical_split]: the U-image of the fork is split by the
       units, s = η_{UM} and t = η_{UTM}.  It IS
       Monad/Monadicity/BeckObjects.v's [canonical_split] at the
       W₀-algebra K M = ⟨UM, Uπ⟩ (Word.v's [Mon_K]), with no transport:
       W₀'s μ is U ε F and K M's structure map is U π, both by
       conversion.
     - [Mon_canonical_U_IsCoequalizer]: Exercise 3, U carries the
       coequalizer to a coequalizer, by Mac Lane's Lemma
       (Structure/Coequalizer/Split.v's [split_coequalizer_is_coequalizer]);
       [Mon_canonical_U_AbsoluteCoequalizer]: so does every functor out
       of Sets after U.

   ROUTE.  Taken: the coequalizer directly in [Mon], the splitting
   downstairs reused from BeckObjects.v.  Not taken: the Eilenberg-Moore
   side, through BeckObjects.v's [em_forget_creates_split] at
   [canonical_split], which coequalizes the pair in W₀-algebras at a
   created algebra on UM whose action agrees with U π only at ≈
   ([created_alg_unique]); its cheapest variant would add Beck.v's
   [coequalizer_along_iso] against the comparison with K M and a
   transport of the coequalizer along Word.v's [Mon_EM_equivalence],
   whose functor is [Mon_K].  It was not built, so its size is not
   measured.

   STRENGTHS.  At [eq_refl]: ε concatenates ([Mon_flatten_fun], the
   [wconcat] of Word.v); π folds ([Mon_evaluate_fun]); the descent of h
   is x ↦ h⟨x⟩ ([Mon_canonical_desc_fun]); the splitting's object, e,
   s and t ([Mon_canonical_split_obj], [Mon_canonical_split_e],
   [Mon_canonical_split_s], [Mon_canonical_split_t]).  At ≈ only: μ
   evaluates each inner word, refused at [eq_refl] at a variable word of
   words (Test/ProbeQuotient479.v, R5; at ≈, C12): the free functor's
   action on arrows is read through universal arrows (Instance/Mon/
   Free.v's header), where ε computes (C11).

   UNIVERSES, by [About] on each of the 22 declaration heads (a script).
   The section binds Sets@{o so} as Word.v's [W0Monad] does; every name
   declares an extensible binder, the free functor's levels being
   unbound in a closed one (Word.v's measurement), and binds o and so
   first, with "o < so".  [Mon_flatten], [Mon_free_evaluate] and
   [Mon_flatten_fun] bind two copies of the free functor's three levels,
   unidentified; [Mon_canonical_presentation] identifies them.  On Coq
   8.19.2 and 8.20.1 ([About] in a build of the files' closure under
   each) each of the 22 binds exactly one level more, as Free.v's
   PORTABILITY note measures for [FreeMonSets] itself.
   No block carries an equation or mentions [Set].
   [Mon_canonical_U_AbsoluteCoequalizer] names its target levels xo xh,
   as the group file's twin does.  No explicit universe instance of a
   constant of the free-functor route is written, its binder count
   differing by version.

   STALE PREMISES, dated from gh.  The Prop. 3.22 block (appended
   2026-07-23; its checkbox 2026-08-01) says "(no category Mon, no
   free-monoid monad)": the first half was stale when appended,
   Theory/Algebra/Monoid/Hom.v's [Mon] and [Mon_Forget] having come with
   PR #191 (merged 2026-07-07), as the factual correction added with the
   checkbox says; the second was accurate when appended and is stale
   since PR #1355 (merged 2026-10-08, #471, Word.v's W₀).  The dates
   are the issue's edit history's: the block 2026-07-23T19:04Z, the
   checkbox with the correction 2026-08-01T12:37Z.  The Exercise 3
   block (appended 2026-07-23) says "Missing only the concrete
   forgetful functor Mon → Sets": stale when appended, by the same
   PR #191.  That block credits the preservation to Split.v's
   [functor_preserves_split]; the fork is split only after U, and what
   makes U's image a coequalizer is Mac Lane's Lemma,
   [split_coequalizer_is_coequalizer], while [functor_preserves_split]
   carries the split image on to functors out of Sets.  Both blocks
   cite files by line; this one cites names.

   NOT DELIVERED.  The group case ("an analogous version ... also holds
   for groups") with its splitting: Instance/Grp/Colimit/Presentation.v
   proves the coequalizer in Grp ([Grp_canonical_presentation]) and not
   the splitting.  Presentations other than the canonical one (Awodey's
   Example 3.20 and Warning 3.21), which #663 tracks.  The
   Eilenberg-Moore route above.  A statement for every monadic
   adjunction, not attempted here: #483's appended Riehl §5.4 block,
   Corollary 5.4.10(ii), asks for exactly that counit presentation, and
   [Mon_canonical_presentation] and [Grp_canonical_presentation] are two
   hand instances of it (the cofork by counit naturality, the descent on
   one-letter words, its homomorphism laws from the cofork at words of
   words). *)

Section MonPresentation.

Universes o so.

Local Notation MonOS :=
  (@Mon@{so o so so} Sets@{o so} Sets_Product_Monoidal@{so o}).
Local Notation UMonOS :=
  (@Mon_Forget@{so o so so} Sets@{o so} Sets_Product_Monoidal@{so o}).

(* Awodey's ε : T²M → TM, "using the multiplication in TM": the counit at
   the free monoid TM, which concatenates a word of words. *)
Definition Mon_flatten@{+} (M : MonOS) :
  FreeMonSets (UMonOS (FreeMonSets (UMonOS M)))
    ~{MonOS}~> FreeMonSets (UMonOS M) :=
  @counit _ _ _ _ free_mon_sets_adjunction_hom (FreeMonSets (UMonOS M)).

(* Awodey's μ = Tπ, "using the multiplication in M": the free map of the
   evaluation, which evaluates each inner word. *)
Definition Mon_free_evaluate@{+} (M : MonOS) :
  FreeMonSets (UMonOS (FreeMonSets (UMonOS M)))
    ~{MonOS}~> FreeMonSets (UMonOS M) :=
  fmap[FreeMonSets]
    (fmap[UMonOS] (@counit _ _ _ _ free_mon_sets_adjunction_hom M)).

(* Awodey's π : TM → M, the evaluation (x₁, …, xₙ) ↦ x₁ ⋯ xₙ. *)
Definition Mon_evaluate@{+} (M : MonOS) :
  FreeMonSets (UMonOS M) ~{MonOS}~> M :=
  @counit _ _ _ _ free_mon_sets_adjunction_hom M.

(* π coforks the pair: naturality of the counit, as Monad/Monadicity/
   Crude.v's [crude_unit_cofork] states it for any adjunction. *)
Lemma Mon_canonical_cofork@{+} (M : MonOS) :
  Mon_evaluate M ∘ Mon_flatten M ≈ Mon_evaluate M ∘ Mon_free_evaluate M.
Proof. exact (crude_unit_cofork free_mon_sets_adjunction_hom M). Qed.

(* Two monoid maps out of a free monoid that agree on the letters agree. *)
Lemma Mon_free_hom_ext@{+} {X : obj[Sets@{o so}]} {L : MonOS}
  (g1 g2 : FreeMonSets X ~{MonOS}~> L) :
  (∀ a : X, mon_fun g1 (word1 a) ≈ mon_fun g2 (word1 a)) → g1 ≈ g2.
Proof.
  intros Hg l.
  transitivity (free_mon_extend (L := L) (fun a => mon_fun g2 (word1 a)) l).
  - exact (free_mon_extend_unique _ g1 Hg l).
  - symmetry.
    apply (free_mon_extend_unique _ g2).
    intro a; reflexivity.
Qed.

(** ** The descent: k ↦ k ∘ i, Awodey's h̄ = h ∘ i *)

Section Descent.

Context (M : MonOS) {c : MonOS}.
Context (k : FreeMonSets (UMonOS M) ~{MonOS}~> c).
Context (Hk : k ∘ Mon_flatten M ≈ k ∘ Mon_free_evaluate M).

(* The cofork read at the word of words [[x, y]]: k⟨x y⟩ ≈ k⟨x(y·1)⟩. *)
Lemma Mon_canonical_desc_mul@{+} (x y : mon_ob M) :
  mon_fun k (word1 (mon_mul M x y))
    ≈ mon_mul c (mon_fun k (word1 x)) (mon_fun k (word1 y)).
Proof using Hk.
  transitivity (mon_fun k (word1 (mon_mul M x (mon_mul M y (mon_one M))))).
  { apply (mon_fun_resp k).
    refine (we_cons _ _ _ _ _ we_nil).
    apply (mon_mul_resp M); [ reflexivity |].
    symmetry; apply mon_one_r. }
  transitivity (mon_fun k
                  (mon_fun (Mon_free_evaluate M) (word1 (word2 x y)))).
  { apply (mon_fun_resp k).
    symmetry.
    exact (free_mon_fmap_is_wmap
             (fmap[UMonOS] (@counit _ _ _ _ free_mon_sets_adjunction_hom M))
             (word1 (word2 x y))). }
  transitivity (mon_fun k (mon_fun (Mon_flatten M) (word1 (word2 x y)))).
  { symmetry; exact (Hk (word1 (word2 x y))). }
  exact (mon_fun_mul k (word1 x) (word1 y)).
Qed.

(* The cofork read at [[]]: k⟨1⟩ ≈ k⟨⟩ ≈ 1. *)
Lemma Mon_canonical_desc_one@{+} :
  mon_fun k (word1 (mon_one M)) ≈ mon_one c.
Proof using Hk.
  transitivity (mon_fun k (mon_fun (Mon_free_evaluate M) (word1 word0))).
  { apply (mon_fun_resp k).
    symmetry.
    exact (free_mon_fmap_is_wmap
             (fmap[UMonOS] (@counit _ _ _ _ free_mon_sets_adjunction_hom M))
             (word1 word0)). }
  transitivity (mon_fun k (mon_fun (Mon_flatten M) (word1 word0))).
  { symmetry; exact (Hk (word1 word0)). }
  exact (mon_fun_one k).
Qed.

Definition Mon_canonical_desc@{+} : M ~{MonOS}~> c :=
  @mk_mon_hom M c (fun x => mon_fun k (word1 x))
    (fun x x' H => mon_fun_resp k _ _ (we_cons _ _ _ _ H we_nil))
    Mon_canonical_desc_mul Mon_canonical_desc_one.

Lemma Mon_canonical_desc_commutes@{+} :
  Mon_canonical_desc ∘ Mon_evaluate M ≈ k.
Proof using Hk.
  apply Mon_free_hom_ext; intro a.
  apply (mon_fun_resp k).
  exact (we_cons _ _ _ _ (mon_one_r M a) we_nil).
Qed.

Lemma Mon_canonical_desc_unique@{+} (v : M ~{MonOS}~> c) :
  v ∘ Mon_evaluate M ≈ k → Mon_canonical_desc ≈ v.
Proof.
  intros Hv x.
  transitivity (mon_fun v (mon_mul M x (mon_one M))).
  - symmetry; exact (Hv (word1 x)).
  - apply (mon_fun_resp v).
    apply mon_one_r.
Qed.

End Descent.

(** ** Awodey, Proposition 3.22 *)

Definition Mon_canonical_presentation@{+} (M : MonOS) :
  IsCoequalizer (Mon_flatten M) (Mon_free_evaluate M) M (Mon_evaluate M).
Proof.
  unshelve econstructor.
  - exact (Mon_canonical_cofork M).
  - intros c k Hk.
    exact {| unique_obj      := Mon_canonical_desc M k Hk;
             unique_property := Mon_canonical_desc_commutes M k Hk;
             uniqueness      := Mon_canonical_desc_unique M k Hk |}.
Defined.

(* "Thus M ≅ F(G)/(r₁ = r₂)": any coequalizer of the pair is M. *)
Definition Mon_presented_iso@{+} (M : MonOS) {q : MonOS}
  {e : FreeMonSets (UMonOS M) ~{MonOS}~> q}
  (E : IsCoequalizer (Mon_flatten M) (Mon_free_evaluate M) q e) :
  M ≅[MonOS] q :=
  coequalizer_unique _ _ (Mon_canonical_presentation M) E.

(** ** Awodey, §3.5 Exercise 3: the forgetful functor preserves it *)

(* The U-image of the fork is split by units: s = η_{UM}, t = η_{UTM}.
   It IS BeckObjects.v's canonical presentation of the W₀-algebra
   K M = ⟨UM, Uπ⟩, with no transport: μ = U ε F and K M's structure map
   is U π, both by conversion. *)
Definition Mon_canonical_split@{+} (M : MonOS) :
  SplitCoequalizer (fmap[UMonOS] (Mon_flatten M))
                   (fmap[UMonOS] (Mon_free_evaluate M)) :=
  @canonical_split Sets@{o so} W0F W0 (UMonOS M) (projT2 (fobj[Mon_K] M)).

Definition Mon_canonical_U_IsCoequalizer@{+} (M : MonOS) :
  IsCoequalizer (fmap[UMonOS] (Mon_flatten M))
    (fmap[UMonOS] (Mon_free_evaluate M)) (UMonOS M)
    (fmap[UMonOS] (Mon_evaluate M)) :=
  split_coequalizer_is_coequalizer _ _ (Mon_canonical_split M).

(* Indeed every functor out of Sets preserves it. *)
Definition Mon_canonical_U_AbsoluteCoequalizer@{xo xh +} (M : MonOS) :
  AbsoluteCoequalizer@{_ _ xo xh _} (fmap[UMonOS] (Mon_flatten M))
    (fmap[UMonOS] (Mon_free_evaluate M)) (UMonOS M)
    (fmap[UMonOS] (Mon_evaluate M)) :=
  split_coequalizer_absolute (Mon_canonical_split M).

(** ** Readbacks *)

Example Mon_flatten_fun@{+} (M : MonOS)
  (ww : list (list (mon_ob M))) :
  mon_fun (Mon_flatten M) ww = wconcat ww := eq_refl.

Example Mon_evaluate_fun@{+} (M : MonOS) (l : list (mon_ob M)) :
  mon_fun (Mon_evaluate M) l = free_mon_extend (fun x => x) l := eq_refl.

Example Mon_canonical_desc_fun@{+} (M : MonOS) {c : MonOS}
  (k : FreeMonSets (UMonOS M) ~{MonOS}~> c)
  (Hk : k ∘ Mon_flatten M ≈ k ∘ Mon_free_evaluate M) (x : mon_ob M) :
  mon_fun (unique_obj (coeq_desc (Mon_canonical_presentation M) k Hk)) x
    = mon_fun k (word1 x) := eq_refl.

Example Mon_canonical_split_obj@{+} (M : MonOS) :
  scoeq_obj (Mon_canonical_split M) = UMonOS M := eq_refl.

Example Mon_canonical_split_e@{+} (M : MonOS) :
  scoeq_e (Mon_canonical_split M) = fmap[UMonOS] (Mon_evaluate M) := eq_refl.

Example Mon_canonical_split_s@{+} (M : MonOS) :
  scoeq_s (Mon_canonical_split M) = free_mon_insert (UMonOS M) := eq_refl.

Example Mon_canonical_split_t@{+} (M : MonOS) :
  scoeq_t (Mon_canonical_split M)
    = free_mon_insert (UMonOS (FreeMonSets (UMonOS M))) := eq_refl.

End MonPresentation.
