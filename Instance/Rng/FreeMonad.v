Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Algebra.Rig.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Rng.Free.

Generalizable All Variables.

(** * The tensor-algebra monad T on Ab, and rings as its algebras *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.4, Exercise 4, printed p. 146 (PDF
         p. 155) — maclane:VI.4:ex4
   Book: Riehl, "Category Theory in Context", Example 5.5.7(ii), printed
         p. 205 (PDF p. 225) — riehl:5.5:example7
   nLab: https://ncatlab.org/nlab/show/tensor+algebra
   nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
   nLab: https://ncatlab.org/nlab/show/monadic+functor

   WHAT THE BOOKS SAY, read from the page image and the PDF.  Mac Lane,
   Exercise 4: "The adjunction ⟨F, G, φ⟩ : Ab ⇀ Rng with G the functor
   "forget the multiplication in a ring" defines a monad T in Ab.  (a)
   Give a direct description of this monad, like that in the text for W,
   with Xⁿ replaced by the n-fold tensor power and coproduct ∐ by the
   (infinite) direct sum of abelian groups.  (b) Give the corresponding
   description of T-algebras and show that the comparison functor from
   rings to T-algebras is an isomorphism."  Riehl, Example 5.5.7(ii):
   "The proof of Corollary 5.5.3 can be adapted to show that the
   forgetful functor U : Ring → Ab is monadic.  The induced monad on Ab is
   the free monoid monad TA := ⨁_{n≥0} A^{⊗n}."  Mac Lane's Rng is the
   rings with identity, Instance/Rng.v's [Rng].  This file is T and part
   (b) through the rings; part (a) is Instance/Ab/TensorPower.v with
   Instance/Rng/FreeMonad/Words.v, and the corresponding description of
   the algebras, Mac Lane's systems ⟨A, ν₀, ν₁, …⟩, is
   Instance/Rng/FreeMonad/System.v.

   THE MONAD.  [TF] is U ◯ F with F Instance/Rng/Free.v's [FreeRngAb]
   (#400, PR #1219) and U [Rng_Forget_Ab]; [TM] is Monad/Comparison.v's
   transparent [Adjunction_Induced_Monad] of Free.v's
   [free_rng_ab_adjunction_hom], the hom-set form of the same adjunction
   that #474 adds to Free.v (same left adjoint and insertion; its unit
   and forward transpose are those of [free_rng_ab_adjunction] at
   [eq_refl]), whose counit is the evaluation of the identity by
   conversion where the universal-arrow form's is not (Free.v's header,
   CORRECTION (#474)).  The hom-set form is not only the way around that
   opacity: it is the book's own presentation, Mac Lane's ⟨F, G, φ⟩
   being an adjunction given by its natural bijection φ (§IV.1), and
   [free_rng_ab_adjunction_hom] is [Build_Adjunction'] applied to exactly
   that φ, Free.v's [free_rng_ab_hom_iso].  No second free ring and no
   second free functor.
   At [eq_refl]: T A is the abelian group of the free ring ([T_obj]), its
   carrier the formal ring expressions [FRTerm A] ([T_carrier]) and its ≈
   [fr_eq] ([T_equiv]); η is the insertion on carriers ([T_ret]),
   a ↦ ⟨a⟩ ([T_ret_fun]); μ = U ε F ([T_join_counit]) evaluates an
   expression of expressions, μ t = fr_eval id t at a variable
   ([T_join_fun]), so it removes the outer brackets: μ⟨t⟩ = t,
   μ(⟨s⟩·⟨t⟩) = s·t, μ(⟨s⟩ + ⟨t⟩) = s + t and μ1 = 1 ([T_join_gen],
   [T_join_mul], [T_join_plus], [T_join_one]).  The monad laws are those
   of the adjunction.  T f relabels the generators at ≈
   ([T_map_relabel]) and is refused at [eq_refl] at a generator and at a
   variable (Test/ProbeFreeRing474.v, R5 and R6): the free functor's
   action on arrows is read through the universal arrows.  η as the whole
   homomorphism record is refused too (R4): it is the composite U id ∘
   insert in Ab, whose proof fields are the composite's.

   ROUTE A, NOT TAKEN.  T as the monad of [free_rng_ab_adjunction]
   itself, the record Free.v already had, costs nothing there and leaves μ
   and the comparison functor's values at ≈: μ at a generator, at a
   variable, at a product and at 1, and the structure map of K R at 1, at
   a product and at a generator are refused at [eq_refl] there (R7 to
   R13; at ≈ they are the controls C19 and C20).  Its cheapest variant,
   turning the two [Qed] layers that block that counit [Defined]
   (Theory/Universal/Arrow.v's [ump_universal_arrows] and Free.v's
   [free_rng_ab_universal]), makes R7 to R13 hold (measured by flipping,
   below), and is not taken here: the first is shared by many
   developments, and issue #1353 tracks it.  Route B, the hom-set form,
   adds six constants to Free.v.

   AN ALGEBRA IS A RING.  For an algebra h : T A → A, [ralg_one α] = h 1
   and [ralg_mul α] a b = h(⟨a⟩·⟨b⟩).  The key lemma [ralg_mul_eval],
   h s ⋆ h t ≈ h(s·t), is one instance of the action law ([ralg_action],
   with T h read as the relabelling); with the unit law ([ralg_unit],
   h⟨a⟩ ≈ a) it gives associativity, both unit laws, both distributive
   laws and both annihilation laws ([ralg_mul_assoc] to
   [ralg_mul_zero_r]), and [ralg_ring α] is the ring on A's own 0, + and
   −, its carrier a set because A's is ([rig_prop] is A's [cmon_prop]).
   h is the evaluation of formal expressions in that ring, "the sum of
   the products", at ≈ ([ralg_fold]).

   Rng ≅ Ab^T (Mac Lane's (b); Riehl's 5.5.7(ii)).  [RngAlg] is Ab^T.
   [Rng_K] is Monad/Comparison.v's [EM_Comparison] of the adjunction:
   K R = ⟨U R, U ε_R⟩, its structure map the evaluation in R ([Rng_K_alg],
   [Rng_K_alg_fun]) with 1 ↦ 1, ⟨a⟩ ↦ a, ⟨a⟩·⟨b⟩ ↦ a·b and ⟨a⟩ + ⟨b⟩ ↦
   a + b ([Rng_K_alg_one], [Rng_K_alg_gen], [Rng_K_alg_mul],
   [Rng_K_alg_plus]), and K f = U f ([Rng_K_map]), all at [eq_refl].
   [EM_to_Rng] sends an algebra to its ring and a map to itself
   ([EM_to_Rng_one], [EM_to_Rng_mul], [EM_to_Rng_add], [EM_to_Rng_map]).
   [Rng_EM_iso : Rng ≅[Cat] RngAlg] has the legs [Rng_K] and [EM_to_Rng]
   ([Rng_EM_iso_to], [Rng_EM_iso_from]) and every component of both
   natural isomorphisms the identity, to and from, at [eq_refl]
   ([Rng_EM_iso_to_from_component], [Rng_EM_iso_from_to_component]).  It
   is built from the two component isomorphisms, as #466, #470 and #471
   build theirs, because through Theory/Equivalence.v's
   [Equivalence_to_Cat_Iso] the component of [iso_from_to] is refused
   (R19) while that of [iso_to_from] holds (C50).  An isomorphism in Cat
   is, by Instance/Cat.v, an equivalence of categories, which the
   identity components bring toward Mac Lane's "isomorphism"; the strict
   identity of the two composites with the identity functors is refused
   (R17, R18).  The ring round trip returns the setoid, 0, +, 1, · and −
   and the maps on the nose ([Rng_rt_setoid] to [Rng_rt_hom]: K R's
   product a·b is the structure map at ⟨a⟩·⟨b⟩, which IS a·b), the whole
   ring being refused (R14) for its law fields alone; the algebra round
   trip keeps the group and the maps ([EM_Rng_rt_carrier],
   [EM_Rng_rt_alg_hom]) and returns the structure map as the evaluation
   in the algebra's ring ([EM_Rng_rt_alg_fun]; at ≈, [ralg_fold]),
   refused at [eq_refl] at a variable (R15) and as the whole algebra
   (R16).  [Rng_EM_equivalence] is the equivalence with the same
   components ([Rng_EM_counit_component], [Rng_EM_unit_component]), and
   [Rng_Forget_Ab_Monadic : Monadic Rng_Forget_Ab] is Riehl's statement,
   in Monad/Comparison.v's sense, by an explicit quasi-inverse; her route
   through Corollary 5.5.3 (Beck) is not reproduced.  [Rng_K_Forget] and
   [EM_to_Rng_Forget] are the commutation with the two forgetful
   functors, the first Monad/Comparison.v's [EM_Comparison_Forget] and
   the second with identity components (both at ≈, read from their
   terms, both [Qed]), at [eq_refl] on objects and on arrows
   ([Rng_K_Forget_obj], [Rng_K_Forget_map], [EM_to_Rng_Forget_obj],
   [EM_to_Rng_Forget_map]).

   THE ISSUE'S PREMISES, dated.  Issue #474 was filed on 2026-07-23.
   Its "no concrete category Ab" and "no Rng" were accurate when filed
   and have been stale since PR #1074 (merged 2026-08-12, [Ab]) and PR
   #1091 (merged 2026-08-14, [Rng]); its dependencies #256, #257 and #310
   were closed on 2026-08-12, 2026-08-14 and 2026-08-18.  "No
   tensor-algebra endofunctor ⨁ₙ A^{⊗n}" held until this change in that
   no such functor was named, though U ◯ F exists since PR #1219 (merged
   2026-08-29); "no Rng → T-Alg comparison" held until this change.
   "Reusing #310's tensor-algebra universal arrow": #310 (PR #1158,
   merged 2026-08-18) delivered the tensor algebra of a module over a
   COMMUTATIVE ring, Instance/Vect/TensorAlgebra.v's [TensorAlg]; the
   universal arrow of Ab ⇀ Rng is #400's (PR #1219), which is what is
   reused.  "Discharge the Monad laws" is supplied by
   [Adjunction_Induced_Monad].  Of the suggested module
   Monad/Instance/TensorAlgebra.v, the directory Monad/Instance does not
   exist; the files are this one, its two satellites and
   Instance/Ab/TensorPower.v.  Its "CLAUDE.md Key Files index" was
   accurate when filed and has been stale since PR #1284 (merged
   2026-09-09), which moved the index to docs/INDEX.md.

   STRENGTHS.  Every [Example] holds at [eq_refl], and
   Test/ProbeFreeRing474.v restates each one (C5 to C15, C21 to C44, C46 to
   C49 and C51 to C54).  Stated at ≈: [T_map_relabel], [ralg_fold], the
   ring laws of an algebra, and the inverse laws of the isomorphism in Cat.
   [T_map_relabel] holds at [eq_refl] once both [Qed] layers behind the
   universal arrows are [Defined] (R5, R6 hold in that flipped copy), so it
   is ≈ here and not ≈ only; [ralg_fold] is at ≈ because an algebra's unit
   law h⟨a⟩ ≈ a is.  Seven proofs end [Defined] (counted by token) and
   fifteen [Qed].  Load-bearing transparency, measured by closing each
   [Defined] of #474's code alone [Qed] in a renamed copy of the five files
   and the probe, and naming the first command that then stops:
   [EM_rng_map] ([EM_to_Rng]), [EM_to_Rng] ([Rng_EM_counit_iso]),
   [Rng_EM_counit_iso] and [Rng_EM_unit_iso] ([Rng_EM_equivalence]),
   [Rng_EM_equivalence] ([Rng_EM_counit_component]) and [Rng_EM_iso]
   ([Rng_EM_iso_to]); [Rng_Forget_Ab_Monadic] is [Defined] by the data
   convention only (closed [Qed], nothing stops).  Thirty-seven of the
   thirty-nine [Defined]s of #474's code are load-bearing in this sense
   (each file's header names its own), the other one being
   Instance/Ab/TensorPower.v's [TW_is_tensor_coproduct].  Every
   refutation of the probe is still refused, and every control accepted, in
   a renamed copy with all ninety-three [Qed]s of #474's code turned
   [Defined], so none is the opacity of #474's own proofs.

   UNIVERSES, read off [About] (every name, by script).  Every name is
   universe polymorphic, in the section [TensorAlgebraMonad] over Ab@{u p}
   and Rng@{u p}, and binds u and p first, with p < u and Set < u, the two
   categories' own bounds; no [Set] but those strict lower bounds, no
   equation in any block, and caps of the standard library's global levels
   only.  A closed @{u p} is refused ("Universes … are unbound", measured
   on the bare composite U ◯ F), so each name declares an extensible
   binder.  Fifty-two names bind six levels: u, p and the four [FreeRngAb]
   carries beyond [Ab]'s ([TF], [TM], the readbacks of T, the ring of an
   algebra, [EM_to_Rng] and the round trips), [Rng_EM_iso] binding instead
   u, p, c (u < c and p < c, from Instance/Cat.v's [Cat@{c u u u p}]) and
   three of the four.  Fifteen bind five, u, p and three of the four:
   [Rng_K] and the fourteen names stated through it.  [T_carrier] and
   [T_equiv] bind seven, the extra level being that of the type at which
   their equation is stated, and five readbacks comparing across a
   composite bind a second copy of three of those four, eight or nine
   in all ([EM_Rng_rt_carrier], [EM_Rng_rt_alg_fun], [EM_Rng_rt_alg_hom],
   [Rng_EM_iso_from_to_component], [Rng_EM_unit_component]).  Compiled on
   Coq 8.19.2 and 8.20.1, each of the 296 names #474 adds binds the same
   levels as on Rocq 9.1.1, the same eleven carry the one equation, and
   [Set] appears only as a strict lower bound, compared by [About] on all
   296 in source overlays: unlike #471's free monoid, [FreeRngAb] binds the
   same levels on every version.  No explicit universe instance of a
   constant #474 adds is written anywhere (a scan of the code of every .v
   file of the tree, comments stripped, finds none).

   NOT DELIVERED.  A strict identity of Rng with Ab^T (refused above) and
   an isomorphism in Instance/StrictCat.v (#484 tracks Beck's theorem
   with an isomorphism conclusion).  A computing T f: the action on
   arrows is [FreeRngAb]'s, and a second free functor computing
   letterwise would be a parallel construction, not taken (the direct
   functor ⨁ₙ (−)^{⊗n} of Words.v computes, is naturally isomorphic to
   T, and carries Words.v's direct monad [TWMonad], isomorphic to T as a
   monad, [T_TW_monad_iso]).  Beck's route to monadicity (Riehl's
   Corollary 5.5.3).  The
   relation to #310's [TensorAlg] (Instance/Vect/TensorAlgebra.v, over a
   commutative ring): comparing it with T at ℤ needs Ab ≅ RMod ℤ, issue
   #1356. *)

Section TensorAlgebraMonad.

Universes u p.

(* ------------------------------------------------------------------------ *)
(** ** T, the monad of the adjunction Ab ⇀ Rng *)

Definition TF@{+} : Ab@{u p} ⟶ Ab@{u p} := Rng_Forget_Ab ◯ FreeRngAb.

Definition TM@{+} : @Monad Ab@{u p} TF :=
  Adjunction_Induced_Monad free_rng_ab_adjunction_hom.

(* T A is the abelian group of formal ring expressions over A. *)
Example T_obj@{+} (A : Ab@{u p}) :
  fobj[TF] A = Rng_Forget_Ab (FreeRngAbObject A) := eq_refl.

Example T_carrier@{+} (A : Ab@{u p}) :
  carrier (cmon_setoid (fobj[TF] A)) = FRTerm A := eq_refl.

Example T_equiv@{+} (A : Ab@{u p}) (s t : FRTerm A) :
  @equiv _ (is_setoid (cmon_setoid (fobj[TF] A))) s t = fr_eq s t
  := eq_refl.

(* η_A is the insertion, as a map of carriers: a ↦ ⟨a⟩. *)
Example T_ret@{+} (A : Ab@{u p}) :
  cmon_map (@ret _ _ TM A) = cmon_map (free_rng_ab_insert A) := eq_refl.

Example T_ret_fun@{+} (A : Ab@{u p}) (a : carrier (cmon_setoid A)) :
  cmon_map (@ret _ _ TM A) a = fr_gen a := eq_refl.

(* μ = U ε F, the evaluation of a formal expression of formal expressions:
   it removes the outer brackets. *)
Example T_join_counit@{+} (A : Ab@{u p}) :
  @join _ _ TM A
    = fmap[Rng_Forget_Ab]
        (@counit _ _ _ _ free_rng_ab_adjunction_hom (FreeRngAb A))
  := eq_refl.

Example T_join_fun@{+} (A : Ab@{u p}) (t : FRTerm (fobj[TF] A)) :
  cmon_map (@join _ _ TM A) t = fr_eval (@id Ab@{u p} (fobj[TF] A)) t
  := eq_refl.

Example T_join_gen@{+} (A : Ab@{u p}) (t : FRTerm A) :
  cmon_map (@join _ _ TM A) (@fr_gen (fobj[TF] A) t) = t := eq_refl.

Example T_join_mul@{+} (A : Ab@{u p}) (s t : FRTerm A) :
  cmon_map (@join _ _ TM A)
    (fr_mul (@fr_gen (fobj[TF] A) s) (@fr_gen (fobj[TF] A) t))
    = fr_mul s t := eq_refl.

Example T_join_plus@{+} (A : Ab@{u p}) (s t : FRTerm A) :
  cmon_map (@join _ _ TM A)
    (fr_plus (@fr_gen (fobj[TF] A) s) (@fr_gen (fobj[TF] A) t))
    = fr_plus s t := eq_refl.

Example T_join_one@{+} (A : Ab@{u p}) :
  cmon_map (@join _ _ TM A) (@fr_one (fobj[TF] A)) = @fr_one A := eq_refl.

(* T f relabels the generators, up to ≈: the action on arrows is
   [FreeRngAb]'s, read through the universal arrows. *)
Lemma T_map_relabel@{+} {A B : Ab@{u p}} (f : A ~{Ab@{u p}}~> B)
  (t : FRTerm A) :
  cmon_map (fmap[TF] f) t ≈ fr_eval (free_rng_ab_insert B ∘[Ab@{u p}] f) t.
Proof.
  apply (free_rng_ab_extend_unique (FreeRngAb B)
           (free_rng_ab_insert B ∘[Ab@{u p}] f) (fmap[FreeRngAb] f)).
  intro a. exact (free_rng_ab_fmap_generators f a).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** An algebra is a ring *)

Definition RngAlg@{+} : Category@{u p p} :=
  @EilenbergMoore@{u u u p} Ab@{u p} TF TM.

Section Alg.

Context {A : Ab@{u p}} (α : @TAlgebra Ab@{u p} TF TM A).

Local Notation h := (cmon_map (t_alg[α])).

Lemma ralg_unit@{+} (a : carrier (cmon_setoid A)) : h (fr_gen a) ≈ a.
Proof. exact (@t_id _ _ _ _ α a). Qed.

(* The action law, with T h read as the relabelling. *)
Lemma ralg_action@{+} (t : FRTerm (fobj[TF] A)) :
  h (fr_eval (free_rng_ab_insert A ∘[Ab@{u p}] t_alg[α]) t)
    ≈ h (fr_eval (@id Ab@{u p} (fobj[TF] A)) t).
Proof.
  transitivity (h (cmon_map (fmap[TF] (t_alg[α])) t)).
  - apply (proper_morphism (cmon_map (t_alg[α]))). symmetry.
    apply T_map_relabel.
  - exact (@t_action _ _ _ _ α t).
Qed.

(* The unit h⟨⟩ = h 1 and the product a ⋆ b = h(⟨a⟩·⟨b⟩). *)
Definition ralg_one@{+} : carrier (cmon_setoid A) := h fr_one.

Definition ralg_mul@{+} (a b : carrier (cmon_setoid A)) :
  carrier (cmon_setoid A) := h (fr_mul (fr_gen a) (fr_gen b)).

(* h(s·t) ≈ h s ⋆ h t: the action law at the expression ⟨s⟩·⟨t⟩ of T T A. *)
Lemma ralg_mul_eval@{+} (s t : FRTerm A) :
  ralg_mul (h s) (h t) ≈ h (fr_mul s t).
Proof.
  exact (ralg_action (fr_mul (@fr_gen (fobj[TF] A) s)
                             (@fr_gen (fobj[TF] A) t))).
Qed.

Lemma ralg_mul_respects@{+} : Proper (equiv ==> equiv ==> equiv) ralg_mul.
Proof.
  intros a a' Ha b b' Hb. unfold ralg_mul.
  apply (proper_morphism (cmon_map (t_alg[α]))).
  exact (fre_mul (fre_gen Ha) (fre_gen Hb)).
Qed.

Lemma ralg_mul_assoc@{+} a b c :
  ralg_mul (ralg_mul a b) c ≈ ralg_mul a (ralg_mul b c).
Proof.
  transitivity (ralg_mul (ralg_mul a b) (h (fr_gen c))).
  { apply ralg_mul_respects; [ reflexivity | symmetry; apply ralg_unit ]. }
  transitivity (h (fr_mul (fr_mul (fr_gen a) (fr_gen b)) (fr_gen c))).
  { exact (ralg_mul_eval (fr_mul (fr_gen a) (fr_gen b)) (fr_gen c)). }
  transitivity (h (fr_mul (fr_gen a) (fr_mul (fr_gen b) (fr_gen c)))).
  { apply (proper_morphism (cmon_map (t_alg[α]))). apply fre_mul_assoc. }
  transitivity (ralg_mul (h (fr_gen a)) (h (fr_mul (fr_gen b) (fr_gen c)))).
  { symmetry. exact (ralg_mul_eval (fr_gen a) (fr_mul (fr_gen b) (fr_gen c))). }
  apply ralg_mul_respects; [ apply ralg_unit | reflexivity ].
Qed.

Lemma ralg_one_l@{+} a : ralg_mul ralg_one a ≈ a.
Proof.
  transitivity (ralg_mul ralg_one (h (fr_gen a))).
  { apply ralg_mul_respects; [ reflexivity | symmetry; apply ralg_unit ]. }
  transitivity (h (fr_mul fr_one (fr_gen a))).
  { exact (ralg_mul_eval fr_one (fr_gen a)). }
  transitivity (h (fr_gen a)).
  { apply (proper_morphism (cmon_map (t_alg[α]))). apply fre_mul_one_l. }
  apply ralg_unit.
Qed.

Lemma ralg_one_r@{+} a : ralg_mul a ralg_one ≈ a.
Proof.
  transitivity (ralg_mul (h (fr_gen a)) ralg_one).
  { apply ralg_mul_respects; [ symmetry; apply ralg_unit | reflexivity ]. }
  transitivity (h (fr_mul (fr_gen a) fr_one)).
  { exact (ralg_mul_eval (fr_gen a) fr_one). }
  transitivity (h (fr_gen a)).
  { apply (proper_morphism (cmon_map (t_alg[α]))). apply fre_mul_one_r. }
  apply ralg_unit.
Qed.

Lemma ralg_distr_l@{+} a b c :
  ralg_mul a (cmon_plus A b c) ≈ cmon_plus A (ralg_mul a b) (ralg_mul a c).
Proof.
  unfold ralg_mul. rewrite <- cmon_map_plus.
  apply (proper_morphism (cmon_map (t_alg[α]))).
  refine (fre_trans (fre_mul (fr_refl _) (fre_gen_plus b c)) _).
  apply fre_distr_l.
Qed.

Lemma ralg_distr_r@{+} a b c :
  ralg_mul (cmon_plus A a b) c ≈ cmon_plus A (ralg_mul a c) (ralg_mul b c).
Proof.
  unfold ralg_mul. rewrite <- cmon_map_plus.
  apply (proper_morphism (cmon_map (t_alg[α]))).
  refine (fre_trans (fre_mul (fre_gen_plus a b) (fr_refl _)) _).
  apply fre_distr_r.
Qed.

Lemma ralg_mul_zero_l@{+} a : ralg_mul (cmon_zero A) a ≈ cmon_zero A.
Proof.
  unfold ralg_mul.
  transitivity (h fr_zero); [ | exact (cmon_map_zero (t_alg[α])) ].
  apply (proper_morphism (cmon_map (t_alg[α]))).
  refine (fre_trans (fre_mul fre_gen_zero (fr_refl _)) _).
  apply fr_mul_zero_l.
Qed.

Lemma ralg_mul_zero_r@{+} a : ralg_mul a (cmon_zero A) ≈ cmon_zero A.
Proof.
  unfold ralg_mul.
  transitivity (h fr_zero); [ | exact (cmon_map_zero (t_alg[α])) ].
  apply (proper_morphism (cmon_map (t_alg[α]))).
  refine (fre_trans (fre_mul (fr_refl _) fre_gen_zero) _).
  apply fr_mul_zero_r.
Qed.

(* The ring of the algebra: A's own 0, + and −, with 1 and ⋆ above.  Its
   carrier is a set because A's is. *)
Definition ralg_rig@{+} : RigObject := {|
  rig_setoid := cmon_setoid A;
  rig_zero := cmon_zero A;
  rig_add := cmon_plus A;
  rig_one := ralg_one;
  rig_mul := ralg_mul;
  rig_add_respects := cmon_plus_respects A;
  rig_mul_respects := ralg_mul_respects;
  rig_add_assoc := cmon_plus_assoc A;
  rig_add_comm := cmon_plus_comm A;
  rig_add_zero_l := cmon_plus_zero_l A;
  rig_mul_assoc := ralg_mul_assoc;
  rig_mul_one_l := ralg_one_l;
  rig_mul_one_r := ralg_one_r;
  rig_distr_l := ralg_distr_l;
  rig_distr_r := ralg_distr_r;
  rig_mul_zero_l := ralg_mul_zero_l;
  rig_mul_zero_r := ralg_mul_zero_r;
  rig_prop := cmon_prop A
|}.

Definition ralg_ring@{+} : RingObject := {|
  ring_rig := ralg_rig;
  ring_neg := ab_neg A;
  ring_neg_respects := ab_neg_respects A;
  ring_neg_l := ab_neg_left A
|}.

(* The structure map IS the evaluation of formal expressions in the ring
   of the algebra, up to ≈: "the sum of the products". *)
Lemma ralg_fold@{+} (t : FRTerm A) :
  fr_eval (R := ralg_ring) (@id Ab@{u p} A) t ≈ h t.
Proof.
  induction t as [ a | | | t1 IH1 t2 IH2 | t IH | t1 IH1 t2 IH2 ]; simpl.
  - symmetry. apply ralg_unit.
  - symmetry. exact (cmon_map_zero (t_alg[α])).
  - reflexivity.
  - rewrite IH1, IH2. symmetry. exact (cmon_map_plus (t_alg[α]) _ _).
  - rewrite IH. symmetry. exact (ab_map_neg (t_alg[α]) _).
  - transitivity (ralg_mul (h t1) (h t2)).
    + apply ralg_mul_respects; assumption.
    + apply ralg_mul_eval.
Qed.

End Alg.

Arguments ralg_one {A} α.
Arguments ralg_mul {A} α a b.
Arguments ralg_rig {A} α.
Arguments ralg_ring {A} α.

(* ------------------------------------------------------------------------ *)
(** ** The comparison functor K and the isomorphism Rng ≅ Ab^T *)

Definition EM_rng_map@{+} {x y : RngAlg} (f : x ~{RngAlg}~> y) :
  ralg_ring (projT2 x) ~{Rng@{u p}}~> ralg_ring (projT2 y).
Proof.
  unshelve refine (@Build_RigHom (ralg_ring (projT2 x)) (ralg_ring (projT2 y))
                    (cmon_map (t_alg_hom[f])) _ _ _ _).
  - exact (cmon_map_zero (t_alg_hom[f])).
  - exact (cmon_map_plus (t_alg_hom[f])).
  - simpl. unfold ralg_one.
    transitivity (cmon_map (t_alg[projT2 y])
                    (cmon_map (fmap[TF] (t_alg_hom[f])) fr_one)).
    + exact (@t_alg_hom_commutes _ _ _ _ _ _ _ f fr_one).
    + apply (proper_morphism (cmon_map (t_alg[projT2 y]))).
      exact (rig_map_one (fmap[FreeRngAb] (t_alg_hom[f]))).
  - intros a b. simpl. unfold ralg_mul.
    transitivity (cmon_map (t_alg[projT2 y])
                    (cmon_map (fmap[TF] (t_alg_hom[f]))
                       (fr_mul (fr_gen a) (fr_gen b)))).
    + exact (@t_alg_hom_commutes _ _ _ _ _ _ _ f
               (fr_mul (fr_gen a) (fr_gen b))).
    + apply (proper_morphism (cmon_map (t_alg[projT2 y]))).
      exact (T_map_relabel (t_alg_hom[f]) (fr_mul (fr_gen a) (fr_gen b))).
Defined.

Definition EM_to_Rng@{+} : RngAlg ⟶ Rng@{u p}.
Proof.
  unshelve refine
    (@Build_Functor RngAlg Rng@{u p} (fun x => ralg_ring (projT2 x))
       (fun x y f => EM_rng_map f) _ _ _).
  - intros x y f g H. exact H.
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(* The comparison functor K : Rng → Ab^T, K R = ⟨U R, U ε_R⟩. *)
Definition Rng_K@{+} : Rng@{u p} ⟶ RngAlg :=
  EM_Comparison free_rng_ab_adjunction_hom.

(* The algebra round trip, with the identity as its component. *)
Definition Rng_EM_counit_iso@{+} (x : RngAlg) :
  @Isomorphism RngAlg (fobj[Rng_K ◯ EM_to_Rng] x) x.
Proof.
  unshelve refine
    (@Build_Isomorphism RngAlg (fobj[Rng_K ◯ EM_to_Rng] x) x
       (@Build_TAlgebraHom Ab@{u p} TF TM (projT1 x) (projT1 x)
          (projT2 (fobj[Rng_K ◯ EM_to_Rng] x)) (projT2 x)
          (@id Ab@{u p} (projT1 x)) _)
       (@Build_TAlgebraHom Ab@{u p} TF TM (projT1 x) (projT1 x)
          (projT2 x) (projT2 (fobj[Rng_K ◯ EM_to_Rng] x))
          (@id Ab@{u p} (projT1 x)) _) _ _).
  - intro t. simpl.
    transitivity (cmon_map (t_alg[projT2 x]) t);
      [ exact (ralg_fold (projT2 x) t) | ].
    apply (proper_morphism (cmon_map (t_alg[projT2 x]))).
    symmetry. exact (@fmap_id _ _ TF (projT1 x) t).
  - intro t. simpl.
    transitivity (cmon_map (t_alg[projT2 x]) (cmon_map (fmap[TF] id) t)).
    + apply (proper_morphism (cmon_map (t_alg[projT2 x]))).
      symmetry. exact (@fmap_id _ _ TF (projT1 x) t).
    + symmetry. exact (ralg_fold (projT2 x) _).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The ring round trip, with the identity as its component: every
   operation comes back on the nose. *)
Definition Rng_EM_unit_iso@{+} (R : Rng@{u p}) :
  @Isomorphism Rng@{u p} (fobj[EM_to_Rng ◯ Rng_K] R) R.
Proof.
  unshelve refine
    (@Build_Isomorphism Rng@{u p} (fobj[EM_to_Rng ◯ Rng_K] R) R
       (@Build_RigHom (fobj[EM_to_Rng ◯ Rng_K] R) R
          (@setoid_morphism_id (rig_setoid R)) _ _ _ _)
       (@Build_RigHom R (fobj[EM_to_Rng ◯ Rng_K] R)
          (@setoid_morphism_id (rig_setoid R)) _ _ _ _) _ _);
    simpl; intros; reflexivity.
Defined.

(* K is an equivalence, with identity components both ways. *)
Definition Rng_EM_equivalence@{+} :
  @EquivalenceOfCategories@{u u u u u p} Rng@{u p} RngAlg Rng_K.
Proof.
  unshelve refine (@Build_EquivalenceOfCategories _ _ Rng_K EM_to_Rng _ _).
  - exists (fun x => Rng_EM_counit_iso x).
    intros x y f a. reflexivity.
  - exists (fun R => iso_sym (Rng_EM_unit_iso R)).
    intros R S f a. reflexivity.
Defined.

(* Riehl, Example 5.5.7(ii): the forgetful functor Rng → Ab is monadic. *)
Definition Rng_Forget_Ab_Monadic@{+} :
  @Monadic@{u u u u u p u u} Rng@{u p} Ab@{u p} Rng_Forget_Ab.
Proof.
  exists FreeRngAb.
  exists free_rng_ab_adjunction_hom.
  exact Rng_EM_equivalence.
Defined.

(* Mac Lane's "the comparison functor from rings to T-algebras is an
   isomorphism": Rng ≅ Ab^T in Cat, from the two component isomorphisms. *)
Definition Rng_EM_iso@{c +} :
  @Isomorphism Cat@{c u u u p} Rng@{u p} RngAlg.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{c u u u p} Rng@{u p} RngAlg Rng_K EM_to_Rng _ _).
  - exists (fun x => Rng_EM_counit_iso x).
    intros x y f a. reflexivity.
  - exists (fun R => Rng_EM_unit_iso R).
    intros R S f a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Commuting with the forgetful functors *)

Definition RngAlg_Forget@{+} : RngAlg ⟶ Ab@{u p} :=
  @EM_Forget Ab@{u p} TF TM.

Theorem Rng_K_Forget@{+} : RngAlg_Forget ◯ Rng_K ≈ Rng_Forget_Ab.
Proof. exact (EM_Comparison_Forget free_rng_ab_adjunction_hom). Qed.

Theorem EM_to_Rng_Forget@{+} : Rng_Forget_Ab ◯ EM_to_Rng ≈ RngAlg_Forget.
Proof.
  exists (fun x => iso_id).
  intros x y f a. reflexivity.
Qed.

Example Rng_K_Forget_obj@{+} (R : Rng@{u p}) :
  fobj[RngAlg_Forget] (fobj[Rng_K] R) = fobj[Rng_Forget_Ab] R := eq_refl.

Example Rng_K_Forget_map@{+} {R S : Rng@{u p}} (f : R ~{Rng@{u p}}~> S) :
  fmap[RngAlg_Forget] (fmap[Rng_K] f) = fmap[Rng_Forget_Ab] f := eq_refl.

Example EM_to_Rng_Forget_obj@{+} (x : RngAlg) :
  fobj[Rng_Forget_Ab] (fobj[EM_to_Rng] x) = fobj[RngAlg_Forget] x
  := eq_refl.

Example EM_to_Rng_Forget_map@{+} {x y : RngAlg} (f : x ~{RngAlg}~> y) :
  fmap[Rng_Forget_Ab] (fmap[EM_to_Rng] f) = fmap[RngAlg_Forget] f
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks *)

(* The two legs of the isomorphism in Cat are the two functors. *)
Example Rng_EM_iso_to@{+} : to Rng_EM_iso = Rng_K := eq_refl.

Example Rng_EM_iso_from@{+} : from Rng_EM_iso = EM_to_Rng := eq_refl.

(* K R = ⟨U R, U ε_R⟩: the structure map evaluates formal expressions in
   R, and so sends 1, ⟨a⟩, ⟨a⟩·⟨b⟩ and ⟨a⟩ + ⟨b⟩ to 1, a, a·b and a + b. *)
Example Rng_K_carrier@{+} (R : Rng@{u p}) :
  projT1 (fobj[Rng_K] R) = Rng_Forget_Ab R := eq_refl.

Example Rng_K_alg@{+} (R : Rng@{u p}) :
  t_alg[projT2 (fobj[Rng_K] R)]
    = fmap[Rng_Forget_Ab] (@counit _ _ _ _ free_rng_ab_adjunction_hom R)
  := eq_refl.

Example Rng_K_alg_fun@{+} (R : Rng@{u p}) (t : FRTerm (Rng_Forget_Ab R)) :
  cmon_map (t_alg[projT2 (fobj[Rng_K] R)]) t
    = fr_eval (@id Ab@{u p} (Rng_Forget_Ab R)) t := eq_refl.

Example Rng_K_alg_one@{+} (R : Rng@{u p}) :
  cmon_map (t_alg[projT2 (fobj[Rng_K] R)]) (@fr_one (Rng_Forget_Ab R))
    = rig_one R := eq_refl.

Example Rng_K_alg_gen@{+} (R : Rng@{u p}) (a : carrier (rig_setoid R)) :
  cmon_map (t_alg[projT2 (fobj[Rng_K] R)]) (@fr_gen (Rng_Forget_Ab R) a) = a
  := eq_refl.

Example Rng_K_alg_mul@{+} (R : Rng@{u p}) (a b : carrier (rig_setoid R)) :
  cmon_map (t_alg[projT2 (fobj[Rng_K] R)])
    (fr_mul (@fr_gen (Rng_Forget_Ab R) a) (@fr_gen (Rng_Forget_Ab R) b))
    = rig_mul R a b := eq_refl.

Example Rng_K_alg_plus@{+} (R : Rng@{u p}) (a b : carrier (rig_setoid R)) :
  cmon_map (t_alg[projT2 (fobj[Rng_K] R)])
    (fr_plus (@fr_gen (Rng_Forget_Ab R) a) (@fr_gen (Rng_Forget_Ab R) b))
    = rig_add R a b := eq_refl.

Example Rng_K_map@{+} {R S : Rng@{u p}} (f : R ~{Rng@{u p}}~> S) :
  t_alg_hom[fmap[Rng_K] f] = fmap[Rng_Forget_Ab] f := eq_refl.

(* The ring of an algebra: 1 = h 1, a·b = h(⟨a⟩·⟨b⟩), and A's own +. *)
Example EM_to_Rng_one@{+} (x : RngAlg) :
  rig_one (fobj[EM_to_Rng] x) = cmon_map (t_alg[projT2 x]) fr_one
  := eq_refl.

Example EM_to_Rng_mul@{+} (x : RngAlg)
  (a b : carrier (cmon_setoid (projT1 x))) :
  rig_mul (fobj[EM_to_Rng] x) a b
    = cmon_map (t_alg[projT2 x]) (fr_mul (fr_gen a) (fr_gen b)) := eq_refl.

Example EM_to_Rng_add@{+} (x : RngAlg) :
  rig_add (fobj[EM_to_Rng] x) = cmon_plus (projT1 x) := eq_refl.

Example EM_to_Rng_map@{+} {x y : RngAlg} (f : x ~{RngAlg}~> y) :
  rig_map (fmap[EM_to_Rng] f) = cmon_map (t_alg_hom[f]) := eq_refl.

(* The ring round trip returns every operation and every map on the
   nose. *)
Example Rng_rt_setoid@{+} (R : Rng@{u p}) :
  rig_setoid (fobj[EM_to_Rng ◯ Rng_K] R) = rig_setoid R := eq_refl.

Example Rng_rt_zero@{+} (R : Rng@{u p}) :
  rig_zero (fobj[EM_to_Rng ◯ Rng_K] R) = rig_zero R := eq_refl.

Example Rng_rt_add@{+} (R : Rng@{u p}) :
  rig_add (fobj[EM_to_Rng ◯ Rng_K] R) = rig_add R := eq_refl.

Example Rng_rt_one@{+} (R : Rng@{u p}) :
  rig_one (fobj[EM_to_Rng ◯ Rng_K] R) = rig_one R := eq_refl.

Example Rng_rt_mul@{+} (R : Rng@{u p}) (a b : carrier (rig_setoid R)) :
  rig_mul (fobj[EM_to_Rng ◯ Rng_K] R) a b = rig_mul R a b := eq_refl.

Example Rng_rt_neg@{+} (R : Rng@{u p}) :
  ring_neg (fobj[EM_to_Rng ◯ Rng_K] R) = ring_neg R := eq_refl.

Example Rng_rt_hom@{+} {R S : Rng@{u p}} (f : R ~{Rng@{u p}}~> S) :
  rig_map (fmap[EM_to_Rng ◯ Rng_K] f) = rig_map f := eq_refl.

(* The algebra round trip keeps the group and the maps on the nose, and
   returns the structure map as the evaluation in the algebra's ring. *)
Example EM_Rng_rt_carrier@{+} (x : RngAlg) :
  projT1 (fobj[Rng_K ◯ EM_to_Rng] x) = projT1 x := eq_refl.

Example EM_Rng_rt_alg_fun@{+} (x : RngAlg) (t : FRTerm (projT1 x)) :
  cmon_map (t_alg[projT2 (fobj[Rng_K ◯ EM_to_Rng] x)]) t
    = fr_eval (R := ralg_ring (projT2 x)) (@id Ab@{u p} (projT1 x)) t
  := eq_refl.

Example EM_Rng_rt_alg_hom@{+} {x y : RngAlg} (f : x ~{RngAlg}~> y) :
  t_alg_hom[fmap[Rng_K ◯ EM_to_Rng] f] = t_alg_hom[f] := eq_refl.

(* Every component of the two natural isomorphisms is the identity, at a
   variable object, to and from. *)
Example Rng_EM_iso_to_from_component@{+} (x : RngAlg) :
  (t_alg_hom[to (projT1 (iso_to_from Rng_EM_iso) x)],
   t_alg_hom[from (projT1 (iso_to_from Rng_EM_iso) x)])
    = (@id Ab@{u p} (projT1 x), @id Ab@{u p} (projT1 x)) := eq_refl.

Example Rng_EM_iso_from_to_component@{+} (R : Rng@{u p}) :
  (rig_map (to (projT1 (iso_from_to Rng_EM_iso) R)),
   rig_map (from (projT1 (iso_from_to Rng_EM_iso) R)))
    = (@setoid_morphism_id (rig_setoid R),
       @setoid_morphism_id (rig_setoid R)) := eq_refl.

Example Rng_EM_counit_component@{+} (x : RngAlg) :
  (t_alg_hom[to (projT1 (@equivalence_counit _ _ _ Rng_EM_equivalence) x)],
   t_alg_hom[from (projT1 (@equivalence_counit _ _ _
                             Rng_EM_equivalence) x)])
    = (@id Ab@{u p} (projT1 x), @id Ab@{u p} (projT1 x)) := eq_refl.

Example Rng_EM_unit_component@{+} (R : Rng@{u p}) :
  (rig_map (to (projT1 (@equivalence_unit _ _ _ Rng_EM_equivalence) R)),
   rig_map (from (projT1 (@equivalence_unit _ _ _ Rng_EM_equivalence) R)))
    = (@setoid_morphism_id (rig_setoid R),
       @setoid_morphism_id (rig_setoid R)) := eq_refl.

End TensorAlgebraMonad.
