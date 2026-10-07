Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Structure.Monoidal.
Require Import Category.Theory.Algebra.Semigroup.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Comparison.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Smgrp.

Generalizable All Variables.

(** * The word monad W, its algebras, and the monadicity of Smgrp *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.4 "Words and Free Semigroups", printed
         pp. 144-146 (PDF pp. 153-155): Proposition 1, pp. 144-145 —
         maclane:VI.4:prop1; Proposition 2, p. 145 — maclane:VI.4:prop2;
         the Corollary, p. 146 — maclane:VI.4:cor1; the remark on the
         comparison functor, p. 146 — maclane:VI.4:remark1
   nLab: https://ncatlab.org/nlab/show/monadic+functor
   nLab: https://ncatlab.org/nlab/show/algebra+over+a+monad
   nLab: https://ncatlab.org/nlab/show/free+monoid

   WHAT THE BOOK SAYS, read from the page images.
     Proposition 1 (→· transliterates the page's dotted arrow of a
     natural transformation, as Monad/Eilenberg/Moore/Limit.v does, and
     ⇀ its arrow of an adjunction): "The monad on Set determined by the
     adjunction Set ⇀ Smgrp is
     W = ⟨W : Set → Set, η : I →· W, μ : W² →· W⟩ where
     WX = ∐_{n=1}^∞ Xⁿ, η_X x = ⟨x⟩ for each x ∈ X, while μ_X is
     μ_X(⟨⟨x11⟩ … ⟨x1n1⟩⟩ … ⟨⟨xk1⟩ … ⟨xknk⟩⟩) = ⟨x11⟩ … ⟨x1n1⟩ … ⟨xk1⟩ …
     ⟨xknk⟩ for all positive integers k, all k-tuples n1, …, nk of
     positive integers, and all xij ∈ X."  From its proof: "μ = GεF …
     More briefly, μ_X applied to a word of words removes the outer pointy
     brackets.  Note that this description allows direct verification of
     the unit and associative laws for the monad W, without overt
     reference to the notion of a semi-group."
     Proposition 2: "For the above word-monad W in Set, the W-algebras
     have the form ⟨S, ν1, ν2, …⟩: A set S equipped with one n-ary
     operation νn : Sⁿ → S for each positive integer n, such that ν1 = 1
     while for every positive k and every k-tuple of positive integers
     n1, …, nk one has the identity νk(νn1 × ⋯ × νnk) = ν_{n1+⋯+nk} :
     S^{n1+⋯+nk} → S. (2)  A morphism f : ⟨S, ν1, …⟩ → ⟨S', ν'1, …⟩ of
     W-algebras is a function f : S → S' which commutes with each νn, so
     that fνn = ν'n fⁿ : Sⁿ → S'."
     The Corollary: "The system ⟨S, ν1, ν2, …⟩ is a W-algebra, as above,
     if and only if ν1 = 1, ν2 : S × S → S is an associative binary
     operation on S, and for all n ≥ 2, ν_{n+1} = νn(ν2 × 1) :
     S^{n+1} → S."
     The remark: "The comparison functor K : Smgrp → Set^W is the evident
     map ⟨S, ν⟩ ↦ ⟨S, 1, ν2, …, νn, …⟩ where νn is the iterate of the
     binary ν.  In other words, K is an isomorphism, but it replaces the
     algebraic system ⟨S, ν⟩ with one associative binary operation by the
     same set with all the iterated operations derived from this binary
     operation."

   PROPOSITION 1.  [WordF] is G ◯ F and [WordMonad] is Monad/
   Comparison.v's transparent [Adjunction_Induced_Monad Sg_adj]
   (Monad/Adjunction.v's [Adjunction_Monad], the issue's donor, is
   opaque by [About]).  At [eq_refl]: W X is the setoid of words
   ([W_obj]), its carrier the sigma ∐_{n≥1} Xⁿ ([W_carrier]); W f acts
   letterwise ([W_map]); η is the insertion as a setoid map ([W_ret]) and
   x ↦ ⟨x⟩ ([W_ret_fun]); μ = G ε F ([W_join_counit]) is the
   concatenation [pwconcat] of a word of words, the fold of juxtaposition
   ([W_join_fun]), and sends ⟨⟨x11⟩⟨x12⟩⟩⟨⟨x21⟩⟩ to ⟨x11⟩⟨x12⟩⟨x21⟩
   ([W_join_literal]).  Its laws are those of the adjunction.  "Direct
   verification": [WordMonad_direct] is Theory/Monad.v's [Build_Monad]
   with η the insertion and μ the concatenation [pwconcat_map], its laws
   proved by induction on words without reference to the adjunction (the
   associative law, three layers of brackets, by [tfold1_tmap] and
   [tfold1_hom]; the unit laws by [tfoldl_letters] and by conversion).
   The fold and its homomorphism lemma are the free semigroup's:
   [pwconcat] folds in [FreeSg X], and [tfold1_hom], quantified over
   semigroup maps, is applied to [pwconcat_hom] and to [FreeSg_map f].
   So the proof avoids the adjunction, not, as Mac Lane's remark has it,
   "overt reference to the notion of a semi-group".  Its unit and
   multiplication ARE W's as setoid maps ([WordMonad_direct_ret],
   [WordMonad_direct_join], at [eq_refl]); as monads the two are refused
   equal (Test/ProbeWord470.v, R6): the data agree and the law proofs do
   not.

   PROPOSITION 2.  A family is [NAry S]: [nu ν n] : S^{n+1} → S for
   each n, with [nu_respects], stated across lengths at no cost since
   [tup_eq] is False there.  ν1 = 1 is [nu_unit]; (2) is [nu_assoc], at
   each k-tuple (w1, …, wk) of words, wi in S^{ni}: ν_k of the values of
   the wi against ν of their concatenation, whose length is n1 + ⋯ + nk.
   Mac Lane reads (2) through W(WX) ≅ ∐_k ∐_n X^{n1+⋯+nk}; here (2) is
   quantified over tuples of words and needs no separate isomorphism: a
   k-tuple of words, each carrying its length, is a point of W(WX), and
   their concatenation is μ ([W_join_fun]).  An algebra ⟨S, h⟩ gives the
   family ν_n = h on Sⁿ ([alg_NAry], [alg_NAry_at] at [eq_refl]), with
   ν1 = 1 from its unit law ([alg_NAry_unit]) and (2) from its action law
   ([alg_NAry_assoc]); a family with the two conditions is an algebra
   whose structure map is the copairing [nu_sharp] and whose two laws ARE
   the two conditions, by conversion ([NAry_alg]).  Family → algebra →
   family returns the family, the whole record at [eq_refl]
   ([NAry_round_trip]); algebra → family → algebra returns h up to ≈
   ([alg_round_trip]), at each (n; t) at [eq_refl] (C31), and as a setoid
   map it is refused (R7), sigT having no η (R2).  The morphism clause,
   both ways: [alg_hom_NAry_hom], [NAry_hom_alg_hom].
   As a category: [WSys], the systems ⟨S, ν1, ν2, …⟩ with ν1 = 1 and (2)
   ([WSystem]) and the maps commuting with every νn, is isomorphic in
   [Cat] to [WordAlg], Set^W ([WSys_EM_iso]): its legs are [WSys_to_EM]
   and [EM_to_WSys] at [eq_refl], and every component of both natural
   isomorphisms is the identity, to and from, at [eq_refl].  The system
   round trip keeps the set, the family and the proof of ν1 = 1 at
   [eq_refl] ([WSys_rt_set], [WSys_rt_nu], [WSys_rt_unit]), and the maps
   ([WSys_rt_hom]); the proof of (2) comes back rebuilt (R9), so the whole
   system is refused (R8); a whole morphism is refused too (R10, well
   typed since a hom type depends on the set and the family alone, and a
   variable sigT pair against its rebuilt pair); the algebra round trip
   is refused on objects (R11), and the composite functor against the
   identity (R12).

   THE COROLLARY.  [cor_conditions ν]: ν1 = 1, ν2 associative, and
   ν_{m+3}(x, y, t) ≈ ν_{m+2}(ν2(x, y), t) for every m, Mac Lane's
   ν_{n+1} = νn(ν2 × 1) at n = m + 2 ≥ 2.  [NAry_corollary] : (ν1 = 1
   and (2)) ↔ [cor_conditions ν].  Forward ([cor_forward]): (2) at three
   k-tuples, (⟨ab⟩, ⟨c⟩), (⟨a⟩, ⟨bc⟩), and ⟨xy⟩ followed by the letters
   of t.  Backward ([cor_backward]): first [cor_iterate], νn ≈ the n-fold
   product of ν2 bracketed to the left (Mac Lane's "Similarly, νn must be
   the n-fold product"), and then (2) is the action law of the
   comparison algebra of that semigroup, Monad/Comparison.v's
   [EM_Comparison_Algebra_action]: the shared route, with no second
   induction on brackets.  In an arbitrary algebra ν3(a, b, c) is
   ν2(ν2(a, b), c) up to ≈ (C45) and not at [eq_refl] (R13); in an
   algebra K S it is at [eq_refl], at every length ([Sg_K_nu_succ]).

   THE REMARK.  [Sg_K] is Monad/Comparison.v's [EM_Comparison Sg_adj].
   Mac Lane's ⟨S, ν⟩ ↦ ⟨S, 1, ν2, …⟩ holds at [eq_refl]: the carrier is S
   ([Sg_K_carrier]); the structure map is G ε_S ([Sg_K_alg]), the product
   of the letters bracketed to the left ([Sg_K_alg_fun]); ν1 = 1
   ([Sg_K_nu1]); ν2 = ν ([Sg_K_nu2]); "νn is the iterate of the binary
   ν", ν_{m+3}(x, y, t) = ν_{m+2}(xy, t) ([Sg_K_nu_succ]); K f is f
   ([Sg_K_map]); and so read as a system ([Sg_K_system_nu],
   [Sg_K_system_nu2]).  [EM_to_Smgrp] makes an algebra a semigroup under
   ν2(a, b) := h⟨ab⟩, associative by [cor_forward].  "K is an
   isomorphism": [Smgrp_EM_iso : SmgrpSets ≅[Cat] WordAlg], its legs
   [Sg_K] and [EM_to_Smgrp] at [eq_refl] and every component of both
   natural isomorphisms the identity, to and from, at [eq_refl].  It is
   built from the two component isomorphisms, as #466 builds
   Instance/SupLat.v's [SupLat_EM_iso], and not as Theory/Equivalence.v's
   [Equivalence_to_Cat_Iso] of the equivalence: through that bridge the
   component of [iso_to_from] is still the identity at [eq_refl] (C67),
   and that of [iso_from_to] is refused (R21), the bridge taking it from
   the symmetry of the unit, Theory/Functor.v's
   [Functor_Setoid_obligation_1], opaque by [About]; the #470 audit
   measured that cause: with a transparent swap of the components in
   place of that symmetry, R21's statement holds at [eq_refl].
   [Smgrp_EM_equivalence] is the equivalence with the same components,
   and [Sg_Forget_Monadic : Monadic Sg_Forget] the monadicity of
   semigroups over Set in Monad/Comparison.v's sense, an equivalence
   (Barr and Wells' "triplable", which Mac Lane's §VI.3 sets beside his
   isomorphism).  The round trips keep the carrier, the curried
   multiplication and the maps at [eq_refl] ([Smgrp_EM_rt_carrier],
   [Smgrp_EM_rt_mul], [Smgrp_EM_rt_hom], [EM_Smgrp_rt_carrier],
   [EM_Smgrp_rt_alg_hom]).  Refused at [eq_refl]: the semigroup round
   trip at a variable (R14) and at a pair (X; σ) (R15); the uncurried
   multiplication there as a function (R16; prod has no η, R3, and at
   each literal pair (a, b) it holds, C66); the algebra round trip (R17)
   and its structure map as a setoid map (R18, the iterated ν2 against
   an arbitrary h); and both composites against the identity functors
   (R19, R20).  So Mac Lane's "isomorphism" is delivered as an
   isomorphism in [Cat] with identity components.  An isomorphism in
   [Cat] is, by Instance/Cat.v, an equivalence of categories, its
   hom-setoid being Theory/Functor.v's [Functor_Setoid], natural
   isomorphism: the issue's "an isomorphism (or, minimally, an
   equivalence)" is met in its "or, minimally, an equivalence" form,
   strengthened by the identity components, which are what bring it
   toward Mac Lane's isomorphism of categories.  A strict identity of the
   two categories is refused (R19, R20).  An isomorphism in
   Instance/StrictCat.v, whose hom-setoid asks Leibniz equality of the
   object maps, would need with these legs fobj[EM_to_Smgrp ◯ Sg_K] A = A
   for every A, so the η of prod under a binder (the multiplication comes
   back as fun p => ν(fst p, snd p), R3 and R16) and the equality of
   rebuilt proof fields: extensionality, argued and not measured.

   THE ISSUE'S PREMISES, dated.  Issue #470 was filed on 2026-07-23.  Its
   "None of this is present" (no category Smgrp, no free-semigroup
   functor) was accurate when filed and held until this change (a grep
   of the .v files for a semigroup category, internal semigroups or free
   semigroups finds prose only); Theory/Category/Semi.v is semigroupoids
   and Theory/Coq/Semigroup.v an ops-only class, as the body says.  Its
   [list_Monad] (Theory/Coq/List.v, with [flatten]) is the free-monoid
   monad as operations on Coq's lists, with no [@Monad Coq list] and an
   [IsMonad] bridge (Theory/Coq/Monad/Proofs.v) covering Identity, arrow
   and Compose alone: accurate when filed and still accurate, Theory/Coq/
   List.v having last changed in c429a82b (2026-06-17); the body cites
   those constants by line, which this tree replaces by their names.  Of
   its suggested modules, Monad/Instance/ does not exist; the files are
   Instance/Smgrp.v (Mac Lane's name for the category, as Instance/Grp.v
   and Instance/SupLat.v use theirs) and this one, with Theory/Algebra/
   Semigroup.v for the internal notion.  Its "CLAUDE.md Key Files index"
   was accurate when filed and has been stale since PR #1284 (merged
   2026-09-09), which moved the index to docs/INDEX.md.

   STRENGTHS.  Every [Example] above holds at [eq_refl], and
   Test/ProbeWord470.v restates each one (C19 to C30, C33 to C44 and C46
   to C65).  At ≈ only: [alg_round_trip], [cor_iterate], and the inverse
   laws of the two isomorphisms in [Cat], natural isomorphisms with
   identity components.  Three readbacks need #1347 (Instance/Sets.v's
   identity and composite with their properness fields as terms):
   [W_ret], [WordMonad_direct_ret] and [WordMonad_direct_join] are
   refused, "cannot unify", when this file is compiled against a built
   tree of master 687ac356, and nothing else of it is.  Nineteen proofs
   end [Defined] (counted by token).  Eighteen are load-bearing, measured
   by closing each alone [Qed] in a scratch copy of the targets and the
   probe, with the first command that then stops: [WordMonad_direct]
   ([WordMonad_direct_ret]), [alg_NAry_unit] ([WSys_rt_unit], its only
   consumer: closed [Qed] with that readback and its control C39 set
   aside, everything else compiles, so it is transparent for that
   readback alone), [NAry_alg] ([NAry_round_trip]),
   [WSystemHom_Setoid], [WSystem_id] and
   [WSystem_compose] ([WSys]), [WSys] ([WSys_to_EM]), [WSys_to_EM] and
   [EM_to_WSys] ([WSys_EM_counit_iso]), [WSys_EM_counit_iso] and
   [WSys_EM_unit_iso] ([WSys_EM_iso]), [WSys_EM_iso] ([WSys_EM_iso_to]),
   [EM_sg_map] ([EM_to_Smgrp]), [EM_to_Smgrp] ([Smgrp_EM_counit_iso]),
   [Smgrp_EM_counit_iso] and [Smgrp_EM_unit_iso]
   ([Smgrp_EM_equivalence]), [Smgrp_EM_equivalence]
   ([Smgrp_EM_counit_component]) and [Smgrp_EM_iso] ([Smgrp_EM_iso_to]);
   [Sg_Forget_Monadic] is [Defined] by the data convention only (closed
   [Qed], nothing stops).  The fifteen lemmas end [Qed].  Two of them,
   the auxiliary fold lemmas [tfoldl_tmap] and [tfold1_tmap], state a
   Leibniz equality between elements of a semigroup, proved by induction
   on the tuple: stronger than ≈, which is all that [WordMonad_direct],
   rewriting with the second, needs (Instance/Smgrp.v's [tfoldl_tapp]
   and [tfold1_tapp] are the other two, and its STRENGTHS records the
   scan that finds no fifth).  Every refutation of the probe stands,
   inside its command, in a copy of the three targets with all their
   forty-one [Qed]s turned [Defined] and [Transparent Obligations] set
   ([About] reporting there transparent what is opaque in the tree), so
   none is the opacity of these files; the dependency closure was not
   flipped, and the causes stated above (no η for sigT and prod, proofs
   rebuilt, data stuck on variables) are read from the terms, but for
   R21's, the opaque obligation, which the #470 audit measured (THE
   REMARK).

   UNIVERSES, read off [About].  The family record [NAry], its fields
   and constructor, [nu_sharp], [nu_unit], [nu2], [nu2_respects] and
   [cor_conditions] bind @{o} with caps only.  The two isomorphisms in
   [Cat] and their eight readbacks bind @{o so c} with o < so, o < c and
   so < c (Instance/Cat.v's [Cat@{c so so so o}]; [Smgrp_EM_iso] is
   [Isomorphism@{c so so}]).  Everything else binds @{o so} with the one
   constraint o < so besides caps: [WordMonad : Monad@{so o} WordF],
   [WordAlg := EilenbergMoore@{so so so o}] (a [Category@{so o o}]),
   [Smgrp_EM_equivalence : EquivalenceOfCategories@{so so so so so o}]
   and [Sg_Forget_Monadic : Monadic@{so so so so so o so so}], the
   instances of Instance/SupLat/Free.v's [SL_Forget_Monadic]; [WSystem]
   is a [Type@{so}].  The caps are the standard library's (pair and sigma
   projections, compose, ID, RelationClasses.Defs, eq_ind, eq_ind_r,
   eq_rect_r, Logic_lemmas.equality, nat_rect, False_rect, prod_rect).
   No [Set] and no equation, on Rocq 9.1.1, Coq 8.19.2 and 8.20.1 alike
   (binders and constraints between bound levels compared by script).

   NOT DELIVERED.  The section's exercises (#471 to #474: W₀ on Mon,
   R-modules, the polynomial rings, rings over Ab).  A strict identity of
   Smgrp and Set^W (refused above), and an isomorphism in
   Instance/StrictCat.v (which would need extensionality, as argued
   above).  Beck's route to monadicity (Monad/Monadicity/Beck.v), not
   taken.  The Kleisli category of W.  A lawful
   [@Monad Coq list] and the categorical laws of Theory/Coq/List.v's
   [list_Monad], the issue's background, still absent. *)

(* ------------------------------------------------------------------------ *)
(** ** Proposition 1: the monad W of the adjunction Set ⇀ Smgrp *)

Definition WordF@{o so} : Sets@{o so} ⟶ Sets@{o so} :=
  Sg_Forget@{o so} ◯ Sg_Free@{o so}.

Definition WordMonad@{o so} : @Monad Sets@{o so} WordF@{o so} :=
  Adjunction_Induced_Monad Sg_adj@{o so}.

(* μ_X: a word of words, its outer brackets removed. *)
Definition pwconcat@{o so} {X : SetoidObject@{o o}}
  (ww : PWord@{o} (PWordObj@{o} X)) : PWord@{o} X :=
  pwfold (A := FreeSg@{o so} X) (fun w => w) ww.

(* W X = ∐_{n≥1} Xⁿ *)
Example W_obj@{o so} (X : SetoidObject@{o o}) :
  fobj[WordF@{o so}] X = PWordObj@{o} X := eq_refl.

Example W_carrier@{o so} (X : SetoidObject@{o o}) :
  carrier (fobj[WordF@{o so}] X) = sigT (fun n : nat => Tup@{o} X n)
  := eq_refl.

(* W f acts letterwise. *)
Example W_map@{o so} {X Y : SetoidObject@{o o}} (f : X ~{Sets@{o so}}~> Y)
  (w : PWord@{o} X) : fmap[WordF@{o so}] f w = pwmap f w := eq_refl.

(* η_X x = ⟨x⟩, as a setoid map. *)
Example W_ret@{o so} (X : SetoidObject@{o o}) :
  @ret _ _ WordMonad@{o so} X = sg_insert@{o so} X := eq_refl.

Example W_ret_fun@{o so} (X : SetoidObject@{o o}) (x : X) :
  @ret _ _ WordMonad@{o so} X x = letter x := eq_refl.

(* μ = G ε F. *)
Example W_join_counit@{o so} (X : SetoidObject@{o o}) :
  @join _ _ WordMonad@{o so} X
    = fmap[Sg_Forget@{o so}]
        (@counit _ _ _ _ Sg_adj@{o so} (fobj[Sg_Free@{o so}] X))
  := eq_refl.

(* μ removes the outer brackets. *)
Example W_join_fun@{o so} (X : SetoidObject@{o o})
  (ww : PWord@{o} (PWordObj@{o} X)) :
  @join _ _ WordMonad@{o so} X ww = pwconcat@{o so} ww := eq_refl.

(* μ⟨⟨x11⟩⟨x12⟩⟩⟨⟨x21⟩⟩ = ⟨x11⟩⟨x12⟩⟨x21⟩, on a literal word of words. *)
Example W_join_literal@{o so} (X : SetoidObject@{o o}) (x11 x12 x21 : X) :
  @join _ _ WordMonad@{o so} X
    (existT (fun n => Tup (PWordObj X) n) 1%nat
       (existT (fun n => Tup X n) 1%nat (x11, x12), letter x21))
  = existT (fun n => Tup X n) 2%nat (x11, (x12, x21)) := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** The monad laws of W, verified directly on words *)

Lemma tfoldl_acc_respects@{o so} {Y : Type@{o}} {A : SmgrpSets@{o so}}
  (h : Y → sg_ob@{o so} A) (n : nat) (acc acc' : sg_ob@{o so} A)
  (t : Tup@{o} Y n) :
  acc ≈ acc' → tfoldl h acc n t ≈ tfoldl h acc' n t.
Proof.
  revert acc acc'; induction n as [|n IH]; intros acc acc' H.
  - exact (sg_mul_respects A _ _ H _ _ (reflexivity _)).
  - destruct t as [y t']. apply IH.
    exact (sg_mul_respects A _ _ H _ _ (reflexivity _)).
Qed.

(* A semigroup map commutes with the fold. *)
Lemma tfoldl_hom@{o so} {Y : Type@{o}} {A B : SmgrpSets@{o so}}
  (g : A ~{SmgrpSets@{o so}}~> B) (h : Y → sg_ob@{o so} A)
  (acc : sg_ob@{o so} A) (n : nat) (t : Tup@{o} Y n) :
  sg_fun g (tfoldl h acc n t)
    ≈ tfoldl (fun y => sg_fun g (h y)) (sg_fun g acc) n t.
Proof.
  revert acc; induction n as [|n IH]; intro acc.
  - exact (sg_fun_mul g acc (h t)).
  - destruct t as [y t']. cbn [tfoldl fst snd].
    rewrite IH.
    apply tfoldl_acc_respects.
    exact (sg_fun_mul g acc (h y)).
Qed.

Lemma tfold1_hom@{o so} {Y : Type@{o}} {A B : SmgrpSets@{o so}}
  (g : A ~{SmgrpSets@{o so}}~> B) (h : Y → sg_ob@{o so} A) (n : nat)
  (t : Tup@{o} Y n) :
  sg_fun g (tfold1 h n t) ≈ tfold1 (fun y => sg_fun g (h y)) n t.
Proof.
  destruct n as [|n]; [ reflexivity | ].
  destruct t as [y t']. exact (tfoldl_hom g h (h y) n t').
Qed.

Lemma tfoldl_tmap@{o so} {Y Z : Type@{o}} {A : SmgrpSets@{o so}}
  (h : Z → sg_ob@{o so} A) (g : Y → Z) (acc : sg_ob@{o so} A) (n : nat)
  (t : Tup@{o} Y n) :
  tfoldl h acc n (tmap g n t) = tfoldl (fun y => h (g y)) acc n t.
Proof.
  revert acc; induction n as [|n IH]; intro acc; [ reflexivity | apply IH ].
Qed.

Lemma tfold1_tmap@{o so} {Y Z : Type@{o}} {A : SmgrpSets@{o so}}
  (h : Z → sg_ob@{o so} A) (g : Y → Z) (n : nat) (t : Tup@{o} Y n) :
  tfold1 h n (tmap g n t) = tfold1 (fun y => h (g y)) n t.
Proof.
  destruct n as [|n]; [ reflexivity | apply tfoldl_tmap ].
Qed.

(* Appending the letters of t one at a time, on the right. *)
Lemma tfoldl_letters@{o so} (X : SetoidObject@{o o}) (m : nat)
  (acc : PWord@{o} X) (t : Tup@{o} X m) :
  tfoldl (A := FreeSg@{o so} X) (fun w => w) acc m (tmap letter m t)
    ≈ pwapp acc (existT _ m t).
Proof.
  revert acc; induction m as [|m IH]; intro acc.
  - reflexivity.
  - destruct t as [z t'].
    transitivity (pwapp (pwapp acc (letter z)) (existT _ m t')).
    + exact (IH t' (pwapp acc (letter z))).
    + exact (pwapp_assoc acc (letter z) (existT _ m t')).
Qed.

(* Concatenation as a semigroup map F(W X) → F X. *)
Definition pwconcat_hom@{o so} (X : SetoidObject@{o o}) :
  FreeSg@{o so} (PWordObj@{o} X) ~{SmgrpSets@{o so}}~> FreeSg@{o so} X :=
  sg_extend@{o so} (A := FreeSg@{o so} X)
    (@setoid_morphism_id@{o o o} (PWordObj@{o} X)).

(* Concatenation as a setoid map W W X → W X. *)
Definition pwconcat_map@{o so} (X : SetoidObject@{o o}) :
  fobj[WordF@{o so}] (fobj[WordF@{o so}] X) ~{Sets@{o so}}~>
  fobj[WordF@{o so}] X :=
  {| morphism := pwconcat@{o so}
   ; proper_morphism := fun ww vv H =>
       tfold1_respects (A := FreeSg@{o so} X) (fun w => w) (fun w => w)
         (fun _ _ E => E) _ _ _ _ H |}.

(* Mac Lane's direct verification of the laws of W: η the one-letter
   words, μ the concatenation, the laws by induction on words, without
   reference to the adjunction.  The fold and its homomorphism lemma are
   the free semigroup's ([pwconcat] folds in [FreeSg X], and [tfold1_hom]
   is applied to [pwconcat_hom] and [FreeSg_map f]), so this is not his
   "without overt reference to the notion of a semi-group". *)
Definition WordMonad_direct@{o so} : @Monad Sets@{o so} WordF@{o so}.
Proof.
  unshelve refine
    (@Build_Monad Sets@{o so} WordF@{o so}
       (fun X => sg_insert@{o so} X)
       (fun X => pwconcat_map@{o so} X) _ _ _ _ _).
  - (* η natural *)
    intros X Y f x. reflexivity.
  - (* μ ∘ Wμ ≈ μ ∘ μW: three layers of brackets *)
    intros X www.
    transitivity (tfold1 (A := FreeSg X) (fun y => pwconcat y)
                    (projT1 www) (projT2 www)).
    + change (tfold1 (A := FreeSg X) (fun w => w) (projT1 www)
                (tmap pwconcat (projT1 www) (projT2 www))
              ≈ tfold1 (A := FreeSg X) (fun y => pwconcat y)
                  (projT1 www) (projT2 www)).
      rewrite tfold1_tmap.
      reflexivity.
    + symmetry.
      exact (tfold1_hom (B := FreeSg X) (pwconcat_hom X)
               (fun w => w) (projT1 www) (projT2 www)).
  - (* μ ∘ Wη ≈ 1 *)
    intros X [k t]. destruct k as [|m]; [ reflexivity | ].
    destruct t as [z t'].
    exact (tfoldl_letters X m (letter z) t').
  - (* μ ∘ ηW ≈ 1 *)
    intros X w. reflexivity.
  - (* μ natural *)
    intros X Y f ww.
    transitivity (tfold1 (A := FreeSg Y)
                    (fun y => sg_fun (FreeSg_map f) y) (projT1 ww) (projT2 ww)).
    + change (tfold1 (A := FreeSg Y) (fun w => w) (projT1 ww)
                (tmap (sg_fun (FreeSg_map f)) (projT1 ww) (projT2 ww))
              ≈ tfold1 (A := FreeSg Y) (fun y => sg_fun (FreeSg_map f) y)
                  (projT1 ww) (projT2 ww)).
      rewrite tfold1_tmap.
      reflexivity.
    + symmetry.
      exact (tfold1_hom (FreeSg_map f) (fun w => w) (projT1 ww) (projT2 ww)).
Defined.

(* Its unit and multiplication ARE those of W, as setoid maps. *)
Example WordMonad_direct_ret@{o so} (X : SetoidObject@{o o}) :
  @ret _ _ WordMonad_direct@{o so} X = @ret _ _ WordMonad@{o so} X
  := eq_refl.

Example WordMonad_direct_join@{o so} (X : SetoidObject@{o o}) :
  @join _ _ WordMonad_direct@{o so} X = @join _ _ WordMonad@{o so} X
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Proposition 2: the W-algebras are the systems ⟨S, ν1, ν2, …⟩ *)

(* The category of W-algebras in Set: [WordAlg] is Set^W. *)
Definition WordAlg@{o so} : Category@{so o o} :=
  @EilenbergMoore@{so so so o} Sets@{o so} WordF@{o so} WordMonad@{o so}.

(* One operation ν_{n+1} : S^{n+1} → S for each n, respecting ≈.  The
   heterogeneous form of the respect law costs nothing, since [tup_eq] is
   False across lengths. *)
Record NAry@{o} (X : SetoidObject@{o o}) : Type@{o} := {
  nu : ∀ n : nat, Tup@{o} X n → X;
  nu_respects : ∀ (n m : nat) (t : Tup@{o} X n) (u : Tup@{o} X m),
    tup_eq n m t u → nu n t ≈ nu m u
}.

Arguments nu {X} _ _ _.
Arguments nu_respects {X} _ _ _ _ _ _.

(* The copairing ∐_n S^(n+1) → S of the family. *)
Definition nu_sharp@{o} {X : SetoidObject@{o o}} (ν : NAry@{o} X)
  (p : PWord@{o} X) : X :=
  nu ν (projT1 p) (projT2 p).

(* ν1 = 1. *)
Definition nu_unit@{o} {X : SetoidObject@{o o}} (ν : NAry@{o} X) :
  Type@{o} :=
  ∀ x : X, nu ν O x ≈ x.

(* (2): νk (ν_{n1} × ⋯ × ν_{nk}) = ν_{n1+⋯+nk}, at each k-tuple of words
   (w1, …, wk), wi in S^{ni}: ν_k of the values of the wi is ν of their
   concatenation w1 ⋯ wk, whose length is n1 + ⋯ + nk. *)
Definition nu_assoc@{o so} {X : SetoidObject@{o o}} (ν : NAry@{o} X) :
  Type@{o} :=
  ∀ (k : nat) (tt : Tup@{o} (PWordObj@{o} X) k),
    nu ν k (tmap (nu_sharp ν) k tt)
      ≈ nu_sharp ν (pwconcat@{o so} (existT _ k tt)).

(* An algebra ⟨S, h⟩ gives a family: ν_n is h on S^n. *)
Definition alg_NAry@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} X) :
  NAry@{o} X :=
  {| nu := fun n t => t_alg[α] (existT (fun n0 => Tup X n0) n t)
   ; nu_respects := fun n m t u H =>
       proper_morphism (t_alg[α]) (existT _ n t) (existT _ m u) H |}.

(* ...in which h is the copairing of its family, at each (n; t). *)
Example alg_NAry_at@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} X) (n : nat)
  (t : Tup@{o} X n) :
  nu (alg_NAry α) n t = t_alg[α] (existT _ n t) := eq_refl.

(* The unit law of the algebra IS ν1 = 1.  Transparent, so that the unit
   law of a system comes back from Set^W on the nose ([WSys_rt_unit]);
   that readback is the only consumer of the transparency (the header's
   STRENGTHS). *)
Definition alg_NAry_unit@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} X) :
  nu_unit (alg_NAry α).
Proof. intro x. exact (@t_id _ _ _ _ α x). Defined.

(* The action law of the algebra gives (2). *)
Lemma alg_NAry_assoc@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} X) :
  nu_assoc@{o so} (alg_NAry α).
Proof.
  intros k tt.
  transitivity (t_alg[α] (fmap[WordF@{o so}] (t_alg[α]) (existT _ k tt))).
  - apply (proper_morphism (t_alg[α])).
    exact (tmap_respects (X := PWordObj X) (Y := X)
             (nu_sharp (alg_NAry α)) (t_alg[α])
             (fun p q H => proper_morphism (t_alg[α])
                             (existT _ (projT1 p) (projT2 p)) q H) k k tt tt
             (tup_eq_refl (X := PWordObj X) k tt)).
  - transitivity (t_alg[α] (pwconcat@{o so} (existT _ k tt))).
    + exact (@t_action _ _ _ _ α (existT _ k tt)).
    + apply (proper_morphism (t_alg[α])).
      exact (tup_eq_refl _ (projT2 (pwconcat@{o so} (existT _ k tt)))).
Qed.

(* A family with ν1 = 1 and (2) is an algebra: its structure map is the
   copairing, and the two algebra laws ARE the two conditions, read at
   each word by conversion. *)
Definition NAry_alg@{o so} {X : SetoidObject@{o o}} (ν : NAry@{o} X)
  (Hu : nu_unit ν) (Ha : nu_assoc@{o so} ν) :
  @TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} X.
Proof.
  unshelve refine
    (@Build_TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} X
       {| morphism := nu_sharp ν
        ; proper_morphism := fun p q H => nu_respects ν _ _ _ _ H |} _ _).
  - intro x. exact (Hu x).
  - intro ww. exact (Ha (projT1 ww) (projT2 ww)).
Defined.

(* Family → algebra → family returns the family itself. *)
Example NAry_round_trip@{o so} {X : SetoidObject@{o o}} (ν : NAry@{o} X)
  (Hu : nu_unit ν) (Ha : nu_assoc@{o so} ν) :
  alg_NAry (NAry_alg@{o so} ν Hu Ha) = ν := eq_refl.

(* Algebra → family → algebra returns the structure map up to ≈: the
   rebuilt map reads h at (projT1 p; projT2 p), and sigT has no η. *)
Lemma alg_round_trip@{o so} {X : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} X) :
  t_alg[NAry_alg@{o so} (alg_NAry α) (alg_NAry_unit α) (alg_NAry_assoc α)]
    ≈ t_alg[α].
Proof.
  intro p. apply (proper_morphism (t_alg[α])).
  exact (tup_eq_refl _ (projT2 p)).
Qed.

(* A morphism of systems: f νn = ν'n fⁿ for every n. *)
Definition NAry_hom@{o so} {X Y : SetoidObject@{o o}} (ν : NAry@{o} X)
  (ν' : NAry@{o} Y) (f : X ~{Sets@{o so}}~> Y) : Type@{o} :=
  ∀ (n : nat) (t : Tup@{o} X n), f (nu ν n t) ≈ nu ν' n (tmap f n t).

(* The morphism clause, both ways: an algebra map is a map commuting with
   every νn, and conversely. *)
Lemma alg_hom_NAry_hom@{o so} {X Y : SetoidObject@{o o}}
  (α : @TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} X)
  (β : @TAlgebra Sets@{o so} WordF@{o so} WordMonad@{o so} Y)
  (f : X ~{Sets@{o so}}~> Y) :
  f ∘ t_alg[α] ≈ t_alg[β] ∘ fmap[WordF@{o so}] f →
  NAry_hom@{o so} (alg_NAry α) (alg_NAry β) f.
Proof. intros H n t. exact (H (existT _ n t)). Qed.

Lemma NAry_hom_alg_hom@{o so} {X Y : SetoidObject@{o o}}
  (ν : NAry@{o} X) (ν' : NAry@{o} Y) (Hu : nu_unit ν)
  (Ha : nu_assoc@{o so} ν) (Hu' : nu_unit ν') (Ha' : nu_assoc@{o so} ν')
  (f : X ~{Sets@{o so}}~> Y) :
  NAry_hom@{o so} ν ν' f →
  f ∘ t_alg[NAry_alg@{o so} ν Hu Ha]
    ≈ t_alg[NAry_alg@{o so} ν' Hu' Ha'] ∘ fmap[WordF@{o so}] f.
Proof. intros H p. exact (H (projT1 p) (projT2 p)). Qed.

(* ------------------------------------------------------------------------ *)
(** ** Proposition 2 as a category: systems ⟨S, ν1, ν2, …⟩ ≅ Set^W *)

Record WSystem@{o so} : Type@{so} := {
  ws_set : SetoidObject@{o o};
  ws_nu : NAry@{o} ws_set;
  ws_unit : nu_unit ws_nu;
  ws_assoc : nu_assoc@{o so} ws_nu
}.

Definition WSystemHom@{o so} (A B : WSystem@{o so}) : Type@{o} :=
  { f : ws_set A ~{Sets@{o so}}~> ws_set B
  & NAry_hom@{o so} (ws_nu A) (ws_nu B) f }.

Definition WSystemHom_Setoid@{o so} (A B : WSystem@{o so}) :
  Setoid@{o o} (WSystemHom@{o so} A B).
Proof.
  refine {| equiv := fun f g =>
                @equiv _ (@homset Sets@{o so} (ws_set A) (ws_set B))
                  (`1 f) (`1 g) |}.
  constructor.
  - intros f. reflexivity.
  - intros f g H. symmetry. exact H.
  - intros f g h H1 H2. transitivity (`1 g); assumption.
Defined.

Definition WSystem_id@{o so} (A : WSystem@{o so}) : WSystemHom@{o so} A A.
Proof.
  exists (@setoid_morphism_id@{o o o} (ws_set A)).
  intros n t. apply (nu_respects (ws_nu A)).
  exact (tup_eq_sym _ _ _ _ (tmap_id n t)).
Defined.

Definition WSystem_compose@{o so} {A B C : WSystem@{o so}}
  (f : WSystemHom@{o so} B C) (g : WSystemHom@{o so} A B) :
  WSystemHom@{o so} A C.
Proof.
  exists (@setoid_morphism_compose@{o o o} _ _ _ (`1 f) (`1 g)).
  intros n t. simpl.
  transitivity (`1 f (nu (ws_nu B) n (tmap (`1 g) n t))).
  - apply (proper_morphism (`1 f)). exact (`2 g n t).
  - transitivity (nu (ws_nu C) n (tmap (`1 f) n (tmap (`1 g) n t))).
    + exact (`2 f n _).
    + apply (nu_respects (ws_nu C)).
      exact (tup_eq_sym _ _ _ _ (tmap_comp (`1 f) (`1 g) n t)).
Defined.

(* The category of the systems of Proposition 2. *)
Definition WSys@{o so} : Category@{so o o}.
Proof.
  unshelve refine
    {| obj     := WSystem@{o so}
     ; hom     := WSystemHom@{o so}
     ; homset  := WSystemHom_Setoid@{o so}
     ; id      := WSystem_id@{o so}
     ; compose := @WSystem_compose@{o so} |}.
  - intros A B C f f' Hf g g' Hg a. simpl.
    transitivity (`1 f (`1 g' a)).
    + apply (proper_morphism (`1 f)). exact (Hg a).
    + exact (Hf _).
  - intros A B f a. reflexivity.
  - intros A B f a. reflexivity.
  - intros A B C D f g h a. reflexivity.
  - intros A B C D f g h a. reflexivity.
Defined.

(* A system is an algebra: the copairing, with the two conditions. *)
Definition WSys_to_EM@{o so} : WSys@{o so} ⟶ WordAlg@{o so}.
Proof.
  unshelve refine
    (@Build_Functor WSys@{o so} WordAlg@{o so}
       (fun A => existT _ (ws_set A)
                   (NAry_alg@{o so} (ws_nu A) (ws_unit A) (ws_assoc A)))
       (fun A B f =>
          @Build_TAlgebraHom Sets@{o so} WordF@{o so} WordMonad@{o so}
            (ws_set A) (ws_set B)
            (NAry_alg@{o so} (ws_nu A) (ws_unit A) (ws_assoc A))
            (NAry_alg@{o so} (ws_nu B) (ws_unit B) (ws_assoc B))
            (`1 f)
            (NAry_hom_alg_hom@{o so} _ _ _ _ _ _ (`1 f) (`2 f)))
       _ _ _).
  - intros A B f g H a. exact (H a).
  - intros A a. reflexivity.
  - intros A B C f g a. reflexivity.
Defined.

(* An algebra is a system: ν_n is h on S^n. *)
Definition EM_to_WSys@{o so} : WordAlg@{o so} ⟶ WSys@{o so}.
Proof.
  unshelve refine
    (@Build_Functor WordAlg@{o so} WSys@{o so}
       (fun x => {| ws_set := projT1 x
                  ; ws_nu := alg_NAry@{o so} (projT2 x)
                  ; ws_unit := alg_NAry_unit@{o so} (projT2 x)
                  ; ws_assoc := alg_NAry_assoc@{o so} (projT2 x) |})
       (fun x y f =>
          existT _ (t_alg_hom[f])
            (alg_hom_NAry_hom@{o so} (projT2 x) (projT2 y) (t_alg_hom[f])
               (@t_alg_hom_commutes _ _ _ _ _ _ _ f)))
       _ _ _).
  - intros x y f g H a. exact (H a).
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(* The algebra round trip through the systems, with the identity as its
   component. *)
Definition WSys_EM_counit_iso@{o so} (x : WordAlg@{o so}) :
  @Isomorphism WordAlg@{o so} (fobj[WSys_to_EM@{o so} ◯ EM_to_WSys@{o so}] x)
    x.
Proof.
  unshelve refine
    (@Build_Isomorphism WordAlg@{o so}
       (fobj[WSys_to_EM@{o so} ◯ EM_to_WSys@{o so}] x) x
       (@Build_TAlgebraHom Sets@{o so} WordF@{o so} WordMonad@{o so}
          (projT1 x) (projT1 x)
          (projT2 (fobj[WSys_to_EM@{o so} ◯ EM_to_WSys@{o so}] x))
          (projT2 x) (@setoid_morphism_id@{o o o} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{o so} WordF@{o so} WordMonad@{o so}
          (projT1 x) (projT1 x) (projT2 x)
          (projT2 (fobj[WSys_to_EM@{o so} ◯ EM_to_WSys@{o so}] x))
          (@setoid_morphism_id@{o o o} (projT1 x)) _) _ _).
  - intro p. simpl. apply (proper_morphism (t_alg[projT2 x])).
    exact (tup_eq_sym _ _ _ _ (tmap_id (projT1 p) (projT2 p))).
  - intro p. simpl. apply (proper_morphism (t_alg[projT2 x])).
    exact (tup_eq_sym _ _ _ _ (tmap_id (projT1 p) (projT2 p))).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The system round trip, with the identity as its component. *)
Definition WSys_EM_unit_iso@{o so} (A : WSys@{o so}) :
  @Isomorphism WSys@{o so} (fobj[EM_to_WSys@{o so} ◯ WSys_to_EM@{o so}] A) A.
Proof.
  unshelve refine
    (@Build_Isomorphism WSys@{o so}
       (fobj[EM_to_WSys@{o so} ◯ WSys_to_EM@{o so}] A) A
       (existT _ (@setoid_morphism_id@{o o o} (ws_set A)) _)
       (existT _ (@setoid_morphism_id@{o o o} (ws_set A)) _) _ _).
  - intros n t. simpl. apply (nu_respects (ws_nu A)).
    exact (tup_eq_sym _ _ _ _ (tmap_id n t)).
  - intros n t. simpl. apply (nu_respects (ws_nu A)).
    exact (tup_eq_sym _ _ _ _ (tmap_id n t)).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* Proposition 2, packaged: the category of systems is isomorphic in Cat
   to Set^W, both legs the two functors and every component of both
   natural isomorphisms the identity.  An isomorphism in Cat is, by
   Instance/Cat.v, an equivalence of categories; the identity components
   are what bring this one toward an isomorphism of categories. *)
Definition WSys_EM_iso@{o so c} :
  @Isomorphism Cat@{c so so so o} WSys@{o so} WordAlg@{o so}.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{c so so so o} WSys@{o so} WordAlg@{o so}
       WSys_to_EM@{o so} EM_to_WSys@{o so} _ _).
  - exists (fun x => WSys_EM_counit_iso@{o so} x).
    intros x y f a. reflexivity.
  - exists (fun A => WSys_EM_unit_iso@{o so} A).
    intros A B f a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** The Corollary: one associative binary operation, iterated *)

Definition nu2@{o} {X : SetoidObject@{o o}} (ν : NAry@{o} X) (a b : X) : X :=
  nu ν 1%nat (a, b).

(* ν1 = 1, ν2 associative, and ν_{n+1} = ν_n (ν2 × 1) for n ≥ 2, read at
   n = m + 2 on the tuple (x, y, t). *)
Definition cor_conditions@{o} {X : SetoidObject@{o o}} (ν : NAry@{o} X) :
  Type@{o} :=
  nu_unit ν
  * (∀ a b c : X, nu2 ν (nu2 ν a b) c ≈ nu2 ν a (nu2 ν b c))
  * (∀ (m : nat) (x y : X) (t : Tup@{o} X m),
       nu ν (S (S m)) (x, (y, t)) ≈ nu ν (S m) (nu2 ν x y, t)).

Lemma nu2_respects@{o} {X : SetoidObject@{o o}} (ν : NAry@{o} X) :
  Proper (equiv ==> equiv ==> equiv) (nu2 ν).
Proof.
  intros a a' Ha b b' Hb. unfold nu2.
  apply (nu_respects ν 1%nat 1%nat). split; assumption.
Qed.

(* (2) at three tuples: (⟨ab⟩, ⟨c⟩), (⟨a⟩, ⟨bc⟩), and ⟨xy⟩ followed by
   the letters of t. *)
Lemma cor_forward@{o so} {X : SetoidObject@{o o}} (ν : NAry@{o} X) :
  nu_unit ν → nu_assoc@{o so} ν → cor_conditions ν.
Proof.
  intros Hu Ha. split; [ split | ].
  - exact Hu.
  - intros a b c.
    (* both sides are ν3(a, b, c) *)
    transitivity (nu ν 2%nat (a, (b, c))).
    + pose proof (Ha 1%nat (existT _ 1%nat (a, b), letter c)) as H.
      transitivity (nu ν 1%nat (nu ν 1%nat (a, b), nu ν O c)); [ | exact H ].
      apply nu2_respects; [ reflexivity | symmetry; exact (Hu c) ].
    + pose proof (Ha 1%nat (letter a, existT _ 1%nat (b, c))) as H.
      symmetry.
      transitivity (nu ν 1%nat (nu ν O a, nu ν 1%nat (b, c))); [ | exact H ].
      apply nu2_respects; [ symmetry; exact (Hu a) | reflexivity ].
  - intros m x y t.
    pose proof (Ha (S m) (existT _ 1%nat (x, y), tmap letter m t)) as H.
    symmetry.
    transitivity (nu ν (S m) (nu ν 1%nat (x, y),
                              tmap (nu_sharp ν) m (tmap letter m t))).
    + apply (nu_respects ν (S m) (S m)). split; [ reflexivity | ].
      clear H. induction m as [|m IH]; [ cbn; symmetry; exact (Hu t) | ].
      destruct t as [z t']. split; [ symmetry; exact (Hu z) | exact (IH t') ].
    + transitivity
        (nu_sharp ν (pwconcat@{o so}
                       (existT _ (S m)
                          (existT _ 1%nat (x, y), tmap letter m t))));
        [ exact H | ].
      apply (nu_respects ν).
      exact (tfoldl_letters X m (existT _ 1%nat (x, y)) t).
Qed.

(* Given the three conditions, ν2 makes S a semigroup... *)
Definition nu2_sg@{o so} {X : SetoidObject@{o o}} (ν : NAry@{o} X)
  (Hc : cor_conditions ν) : SmgrpSets@{o so} :=
  mk_sg_obj@{o so} X (nu2 ν) (nu2_respects ν) (snd (fst Hc)).

(* ...and νn is its n-fold product: Mac Lane's "Similarly, νn must be the
   n-fold product". *)
Lemma cor_iterate@{o so} {X : SetoidObject@{o o}} (ν : NAry@{o} X)
  (Hc : cor_conditions ν) (n : nat) (t : Tup@{o} X n) :
  nu ν n t ≈ tfold1 (A := nu2_sg@{o so} ν Hc) (fun s => s) n t.
Proof.
  destruct n as [|n]; [ exact (fst (fst Hc) t) | ].
  revert t; induction n as [|n IH]; intro t.
  - destruct t as [x y]. reflexivity.
  - destruct t as [x [y t']].
    transitivity (nu ν (S n) (nu2 ν x y, t')).
    + exact (snd Hc n x y t').
    + exact (IH (nu2 ν x y, t')).
Qed.

(* Backward: the iterated products satisfy (2), because the comparison
   algebra of that semigroup satisfies its action law
   ([EM_Comparison_Algebra_action], Monad/Comparison.v). *)
Lemma cor_backward@{o so} {X : SetoidObject@{o o}} (ν : NAry@{o} X) :
  cor_conditions ν → nu_unit ν * nu_assoc@{o so} ν.
Proof.
  intro Hc. split; [ exact (fst (fst Hc)) | ].
  intros k tt.
  set (A := nu2_sg@{o so} ν Hc).
  pose proof (@EM_Comparison_Algebra_action _ _ _ _ Sg_adj@{o so} A
                (existT _ k tt)) as Hact.
  transitivity
    (tfold1 (A := A) (fun s => s) k
       (tmap (fun p => tfold1 (A := A) (fun s => s) (projT1 p) (projT2 p))
          k tt)).
  - transitivity
      (nu ν k (tmap (fun p => tfold1 (A := A) (fun s => s)
                                (projT1 p) (projT2 p)) k tt)).
    + apply (nu_respects ν k k).
      apply (tmap_respects (X := PWordObj X) (Y := X)).
      * intros p q Hpq. unfold nu_sharp.
        transitivity (nu ν (projT1 q) (projT2 q));
          [ exact (nu_respects ν _ _ _ _ Hpq) | exact (cor_iterate ν Hc _ _) ].
      * exact (tup_eq_refl (X := PWordObj X) k tt).
    + exact (cor_iterate ν Hc k _).
  - transitivity (tfold1 (A := A) (fun s => s) _
                    (projT2 (pwconcat@{o so} (existT _ k tt)))).
    + exact Hact.
    + symmetry. exact (cor_iterate ν Hc _ _).
Qed.

(* The Corollary: ⟨S, ν1, ν2, …⟩ is a W-algebra iff ν1 = 1, ν2 is
   associative and ν_{n+1} = ν_n (ν2 × 1) for n ≥ 2. *)
Theorem NAry_corollary@{o so} {X : SetoidObject@{o o}} (ν : NAry@{o} X) :
  iffT@{o o} (nu_unit ν * nu_assoc@{o so} ν) (cor_conditions ν).
Proof.
  split.
  - intros [Hu Ha]. exact (cor_forward ν Hu Ha).
  - exact (cor_backward ν).
Qed.

(* ------------------------------------------------------------------------ *)
(** ** The comparison K : Smgrp → Set^W is an isomorphism *)

Definition Sg_K@{o so} : SmgrpSets@{o so} ⟶ WordAlg@{o so} :=
  EM_Comparison Sg_adj@{o so}.

(* The semigroup of an algebra: ν2(a, b) = h⟨a b⟩, associative by the
   Corollary's forward half. *)
Definition EM_sg@{o so} (x : WordAlg@{o so}) : SmgrpSets@{o so} :=
  nu2_sg@{o so} (alg_NAry (projT2 x))
    (cor_forward (alg_NAry (projT2 x)) (alg_NAry_unit (projT2 x))
       (alg_NAry_assoc (projT2 x))).

Definition EM_sg_map@{o so} {x y : WordAlg@{o so}}
  (f : x ~{WordAlg@{o so}}~> y) : EM_sg@{o so} x ~{SmgrpSets@{o so}}~> EM_sg y.
Proof.
  refine (@mk_sg_hom@{o so} (EM_sg x) (EM_sg y) (t_alg_hom[f])
            (proper_morphism (t_alg_hom[f])) _).
  intros a b.
  exact (@t_alg_hom_commutes _ _ _ _ _ _ _ f (existT _ 1%nat (a, b))).
Defined.

Definition EM_to_Smgrp@{o so} : WordAlg@{o so} ⟶ SmgrpSets@{o so}.
Proof.
  unshelve refine
    (@Build_Functor WordAlg@{o so} SmgrpSets@{o so} EM_sg@{o so}
       (fun x y f => EM_sg_map@{o so} f) _ _ _).
  - intros x y f g H. exact H.
  - intros x a. reflexivity.
  - intros x y z f g a. reflexivity.
Defined.

(* The algebra round trip, with the identity as its component. *)
Definition Smgrp_EM_counit_iso@{o so} (x : WordAlg@{o so}) :
  @Isomorphism WordAlg@{o so} (fobj[Sg_K@{o so} ◯ EM_to_Smgrp@{o so}] x) x.
Proof.
  set (ν := alg_NAry (projT2 x)).
  set (Hc := cor_forward ν (alg_NAry_unit (projT2 x))
               (alg_NAry_assoc (projT2 x))).
  unshelve refine
    (@Build_Isomorphism WordAlg@{o so}
       (fobj[Sg_K@{o so} ◯ EM_to_Smgrp@{o so}] x) x
       (@Build_TAlgebraHom Sets@{o so} WordF@{o so} WordMonad@{o so}
          (projT1 x) (projT1 x)
          (projT2 (fobj[Sg_K@{o so} ◯ EM_to_Smgrp@{o so}] x)) (projT2 x)
          (@setoid_morphism_id@{o o o} (projT1 x)) _)
       (@Build_TAlgebraHom Sets@{o so} WordF@{o so} WordMonad@{o so}
          (projT1 x) (projT1 x) (projT2 x)
          (projT2 (fobj[Sg_K@{o so} ◯ EM_to_Smgrp@{o so}] x))
          (@setoid_morphism_id@{o o o} (projT1 x)) _) _ _).
  - intro p. cbn.
    transitivity (nu ν (projT1 p) (projT2 p)).
    + symmetry. exact (cor_iterate ν Hc (projT1 p) (projT2 p)).
    + apply (proper_morphism (t_alg[projT2 x])).
      exact (tup_eq_sym _ _ _ _ (tmap_id (projT1 p) (projT2 p))).
  - intro p. cbn.
    transitivity (nu ν (projT1 p) (projT2 p)).
    + apply (proper_morphism (t_alg[projT2 x])).
      exact (tup_eq_refl _ (projT2 p)).
    + transitivity (tfold1 (A := EM_sg x) (fun s => s) (projT1 p) (projT2 p)).
      * exact (cor_iterate ν Hc (projT1 p) (projT2 p)).
      * apply (tfold1_respects (A := EM_sg x) (fun s => s) (fun s => s)
                 (fun a b H => H)).
        exact (tup_eq_sym _ _ _ _ (tmap_id (projT1 p) (projT2 p))).
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The semigroup round trip, with the identity as its component. *)
Definition Smgrp_EM_unit_iso@{o so} (A : SmgrpSets@{o so}) :
  @Isomorphism SmgrpSets@{o so} (fobj[EM_to_Smgrp@{o so} ◯ Sg_K@{o so}] A) A.
Proof.
  unshelve refine
    (@Build_Isomorphism SmgrpSets@{o so}
       (fobj[EM_to_Smgrp@{o so} ◯ Sg_K@{o so}] A) A
       (@mk_sg_hom@{o so} (fobj[EM_to_Smgrp@{o so} ◯ Sg_K@{o so}] A) A
          (fun a => a) (fun a b H => H) _)
       (@mk_sg_hom@{o so} A (fobj[EM_to_Smgrp@{o so} ◯ Sg_K@{o so}] A)
          (fun a => a) (fun a b H => H) _) _ _).
  - intros a b. reflexivity.
  - intros a b. reflexivity.
  - intro a. reflexivity.
  - intro a. reflexivity.
Defined.

(* The Remark: K is an equivalence, with identity components both ways. *)
Definition Smgrp_EM_equivalence@{o so} :
  @EquivalenceOfCategories@{so so so so so o} SmgrpSets@{o so}
    WordAlg@{o so} Sg_K@{o so}.
Proof.
  unshelve refine
    (@Build_EquivalenceOfCategories _ _ Sg_K@{o so} EM_to_Smgrp@{o so} _ _).
  - exists (fun x => Smgrp_EM_counit_iso@{o so} x).
    intros x y f a. reflexivity.
  - exists (fun A => iso_sym (Smgrp_EM_unit_iso@{o so} A)).
    intros A B f a. reflexivity.
Defined.

(* Semigroups are monadic over Set. *)
Definition Sg_Forget_Monadic@{o so} :
  @Monadic@{so so so so so o so so} SmgrpSets@{o so} Sets@{o so}
    Sg_Forget@{o so}.
Proof.
  exists Sg_Free@{o so}.
  exists Sg_adj@{o so}.
  exact Smgrp_EM_equivalence@{o so}.
Defined.

(* "In other words, K is an isomorphism": Smgrp ≅ Set^W in Cat, built from
   the two component isomorphisms so that both of its natural
   isomorphisms have the identity as every component.  An isomorphism in
   Cat is, by Instance/Cat.v, an equivalence of categories: this is the
   issue's "or, minimally, an equivalence", strengthened by the identity
   components toward Mac Lane's isomorphism (the header's THE REMARK). *)
Definition Smgrp_EM_iso@{o so c} :
  @Isomorphism Cat@{c so so so o} SmgrpSets@{o so} WordAlg@{o so}.
Proof.
  unshelve refine
    (@Build_Isomorphism Cat@{c so so so o} SmgrpSets@{o so} WordAlg@{o so}
       Sg_K@{o so} EM_to_Smgrp@{o so} _ _).
  - exists (fun x => Smgrp_EM_counit_iso@{o so} x).
    intros x y f a. reflexivity.
  - exists (fun A => Smgrp_EM_unit_iso@{o so} A).
    intros A B f a. reflexivity.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** Readbacks *)

(* The two legs of each isomorphism in Cat are the two functors. *)
Example Smgrp_EM_iso_to@{o so c} :
  to Smgrp_EM_iso@{o so c} = Sg_K@{o so} := eq_refl.

Example Smgrp_EM_iso_from@{o so c} :
  from Smgrp_EM_iso@{o so c} = EM_to_Smgrp@{o so} := eq_refl.

Example WSys_EM_iso_to@{o so c} :
  to WSys_EM_iso@{o so c} = WSys_to_EM@{o so} := eq_refl.

Example WSys_EM_iso_from@{o so c} :
  from WSys_EM_iso@{o so c} = EM_to_WSys@{o so} := eq_refl.

(* The Remark's K ⟨S, ν⟩ = ⟨S, 1, ν2, …⟩: the carrier, the structure map
   G ε_S, its value the left-bracketed product, ν1 = 1, ν2 = ν, and νn the
   iterate of ν. *)
Example Sg_K_carrier@{o so} (A : SmgrpSets@{o so}) :
  projT1 (fobj[Sg_K@{o so}] A) = sg_ob A := eq_refl.

Example Sg_K_alg@{o so} (A : SmgrpSets@{o so}) :
  t_alg[projT2 (fobj[Sg_K@{o so}] A)]
    = fmap[Sg_Forget@{o so}] (@counit _ _ _ _ Sg_adj@{o so} A) := eq_refl.

Example Sg_K_alg_fun@{o so} (A : SmgrpSets@{o so})
  (p : PWord@{o} (sg_ob A)) :
  t_alg[projT2 (fobj[Sg_K@{o so}] A)] p = pwfold (fun s => s) p := eq_refl.

Example Sg_K_nu1@{o so} (A : SmgrpSets@{o so}) (x : sg_ob A) :
  t_alg[projT2 (fobj[Sg_K@{o so}] A)] (letter x) = x := eq_refl.

Example Sg_K_nu2@{o so} (A : SmgrpSets@{o so}) (a b : sg_ob A) :
  t_alg[projT2 (fobj[Sg_K@{o so}] A)] (existT _ 1%nat (a, b))
    = sg_mul A a b := eq_refl.

Example Sg_K_nu_succ@{o so} (A : SmgrpSets@{o so}) (m : nat)
  (x y : sg_ob A) (t : Tup@{o} (sg_ob A) m) :
  t_alg[projT2 (fobj[Sg_K@{o so}] A)] (existT _ (S (S m)) (x, (y, t)))
    = t_alg[projT2 (fobj[Sg_K@{o so}] A)]
        (existT _ (S m) (sg_mul A x y, t)) := eq_refl.

Example Sg_K_map@{o so} {A B : SmgrpSets@{o so}}
  (f : A ~{SmgrpSets@{o so}}~> B) :
  t_alg_hom[fmap[Sg_K@{o so}] f] = `1 f := eq_refl.

(* The same as a system: ⟨S, 1, ν2, …⟩ with ν2 the multiplication. *)
Example Sg_K_system_nu@{o so} (A : SmgrpSets@{o so}) (n : nat)
  (t : Tup@{o} (sg_ob A) n) :
  nu (ws_nu (fobj[EM_to_WSys@{o so} ◯ Sg_K@{o so}] A)) n t
    = tfold1 (fun s => s) n t := eq_refl.

Example Sg_K_system_nu2@{o so} (A : SmgrpSets@{o so}) (a b : sg_ob A) :
  nu2 (ws_nu (fobj[EM_to_WSys@{o so} ◯ Sg_K@{o so}] A)) a b = sg_mul A a b
  := eq_refl.

(* Proposition 2's functors on data. *)
Example WSys_to_EM_alg@{o so} (A : WSys@{o so}) (p : PWord@{o} (ws_set A)) :
  t_alg[projT2 (fobj[WSys_to_EM@{o so}] A)] p = nu_sharp (ws_nu A) p
  := eq_refl.

Example EM_to_WSys_nu@{o so} (x : WordAlg@{o so}) (n : nat)
  (t : Tup@{o} (projT1 x) n) :
  nu (ws_nu (fobj[EM_to_WSys@{o so}] x)) n t
    = t_alg[projT2 x] (existT _ n t) := eq_refl.

(* The round trips on data. *)
Example Smgrp_EM_rt_carrier@{o so} (A : SmgrpSets@{o so}) :
  sg_ob (fobj[EM_to_Smgrp@{o so} ◯ Sg_K@{o so}] A) = sg_ob A := eq_refl.

Example Smgrp_EM_rt_mul@{o so} (A : SmgrpSets@{o so}) :
  sg_mul (fobj[EM_to_Smgrp@{o so} ◯ Sg_K@{o so}] A) = sg_mul A := eq_refl.

Example Smgrp_EM_rt_hom@{o so} {A B : SmgrpSets@{o so}}
  (f : A ~{SmgrpSets@{o so}}~> B) :
  sg_fun (fmap[EM_to_Smgrp@{o so} ◯ Sg_K@{o so}] f) = sg_fun f := eq_refl.

Example EM_Smgrp_rt_carrier@{o so} (x : WordAlg@{o so}) :
  projT1 (fobj[Sg_K@{o so} ◯ EM_to_Smgrp@{o so}] x) = projT1 x := eq_refl.

Example EM_Smgrp_rt_alg_hom@{o so} {x y : WordAlg@{o so}}
  (f : x ~{WordAlg@{o so}}~> y) :
  t_alg_hom[fmap[Sg_K@{o so} ◯ EM_to_Smgrp@{o so}] f] = t_alg_hom[f]
  := eq_refl.

Example WSys_rt_set@{o so} (A : WSys@{o so}) :
  ws_set (fobj[EM_to_WSys@{o so} ◯ WSys_to_EM@{o so}] A) = ws_set A
  := eq_refl.

Example WSys_rt_nu@{o so} (A : WSys@{o so}) :
  ws_nu (fobj[EM_to_WSys@{o so} ◯ WSys_to_EM@{o so}] A) = ws_nu A
  := eq_refl.

Example WSys_rt_unit@{o so} (A : WSys@{o so}) :
  ws_unit (fobj[EM_to_WSys@{o so} ◯ WSys_to_EM@{o so}] A) = ws_unit A
  := eq_refl.

Example WSys_rt_hom@{o so} {A B : WSys@{o so}} (f : A ~{WSys@{o so}}~> B) :
  `1 (fmap[EM_to_WSys@{o so} ◯ WSys_to_EM@{o so}] f) = `1 f := eq_refl.

Example EM_WSys_rt_carrier@{o so} (x : WordAlg@{o so}) :
  projT1 (fobj[WSys_to_EM@{o so} ◯ EM_to_WSys@{o so}] x) = projT1 x
  := eq_refl.

Example EM_WSys_rt_alg_hom@{o so} {x y : WordAlg@{o so}}
  (f : x ~{WordAlg@{o so}}~> y) :
  t_alg_hom[fmap[WSys_to_EM@{o so} ◯ EM_to_WSys@{o so}] f] = t_alg_hom[f]
  := eq_refl.

(* Every component of the natural isomorphisms is the identity, at a
   variable object, to and from. *)
Example Smgrp_EM_iso_to_from_component@{o so c} (x : WordAlg@{o so}) :
  (t_alg_hom[to (projT1 (iso_to_from Smgrp_EM_iso@{o so c}) x)],
   t_alg_hom[from (projT1 (iso_to_from Smgrp_EM_iso@{o so c}) x)])
    = (@setoid_morphism_id@{o o o} (projT1 x),
       @setoid_morphism_id@{o o o} (projT1 x)) := eq_refl.

Example Smgrp_EM_iso_from_to_component@{o so c} (A : SmgrpSets@{o so}) :
  (sg_fun (to (projT1 (iso_from_to Smgrp_EM_iso@{o so c}) A)),
   sg_fun (from (projT1 (iso_from_to Smgrp_EM_iso@{o so c}) A)))
    = ((fun a : sg_ob A => a), (fun a : sg_ob A => a)) := eq_refl.

Example Smgrp_EM_counit_component@{o so} (x : WordAlg@{o so}) :
  (t_alg_hom[to (projT1 (@equivalence_counit _ _ _
                           Smgrp_EM_equivalence@{o so}) x)],
   t_alg_hom[from (projT1 (@equivalence_counit _ _ _
                             Smgrp_EM_equivalence@{o so}) x)])
    = (@setoid_morphism_id@{o o o} (projT1 x),
       @setoid_morphism_id@{o o o} (projT1 x)) := eq_refl.

Example Smgrp_EM_unit_component@{o so} (A : SmgrpSets@{o so}) :
  (sg_fun (to (projT1 (@equivalence_unit _ _ _
                         Smgrp_EM_equivalence@{o so}) A)),
   sg_fun (from (projT1 (@equivalence_unit _ _ _
                           Smgrp_EM_equivalence@{o so}) A)))
    = ((fun a : sg_ob A => a), (fun a : sg_ob A => a)) := eq_refl.

Example WSys_EM_iso_to_from_component@{o so c} (x : WordAlg@{o so}) :
  (t_alg_hom[to (projT1 (iso_to_from WSys_EM_iso@{o so c}) x)],
   t_alg_hom[from (projT1 (iso_to_from WSys_EM_iso@{o so c}) x)])
    = (@setoid_morphism_id@{o o o} (projT1 x),
       @setoid_morphism_id@{o o o} (projT1 x)) := eq_refl.

Example WSys_EM_iso_from_to_component@{o so c} (A : WSys@{o so}) :
  (`1 (to (projT1 (iso_from_to WSys_EM_iso@{o so c}) A)),
   `1 (from (projT1 (iso_from_to WSys_EM_iso@{o so c}) A)))
    = (@setoid_morphism_id@{o o o} (ws_set A),
       @setoid_morphism_id@{o o o} (ws_set A)) := eq_refl.
