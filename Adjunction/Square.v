Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Sets.
Require Import Category.Adjunction.Compose.
Require Import Category.Adjunction.Conjugate.
Require Import Category.Adjunction.Map.

Generalizable All Variables.

(** * Adjoint squares (Kelly) and Palmquist's bijection *)

(* nLab: https://ncatlab.org/nlab/show/mate
   nLab: https://ncatlab.org/nlab/show/adjoint+functor

   Mac Lane, "Categories for the Working Mathematician", 2nd ed., §IV.7,
   book p. 103, Exercises 4 and 5, verbatim:

     "4. (Kelly.) An adjoint square is an array of categories, functors,
      adjunctions, and natural transformations ⟨F,G,φ⟩ : X ⇀ A,
      ⟨F',G',φ'⟩ : X' ⇀ A', H : X → X', K : A → A', σ : F'H ⇒ KF,
      τ : HG ⇒ G'K, such that the following diagram of hom-sets always
      commutes
          A(Fx,a) --K--> A'(KFx,Ka) --(σx)*--> A'(F'Hx,Ka)
            |φ                                      |φ'
          X(x,Ga) --H--> X'(Hx,HGa) --(τa)*--> X'(Hx,G'Ka).
      Express this last condition variously in terms of unit and counit of
      the adjunctions and prove that each of σ, τ determines the other.
      (The case H = K = identity functor is that treated in the text
      above.)

      5. (Palmquist.) Given H, K, and the two adjunctions as in Exercise 4,
      establish a bijection between natural transformations α : F'HG ⇒ K
      and natural transformations β : H ⇒ G'KF."

   (The book sets the first hom-set arrow as a superscript star,
   precomposition with σx, and the second as a subscript star,
   postcomposition with τa; both are transcribed above as a plain star.
   The code has them the same way round: in [AdjointSquare] σ enters as
   [fmap[K] k ∘ sigma x] and τ as [tau a ∘ fmap[L] ⌊ k ⌋].)

   Riehl, "Category Theory in Context", 2nd ed., §4.3, Exercise 4.3.v asks
   in addition that the mates correspondence commute with horizontal
   composition of the bounding functors and with vertical composition of
   the adjunctions.

   TREE VOCABULARY.  Mac Lane's X is D, his A is C, his G is U, his H is
   L, and his K is K; the two adjunctions are A : F ⊣ U with F : D ⟶ C
   and U : C ⟶ D, and A' : F' ⊣ U' with F' : D' ⟶ C' and U' : C' ⟶ D'.
   His σ is a [SqSigma], his τ a [SqTau], and his commuting square is
   [AdjointSquare].

   ** What is here

   (A) The condition [AdjointSquare], quantified over EVERY transposable
   arrow, with [AdjointSquareFrom] (the same square read through the
   inverse transposes) and Mac Lane's two unit/counit forms
   [AdjointSquareUnit] and [AdjointSquareCounit]; the two mate operators
   [sq_mate] and [sq_mate_inv], defined by the transpose exactly as
   Adjunction/Conjugate.v:328/:345 defines [conj_mate]/[conj_mate_inv];
   and the ledger of passages between the four forms, in which EVERY
   hypothesis is an explicit argument so that each type records what it
   consumes.  [adjoint_square_iff_mate] and [adjoint_square_iff_mate_inv]
   are "each of σ, τ determines the other".

   (B) Five [eq_refl] identifications with Adjunction/Conjugate.v at
   K = L = Id and five with Adjunction/Map.v at invertible comparison
   families, so this file is an UPGRADE of those two rather than a
   parallel construction; neither donor is edited and neither is
   re-derived.

   (C) [Transform]-typed wrappers [SqMate]/[SqMateInv] and the bijection
   [square_bijection] : sq_dom ≅ sq_cod in Sets, packaged with
   Adjunction/Conjugate.v:440's inline [{| carrier := … |}] idiom.

   (D) Palmquist's bijection [palmquist_bijection], built DIRECTLY with
   both round trips, together with the two generic factor bijections
   ([precomp_bijection] along F ⊣ U, [postcomp_bijection] along F' ⊣ U')
   and two factorisations of it: [palm_to_via_mate] through the mate, and
   [palm_two_factor_agrees]/[palm_two_factor_spliced] through the two
   factors.

   (E) Riehl 4.3.v as two compatibility LAWS: [adjoint_square_paste_h] and
   [sq_mate_paste_h] for horizontal pasting, [adjoint_square_paste_v] and
   [sq_mate_paste_v] for vertical pasting over Adjunction/Compose.v:173's
   [Adjunction_Compose].  Both mate laws are proved BY UNIQUENESS
   ([SqMate_uniq]), not by a second chase.

   ** The design decision, and why (measured)

   The condition is stated over BARE COMPONENT FAMILIES rather than over
   [Transform]s, and that choice is forced twice over.

   First, it is what makes (B) hold at Leibniz equality of TYPES.  At
   K = L = Id a [Transform]-typed condition would speak of
   F' ◯ Id[D] ⟹ Id[C] ◯ F, which is not the type F' ⟹ F: the two functor
   records carry different [fmap_respects], [fmap_id] and [fmap_comp]
   fields, which are data here.  Over bare families the padding does not
   arise, because [Compose]'s object action is literal composition
   (Theory/Functor.v:261, inside the :259 [Program Definition]), so a
   component already has the type the bare family wants.

   Second, it is what keeps the two adjunctions' hom universes APART.
   Measured with [About] under [Set Printing Universes] on this file:
   THIRTY-SEVEN constants — the whole of section (A), the ten engine
   constants [AdjointSquare], [SqSigma], [SqTau], [SigmaNat], [TauNat],
   [sq_mate], [sq_mate_inv], [adjoint_square_iff_mate],
   [adjoint_square_iff_mate_inv] and [sq_hom_iff_from] among them, plus
   the five Map.v readbacks — carry exactly the two block equations u0 = u2 and
   u6 = u8 — each adjunction's own two hom levels — and relate the two
   PAIRS by BOUNDS only, never by an equation: u0 <= u6 and u2 <= u8, with
   the redundant consequence u0 <= u8 or u2 <= u6 also printed on six of
   the ten engine constants.  Every [Transform]-typed constant in (C), and
   every four-category one in (D), instead carries u0 = u2, u0 = u6,
   u0 = u8 and u6 = u8: all four categories' hom-and-proof levels become
   one.  The two generic factor bijections of (D) bind THREE categories and
   carry u0 = u2 and u0 = u6 only; the pasting sections of (E) collapse
   differently and are described below.  The donor of the four-equation
   collapse is [Compose]: under a section declaring the two hom levels
   strictly apart, the whole body of the condition is formable — the two
   component families, [AdjointSquare] itself, [sq_mate] and
   [adjoint_square_iff_mate] are all accepted — while [F' ◯ L], [K ◯ F],
   [L ◯ U] and [U' ◯ K] are each refused with "universe inconsistency".

   Adjunction/Map.v's four passages are NOT reusable by instantiation, and
   the obstruction is in the TYPE rather than in the proof terms:
   [MapAdjHom] demands a family of ISOMORPHISM records ∀ x, K (F x) ≅
   F' (L x), of which a bare family supplies one leg and cannot manufacture
   the other three fields.  The four legs are therefore rebuilt here, with
   Map.v's own proofs, [to (be _)]/[from (al _)] replaced by [tau _]/
   [sigma _] and [compare_left_nat_from Hal] by the bare [SigmaNat]
   hypothesis; no new argument appears anywhere.  Map.v is not weakened:
   it becomes the invertible-comparison instance, [square_is_map_adj_hom].

   The two naturality donors are consumed rather than copied:
   Adjunction/Conjugate.v:161's [conj_unit_nat] and :168's
   [conj_counit_nat] discharge with only one adjunction and are used as
   [conj_unit_nat A g] / [conj_counit_nat A f].

   ** The ledger, by what each passage consumes

   NO naturality at all: [sq_hom_to_unit], [sq_hom_to_counit],
   [sq_hom_to_mate], [sq_hom_to_mate_inv], and [sq_hom_iff_from] in BOTH
   directions.  Only [TauNat tau]: [sq_unit_to_hom], [sq_mate_inv_to_hom],
   [sq_hom_iff_unit], [adjoint_square_iff_mate_inv],
   [adjoint_square_sq_mate_inv], [sq_mate_mate_inv], [sq_mate_inv_nat].
   Only [SigmaNat sigma]: [sq_counit_to_hom], [sq_mate_to_hom],
   [sq_hom_iff_counit], [adjoint_square_iff_mate],
   [adjoint_square_sq_mate], [sq_mate_inv_mate], [sq_mate_nat].  Both:
   [sq_unit_iff_counit].  This mirrors Map.v's ledger; the ADDITION beyond
   it is [sq_hom_iff_from], which consumes neither and which Map.v does not
   state at all (its identity-bounding-functor case is
   Adjunction/Conjugate.v:145's [conjugate_iff_from]).

   ** Strengths, strict first

   TWENTY-SIX statements close by [eq_refl] (criterion: a declaration whose
   body is literally [eq_refl], counted over the whole file):
   [square_is_conjugate], [square_unit_is_conjugate_unit],
   [square_counit_is_conjugate_counit], [sq_mate_is_conj_mate],
   [sq_mate_inv_is_conj_mate_inv], [square_is_map_adj_hom],
   [square_unit_is_map_adj_unit], [square_counit_is_map_adj_counit],
   [tau_nat_is_compare_right], [sigma_nat_is_compare_left_from],
   [adjoint_square_T_is_bare], [SqMate_component], [SqMateInv_component],
   [sq_dom_setoid], [sq_cod_setoid], [bracket_fobj_left],
   [bracket_fmap_left], [comp_type_left], [comp_type_right],
   [bracket_transform_type_right], [palm_dom_setoid], [palm_cod_setoid],
   [sq_mate_is_post_of_pre], [sq_mate_inv_is_pre_of_post],
   [fun_comp_assoc_component] and [AB_to_strict].  One of the twenty-six,
   [bracket_transform_type_right], is an [X = X] after parsing: [◯]
   associates to the left, so [L ⟹ U' ◯ K ◯ F] and
   [L ⟹ (U' ◯ K) ◯ F] elaborate to the same term, and the Example records
   the parser's convention rather than a bracketing fact.  The bracketing
   content sits in [bracket_fobj_left] and [bracket_fmap_left], which
   compare [F' ◯ L ◯ U] against [F' ◯ (L ◯ U)], two different records.

   Two of them carry the load in (D).  [sq_mate_is_post_of_pre] and
   [sq_mate_inv_is_pre_of_post] say that the mate ABSORBS one pre/post
   pair on the nose, which is exactly why the mate route through
   [palm_via_mate] lands every endpoint at the natural left-associated
   bracketing and needs no associator, while the two-factor route
   re-brackets its codomain and does.  [AB_to_strict] says the composite
   adjunction's transposes are definitional, which is why the vertical
   pasting goes entirely through the hom-set form and never touches the
   composite's unit or counit — the composite's unit agrees with the
   whiskered formula only up to ≈ ([AB_unit_upto], and the strict form is
   refuted).

   The identifications that hold only up to ≈, each with its cause:
   [palm_to_via_mate] (one naturality of α at ε (F x) plus
   [fmap_counit_unit]); [palm_two_factor_agrees] (one [to_adj_nat_l]);
   [palm_two_factor_spliced] (the same, plus the associator's component,
   which [fun_comp_assoc_component] pins as [fmap[U'] id] and NOT [id]);
   [sq_mate_pasting] and [sq_mate_inv_pasting] (one [to_adj_unit] resp.
   [from_adj_counit]).  Also refuted at [eq_refl], and not repaired here:
   the two bracketings (F' ◯ L) ◯ U and F' ◯ (L ◯ U) are different functor
   records although their object and arrow actions agree, so the whole-
   [Transform] statements are bracketing-sensitive where the componentwise
   ones are not; and at K = L = Id the RECORD-level comparisons with
   Adjunction/Conjugate.v ([sq_dom] against [conj_dom], [square_bijection]
   against [conjugate_bijection]) are refused, though the COMPONENT-level
   ones above are [eq_refl].

   ** Universes, off both binder and block

   Every constant that binds all four categories — 97 of the 156 — is over
   C : Category@{u u0 u0}, D : Category@{u1 u2 u2}, C' : Category@{u5 u6 u6},
   D' : Category@{u7 u8 u8}; and in EVERY [Category] binder of every
   constant in the file, the three-category factor bijections and the
   six-category pasting sections included, hom is identified with proof by
   reusing the level variable, with NO block equation saying so; a
   block-only reading reports no such identification.  One donor is
   [Adjunction]: under a section declaring ch < cp, the category, its
   hom-sets, its identities, functors in BOTH directions and a [Transform]
   between two of them are all accepted, and [Fu ⊣ Uu] is refused.
   [Compose] is a SECOND, independent donor: in the same section, with no
   adjunction in the command, [Uq ◯ Fq] is refused too, so [Adjunction] is
   sufficient but not necessary (Test/ProbeSquare398.v, N24).
   The identification of C's hom level with D's has a different and earlier
   donor, functors in both directions: [Functor] bounds source-hom by
   target-hom, so under ch < dh the type Cu ⟶ Du is accepted and Du ⟶ Cu
   is refused, before any adjunction is formed.  Neither is claimed
   unavoidable; both are inherited.

   The four OBJECT universes are free of one another throughout, and there
   is NO word-bounded [Set] in any binder or any block of the constants
   measured.  The pasting sections collapse more, and visibly: the
   horizontal one identifies the three columns' hom levels (u2 = u7,
   u2 = u10) and the vertical one identifies six categories' hom-and-proof
   levels to a single level.

   ** Pinned

   With three exceptions named at the end of this section, every
   refutation this header reports, and every universe donor it names, is
   pinned in Test/ProbeSquare398.v: 25 refutation commands = 1 instrument
   + 24 negatives (12 conversion, 3 typing, 9 formability), each stripped
   one at a time and compiled alone with its whole error read,
   rename-simulated 14/14 over the constants the negatives name.  The
   bridge Instance/Cat/Bicategory/Square.v's strict form is pinned in the
   same file.  The exceptions: of the five identifications listed above
   as holding only up to ≈, two are pinned (N1 and N2) and three are NOT
   — the strict [eq_refl] forms of [palm_two_factor_spliced],
   [sq_mate_pasting] and [sq_mate_inv_pasting] were each MEASURED to be
   refused, out of tree, and are guarded nowhere.

   ** Not delivered

   No category and no double category of adjunction squares: no identity
   square, no associativity or unit law for either pasting, no interchange
   between the two pastings, and no setoid on squares — so the mate is NOT
   exhibited AS A FUNCTOR, and Riehl 4.3.v is discharged here as the two
   compatibility LAWS in ordinary-category vocabulary: the Cat case of
   Riehl's bicategorical statement, though nothing here is formed in Cat.
   Theory/Bicategory/Mates.v's descope ledger 10, which is about an
   ARBITRARY bicategory, is untouched and that file is not edited.  No
   pasting for [sq_mate_inv]; nothing relates either pasting to
   Adjunction/Conjugate.v:474's [conjugate_compose]; no naturality of any
   of the identifications in the bounding functors; no concrete witness at
   a named pair of adjunctions; nothing is registered as an [Instance].
   The comparison with Theory/Bicategory/Mates.v's [mate] is NOT here: it
   is the sibling Instance/Cat/Bicategory/Square.v, kept separate because
   requiring Instance/Cat/Bicategory/Adjunction pulls in
   Adjunction/Natural/Transformation, whose [unit] and [counit] shadow
   Theory/Adjunction.v's.

   ** Three sentences of the issue that are stale

   Its "Missing for Exercise 4: the adjoint-square condition itself,
   quantified over all transposable arrows" is stale since #393:
   Adjunction/Map.v:289's [MapAdjHom] IS that square over every
   transposable arrow.  What was genuinely absent is only the BARE-FAMILY
   generality, and [square_is_map_adj_hom] measures exactly that gap by
   closing it at [eq_refl].  Its "the exercise's first ask … has exactly
   one in-tree expression" is stale twice over: Map.v:294/:299 state the
   unit and counit forms with six passages between them at :304, :313,
   :328, :339, :355 and :361, and at H = K = Id
   Adjunction/Conjugate.v:309's [conjugate_characterizations] gives four
   equivalent forms.  And its "nor the packaging as an isomorphism of
   setoids" overlooks the precedent this file copies,
   Adjunction/Conjugate.v:445's [conjugate_bijection].  Two further notes.
   The Riehl checkbox's command
   [rg 'mate_compose|mate_functorial|mate_hcomp|mate_vcomp'] is claimed to
   return no hits; as written, un-anchored, and run over the tree EXCLUDING
   this file (which quotes the command and so matches itself), it returns
   18 lines in 5 files — Adjunction/Choice.v, Adjunction/Parameter.v,
   Adjunction/Conjugate.v, Instance/Adj.v and Test/ProbeChoice397.v — and
   all 18 match [conj_mate_compose] as a substring.  The claim survives
   only under [rg -w], which returns none.  And the
   "associator bookkeeping lining up the two factors" turns out to be
   AVOIDABLE rather than merely unwritten: the mate route needs none, and
   where one is wanted the tree already supplies it as
   Theory/Natural/Transformation.v:201's [fun_comp_assoc]. *)

(* ====================================================================== *)
(* (A) The condition, over BARE component families.                       *)
(* ====================================================================== *)

Section AdjointSquareCompare.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').

Notation "⌊ f ⌋"  := (to   (@adj _ _ _ _ A  _ _) f).
Notation "⌈ f ⌉"  := (from (@adj _ _ _ _ A  _ _) f).
Notation "⌊ f ⌋²" := (to   (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "⌈ f ⌉²" := (from (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "'η' x"  := (@unit   _ _ _ _ A  x) (at level 9).
Notation "'ε' a"  := (@counit _ _ _ _ A  a) (at level 9).
Notation "'η²' x" := (@unit   _ _ _ _ A' x) (at level 9).
Notation "'ε²' a" := (@counit _ _ _ _ A' a) (at level 9).

(* The two comparison families of Mac Lane's array. *)

Definition SqSigma : Type := ∀ x : D, F' (L x) ~> K (F x).
Definition SqTau   : Type := ∀ a : C, L (U a) ~> U' (K a).

(* Naturality, stated on the bare families.  Neither predicate mentions an
   adjunction, exactly as Map.v's [CompareLeftNat]/[CompareRightNat] do not. *)

Definition SigmaNat (sigma : SqSigma) : Type :=
  ∀ (x y : D) (f : x ~> y),
    sigma y ∘ fmap[F'] (fmap[L] f) ≈ fmap[K] (fmap[F] f) ∘ sigma x.

Definition TauNat (tau : SqTau) : Type :=
  ∀ (a b : C) (f : a ~> b),
    tau b ∘ fmap[L] (fmap[U] f) ≈ fmap[U'] (fmap[K] f) ∘ tau a.

(* Mac Lane's commuting square of hom-sets, quantified over every
   transposable arrow rather than evaluated at one distinguished argument. *)

Definition AdjointSquare (sigma : SqSigma) (tau : SqTau) : Type :=
  ∀ (x : D) (a : C) (k : F x ~> a),
    ⌊ fmap[K] k ∘ sigma x ⌋² ≈ tau a ∘ fmap[L] ⌊ k ⌋.

(* The same square read through the inverse transposes. *)

Definition AdjointSquareFrom (sigma : SqSigma) (tau : SqTau) : Type :=
  ∀ (x : D) (a : C) (g : x ~> U a),
    ⌈ tau a ∘ fmap[L] g ⌉² ≈ fmap[K] ⌈ g ⌉ ∘ sigma x.

(* Mac Lane's Lη = η'L and Kε = ε'K, with the comparison families split
   across the two sides in Map.v's orientation. *)

Definition AdjointSquareUnit (sigma : SqSigma) (tau : SqTau) : Type :=
  ∀ x : D, tau (F x) ∘ fmap[L] (η x) ≈ fmap[U'] (sigma x) ∘ η² (L x).

Definition AdjointSquareCounit (sigma : SqSigma) (tau : SqTau) : Type :=
  ∀ a : C, fmap[K] (ε a) ∘ sigma (U a) ≈ ε² (K a) ∘ fmap[F'] (tau a).

(* ---- the two mate operators, defined BY THE TRANSPOSE ---- *)

Definition sq_mate (sigma : SqSigma) : SqTau :=
  λ a, ⌊ fmap[K] (ε a) ∘ sigma (U a) ⌋².

Definition sq_mate_inv (tau : SqTau) : SqSigma :=
  λ x, ⌈ tau (F x) ∘ fmap[L] (η x) ⌉².

(* The whiskered pasting spellings, up to ≈. *)

Lemma sq_mate_pasting (sigma : SqSigma) (a : C) :
  sq_mate sigma a
    ≈ fmap[U'] (fmap[K] (ε a) ∘ sigma (U a)) ∘ η² (L (U a)).
Proof. unfold sq_mate; now rewrite (to_adj_unit (H:=A')). Qed.

Lemma sq_mate_inv_pasting (tau : SqTau) (x : D) :
  sq_mate_inv tau x
    ≈ ε² (K (F x)) ∘ fmap[F'] (tau (F x) ∘ fmap[L] (η x)).
Proof. unfold sq_mate_inv; now rewrite (from_adj_counit (H:=A')). Qed.

(* ---- the ledger; every hypothesis is an explicit argument ---- *)

Lemma sq_hom_to_unit (sigma : SqSigma) (tau : SqTau) :
  AdjointSquare sigma tau → AdjointSquareUnit sigma tau.
Proof.
  intros H x.
  pose proof (H x (F x) id) as Hx.
  rewrite fmap_id, id_left in Hx.
  rewrite (to_adj_unit (H:=A')) in Hx.
  now rewrite <- Hx.
Qed.

Lemma sq_unit_to_hom (sigma : SqSigma) (tau : SqTau) :
  TauNat tau → AdjointSquareUnit sigma tau → AdjointSquare sigma tau.
Proof.
  intros Ht H x a k.
  rewrite (to_adj_unit (H:=A')).
  rewrite fmap_comp.
  rewrite <- comp_assoc.
  rewrite <- (H x : _ ≈ _).
  rewrite comp_assoc.
  rewrite <- (Ht (F x) a k).
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  now rewrite <- (to_adj_unit (H:=A)).
Qed.

Lemma sq_hom_to_counit (sigma : SqSigma) (tau : SqTau) :
  AdjointSquare sigma tau → AdjointSquareCounit sigma tau.
Proof.
  intros H a.
  pose proof (H (U a) a (ε a)) as Ha.
  rewrite (to_adj_counit (H:=A)) in Ha.
  rewrite fmap_id, id_right in Ha.
  apply (snd (adj_univ (H:=A') _ _)) in Ha.
  rewrite Ha.
  now rewrite (from_adj_counit (H:=A')).
Qed.

Lemma sq_counit_to_hom (sigma : SqSigma) (tau : SqTau) :
  SigmaNat sigma → AdjointSquareCounit sigma tau → AdjointSquare sigma tau.
Proof.
  intros Hs H x a k.
  apply (fst (adj_univ (H:=A') _ _)).
  rewrite (from_adj_counit (H:=A')).
  rewrite fmap_comp.
  rewrite comp_assoc.
  rewrite <- (H a : _ ≈ _).
  rewrite <- comp_assoc.
  rewrite (Hs _ _ ⌊ k ⌋).
  rewrite comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- (from_adj_counit (H:=A)).
  now rewrite (to_adj_comp_law (H:=A)).
Qed.

Theorem sq_hom_iff_unit (sigma : SqSigma) (tau : SqTau) :
  TauNat tau → (AdjointSquare sigma tau ↔ AdjointSquareUnit sigma tau).
Proof.
  intros Ht; split; [ exact (sq_hom_to_unit sigma tau)
                    | exact (sq_unit_to_hom sigma tau Ht) ].
Qed.

Theorem sq_hom_iff_counit (sigma : SqSigma) (tau : SqTau) :
  SigmaNat sigma → (AdjointSquare sigma tau ↔ AdjointSquareCounit sigma tau).
Proof.
  intros Hs; split; [ exact (sq_hom_to_counit sigma tau)
                    | exact (sq_counit_to_hom sigma tau Hs) ].
Qed.

Theorem sq_unit_iff_counit (sigma : SqSigma) (tau : SqTau) :
  SigmaNat sigma → TauNat tau →
  (AdjointSquareUnit sigma tau ↔ AdjointSquareCounit sigma tau).
Proof.
  intros Hs Ht; split; intro H.
  - exact (sq_hom_to_counit sigma tau (sq_unit_to_hom sigma tau Ht H)).
  - exact (sq_hom_to_unit sigma tau (sq_counit_to_hom sigma tau Hs H)).
Qed.

Theorem sq_hom_iff_from (sigma : SqSigma) (tau : SqTau) :
  AdjointSquare sigma tau ↔ AdjointSquareFrom sigma tau.
Proof.
  split.
  - intros H x a g.
    pose proof (H x a ⌈ g ⌉) as Hg.
    rewrite (from_adj_comp_law (H:=A)) in Hg.
    rewrite <- Hg.
    now rewrite (to_adj_comp_law (H:=A')).
  - intros H x a k.
    pose proof (H x a ⌊ k ⌋) as Hk.
    rewrite (to_adj_comp_law (H:=A)) in Hk.
    rewrite <- Hk.
    now rewrite (from_adj_comp_law (H:=A')).
Qed.

(* ---- each of sigma, tau determines the other ---- *)

Theorem sq_hom_to_mate (sigma : SqSigma) (tau : SqTau) :
  AdjointSquare sigma tau → ∀ a, tau a ≈ sq_mate sigma a.
Proof.
  intros H a.
  unfold sq_mate.
  rewrite (H (U a) a (ε a)).
  rewrite (to_adj_counit (H:=A)).
  now rewrite fmap_id, id_right.
Qed.

Theorem sq_mate_to_hom (sigma : SqSigma) (tau : SqTau) :
  SigmaNat sigma → (∀ a, tau a ≈ sq_mate sigma a) → AdjointSquare sigma tau.
Proof.
  intros Hs H.
  apply (sq_counit_to_hom sigma tau Hs).
  intros a.
  rewrite (H a).
  unfold sq_mate.
  rewrite <- (from_adj_counit (H:=A')).
  now rewrite (to_adj_comp_law (H:=A')).
Qed.

Theorem adjoint_square_iff_mate (sigma : SqSigma) (tau : SqTau) :
  SigmaNat sigma →
  (AdjointSquare sigma tau ↔ (∀ a, tau a ≈ sq_mate sigma a)).
Proof.
  intros Hs; split; [ exact (sq_hom_to_mate sigma tau)
                    | exact (sq_mate_to_hom sigma tau Hs) ].
Qed.

Theorem sq_hom_to_mate_inv (sigma : SqSigma) (tau : SqTau) :
  AdjointSquare sigma tau → ∀ x, sigma x ≈ sq_mate_inv tau x.
Proof.
  intros H x.
  unfold sq_mate_inv.
  rewrite (sq_hom_to_unit sigma tau H x).
  rewrite <- (to_adj_unit (H:=A')).
  now rewrite (to_adj_comp_law (H:=A')).
Qed.

Theorem sq_mate_inv_to_hom (sigma : SqSigma) (tau : SqTau) :
  TauNat tau → (∀ x, sigma x ≈ sq_mate_inv tau x) → AdjointSquare sigma tau.
Proof.
  intros Ht H.
  apply (sq_unit_to_hom sigma tau Ht).
  intros x.
  rewrite (H x).
  unfold sq_mate_inv.
  rewrite <- (to_adj_unit (H:=A')).
  now rewrite (from_adj_comp_law (H:=A')).
Qed.

Theorem adjoint_square_iff_mate_inv (sigma : SqSigma) (tau : SqTau) :
  TauNat tau →
  (AdjointSquare sigma tau ↔ (∀ x, sigma x ≈ sq_mate_inv tau x)).
Proof.
  intros Ht; split; [ exact (sq_hom_to_mate_inv sigma tau)
                    | exact (sq_mate_inv_to_hom sigma tau Ht) ].
Qed.

(* ---- naturality of the two mates ---- *)

Lemma sq_mate_nat (sigma : SqSigma) : SigmaNat sigma → TauNat (sq_mate sigma).
Proof.
  intros Hs a b f.
  unfold sq_mate.
  rewrite <- (to_adj_nat_r (Adjunction:=A')).
  rewrite <- (to_adj_nat_l (Adjunction:=A')).
  apply (to_adj_respects (H:=A')).
  rewrite <- !comp_assoc.
  rewrite (Hs _ _ (fmap[U] f)).
  rewrite !comp_assoc.
  rewrite <- !fmap_comp.
  apply compose_respects; [| reflexivity ].
  apply fmap_respects.
  now rewrite (conj_counit_nat A f).
Qed.

Lemma sq_mate_inv_nat (tau : SqTau) : TauNat tau → SigmaNat (sq_mate_inv tau).
Proof.
  intros Ht x y f.
  unfold sq_mate_inv.
  rewrite <- (from_adj_nat_r (Adjunction:=A')).
  rewrite <- (from_adj_nat_l (Adjunction:=A')).
  apply (from_adj_respects (H:=A')).
  rewrite <- comp_assoc.
  rewrite <- fmap_comp.
  rewrite <- (conj_unit_nat A f).
  rewrite fmap_comp.
  rewrite !comp_assoc.
  now rewrite (Ht _ _ (fmap[F] f)).
Qed.

(* ---- existence, and the two round trips ---- *)

Theorem adjoint_square_sq_mate (sigma : SqSigma) :
  SigmaNat sigma → AdjointSquare sigma (sq_mate sigma).
Proof.
  intros Hs; apply (sq_mate_to_hom sigma (sq_mate sigma) Hs).
  intro a; reflexivity.
Qed.

Theorem adjoint_square_sq_mate_inv (tau : SqTau) :
  TauNat tau → AdjointSquare (sq_mate_inv tau) tau.
Proof.
  intros Ht; apply (sq_mate_inv_to_hom (sq_mate_inv tau) tau Ht).
  intro x; reflexivity.
Qed.

Corollary sq_mate_inv_mate (sigma : SqSigma) :
  SigmaNat sigma → ∀ x, sq_mate_inv (sq_mate sigma) x ≈ sigma x.
Proof.
  intros Hs x; symmetry.
  exact (sq_hom_to_mate_inv sigma (sq_mate sigma)
           (adjoint_square_sq_mate sigma Hs) x).
Qed.

Corollary sq_mate_mate_inv (tau : SqTau) :
  TauNat tau → ∀ a, sq_mate (sq_mate_inv tau) a ≈ tau a.
Proof.
  intros Ht a; symmetry.
  exact (sq_hom_to_mate (sq_mate_inv tau) tau
           (adjoint_square_sq_mate_inv tau Ht) a).
Qed.

End AdjointSquareCompare.

(* ====================================================================== *)
(* (B) The condition SUBSUMES its two in-tree special cases, at Leibniz   *)
(*     equality of TYPES.                                                 *)
(* ====================================================================== *)

Section SquareIdCase.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context {F' : D ⟶ C} {U' : C ⟶ D}.
Context (A : F ⊣ U) (A' : F' ⊣ U').

Example square_is_conjugate (s : F' ⟹ F) (t : U ⟹ U') :
  AdjointSquare A A' Id[C] Id[D] (transform[s]) (transform[t])
    = Conjugate A A' s t := eq_refl.

Example square_unit_is_conjugate_unit (s : F' ⟹ F) (t : U ⟹ U') :
  AdjointSquareUnit A A' Id[C] Id[D] (transform[s]) (transform[t])
    = ConjugateUnit A A' s t := eq_refl.

Example square_counit_is_conjugate_counit (s : F' ⟹ F) (t : U ⟹ U') :
  AdjointSquareCounit A A' Id[C] Id[D] (transform[s]) (transform[t])
    = ConjugateCounit A A' s t := eq_refl.

Example sq_mate_is_conj_mate (s : F' ⟹ F) (a : C) :
  sq_mate A A' Id[C] Id[D] (transform[s]) a = conj_mate A A' s a := eq_refl.

Example sq_mate_inv_is_conj_mate_inv (t : U ⟹ U') (x : D) :
  sq_mate_inv A A' Id[C] Id[D] (transform[t]) x
    = conj_mate_inv A A' t x := eq_refl.

End SquareIdCase.

Section SquareMapCase.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').
Context (al : ∀ x : D, K (F x) ≅ F' (L x)).
Context (be : ∀ a : C, L (U a) ≅ U' (K a)).

Example square_is_map_adj_hom :
  AdjointSquare A A' K L (fun x => from (al x)) (fun a => to (be a))
    = MapAdjHom A A' K L al be := eq_refl.

Example square_unit_is_map_adj_unit :
  AdjointSquareUnit A A' K L (fun x => from (al x)) (fun a => to (be a))
    = MapAdjUnit A A' K L al be := eq_refl.

Example square_counit_is_map_adj_counit :
  AdjointSquareCounit A A' K L (fun x => from (al x)) (fun a => to (be a))
    = MapAdjCounit A A' K L al be := eq_refl.

Example tau_nat_is_compare_right :
  TauNat K L (fun a => to (be a)) = CompareRightNat K L be := eq_refl.

Example sigma_nat_is_compare_left_from :
  SigmaNat K L (fun x => from (al x))
    = (∀ (x y : D) (f : x ~> y),
         from (al y) ∘ fmap[F'] (fmap[L] f)
           ≈ fmap[K] (fmap[F] f) ∘ from (al x)) := eq_refl.

End SquareMapCase.

(* ====================================================================== *)
(* (C) Transform-typed wrappers and the bijection in Sets.                *)
(* ====================================================================== *)

Section SquareBijection.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').

Definition AdjointSquareT
  (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) : Type :=
  AdjointSquare A A' K L (fun x => sg x) (fun a => ta a).

Example adjoint_square_T_is_bare
  (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT sg ta
    = AdjointSquare A A' K L (fun x => sg x) (fun a => ta a) := eq_refl.

(* A component family of a Transform meets the bare engine with no
   transport, and [naturality_sym] IS the naturality predicate. *)

Lemma transform_SigmaNat (s : F' ◯ L ⟹ K ◯ F) : SigmaNat K L (transform[s]).
Proof. intros x y f; exact (naturality_sym s x y f). Qed.

Lemma transform_TauNat (t : L ◯ U ⟹ U' ◯ K) : TauNat K L (transform[t]).
Proof. intros a b f; exact (naturality_sym t a b f). Qed.

Program Definition SqMate (sg : F' ◯ L ⟹ K ◯ F) : L ◯ U ⟹ U' ◯ K := {|
  transform := sq_mate A A' K L (transform[sg])
|}.
Next Obligation.
  symmetry; exact (sq_mate_nat A A' K L _ (transform_SigmaNat sg) _ _ f).
Qed.
Next Obligation.
  exact (sq_mate_nat A A' K L _ (transform_SigmaNat sg) _ _ f).
Qed.

Program Definition SqMateInv (ta : L ◯ U ⟹ U' ◯ K) : F' ◯ L ⟹ K ◯ F := {|
  transform := sq_mate_inv A A' K L (transform[ta])
|}.
Next Obligation.
  symmetry; exact (sq_mate_inv_nat A A' K L _ (transform_TauNat ta) _ _ f).
Qed.
Next Obligation.
  exact (sq_mate_inv_nat A A' K L _ (transform_TauNat ta) _ _ f).
Qed.

Example SqMate_component (sg : F' ◯ L ⟹ K ◯ F) (a : C) :
  SqMate sg a = sq_mate A A' K L (transform[sg]) a := eq_refl.

Example SqMateInv_component (ta : L ◯ U ⟹ U' ◯ K) (x : D) :
  SqMateInv ta x = sq_mate_inv A A' K L (transform[ta]) x := eq_refl.

Theorem AdjointSquareT_SqMate (sg : F' ◯ L ⟹ K ◯ F) :
  AdjointSquareT sg (SqMate sg).
Proof. exact (adjoint_square_sq_mate A A' K L _ (transform_SigmaNat sg)). Qed.

Theorem SqMate_uniq (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT sg ta → ta ≈ SqMate sg.
Proof. intros H a; exact (sq_hom_to_mate A A' K L _ _ H a). Qed.

Theorem AdjointSquareT_SqMateInv (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT (SqMateInv ta) ta.
Proof.
  exact (adjoint_square_sq_mate_inv A A' K L _ (transform_TauNat ta)).
Qed.

Theorem SqMateInv_uniq (sg : F' ◯ L ⟹ K ◯ F) (ta : L ◯ U ⟹ U' ◯ K) :
  AdjointSquareT sg ta → sg ≈ SqMateInv ta.
Proof. intros H x; exact (sq_hom_to_mate_inv A A' K L _ _ H x). Qed.

Definition sq_dom : SetoidObject := {| carrier := F' ◯ L ⟹ K ◯ F |}.
Definition sq_cod : SetoidObject := {| carrier := L ◯ U ⟹ U' ◯ K |}.

Example sq_dom_setoid :
  is_setoid sq_dom = @Transform_Setoid D C' (F' ◯ L) (K ◯ F) := eq_refl.
Example sq_cod_setoid :
  is_setoid sq_cod = @Transform_Setoid C D' (L ◯ U) (U' ◯ K) := eq_refl.

#[local] Obligation Tactic := idtac.

Program Definition square_bijection : @Isomorphism Sets sq_dom sq_cod := {|
  to   := {| morphism := SqMate |};
  from := {| morphism := SqMateInv |}
|}.
Next Obligation.
  intros s s' Hs a; simpl; unfold sq_mate.
  now rewrite (Hs (U a)).
Qed.
Next Obligation.
  intros t t' Ht x; simpl; unfold sq_mate_inv.
  now rewrite (Ht (F x)).
Qed.
Next Obligation.
  intros t a; simpl.
  exact (sq_mate_mate_inv A A' K L (transform[t]) (transform_TauNat t) a).
Qed.
Next Obligation.
  intros s x; simpl.
  exact (sq_mate_inv_mate A A' K L (transform[s]) (transform_SigmaNat s) x).
Qed.

Definition square_nat_bijection :
  (F' ◯ L ⟹ K ◯ F) ≊ (L ◯ U ⟹ U' ◯ K) := square_bijection.

End SquareBijection.

(* ====================================================================== *)
(* (D) Palmquist's bijection, and its two factorisations.                 *)
(* ====================================================================== *)

Section PrecompFactor.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {X : Category}.

Notation "'η' x"  := (@unit   _ _ _ _ A  x) (at level 9).
Notation "'ε' a"  := (@counit _ _ _ _ A  a) (at level 9).

#[local] Obligation Tactic := idtac.

Program Definition pre_to {Y : D ⟶ X} {Z : C ⟶ X} (th : Y ◯ U ⟹ Z)
  : Y ⟹ Z ◯ F := {| transform := fun x => th (F x) ∘ fmap[Y] (η x) |}.
Next Obligation.
  intros Y Z th x y g; simpl.
  rewrite comp_assoc.
  rewrite (naturality th _ _ (fmap[F] g)); simpl.
  rewrite <- !comp_assoc, <- !fmap_comp.
  apply compose_respects; [ reflexivity | ].
  apply fmap_respects; now rewrite (conj_unit_nat A g).
Qed.
Next Obligation. symmetry; now apply pre_to_obligation_1. Qed.

Program Definition pre_from {Y : D ⟶ X} {Z : C ⟶ X} (ps : Y ⟹ Z ◯ F)
  : Y ◯ U ⟹ Z := {| transform := fun a => fmap[Z] (ε a) ∘ ps (U a) |}.
Next Obligation.
  intros Y Z ps a b f; simpl.
  rewrite comp_assoc, <- fmap_comp.
  rewrite (conj_counit_nat A f), fmap_comp.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  now rewrite (naturality ps _ _ (fmap[U] f)).
Qed.
Next Obligation. symmetry; now apply pre_from_obligation_1. Qed.

Theorem pre_from_to {Y : D ⟶ X} {Z : C ⟶ X} (th : Y ◯ U ⟹ Z) :
  pre_from (pre_to th) ≈ th.
Proof.
  intros a; simpl.
  rewrite comp_assoc.
  rewrite (naturality th _ _ (ε a)); simpl.
  rewrite <- comp_assoc, <- fmap_comp.
  rewrite (fmap_counit_unit (H:=A)).
  now rewrite fmap_id, id_right.
Qed.

Theorem pre_to_from {Y : D ⟶ X} {Z : C ⟶ X} (ps : Y ⟹ Z ◯ F) :
  pre_to (pre_from ps) ≈ ps.
Proof.
  intros x; simpl.
  rewrite <- comp_assoc.
  rewrite <- (naturality ps _ _ (η x)); simpl.
  rewrite comp_assoc, <- fmap_comp.
  rewrite (counit_fmap_unit (H:=A)).
  now rewrite fmap_id, id_left.
Qed.

Lemma pre_to_respects {Y : D ⟶ X} {Z : C ⟶ X} (t t' : Y ◯ U ⟹ Z) :
  t ≈ t' → pre_to t ≈ pre_to t'.
Proof. intros H x; simpl; now rewrite (H (F x)). Qed.

Lemma pre_from_respects {Y : D ⟶ X} {Z : C ⟶ X} (t t' : Y ⟹ Z ◯ F) :
  t ≈ t' → pre_from t ≈ pre_from t'.
Proof. intros H a; simpl; now rewrite (H (U a)). Qed.

Definition precomp_dom (Y : D ⟶ X) (Z : C ⟶ X) : SetoidObject :=
  {| carrier := Y ◯ U ⟹ Z |}.
Definition precomp_cod (Y : D ⟶ X) (Z : C ⟶ X) : SetoidObject :=
  {| carrier := Y ⟹ Z ◯ F |}.

Program Definition precomp_bijection (Y : D ⟶ X) (Z : C ⟶ X) :
  @Isomorphism Sets (precomp_dom Y Z) (precomp_cod Y Z) := {|
  to   := {| morphism := @pre_to Y Z |};
  from := {| morphism := @pre_from Y Z |}
|}.
Next Obligation. repeat intro; now apply pre_to_respects. Qed.
Next Obligation. repeat intro; now apply pre_from_respects. Qed.
Next Obligation. repeat intro; simpl; now apply pre_to_from. Qed.
Next Obligation. repeat intro; simpl; now apply pre_from_to. Qed.

End PrecompFactor.

Section PostcompFactor.

Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context {X : Category}.

Notation "⌊ f ⌋²" := (to   (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "⌈ f ⌉²" := (from (@adj _ _ _ _ A' _ _) f) (at level 0).

#[local] Obligation Tactic := idtac.

Program Definition post_to {Y : X ⟶ D'} {Z : X ⟶ C'} (th : F' ◯ Y ⟹ Z)
  : Y ⟹ U' ◯ Z := {| transform := fun x => ⌊ th x ⌋² |}.
Next Obligation.
  intros Y Z th x y g; simpl.
  rewrite <- (to_adj_nat_r (Adjunction:=A')).
  rewrite (naturality th _ _ g); simpl.
  now rewrite (to_adj_nat_l (Adjunction:=A')).
Qed.
Next Obligation. symmetry; now apply post_to_obligation_1. Qed.

Program Definition post_from {Y : X ⟶ D'} {Z : X ⟶ C'} (ps : Y ⟹ U' ◯ Z)
  : F' ◯ Y ⟹ Z := {| transform := fun x => ⌈ ps x ⌉² |}.
Next Obligation.
  intros Y Z ps x y g; simpl.
  rewrite <- (from_adj_nat_r (Adjunction:=A')).
  rewrite (naturality ps _ _ g); simpl.
  now rewrite (from_adj_nat_l (Adjunction:=A')).
Qed.
Next Obligation. symmetry; now apply post_from_obligation_1. Qed.

Theorem post_from_to {Y : X ⟶ D'} {Z : X ⟶ C'} (th : F' ◯ Y ⟹ Z) :
  post_from (post_to th) ≈ th.
Proof. intros x; simpl; apply (to_adj_comp_law (H:=A')). Qed.

Theorem post_to_from {Y : X ⟶ D'} {Z : X ⟶ C'} (ps : Y ⟹ U' ◯ Z) :
  post_to (post_from ps) ≈ ps.
Proof. intros x; simpl; apply (from_adj_comp_law (H:=A')). Qed.

Lemma post_to_respects {Y : X ⟶ D'} {Z : X ⟶ C'} (t t' : F' ◯ Y ⟹ Z) :
  t ≈ t' → post_to t ≈ post_to t'.
Proof. intros H x; simpl; now rewrite (H x). Qed.

Lemma post_from_respects {Y : X ⟶ D'} {Z : X ⟶ C'} (t t' : Y ⟹ U' ◯ Z) :
  t ≈ t' → post_from t ≈ post_from t'.
Proof. intros H x; simpl; now rewrite (H x). Qed.

Definition postcomp_dom (Y : X ⟶ D') (Z : X ⟶ C') : SetoidObject :=
  {| carrier := F' ◯ Y ⟹ Z |}.
Definition postcomp_cod (Y : X ⟶ D') (Z : X ⟶ C') : SetoidObject :=
  {| carrier := Y ⟹ U' ◯ Z |}.

Program Definition postcomp_bijection (Y : X ⟶ D') (Z : X ⟶ C') :
  @Isomorphism Sets (postcomp_dom Y Z) (postcomp_cod Y Z) := {|
  to   := {| morphism := @post_to Y Z |};
  from := {| morphism := @post_from Y Z |}
|}.
Next Obligation. repeat intro; now apply post_to_respects. Qed.
Next Obligation. repeat intro; now apply post_from_respects. Qed.
Next Obligation. repeat intro; simpl; now apply post_to_from. Qed.
Next Obligation. repeat intro; simpl; now apply post_from_to. Qed.

End PostcompFactor.

Section Palmquist.

Context {C D : Category}.
Context {F : D ⟶ C} {U : C ⟶ D}.
Context (A : F ⊣ U).
Context {C' D' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'}.
Context (A' : F' ⊣ U').
Context (K : C ⟶ C') (L : D ⟶ D').

Notation "⌊ f ⌋²" := (to   (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "⌈ f ⌉²" := (from (@adj _ _ _ _ A' _ _) f) (at level 0).
Notation "'η' x"  := (@unit   _ _ _ _ A  x) (at level 9).
Notation "'ε' a"  := (@counit _ _ _ _ A  a) (at level 9).

(* [◯] is left associative, so [F' ◯ L ◯ U] is [(F' ◯ L) ◯ U].  The two
   bracketings agree on objects and arrows but not as functor records. *)

Example bracket_fobj_left (a : C) :
  fobj[F' ◯ L ◯ U] a = fobj[F' ◯ (L ◯ U)] a := eq_refl.

Example bracket_fmap_left (a b : C) (f : a ~> b) :
  fmap[F' ◯ L ◯ U] f = fmap[F' ◯ (L ◯ U)] f := eq_refl.

Example comp_type_left (a : C) :
  (fobj[F' ◯ L ◯ U] a ~> fobj[K] a) = (F' (L (U a)) ~> K a) := eq_refl.

Example comp_type_right (x : D) :
  (fobj[L] x ~> fobj[U' ◯ K ◯ F] x) = (L x ~> U' (K (F x))) := eq_refl.

Example bracket_transform_type_right :
  (L ⟹ U' ◯ K ◯ F) = (L ⟹ (U' ◯ K) ◯ F) := eq_refl.

#[local] Obligation Tactic := idtac.

Program Definition palm_to (al : F' ◯ L ◯ U ⟹ K) : L ⟹ U' ◯ K ◯ F := {|
  transform := fun x => ⌊ al (F x) ⌋² ∘ fmap[L] (η x)
|}.
Next Obligation.
  intros al x y f; simpl.
  rewrite comp_assoc.
  rewrite <- (to_adj_nat_r (Adjunction:=A')).
  rewrite (naturality al _ _ (fmap[F] f)); simpl.
  rewrite (to_adj_nat_l (Adjunction:=A')).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite <- !fmap_comp.
  apply fmap_respects.
  now rewrite (conj_unit_nat A f).
Qed.
Next Obligation. symmetry; now apply palm_to_obligation_1. Qed.

Program Definition palm_from (be : L ⟹ U' ◯ K ◯ F) : F' ◯ L ◯ U ⟹ K := {|
  transform := fun a => fmap[K] (ε a) ∘ ⌈ be (U a) ⌉²
|}.
Next Obligation.
  intros be a b f; simpl.
  rewrite comp_assoc, <- fmap_comp.
  rewrite (conj_counit_nat A f), fmap_comp, <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite <- (from_adj_nat_r (Adjunction:=A')).
  rewrite (naturality be _ _ (fmap[U] f)); simpl.
  now rewrite (from_adj_nat_l (Adjunction:=A')).
Qed.
Next Obligation. symmetry; now apply palm_from_obligation_1. Qed.

Theorem palm_from_to (al : F' ◯ L ◯ U ⟹ K) : palm_from (palm_to al) ≈ al.
Proof.
  intros a; simpl.
  rewrite (from_adj_nat_l (Adjunction:=A')).
  rewrite (to_adj_comp_law (H:=A')).
  rewrite comp_assoc.
  rewrite (naturality al _ _ (ε a)); simpl.
  rewrite <- !comp_assoc, <- !fmap_comp.
  rewrite (fmap_counit_unit (H:=A)).
  now rewrite !fmap_id, id_right.
Qed.

Theorem palm_to_from (be : L ⟹ U' ◯ K ◯ F) : palm_to (palm_from be) ≈ be.
Proof.
  intros x; simpl.
  rewrite (to_adj_nat_r (Adjunction:=A')).
  rewrite (from_adj_comp_law (H:=A')).
  rewrite <- comp_assoc.
  rewrite <- (naturality be _ _ (η x)); simpl.
  rewrite comp_assoc, <- !fmap_comp.
  rewrite (counit_fmap_unit (H:=A)).
  now rewrite !fmap_id, id_left.
Qed.

Lemma palm_to_respects (al al' : F' ◯ L ◯ U ⟹ K) :
  al ≈ al' → palm_to al ≈ palm_to al'.
Proof. intros H x; simpl; now rewrite (H (F x)). Qed.

Lemma palm_from_respects (be be' : L ⟹ U' ◯ K ◯ F) :
  be ≈ be' → palm_from be ≈ palm_from be'.
Proof. intros H a; simpl; now rewrite (H (U a)). Qed.

Definition palm_dom : SetoidObject := {| carrier := F' ◯ L ◯ U ⟹ K |}.
Definition palm_cod : SetoidObject := {| carrier := L ⟹ U' ◯ K ◯ F |}.

Example palm_dom_setoid :
  is_setoid palm_dom = @Transform_Setoid C C' (F' ◯ L ◯ U) K := eq_refl.
Example palm_cod_setoid :
  is_setoid palm_cod = @Transform_Setoid D D' L (U' ◯ K ◯ F) := eq_refl.

Program Definition palmquist_bijection :
  @Isomorphism Sets palm_dom palm_cod := {|
  to   := {| morphism := palm_to |};
  from := {| morphism := palm_from |}
|}.
Next Obligation. exact palm_to_respects. Qed.
Next Obligation. exact palm_from_respects. Qed.
Next Obligation. exact palm_to_from. Qed.
Next Obligation. exact palm_from_to. Qed.

Definition palmquist_nat_bijection :
  (F' ◯ L ◯ U ⟹ K) ≊ (L ⟹ U' ◯ K ◯ F) := palmquist_bijection.

(* ---- the mate absorbs one pre/post pair ON THE NOSE ---- *)

Example sq_mate_is_post_of_pre (sg : F' ◯ L ⟹ K ◯ F) (a : C) :
  sq_mate A A' K L (transform[sg]) a
    = ⌊ pre_from A (Y:=F' ◯ L) (Z:=K) sg a ⌋² := eq_refl.

Example sq_mate_inv_is_pre_of_post (ta : L ◯ U ⟹ U' ◯ K) (x : D) :
  sq_mate_inv A A' K L (transform[ta]) x
    = ⌈ pre_to A (Y:=L) (Z:=U' ◯ K) ta x ⌉² := eq_refl.

(* ---- Palmquist factors through the mate, with NO associator ---- *)

Definition palm_via_mate (al : F' ◯ L ◯ U ⟹ K) : L ⟹ U' ◯ K ◯ F :=
  pre_to A (Y:=L) (Z:=U' ◯ K)
    (SqMate A A' K L (pre_to A (Y:=F' ◯ L) (Z:=K) al)).

Theorem palm_to_via_mate (al : F' ◯ L ◯ U ⟹ K) :
  palm_via_mate al ≈ palm_to al.
Proof.
  intros x; simpl.
  apply compose_respects; [ | reflexivity ].
  apply (to_adj_respects (H:=A')).
  rewrite comp_assoc.
  rewrite (naturality al _ _ (ε (F x))); simpl.
  rewrite <- comp_assoc, <- !fmap_comp.
  rewrite (fmap_counit_unit (H:=A)).
  now rewrite !fmap_id, id_right.
Qed.

(* ---- the two-factor route, which DOES meet the associator ---- *)

Definition palm_two_factor (al : F' ◯ L ◯ U ⟹ K) : L ⟹ U' ◯ (K ◯ F) :=
  post_to A' (Y:=L) (Z:=K ◯ F) (pre_to A (Y:=F' ◯ L) (Z:=K) al).

Theorem palm_two_factor_agrees (al : F' ◯ L ◯ U ⟹ K) (x : D) :
  palm_to al x ≈ palm_two_factor al x.
Proof.
  simpl.
  rewrite <- (to_adj_nat_l (Adjunction:=A')).
  reflexivity.
Qed.

Theorem palm_two_factor_spliced (al : F' ◯ L ◯ U ⟹ K) :
  palm_to al ≈ fun_comp_assoc (F:=U') (G:=K) (H:=F) ∙ palm_two_factor al.
Proof.
  intros x; simpl.
  rewrite (to_adj_nat_l (Adjunction:=A')).
  rewrite fmap_id, id_left.
  reflexivity.
Qed.

Example fun_comp_assoc_component (x : D) :
  transform[fun_comp_assoc (F:=U') (G:=K) (H:=F)] x = fmap[U'] id := eq_refl.

Theorem fun_comp_assoc_is_id (x : D) :
  transform[fun_comp_assoc (F:=U') (G:=K) (H:=F)] x ≈ id.
Proof. simpl; now rewrite !fmap_id. Qed.

End Palmquist.

(* ====================================================================== *)
(* (E) Riehl 4.3.v: horizontal and vertical pasting.                      *)
(* ====================================================================== *)

Section HorizontalPaste.

Context {C D : Category} {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {C' D' : Category} {F' : D' ⟶ C'} {U' : C' ⟶ D'} (A' : F' ⊣ U').
Context {C'' D'' : Category} {F'' : D'' ⟶ C''} {U'' : C'' ⟶ D''}.
Context (A'' : F'' ⊣ U'').
Context (K : C ⟶ C') (L : D ⟶ D').
Context (K' : C' ⟶ C'') (L' : D' ⟶ D'').

#[local] Obligation Tactic := idtac.

Program Definition paste_h_sigma
  (sg1 : F' ◯ L ⟹ K ◯ F) (sg2 : F'' ◯ L' ⟹ K' ◯ F')
  : F'' ◯ (L' ◯ L) ⟹ (K' ◯ K) ◯ F :=
  {| transform := fun x => fmap[K'] (sg1 x) ∘ sg2 (L x) |}.
Next Obligation.
  intros sg1 sg2 x y f; simpl.
  rewrite comp_assoc, <- !fmap_comp.
  rewrite (naturality sg1 _ _ f); simpl.
  rewrite fmap_comp, <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  now rewrite (naturality sg2 _ _ (fmap[L] f)).
Qed.
Next Obligation. symmetry; now apply paste_h_sigma_obligation_1. Qed.

Program Definition paste_h_tau
  (ta1 : L ◯ U ⟹ U' ◯ K) (ta2 : L' ◯ U' ⟹ U'' ◯ K')
  : (L' ◯ L) ◯ U ⟹ U'' ◯ (K' ◯ K) :=
  {| transform := fun a => ta2 (K a) ∘ fmap[L'] (ta1 a) |}.
Next Obligation.
  intros ta1 ta2 a b f; simpl.
  rewrite comp_assoc.
  rewrite (naturality ta2 _ _ (fmap[K] f)); simpl.
  rewrite <- !comp_assoc, <- !fmap_comp.
  apply compose_respects; [ reflexivity | ].
  apply fmap_respects.
  now rewrite (naturality ta1 _ _ f).
Qed.
Next Obligation. symmetry; now apply paste_h_tau_obligation_1. Qed.

Theorem adjoint_square_paste_h
  (sg1 : F' ◯ L ⟹ K ◯ F) (ta1 : L ◯ U ⟹ U' ◯ K)
  (sg2 : F'' ◯ L' ⟹ K' ◯ F') (ta2 : L' ◯ U' ⟹ U'' ◯ K') :
  AdjointSquareT A A' K L sg1 ta1 →
  AdjointSquareT A' A'' K' L' sg2 ta2 →
  AdjointSquareT A A'' (K' ◯ K) (L' ◯ L)
    (paste_h_sigma sg1 sg2) (paste_h_tau ta1 ta2).
Proof.
  intros H1 H2 x a k; simpl.
  rewrite comp_assoc, <- fmap_comp.
  rewrite (H2 (L x) (K a) (fmap[K] k ∘ sg1 x)).
  rewrite (H1 x a k).
  rewrite fmap_comp.
  now rewrite comp_assoc.
Qed.

Corollary sq_mate_paste_h
  (sg1 : F' ◯ L ⟹ K ◯ F) (sg2 : F'' ◯ L' ⟹ K' ◯ F') :
  SqMate A A'' (K' ◯ K) (L' ◯ L) (paste_h_sigma sg1 sg2)
    ≈ paste_h_tau (SqMate A A' K L sg1) (SqMate A' A'' K' L' sg2).
Proof.
  symmetry.
  apply (SqMate_uniq A A'').
  apply adjoint_square_paste_h; apply AdjointSquareT_SqMate.
Qed.

End HorizontalPaste.

Section VerticalPaste.

Context {D C E : Category}.
Context {F : D ⟶ C} {U : C ⟶ D} (A : F ⊣ U).
Context {G : C ⟶ E} {V : E ⟶ C} (B : G ⊣ V).
Context {D' C' E' : Category}.
Context {F' : D' ⟶ C'} {U' : C' ⟶ D'} (A' : F' ⊣ U').
Context {G' : C' ⟶ E'} {V' : E' ⟶ C'} (B' : G' ⊣ V').
Context (L : D ⟶ D') (K : C ⟶ C') (M : E ⟶ E').

#[local] Obligation Tactic := idtac.

Program Definition paste_v_sigma
  (sg1 : F' ◯ L ⟹ K ◯ F) (sg2 : G' ◯ K ⟹ M ◯ G)
  : (G' ◯ F') ◯ L ⟹ M ◯ (G ◯ F) :=
  {| transform := fun x => sg2 (F x) ∘ fmap[G'] (sg1 x) |}.
Next Obligation.
  intros sg1 sg2 x y f; simpl.
  rewrite comp_assoc.
  rewrite (naturality sg2 _ _ (fmap[F] f)); simpl.
  rewrite <- !comp_assoc, <- !fmap_comp.
  apply compose_respects; [ reflexivity | ].
  apply fmap_respects.
  now rewrite (naturality sg1 _ _ f).
Qed.
Next Obligation. symmetry; now apply paste_v_sigma_obligation_1. Qed.

Program Definition paste_v_tau
  (ta1 : L ◯ U ⟹ U' ◯ K) (ta2 : K ◯ V ⟹ V' ◯ M)
  : L ◯ (U ◯ V) ⟹ (U' ◯ V') ◯ M :=
  {| transform := fun e => fmap[U'] (ta2 e) ∘ ta1 (V e) |}.
Next Obligation.
  intros ta1 ta2 e e2 f; simpl.
  rewrite comp_assoc, <- !fmap_comp.
  rewrite (naturality ta2 _ _ f); simpl.
  rewrite fmap_comp, <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  now rewrite (naturality ta1 _ _ (fmap[V] f)).
Qed.
Next Obligation. symmetry; now apply paste_v_tau_obligation_1. Qed.

Definition AB  : (G ◯ F) ⊣ (U ◯ V)     := Adjunction_Compose A B.
Definition AB' : (G' ◯ F') ⊣ (U' ◯ V') := Adjunction_Compose A' B'.

(* The composite's transposes are definitional; its unit is not. *)

Example AB_to_strict (x : D) (e : E) (k : G (F x) ~> e) :
  to (@adj _ _ _ _ AB x e) k
    = to (@adj _ _ _ _ A x (V e)) (to (@adj _ _ _ _ B (F x) e) k) := eq_refl.

Theorem AB_unit_upto (x : D) :
  @unit _ _ _ _ AB x
    ≈ fmap[U] (@unit _ _ _ _ B (F x)) ∘ @unit _ _ _ _ A x.
Proof. apply Adjunction_Compose_unit. Qed.

Theorem adjoint_square_paste_v
  (sg1 : F' ◯ L ⟹ K ◯ F) (ta1 : L ◯ U ⟹ U' ◯ K)
  (sg2 : G' ◯ K ⟹ M ◯ G) (ta2 : K ◯ V ⟹ V' ◯ M) :
  AdjointSquareT A A' K L sg1 ta1 →
  AdjointSquareT B B' M K sg2 ta2 →
  AdjointSquareT AB AB' M L (paste_v_sigma sg1 sg2) (paste_v_tau ta1 ta2).
Proof.
  intros H1 H2 x e k; simpl.
  rewrite comp_assoc.
  rewrite (to_adj_nat_l (Adjunction:=B')).
  rewrite (H2 (F x) e k).
  rewrite <- (comp_assoc (ta2 e)
                (fmap[K] (to (@adj _ _ _ _ B (F x) e) k)) (sg1 x)).
  rewrite (to_adj_nat_r (Adjunction:=A')).
  rewrite (H1 x (V e) (to (@adj _ _ _ _ B (F x) e) k)).
  now rewrite comp_assoc.
Qed.

Corollary sq_mate_paste_v
  (sg1 : F' ◯ L ⟹ K ◯ F) (sg2 : G' ◯ K ⟹ M ◯ G) :
  SqMate AB AB' M L (paste_v_sigma sg1 sg2)
    ≈ paste_v_tau (SqMate A A' K L sg1) (SqMate B B' M K sg2).
Proof.
  symmetry.
  apply (SqMate_uniq AB AB').
  apply adjoint_square_paste_v; apply AdjointSquareT_SqMate.
Qed.

End VerticalPaste.
