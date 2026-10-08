Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Adjunction.Map.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Morphism.
Require Import Category.Monad.Morphism.Algebra.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Monad.Monadicity.Beck.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.

Generalizable All Variables.

(** * Comparisons of two resolutions of one monad *)

(* Book: Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
         Springer GTM 5, 1998, §VI.7 "Beck's Theorem", printed pp. 153-154
         (PDF pp. 162-163): the definition of a comparison, p. 153 —
         maclane:VI.7:def1; the Lemma, pp. 153-154 — maclane:VI.7:lem1.
   Book: Awodey, "Category Theory", 1st ed. (Carnegie Mellon pre-print,
         September 2005), §10.3, the comparison functor, printed p. 277
         (PDF p. 286) — awodey:10.3:construction-comparison-functor.
   Book: Riehl, "Category Theory in Context", §5.2, the category Adj_T,
         printed pp. 192-193 (PDF pp. 212-213) — riehl:5.2:construction-adjT.
   nLab: https://ncatlab.org/nlab/show/monadic+adjunction

   WHAT THE BOOKS SAY, read from the page images.  Mac Lane, p. 153: "Now
   consider any other adjunction ⟨F', G', η', ε'⟩ : X ⇀ A' which defines
   the same monad in X.  By a comparison (of F' to F) we mean a functor
   M : A' → A with MF' = F and GM = G'; as already noted, such a
   comparison is a morphism of adjunctions and hence satisfies Mε' = εM.
   Lemma.  If G satisfies hypothesis (iii) of the theorem on the creation
   of coequalizers, then there is a unique comparison M : A' → A."  The
   proof: "If M exists, then FGM = MF'G' and Mε' = εM, so M must carry
   the canonical presentation of a' to the canonical presentation of
   Ma'", a fork FGFG'a' ⇉ FG'a' → Ma' whose arrow k "must be
   Mε'_{a'} = ε_{Ma'}"; its G-image is split, G creates its coequalizer,
   so "the comparison M is unique if it exists"; M f is the factorization
   of k_b ∘ FG'f through k.  Of G^T: "this lemma will incidentally
   provide a new proof of the comparison theorem (§3)."  Awodey, p. 277:
   from F ⊣ U, "we then get a comparison functor Φ : D → C^T, with
   U^T ∘ Φ ≅ U, Φ ∘ F = F^T ...  In fact, Φ is unique with this
   property."  Riehl, p. 192: a morphism of Adj_T "is a functor
   K : D → D' commuting with both the left and right adjoints, i.e., so
   that KF = F' and U'K = U"; it is a strict morphism of adjunctions,
   so "(i) the whiskered composites Kε = ε'K ... coincide, and (ii)
   application of the functor K commutes with adjoint transposition:
   for all c ∈ C and d ∈ D", the square C(c, Ud) → D(Fc, d) →
   D'(KFc, Kd) = D'(F'c, Kd) against C(c, U'Kd) → D'(F'c, Kd) commutes
   (p. 193).

   THE READING.  Over adjunctions Adj : F ⊣ G (A over X) and
   Adj' : F' ⊣ G' (A' over X), "defines the same monad" is data, θ, an
   isomorphism in Monad/Morphism.v's [Monads X] from the monad
   Monad/Comparison.v's [Adjunction_Induced_Monad Adj'] to that of Adj;
   its components are θ_x : G'F'x → GFx and φ_x : GFx → G'F'x.  A
   [Comparison] over θ is a functor M ([cmp_functor]) with MF' ≈ F
   ([cmp_left], components α) and GM ≈ G' ([cmp_right], components β),
   both natural isomorphisms of [Functor_Setoid], and [cmp_monad]: the
   identification G'F' ≅ GMF' ≅ GF that α and β induce, at x the
   composite G α_x ∘ β⁻¹_{F'x}, is θ_x.  In Mac Lane's text all three
   identifications are equalities and [cmp_monad] holds trivially.  The
   strict reading, Leibniz equations of objects as in Adjunction/Map.v's
   [AdjSquares] or #475's strict triangles, is not taken, on two
   measured grounds.  At the Eilenberg–Moore resolution the canonical
   comparison does not satisfy MF' = F on objects at [eq_refl]: K (F x)
   and F^T x agree on carrier and structure map at [eq_refl] and differ
   in the law fields of their [TAlgebra] records
   (Test/ProbeResolution482.v, R1 with controls C1 and C2; their Leibniz
   equality is neither proved nor refuted).  And Monad/Monadicity/Beck.v's
   [CreatesUSplitCoequalizers] creates a coequalizer only up to a
   compatible isomorphism (that file's header), so the Lemma's existence
   half delivers GM ≅ G', not GM = G'.  [cmp_monad] is what the
   uniqueness half consumes: [cmp_e_G] uses it, through [cmp_monad_inv],
   to identify the algebra structure M carries on G' a with that of
   [Comparison_alg].  It is necessary.  Uniqueness is relative to θ:
   Instance/Fun/Action/Monad/Comparison.v's [K_Comparison] is a
   comparison over a monad automorphism θ_σ, and no comparison over the
   identity identification has a functor ≈ to it
   ([K_no_coherent_comparison]).  And without it even Mε' ≈ εM is lost:
   at the Eilenberg–Moore adjunction of H × (−) for a group H and h ≠ 1,
   M := Id with α_x(n, y) := (n h, y) and β := id has both triangles,
   while the counit condition compares ε_a, (n, a) ↦ n·a, with
   ε_a ∘ α_{G a}, (n, a) ↦ (n h)·a, which differ at the free H-set on
   one point; the identification it induces, (n, y) ↦ (n h, y),
   preserves no unit, so no θ makes it a comparison (argued here, not
   compiled).

   A COMPARISON IS A MAP OF ADJUNCTIONS.  [Comparison_squares] is Map.v's
   ≈ reading [WeakAdjSquares], with K := M and L := Id[X]; Mac Lane's
   unit condition Lη = η'L is [Comparison_unit], from [cmp_monad] and the
   unit law [mh_ret] of θ; [Comparison_map] is the
   [WeakMapOfAdjunctions], by Map.v's [weak_hom_iff_unit] (its two
   functors read back at [eq_refl]: [Comparison_map_K],
   [Comparison_map_L]).  Mac Lane's Mε' = εM is [Comparison_counit], the
   counit condition, by [weak_hom_iff_counit], and
   [Comparison_counit_fused] states it with the isomorphisms written out.
   Riehl's (i) is the same equation; her (ii) is [Comparison_transpose],
   from the map's hom condition.

   THE LEMMA, EXISTENCE.  Given CR : [CreatesUSplitCoequalizers G],
   [Comparison_exists] is a comparison over θ.  Its functor
   [Comparison_functor] is Beck.v's [Beck_Inverse] after
   [Comparison_alg], θ* of [EM_Comparison Adj']
   (Monad/Morphism/Algebra.v's [mh_EM] at φ): the algebra
   (G' a, G'ε'_a ∘ φ_{G'a}), at
   [eq_refl] ([Comparison_alg_carrier], [Comparison_alg_action]).  So M a
   is the coequalizer G creates over that algebra's canonical
   presentation FGFG'a ⇉ FG'a ([Comparison_functor_obj], [eq_refl]), and
   M f is Beck.v's descent through it, Mac Lane's construction.  GM ≈ G'
   is [Comparison_right], with Beck.v's [beck_to] and [beck_from] as
   components ([Comparison_right_to], [Comparison_right_from],
   [eq_refl]) and [beck_counit_coherence] as naturality.  MF' ≈ F is
   [Comparison_left]: F x with ε_{Fx} ∘ Fθ_x ([cmp_free_e]) also lies
   over the split coequalizer ([cmp_free_e_cofork], [cmp_free_iso_e],
   through [cmp_theta_join], the law [mh_join] of θ), and Beck.v's
   [create_coeq_unique] supplies the isomorphism; [Comparison_coherence]
   is [cmp_monad], by the triangle identity.

   THE LEMMA, UNIQUENESS.  For any comparison P over θ, [cmp_e] is
   Mac Lane's k = Mε'_a read through α, and [cmp_e_counit] his "k must be
   Mε'_{a'} = ε_{Ma'}", read through β.  It coforks the presentation
   ([cmp_e_cofork]) and lies over the split coequalizer
   ([cmp_e_iso], by [cmp_e_G]), so the reflection clause of creation
   makes it a coequalizer ([cmp_e_coeq]), and [create_coeq_unique]
   identifies P a with M a ([cmp_unique_iso], [cmp_unique_iso_e]).
   [Comparison_unique_to] is the natural isomorphism, natural by
   [cmp_unique_iso_natural], from [cmp_e_natural]; [Comparison_unique]:
   any two comparisons over θ have ≈ functors.  The isomorphism is a
   morphism of comparisons ([Comparison_unique_to_left],
   [Comparison_unique_to_right]: it commutes with both triangles), and
   the only natural family of arrows commuting with the left ones
   ([Comparison_unique_cell], by [Comparison_exists_e]).  Pairwise,
   between any two comparisons P and Q over θ, the composite of their
   isomorphisms to the constructed one commutes with the left triangles
   ([Comparison_unique_pair_left]) and is the only natural family of
   arrows that does ([Comparison_unique_pair_cell], from the
   coequalizer at P directly): the comparison is unique up to a unique
   compatible isomorphism.

   THE EILENBERG–MOORE RESOLUTION.  [EM_Monad_iso]: F^T ⊣ G^T defines T,
   an isomorphism in [Monads X] whose components are the identity
   ([EM_Monad_iso_to], [EM_Monad_iso_from], [eq_refl]), Mac Lane's §VI.2
   Theorem 1 packaged as Monad/Morphism/Algebra.v records it was not.
   With Beck.v's [monadic_creates], the Lemma makes that resolution
   terminal in the weak sense: every adjunction Adj' with an isomorphism
   θ' of its monad to T has a comparison into it ([EM_terminal], over
   [EM_terminal_theta]), unique up to isomorphism
   ([EM_terminal_unique]).  Awodey's clause: [EM_Comparison] is a
   comparison ([EM_Comparison_Comparison]) with Monad/Comparison.v's
   [EM_Comparison_Free] and [EM_Comparison_Forget] as its triangles, over
   [EM_Comparison_theta], whose components are the identity
   ([EM_Comparison_theta_to]); [EM_Comparison_unique]: every comparison
   over that θ is ≈ [EM_Comparison], and [EM_Comparison_unique_cell]:
   up to a unique compatible isomorphism.  Without the coherence the
   clause is false, in the issue's reading and in Awodey's printed one
   (NOT DELIVERED).  Mac Lane's "new proof of the comparison theorem" is
   the Lemma at that resolution.  Its existence half is not new:
   [Comparison_exists] there, whose functor is [EM_Comparison_via_Lemma],
   is built from [EM_Comparison] itself, through [Comparison_alg].  Its
   uniqueness half is the new part, [EM_Comparison_unique] and
   [EM_Comparison_unique_cell].  [EM_Comparison_via_Lemma_agrees]
   identifies the Lemma's construction with K: the two agree on carriers
   at [eq_refl] and their structure maps are refused there (the probe's
   C3, R2a and R2, conversion boundaries; their Leibniz equality is
   neither proved nor refuted), so the uniqueness is up to isomorphism,
   not on the nose.
   For [cmp_monad] at [EM_Comparison] the two triangles must compute:
   [EM_Comparison_Forget] and [EM_Comparison_Free] end [Defined] since
   this change, read back at [eq_refl] ([EM_Comparison_Forget_components],
   [EM_Comparison_Free_components]).

   STRENGTHS.  Every [Example] here holds at [eq_refl], twelve, each
   restated in Test/ProbeResolution482.v (C6 to C17); every other
   statement is at ≈.  Refused at [eq_refl], by conversion, each stripped
   in a copy of the whole probe: R1 (above), R2a and R2 (the Lemma's
   comparison against [EM_Comparison] on structure maps and objects), R3
   ([EM_Comparison_coherence] at [eq_refl]: id ∘ id against id in a
   variable category, control C5).  Six proofs end [Defined] and
   thirty-three [Qed] (counted by token).  Each [Defined] is load-bearing,
   measured by closing it alone [Qed] in a copy of this file and naming
   the first command that then stops: [Comparison_squares]
   ([Comparison_unit]), [Comparison_right] ([Comparison_right_to]),
   [Comparison_left] ([Comparison_coherence]), [EM_Monad_to] and
   [EM_Monad_from] (each [EM_Monad_iso]), [EM_Monad_iso]
   ([EM_Monad_iso_to]).  With Monad/Comparison.v's two triangles closed
   [Qed] again, [EM_Comparison_Forget_components] stops, refused with
   cannot unify "projT1 (EM_Comparison_Forget Adj) a" and "iso_id", and
   without the readbacks [EM_Comparison_coherence] stops.

   UNIVERSES, read off [About] under Set Printing Universes, every one of
   the seventy-five names (the seventy-four heads of the .glob file and
   the record's constructor [Build_Comparison]; no [Program] is used, and
   no obligation or subproof constant exists).  Every name is universe
   polymorphic and binds eight to twenty-one levels; no block mentions
   [Set] and none carries an equation.  Over two adjunctions with X in
   common, X, A and A' share one hom-and-proof level in the binder:
   Theory/Adjunction.v's [Adjunction] identifies the hom and proof levels
   of its two categories.  [Monads X] is written [Monads@{_ _ m1 m2} X],
   its object and hom levels declared apart by a section [Universes];
   unannotated, minimization identified them (θ's type read
   [Isomorphism@{u7 u7 u7}], measured; #475's [Restricted_Monad_iso]
   carries the same identification).  The standard library's caps are
   inherited.  ID.u0 and compose.u0-u2, the caps of Theory/Adjunction.v's
   [Adjunction] (in its own block), and Specif's Projections.u0-u1, the
   sigma projections, those of Monad/Morphism.v's [Monads] and of
   Monad/Eilenberg/Moore.v's [EilenbergMoore] (each in its own block),
   are in all seventy-five blocks, through the section contexts and the
   statements.  The others come each from its first carrier:
   prod_rect.u0-u2 first at [Comparison_map], through Map.v's
   [weak_hom_iff_unit], and at [Comparison_right_iso], through Beck.v's
   [beck_to]; projections.u0-u1
   (Datatypes' fst and snd) first at [Comparison_map], by its own [snd],
   and at [Comparison_functor], through [Beck_Inverse]; and
   Logic_lemmas.equality.u0 only in the Eilenberg–Moore sections, first at
   [EM_Monad_to], through Monad/Eilenberg/Moore/Adjunction.v's
   [EM_Adjunction].  No explicit universe instance of a constant this
   change adds is written.  Compiled on Coq 8.19.2 and 8.20.1 in source
   overlays, each of the seventy-five names binds the same number of
   levels as on Rocq 9.1.1, with no equation and no [Set] (compared by
   [About], by script).

   NOT DELIVERED.  The strict reading (above).  Awodey's clause without
   [cmp_monad], which is false: Instance/Fun/Action/Monad/Comparison.v
   refutes it in the issue's reading, U^T ∘ Φ ≈ U and Φ ∘ F ≈ F^T
   ([bare_awodey_refuted], at the adjunction of LZ-sets for a
   three-element monoid LZ), and in Awodey's printed one, U^T ∘ Φ ≅ U and
   Φ ∘ F = F^T with = read as Theory/Functor.v's [Functor_StrictEq_Setoid]
   ([printed_awodey_not_unique], at the Kleisli resolution of the same
   monad).  With [cmp_monad] it holds ([EM_Comparison_unique]), and with
   an equality in both places it is Mac Lane's §VI.3 Theorem 1, in set
   theory; that all-strict reading is not formalized.  The category of
   resolutions of a monad and its initial and terminal objects (issue
   #476), and with it the identity and the
   composite of comparisons; Mac Lane's own use of the Lemma, MK = 1 and
   KM = 1 proving Theorem 1 (i), whose statement Beck.v's
   [beck_monadicity] already proves by the crude route (the cheapest
   variant: those two comparisons, a transport of a comparison along ≈
   of θ, and two applications of [Comparison_unique]).

   THE ISSUE'S PREMISES, dated.  Issue #482 was filed on 2026-07-23; its
   Awodey section was appended on 2026-07-29 and its Riehl section on
   2026-07-31 (the body's edit history).  "No general comparison of two
   adjunctions defining the same monad" was accurate when filed and held
   until this change; but its ground, that "searches for
   morphism/map/comparison of adjunctions ... turn up only concrete
   resolutions", has been stale since PR #1260 (merged 2026-09-04) as to
   maps of adjunctions: Adjunction/Map.v's [WeakMapOfAdjunctions] is the
   general notion of which a comparison is the case L = Id[X], and this
   file builds on it.  "EM_Comparison ... only for A' = X^T, and not the
   compatibility M ∘ ε' = ε ∘ M" and "the
   uniqueness content is realized only via Beck_Inverse" were accurate
   when filed and held until this change.  The Awodey section's "nothing
   of the form ∀ K, ... K ≈ EM_Comparison exists" was accurate when
   appended and held until this change; its list of the uniqueness
   lemmas of Monad/ omitted Beck.v's [create_coeq_unique], on master since
   PR #201 (merged 2026-07-19), which this file uses, and since then
   [em_alg_unique] (PR #1083, merged 2026-08-13) and
   [Kleisli_Comparison_unique] (PR #1362, merged 2026-10-08) joined it,
   none of them about the Eilenberg–Moore comparison functor.  The
   Definition of Done's "CLAUDE.md Key Files index" was accurate when
   filed and has been stale since PR #1284 (merged 2026-09-09), which
   moved the index to docs/INDEX.md. *)

(* ------------------------------------------------------------------------ *)
(** ** Definition: a comparison over an identification of the monads *)

Section ComparisonDef.

(* The object and hom levels of [Monads X], kept apart (see UNIVERSES). *)
Universes m1 m2.

Context {X : Category}.
Context {A : Category} {F : X ⟶ A} {G : A ⟶ X} (Adj : F ⊣ G).
Context {A' : Category} {F' : X ⟶ A'} {G' : A' ⟶ X} (Adj' : F' ⊣ G').
Context (θ : @Isomorphism (Monads@{_ _ m1 m2} X)
               (G' ◯ F'; Adjunction_Induced_Monad Adj')
               (G ◯ F; Adjunction_Induced_Monad Adj)).

(* Mac Lane's M F' = F and G M = G', each up to a natural isomorphism, and
   the identification of the two monads they induce, G' F' ≅ G M F' ≅ G F,
   is the given one. *)
Record Comparison : Type := {
  cmp_functor : A' ⟶ A;
  cmp_left : cmp_functor ◯ F' ≈ F;
  cmp_right : G ◯ cmp_functor ≈ G';
  cmp_monad (x : X) :
    fmap[G] (to (`1 cmp_left x)) ∘ from (`1 cmp_right (F' x))
      ≈ transform[mh_transform (to θ)] x
}.

Lemma cmp_theta_to_from (x : X) :
  transform[mh_transform (to θ)] x ∘ transform[mh_transform (from θ)] x
    ≈ id.
Proof. exact (iso_to_from θ x). Qed.

Lemma cmp_theta_from_to (x : X) :
  transform[mh_transform (from θ)] x ∘ transform[mh_transform (to θ)] x
    ≈ id.
Proof. exact (iso_from_to θ x). Qed.

(* ------------------------------------------------------------------------ *)
(** ** A comparison is a map of adjunctions (Adjunction/Map.v) *)

Section Squares.

Context (P : Comparison).

Local Notation M := (cmp_functor P).
Local Notation al x := (`1 (cmp_left P) x).
Local Notation be a := (`1 (cmp_right P) a).

(* The coherence read backwards: β ∘ G α⁻¹ is θ⁻¹. *)
Lemma cmp_monad_inv (x : X) :
  to (be (F' x)) ∘ fmap[G] (from (al x))
    ≈ transform[mh_transform (from θ)] x.
Proof.
  transitivity (to (be (F' x)) ∘ fmap[G] (from (al x))
                  ∘ (transform[mh_transform (to θ)] x
                       ∘ transform[mh_transform (from θ)] x)).
  { rewrite cmp_theta_to_from. symmetry. apply id_right. }
  rewrite <- (cmp_monad P x).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc (to (be (F' x)))).
  simpl.
  rewrite <- (@fmap_comp _ _ G).
  rewrite iso_from_to, fmap_id, id_right.
  rewrite iso_to_from.
  apply id_left.
Qed.

(* The squares of Map.v's ≈ reading, with K := M and L := Id[X]. *)
Definition Comparison_squares : @WeakAdjSquares A' X F' G' A X F G.
Proof using P.
  unshelve refine {| wsq_K := M; wsq_L := Id[X] |}.
  - exists (fun x => al x).
    intros x y f.
    exact (`2 (cmp_left P) x y f).
  - exists (fun a => iso_sym (be a)).
    intros a b f; simpl.
    rewrite (`2 (cmp_right P) a b f).
    rewrite !comp_assoc.
    rewrite iso_to_from, id_left.
    rewrite <- comp_assoc.
    rewrite iso_to_from.
    symmetry. apply id_right.
Defined.

(* Mac Lane's L η = η' L at L := Id, from the coherence and [mh_ret]. *)
Lemma Comparison_unit : WeakSquaresUnit Adj' Adj Comparison_squares.
Proof.
  intros x; simpl.
  transitivity (fmap[G] (from (al x)) ∘ (fmap[G] (to (al x))
                  ∘ from (be (F' x))) ∘ @unit _ _ _ _ Adj' x).
  { rewrite !comp_assoc.
    rewrite <- (@fmap_comp _ _ G).
    rewrite iso_from_to, fmap_id, id_left.
    reflexivity. }
  rewrite (cmp_monad P x).
  rewrite <- comp_assoc.
  apply compose_respects; [ reflexivity | ].
  exact (@mh_ret _ _ _ _ _ (to θ) x).
Qed.

(* "Such a comparison is a morphism of adjunctions". *)
Definition Comparison_map : WeakMapOfAdjunctions Adj' Adj :=
  {| wmap_squares := Comparison_squares;
     wmap_hom := snd (weak_hom_iff_unit Adj' Adj Comparison_squares)
                   Comparison_unit |}.

Example Comparison_map_K :
  wsq_K (wmap_squares Adj' Adj Comparison_map) = M := eq_refl.

Example Comparison_map_L :
  wsq_L (wmap_squares Adj' Adj Comparison_map) = Id[X] := eq_refl.

(* "... and hence satisfies M ε' = ε M": Map.v's counit condition. *)
Theorem Comparison_counit : WeakSquaresCounit Adj' Adj Comparison_squares.
Proof.
  exact (fst (weak_hom_iff_counit Adj' Adj Comparison_squares)
           (wmap_hom Adj' Adj Comparison_map)).
Qed.

(* The same, with the isomorphisms of the two triangles written out. *)
Theorem Comparison_counit_fused (a : A') :
  fmap[M] (@counit _ _ _ _ Adj' a)
    ≈ @counit _ _ _ _ Adj (M a) ∘ fmap[F] (from (be a)) ∘ to (al (G' a)).
Proof.
  pose proof (Comparison_counit a) as H; simpl in H.
  rewrite <- H.
  rewrite <- comp_assoc.
  rewrite iso_from_to.
  symmetry. apply id_right.
Qed.

(* Riehl's (ii): the comparison commutes with adjoint transposition. *)
Theorem Comparison_transpose (x : X) (a : A') (g : x ~> G' a) :
  fmap[M] (from (@adj _ _ _ _ Adj' x a) g) ∘ from (al x)
    ≈ from (@adj _ _ _ _ Adj x (M a)) (from (be a) ∘ g).
Proof.
  pose proof (wmap_hom Adj' Adj Comparison_map x a
                (from (@adj _ _ _ _ Adj' x a) g)) as H; simpl in H.
  apply (snd (adj_univ (H:=Adj) _ _)).
  rewrite H.
  apply compose_respects; [ reflexivity | ].
  apply (from_adj_comp_law (H:=Adj')).
Qed.

End Squares.

(* ------------------------------------------------------------------------ *)
(** ** The Lemma, existence: through Beck.v's created coequalizers *)

Section Existence.

Context (CR : CreatesUSplitCoequalizers G).

Local Notation T := (Adjunction_Induced_Monad Adj).
Local Notation EMT := (@EilenbergMoore X (G ◯ F) T).
Local Notation th x := (transform[mh_transform (to θ)] x).
Local Notation ph x := (transform[mh_transform (from θ)] x).

(* The T-algebra on G' a: θ* of the comparison algebra of F' ⊣ G'. *)
Definition Comparison_alg : A' ⟶ EMT := mh_EM (from θ) ◯ EM_Comparison Adj'.

Example Comparison_alg_carrier (a : A') : `1 (Comparison_alg a) = G' a
  := eq_refl.

Example Comparison_alg_action (a : A') :
  t_alg[`2 (Comparison_alg a)] = fmap[G'] (@counit _ _ _ _ Adj' a) ∘ ph (G' a)
  := eq_refl.

(* M a is the coequalizer G creates over the canonical presentation. *)
Definition Comparison_functor : A' ⟶ A :=
  Beck_Inverse Adj CR ◯ Comparison_alg.

Example Comparison_functor_obj (a : A') :
  fobj[Comparison_functor] a = beck_G_obj Adj CR (Comparison_alg a) := eq_refl.

Definition Comparison_right_iso (a : A') : G (Comparison_functor a) ≅ G' a :=
  @Build_Isomorphism X (G (Comparison_functor a)) (G' a)
    (beck_to Adj CR (Comparison_alg a)) (beck_from Adj CR (Comparison_alg a))
    (beck_to_from Adj CR (Comparison_alg a))
    (beck_from_to Adj CR (Comparison_alg a)).

Definition Comparison_right : G ◯ Comparison_functor ≈ G'.
Proof.
  exists Comparison_right_iso.
  intros a b f.
  exact (beck_counit_coherence Adj CR (fmap[Comparison_alg] f)).
Defined.

Example Comparison_right_to (a : A') :
  to (`1 Comparison_right a) = beck_to Adj CR (Comparison_alg a) := eq_refl.

Example Comparison_right_from (a : A') :
  from (`1 Comparison_right a)
    = fmap[G] (beck_e Adj CR (Comparison_alg a)) ∘ @unit _ _ _ _ Adj (G' a)
  := eq_refl.

(* θ carries μ' to μ along T θ: θ_x ∘ μ'_x ∘ φ_{T' x} ≈ μ_x ∘ T θ_x. *)
Lemma cmp_theta_join (x : X) :
  th x ∘ (fmap[G'] (@counit _ _ _ _ Adj' (F' x)) ∘ ph (G' (F' x)))
    ≈ fmap[G] (@counit _ _ _ _ Adj (F x)) ∘ fmap[G] (fmap[F] (th x)).
Proof.
  rewrite comp_assoc.
  pose proof (@mh_join _ _ _ _ _ (to θ) x) as Hj; simpl in Hj.
  rewrite Hj; clear Hj.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  pose proof (naturality (mh_transform (from θ)) _ _ (th x)) as Hn;
    simpl in Hn.
  rewrite Hn; clear Hn.
  rewrite comp_assoc.
  rewrite (cmp_theta_to_from (G (F x))).
  apply id_left.
Qed.

(* The arrow that exhibits F x as the created object at F' x. *)
Definition cmp_free_e (x : X) : F (G' (F' x)) ~> F x :=
  @counit _ _ _ _ Adj (F x) ∘ fmap[F] (th x).

Lemma cmp_free_e_cofork (x : X) :
  cmp_free_e x ∘ crude_pair_l Adj (Comparison_alg (F' x))
    ≈ cmp_free_e x ∘ crude_pair_r Adj (Comparison_alg (F' x)).
Proof.
  unfold cmp_free_e, crude_pair_l, crude_pair_r; simpl.
  rewrite <- !comp_assoc.
  rewrite <- (adj_counit_natural Adj (fmap[F] (th x))).
  rewrite <- (@fmap_comp _ _ F).
  pose proof (cmp_theta_join x) as Hj; simpl in Hj.
  rewrite Hj; clear Hj.
  rewrite (@fmap_comp _ _ F).
  rewrite !comp_assoc.
  apply compose_respects; [ | reflexivity ].
  rewrite (adj_counit_natural Adj (@counit _ _ _ _ Adj (F x))).
  reflexivity.
Qed.

Definition cmp_free_iso (x : X) : G (F x) ≅ G' (F' x) :=
  @Build_Isomorphism X (G (F x)) (G' (F' x)) (ph x) (th x)
    (cmp_theta_from_to x) (cmp_theta_to_from x).

Lemma cmp_free_iso_e (x : X) :
  to (cmp_free_iso x) ∘ fmap[G] (cmp_free_e x)
    ≈ scoeq_e (beck_split Adj (Comparison_alg (F' x))).
Proof.
  unfold cmp_free_e; simpl.
  rewrite (@fmap_comp _ _ G).
  pose proof (cmp_theta_join x) as Hj; simpl in Hj.
  rewrite <- Hj; clear Hj.
  rewrite comp_assoc.
  pose proof (cmp_theta_from_to x) as Hi; simpl in Hi.
  rewrite Hi; clear Hi.
  apply id_left.
Qed.

(* Both M (F' x) and F x lie over the split coequalizer, so the two are
   isomorphic, compatibly with the coequalizing arrows. *)
Definition Comparison_left_data (x : X) :=
  create_coeq_unique CR
    (crude_pair_l Adj (Comparison_alg (F' x)))
    (crude_pair_r Adj (Comparison_alg (F' x)))
    (beck_split Adj (Comparison_alg (F' x)))
    (beck_e Adj CR (Comparison_alg (F' x))) (cmp_free_e x)
    (beck_cofork Adj CR (Comparison_alg (F' x))) (cmp_free_e_cofork x)
    (beck_iso Adj CR (Comparison_alg (F' x)))
    (beck_iso_e Adj CR (Comparison_alg (F' x)))
    (cmp_free_iso x) (cmp_free_iso_e x).

Definition Comparison_left_iso (x : X) : Comparison_functor (F' x) ≅ F x :=
  `1 (Comparison_left_data x).

Lemma Comparison_left_iso_e (x : X) :
  to (Comparison_left_iso x) ∘ beck_e Adj CR (Comparison_alg (F' x))
    ≈ cmp_free_e x.
Proof. exact (`2 (Comparison_left_data x)). Qed.

Definition Comparison_left : Comparison_functor ◯ F' ≈ F.
Proof.
  exists Comparison_left_iso.
  intros x y f.
  apply (@epic _ _ _ _ (beck_e_epic Adj CR (Comparison_alg (F' x)))).
  change (beck_G_map Adj CR (fmap[Comparison_alg] (fmap[F'] f))
            ∘ beck_e Adj CR (Comparison_alg (F' x))
          ≈ from (Comparison_left_iso y) ∘ fmap[F] f
              ∘ to (Comparison_left_iso x)
              ∘ beck_e Adj CR (Comparison_alg (F' x))).
  rewrite (beck_G_map_commutes Adj CR
             (fmap[Comparison_alg] (fmap[F'] f))).
  rewrite <- (comp_assoc _ (to (Comparison_left_iso x))).
  rewrite Comparison_left_iso_e.
  unfold cmp_free_e.
  rewrite (comp_assoc _ (@counit _ _ _ _ Adj (F x))).
  rewrite <- (comp_assoc _ (fmap[F] f) (@counit _ _ _ _ Adj (F x))).
  rewrite <- (adj_counit_natural Adj (fmap[F] f)).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (fmap[F] (fmap[G] (fmap[F] f)))).
  rewrite <- (@fmap_comp _ _ F).
  pose proof (naturality (mh_transform (to θ)) _ _ f) as Hn; simpl in Hn.
  rewrite Hn; clear Hn.
  rewrite (@fmap_comp _ _ F).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (@counit _ _ _ _ Adj (F y))).
  change (@counit _ _ _ _ Adj (F y) ∘ fmap[F] (th y)) with (cmp_free_e y).
  rewrite <- Comparison_left_iso_e.
  rewrite !comp_assoc.
  rewrite iso_from_to, id_left.
  reflexivity.
Defined.

Lemma Comparison_coherence (x : X) :
  fmap[G] (to (`1 Comparison_left x)) ∘ from (`1 Comparison_right (F' x))
    ≈ th x.
Proof.
  change (fmap[G] (to (Comparison_left_iso x))
            ∘ (fmap[G] (beck_e Adj CR (Comparison_alg (F' x)))
                 ∘ @unit _ _ _ _ Adj (G' (F' x)))
          ≈ th x).
  rewrite comp_assoc.
  rewrite <- (@fmap_comp _ _ G).
  rewrite Comparison_left_iso_e.
  unfold cmp_free_e.
  rewrite (@fmap_comp _ _ G).
  rewrite <- comp_assoc.
  rewrite <- (adj_unit_natural Adj (th x)).
  rewrite comp_assoc.
  rewrite (@fmap_counit_unit _ _ _ _ Adj (F x)).
  apply id_left.
Qed.

Definition Comparison_exists : Comparison :=
  {| cmp_functor := Comparison_functor;
     cmp_left := Comparison_left;
     cmp_right := Comparison_right;
     cmp_monad := Comparison_coherence |}.

End Existence.

(* ------------------------------------------------------------------------ *)
(** ** The Lemma, uniqueness: Mac Lane's canonical presentation *)

Section Uniqueness.

Context (CR : CreatesUSplitCoequalizers G).
Context (P : Comparison).

Local Notation M0 := (cmp_functor P).
Local Notation al x := (`1 (cmp_left P) x).
Local Notation be a := (`1 (cmp_right P) a).
Local Notation th x := (transform[mh_transform (to θ)] x).
Local Notation ph x := (transform[mh_transform (from θ)] x).

(* Mac Lane's k = M ε'_a, read through α. *)
Definition cmp_e (a : A') : F (G' a) ~> M0 a :=
  fmap[M0] (@counit _ _ _ _ Adj' a) ∘ from (al (G' a)).

(* "... k must be M ε'_a = ε_{M a}", read through β. *)
Lemma cmp_e_counit (a : A') :
  cmp_e a ≈ @counit _ _ _ _ Adj (M0 a) ∘ fmap[F] (from (be a)).
Proof.
  unfold cmp_e.
  rewrite (Comparison_counit_fused P a).
  rewrite <- !comp_assoc.
  simpl.
  rewrite iso_to_from.
  rewrite id_right.
  reflexivity.
Qed.

Lemma cmp_e_G (a : A') :
  fmap[G] (cmp_e a)
    ≈ from (be a) ∘ (fmap[G'] (@counit _ _ _ _ Adj' a) ∘ ph (G' a)).
Proof.
  unfold cmp_e.
  rewrite (@fmap_comp _ _ G).
  pose proof (`2 (cmp_right P) _ _ (@counit _ _ _ _ Adj' a)) as Hn;
    simpl in Hn.
  simpl.
  rewrite Hn; clear Hn.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  apply compose_respects; [ reflexivity | ].
  pose proof (cmp_monad_inv P (G' a)) as Hm; simpl in Hm.
  exact Hm.
Qed.

Lemma cmp_e_cofork (a : A') :
  cmp_e a ∘ crude_pair_l Adj (Comparison_alg a)
    ≈ cmp_e a ∘ crude_pair_r Adj (Comparison_alg a).
Proof.
  change (cmp_e a ∘ @counit _ _ _ _ Adj (F (G' a))
          ≈ cmp_e a ∘ fmap[F] (fmap[G'] (@counit _ _ _ _ Adj' a)
                                 ∘ ph (G' a))).
  rewrite !(cmp_e_counit a).
  rewrite <- !comp_assoc.
  rewrite <- (adj_counit_natural Adj (fmap[F] (from (be a)))).
  rewrite !comp_assoc.
  rewrite <- (adj_counit_natural Adj (@counit _ _ _ _ Adj (M0 a))).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite <- !(@fmap_comp _ _ F).
  apply fmap_respects.
  rewrite <- (@fmap_comp _ _ G).
  rewrite <- (cmp_e_counit a).
  apply cmp_e_G.
Qed.

Lemma cmp_e_iso (a : A') :
  to (be a) ∘ fmap[G] (cmp_e a)
    ≈ scoeq_e (beck_split Adj (Comparison_alg a)).
Proof.
  rewrite (cmp_e_G a).
  rewrite !comp_assoc.
  simpl.
  rewrite iso_to_from.
  rewrite id_left.
  reflexivity.
Qed.

(* M0 a is a coequalizer of the canonical presentation of a: the
   reflection clause of creation. *)
Definition cmp_e_coeq (a : A') :
  IsCoequalizer (crude_pair_l Adj (Comparison_alg a))
    (crude_pair_r Adj (Comparison_alg a)) (M0 a) (cmp_e a) :=
  @create_coeq_reflects A X G CR _ _
    (crude_pair_l Adj (Comparison_alg a))
    (crude_pair_r Adj (Comparison_alg a))
    (beck_split Adj (Comparison_alg a)) (M0 a) (cmp_e a)
    (cmp_e_cofork a) (be a) (cmp_e_iso a).

Definition cmp_unique_data (a : A') :=
  create_coeq_unique CR
    (crude_pair_l Adj (Comparison_alg a))
    (crude_pair_r Adj (Comparison_alg a))
    (beck_split Adj (Comparison_alg a))
    (cmp_e a) (beck_e Adj CR (Comparison_alg a))
    (cmp_e_cofork a) (beck_cofork Adj CR (Comparison_alg a))
    (be a) (cmp_e_iso a)
    (beck_iso Adj CR (Comparison_alg a))
    (beck_iso_e Adj CR (Comparison_alg a)).

Definition cmp_unique_iso (a : A') : M0 a ≅ Comparison_functor CR a :=
  `1 (cmp_unique_data a).

Lemma cmp_unique_iso_e (a : A') :
  to (cmp_unique_iso a) ∘ cmp_e a ≈ beck_e Adj CR (Comparison_alg a).
Proof. exact (`2 (cmp_unique_data a)). Qed.

Lemma cmp_e_natural {a b : A'} (f : a ~> b) :
  fmap[M0] f ∘ cmp_e a ≈ cmp_e b ∘ fmap[F] (fmap[G'] f).
Proof.
  unfold cmp_e.
  rewrite !comp_assoc.
  rewrite <- (@fmap_comp _ _ M0).
  rewrite <- (adj_counit_natural Adj' f).
  rewrite (@fmap_comp _ _ M0).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  pose proof (`2 (cmp_left P) _ _ (fmap[G'] f)) as Hn; simpl in Hn.
  simpl.
  rewrite Hn; clear Hn.
  rewrite <- !comp_assoc.
  rewrite iso_to_from.
  rewrite id_right.
  reflexivity.
Qed.

(* The isomorphisms are natural, by the naturality of Mac Lane's k. *)
Lemma cmp_unique_iso_natural {a b : A'} (f : a ~> b) :
  fmap[M0] f
    ≈ from (cmp_unique_iso b) ∘ fmap[Comparison_functor CR] f
        ∘ to (cmp_unique_iso a).
Proof.
  apply (@epic _ _ _ _ (coequalizer_epic _ _ (cmp_e_coeq a))).
  rewrite (cmp_e_natural f).
  change (cmp_e b ∘ fmap[F] (fmap[G'] f)
          ≈ from (cmp_unique_iso b)
              ∘ beck_G_map Adj CR (fmap[Comparison_alg] f)
              ∘ to (cmp_unique_iso a) ∘ cmp_e a).
  rewrite <- (comp_assoc _ (to (cmp_unique_iso a))).
  rewrite cmp_unique_iso_e.
  rewrite <- comp_assoc.
  rewrite (beck_G_map_commutes Adj CR (fmap[Comparison_alg] f)).
  rewrite comp_assoc.
  rewrite <- cmp_unique_iso_e.
  rewrite !comp_assoc.
  rewrite iso_from_to, id_left.
  reflexivity.
Qed.

Theorem Comparison_unique_to : M0 ≈ Comparison_functor CR.
Proof.
  exists cmp_unique_iso.
  intros a b f.
  exact (cmp_unique_iso_natural f).
Qed.

End Uniqueness.

(* ------------------------------------------------------------------------ *)
(** ** The isomorphism is a morphism of comparisons, and the only one *)

Section Cell.

Context (CR : CreatesUSplitCoequalizers G).
Context (P : Comparison).

Local Notation M0 := (cmp_functor P).
Local Notation al x := (`1 (cmp_left P) x).
Local Notation be a := (`1 (cmp_right P) a).
Local Notation ph x := (transform[mh_transform (from θ)] x).

(* The algebra's unit law makes G (cmp_e a) a split epimorphism. *)
Lemma cmp_e_G_split (a : A') :
  fmap[G] (cmp_e P a) ∘ (@unit _ _ _ _ Adj (G' a) ∘ to (be a)) ≈ id.
Proof.
  rewrite (cmp_e_G P a).
  transitivity (from (be a)
                  ∘ ((fmap[G'] (@counit _ _ _ _ Adj' a) ∘ ph (G' a))
                       ∘ @unit _ _ _ _ Adj (G' a)) ∘ to (be a)).
  { rewrite !comp_assoc. reflexivity. }
  pose proof (@t_id X (G ◯ F) (Adjunction_Induced_Monad Adj) (G' a)
                (`2 (Comparison_alg a))) as Hu; simpl in Hu.
  simpl.
  rewrite Hu; clear Hu.
  rewrite id_right.
  apply iso_from_to.
Qed.

Lemma Comparison_unique_to_right (a : A') :
  to (`1 (Comparison_right CR) a) ∘ fmap[G] (to (cmp_unique_iso CR P a))
    ≈ to (be a).
Proof.
  rewrite <- (id_right (to (`1 (Comparison_right CR) a)
                          ∘ fmap[G] (to (cmp_unique_iso CR P a)))).
  rewrite <- (cmp_e_G_split a).
  rewrite !comp_assoc.
  rewrite <- (comp_assoc _ (fmap[G] (to (cmp_unique_iso CR P a)))).
  rewrite <- (@fmap_comp _ _ G).
  rewrite (cmp_unique_iso_e CR P a).
  change (beck_to Adj CR (Comparison_alg a)
            ∘ fmap[G] (beck_e Adj CR (Comparison_alg a))
            ∘ @unit _ _ _ _ Adj (G' a) ∘ to (be a) ≈ to (be a)).
  rewrite (beck_to_e Adj CR (Comparison_alg a)).
  pose proof (@t_id X (G ◯ F) (Adjunction_Induced_Monad Adj) (G' a)
                (`2 (Comparison_alg a))) as Hu; simpl in Hu.
  simpl.
  rewrite Hu; clear Hu.
  apply id_left.
Qed.

Lemma Comparison_unique_to_left (x : X) :
  to (`1 (Comparison_left CR) x) ∘ to (cmp_unique_iso CR P (F' x))
    ≈ to (al x).
Proof.
  apply (@epic _ _ _ _ (coequalizer_epic _ _ (cmp_e_coeq CR P (F' x)))).
  rewrite <- comp_assoc.
  rewrite (cmp_unique_iso_e CR P (F' x)).
  rewrite (Comparison_left_iso_e CR x).
  rewrite (cmp_e_counit P (F' x)).
  rewrite comp_assoc.
  simpl.
  rewrite <- (adj_counit_natural Adj (to (al x))).
  rewrite <- comp_assoc.
  rewrite <- (@fmap_comp _ _ F).
  unfold cmp_free_e.
  apply compose_respects; [ reflexivity | ].
  apply fmap_respects.
  symmetry.
  pose proof (cmp_monad P x) as Hm; simpl in Hm.
  exact Hm.
Qed.

(* At the constructed comparison, Mac Lane's k is the created arrow. *)
Lemma Comparison_exists_e (a : A') :
  cmp_e (Comparison_exists CR) a ≈ beck_e Adj CR (Comparison_alg a).
Proof.
  rewrite (cmp_e_counit (Comparison_exists CR) a).
  change (@counit _ _ _ _ Adj (Comparison_functor CR a)
            ∘ fmap[F] (fmap[G] (beck_e Adj CR (Comparison_alg a))
                         ∘ @unit _ _ _ _ Adj (G' a))
          ≈ beck_e Adj CR (Comparison_alg a)).
  rewrite (@fmap_comp _ _ F).
  rewrite comp_assoc.
  rewrite (adj_counit_natural Adj (beck_e Adj CR (Comparison_alg a))).
  rewrite <- comp_assoc.
  rewrite (@counit_fmap_unit _ _ _ _ Adj (G' a)).
  apply id_right.
Qed.

Theorem Comparison_unique_cell
  (k : ∀ a : A', M0 a ~> Comparison_functor CR a)
  (Hk : ∀ (a b : A') (f : a ~> b),
     fmap[Comparison_functor CR] f ∘ k a ≈ k b ∘ fmap[M0] f)
  (Hl : ∀ x : X, to (`1 (Comparison_left CR) x) ∘ k (F' x) ≈ to (al x))
  (a : A') : k a ≈ to (cmp_unique_iso CR P a).
Proof.
  apply (@epic _ _ _ _ (coequalizer_epic _ _ (cmp_e_coeq CR P a))).
  rewrite (cmp_unique_iso_e CR P a).
  rewrite <- (Comparison_exists_e a).
  unfold cmp_e.
  transitivity ((k a ∘ fmap[M0] (@counit _ _ _ _ Adj' a))
                  ∘ from (al (G' a))).
  { apply comp_assoc. }
  transitivity ((fmap[Comparison_functor CR] (@counit _ _ _ _ Adj' a)
                   ∘ k (F' (G' a))) ∘ from (al (G' a))).
  { apply compose_respects; [ symmetry; apply Hk | reflexivity ]. }
  transitivity (fmap[Comparison_functor CR] (@counit _ _ _ _ Adj' a)
                  ∘ (k (F' (G' a)) ∘ from (al (G' a)))).
  { apply comp_assoc_sym. }
  apply compose_respects; [ reflexivity | ].
  transitivity ((from (Comparison_left_iso CR (G' a))
                   ∘ (to (Comparison_left_iso CR (G' a)) ∘ k (F' (G' a))))
                  ∘ from (al (G' a))).
  { apply compose_respects; [ | reflexivity ].
    rewrite comp_assoc, iso_from_to, id_left. reflexivity. }
  transitivity ((from (Comparison_left_iso CR (G' a)) ∘ to (al (G' a)))
                  ∘ from (al (G' a))).
  { apply compose_respects; [ | reflexivity ].
    apply compose_respects; [ reflexivity | apply Hl ]. }
  rewrite <- comp_assoc.
  simpl.
  rewrite iso_to_from.
  apply id_right.
Qed.

End Cell.

(* The Lemma: any two comparisons over θ are isomorphic. *)
Theorem Comparison_unique (CR : CreatesUSplitCoequalizers G)
  (P Q : Comparison) : cmp_functor P ≈ cmp_functor Q.
Proof.
  transitivity (Comparison_functor CR).
  - apply Comparison_unique_to.
  - symmetry. apply Comparison_unique_to.
Qed.

(* Pairwise: between two comparisons P and Q over θ, the composite of
   their isomorphisms to the constructed one commutes with the left
   triangles (it is natural by [cmp_unique_iso_natural]) ... *)
Lemma Comparison_unique_pair_left (CR : CreatesUSplitCoequalizers G)
  (P Q : Comparison) (x : X) :
  to (`1 (cmp_left Q) x)
    ∘ (from (cmp_unique_iso CR Q (F' x)) ∘ to (cmp_unique_iso CR P (F' x)))
    ≈ to (`1 (cmp_left P) x).
Proof.
  rewrite <- (Comparison_unique_to_left CR Q x).
  rewrite <- (Comparison_unique_to_left CR P x).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite comp_assoc.
  rewrite iso_to_from, id_left.
  reflexivity.
Qed.

(* ... and is the only natural family of arrows that does. *)
Theorem Comparison_unique_pair_cell (CR : CreatesUSplitCoequalizers G)
  (P Q : Comparison)
  (k : ∀ a : A', cmp_functor P a ~> cmp_functor Q a)
  (Hk : ∀ (a b : A') (f : a ~> b),
     fmap[cmp_functor Q] f ∘ k a ≈ k b ∘ fmap[cmp_functor P] f)
  (Hl : ∀ x : X,
     to (`1 (cmp_left Q) x) ∘ k (F' x) ≈ to (`1 (cmp_left P) x))
  (a : A') :
  k a ≈ from (cmp_unique_iso CR Q a) ∘ to (cmp_unique_iso CR P a).
Proof.
  enough (H : to (cmp_unique_iso CR Q a) ∘ k a
                ≈ to (cmp_unique_iso CR P a)).
  { rewrite <- H. rewrite comp_assoc, iso_from_to, id_left. reflexivity. }
  apply (@epic _ _ _ _ (coequalizer_epic _ _ (cmp_e_coeq CR P a))).
  rewrite (cmp_unique_iso_e CR P a).
  rewrite <- (cmp_unique_iso_e CR Q a).
  unfold cmp_e.
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite comp_assoc.
  rewrite <- (Hk _ _ (@counit _ _ _ _ Adj' a)).
  rewrite <- !comp_assoc.
  apply compose_respects; [ reflexivity | ].
  rewrite <- (id_left (k (F' (G' a)))).
  rewrite <- (iso_from_to (`1 (cmp_left Q) (G' a))).
  rewrite <- !comp_assoc.
  rewrite (comp_assoc (to (`1 (cmp_left Q) (G' a)))).
  rewrite (Hl (G' a)).
  rewrite iso_to_from, id_right.
  reflexivity.
Qed.

End ComparisonDef.

(* ------------------------------------------------------------------------ *)
(** ** The Eilenberg–Moore resolution: terminal in the weak sense *)

Section EMResolution.

Universes m1 m2.

Context {X : Category} (T : X ⟶ X) `{H : @Monad X T}.

Local Notation TE := (Adjunction_Induced_Monad (@EM_Adjunction X T H)).

(* F^T ⊣ G^T defines T: its unit is id ∘ η and its multiplication
   μ ∘ T id, so the identity components are a morphism of monads each
   way. *)

Definition EM_Monad_to : MonadHom TE H.
Proof.
  unshelve refine
    {| mh_transform :=
         Build_Transform' (F:=EM_Forget T ◯ EM_Free T) (G:=T)
           (fun x => id) _ |}.
  - intros x y f; simpl. rewrite id_left, id_right. reflexivity.
  - intros x; simpl. rewrite id_left. exact (@EM_unit_agrees X T H x).
  - intros x; simpl.
    rewrite id_left.
    rewrite (@EM_join_agrees X T H x).
    rewrite fmap_id, !id_right.
    reflexivity.
Defined.

Definition EM_Monad_from : MonadHom H TE.
Proof.
  unshelve refine
    {| mh_transform :=
         Build_Transform' (F:=T) (G:=EM_Forget T ◯ EM_Free T)
           (fun x => id) _ |}.
  - intros x y f; simpl. rewrite id_left, id_right. reflexivity.
  - intros x; simpl. rewrite id_left. symmetry.
    exact (@EM_unit_agrees X T H x).
  - intros x; simpl.
    rewrite id_left.
    rewrite (@EM_join_agrees X T H x).
    rewrite fmap_id, !id_right.
    reflexivity.
Defined.

Definition EM_Monad_iso :
  @Isomorphism (Monads@{_ _ m1 m2} X) (EM_Forget T ◯ EM_Free T; TE) (T; H).
Proof.
  unshelve refine (@Build_Isomorphism (Monads@{_ _ m1 m2} X)
                     (EM_Forget T ◯ EM_Free T; TE) (T; H)
                     EM_Monad_to EM_Monad_from _ _).
  - intros x; simpl. apply id_left.
  - intros x; simpl. apply id_left.
Defined.

Example EM_Monad_iso_to (x : X) :
  transform[mh_transform (to EM_Monad_iso)] x = id := eq_refl.

Example EM_Monad_iso_from (x : X) :
  transform[mh_transform (from EM_Monad_iso)] x = id := eq_refl.

Section Terminal.

Context {A' : Category} {F' : X ⟶ A'} {G' : A' ⟶ X} (Adj' : F' ⊣ G').
Context (θ' : @Isomorphism (Monads@{_ _ m1 m2} X)
                (G' ◯ F'; Adjunction_Induced_Monad Adj') (T; H)).

Definition EM_terminal_theta :
  @Isomorphism (Monads@{_ _ m1 m2} X)
    (G' ◯ F'; Adjunction_Induced_Monad Adj')
    (EM_Forget T ◯ EM_Free T; TE) :=
  iso_compose (iso_sym EM_Monad_iso) θ'.

Definition EM_terminal :
  Comparison (@EM_Adjunction X T H) Adj' EM_terminal_theta :=
  Comparison_exists (@EM_Adjunction X T H) Adj' EM_terminal_theta
    (@monadic_creates X T H).

Theorem EM_terminal_unique
  (P Q : Comparison (@EM_Adjunction X T H) Adj' EM_terminal_theta) :
  cmp_functor _ _ _ P ≈ cmp_functor _ _ _ Q.
Proof.
  exact (Comparison_unique (@EM_Adjunction X T H) Adj' EM_terminal_theta
           (@monadic_creates X T H) P Q).
Qed.

End Terminal.

End EMResolution.

(* ------------------------------------------------------------------------ *)
(** ** [EM_Comparison] is a comparison into the Eilenberg–Moore
       resolution and, over the identity identification of the two
       monads, the only one, up to a unique compatible isomorphism *)

Section EMComparison.

Universes m1 m2.

Context {X A : Category} {F : X ⟶ A} {G : A ⟶ X} (Adj : F ⊣ G).

Local Notation T := (Adjunction_Induced_Monad Adj).
Local Notation EMAdj := (@EM_Adjunction X (G ◯ F) T).

Definition EM_Comparison_theta :
  @Isomorphism (Monads@{_ _ m1 m2} X) (G ◯ F; T)
    (EM_Forget (G ◯ F) ◯ EM_Free (G ◯ F); Adjunction_Induced_Monad EMAdj) :=
  iso_sym (@EM_Monad_iso X (G ◯ F) T).

Example EM_Comparison_theta_to (x : X) :
  transform[mh_transform (to EM_Comparison_theta)] x = id := eq_refl.

(* The two triangles of Monad/Comparison.v, read back on the nose. *)
Example EM_Comparison_Forget_components (a : A) :
  `1 (EM_Comparison_Forget Adj) a = iso_id := eq_refl.

Example EM_Comparison_Free_components (x : X) :
  `1 (EM_Comparison_Free Adj) x = EM_Comparison_Free_iso Adj x := eq_refl.

Lemma EM_Comparison_coherence (x : X) :
  fmap[EM_Forget (G ◯ F)] (to (`1 (EM_Comparison_Free Adj) x))
    ∘ from (`1 (EM_Comparison_Forget Adj) (F x))
    ≈ transform[mh_transform (to EM_Comparison_theta)] x.
Proof. simpl. apply id_left. Qed.

Definition EM_Comparison_Comparison :
  Comparison EMAdj Adj EM_Comparison_theta :=
  {| cmp_functor := EM_Comparison Adj;
     cmp_left := EM_Comparison_Free Adj;
     cmp_right := EM_Comparison_Forget Adj;
     cmp_monad := EM_Comparison_coherence |}.

(* Awodey's clause in its coherent form: over the identity identification
   of the two monads, every comparison is ≈ the comparison functor.
   Without that coherence the clause is false
   (Instance/Fun/Action/Monad/Comparison.v). *)
Theorem EM_Comparison_unique
  (P : Comparison EMAdj Adj EM_Comparison_theta) :
  cmp_functor _ _ _ P ≈ EM_Comparison Adj.
Proof.
  exact (Comparison_unique EMAdj Adj EM_Comparison_theta
           (@monadic_creates X (G ◯ F) T) P EM_Comparison_Comparison).
Qed.

(* ... up to a unique compatible isomorphism: the composite of the two
   isomorphisms to the constructed comparison is the only natural family
   commuting with the left triangles. *)
Theorem EM_Comparison_unique_cell
  (P : Comparison EMAdj Adj EM_Comparison_theta)
  (k : ∀ a : A, cmp_functor _ _ _ P a ~> EM_Comparison Adj a)
  (Hk : ∀ (a b : A) (f : a ~> b),
     fmap[EM_Comparison Adj] f ∘ k a ≈ k b ∘ fmap[cmp_functor _ _ _ P] f)
  (Hl : ∀ x : X,
     to (`1 (EM_Comparison_Free Adj) x) ∘ k (F x)
       ≈ to (`1 (cmp_left _ _ _ P) x))
  (a : A) :
  k a ≈ from (cmp_unique_iso EMAdj Adj EM_Comparison_theta
                (@monadic_creates X (G ◯ F) T) EM_Comparison_Comparison a)
          ∘ to (cmp_unique_iso EMAdj Adj EM_Comparison_theta
                  (@monadic_creates X (G ◯ F) T) P a).
Proof.
  exact (Comparison_unique_pair_cell EMAdj Adj EM_Comparison_theta
           (@monadic_creates X (G ◯ F) T) P EM_Comparison_Comparison
           k Hk Hl a).
Qed.

(* Mac Lane: the Lemma at the Eilenberg–Moore resolution "will incidentally
   provide a new proof of the comparison theorem". *)
Definition EM_Comparison_via_Lemma : A ⟶ @EilenbergMoore X (G ◯ F) T :=
  Comparison_functor EMAdj Adj EM_Comparison_theta
    (@monadic_creates X (G ◯ F) T).

Theorem EM_Comparison_via_Lemma_agrees :
  EM_Comparison Adj ≈ EM_Comparison_via_Lemma.
Proof.
  exact (Comparison_unique_to EMAdj Adj EM_Comparison_theta
           (@monadic_creates X (G ◯ F) T) EM_Comparison_Comparison).
Qed.

End EMComparison.
