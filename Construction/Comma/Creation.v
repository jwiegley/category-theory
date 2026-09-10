Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Equalizer.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.One.
Require Import Category.Instance.Parallel.

Set Universe Polymorphism.

Generalizable All Variables.

(** * The comma projection creates limits *)

(* nLab: https://ncatlab.org/nlab/show/comma+category#limits_and_colimits
   nLab: https://ncatlab.org/nlab/show/created+limit

   The projection [comma_proj2 : =(d) ↓ U ⟶ C] creates limits, as the prose
   at Construction/Comma.v:100 and Construction/Comma/Limit.v:33 has always
   said.  Construction/Comma/Limit.v proves existence; what is added here is
   the reflection clause [comma_creates_reflect] and the packaging
   [comma_CreatesLimit] against Structure/Limit/Creation.v.  Nothing in
   Construction/Comma/Limit.v is changed.

   Two consequences worth naming.  First, [PreservesImageLimit]
   (Construction/Comma/Limit.v:110), the honest cone-level hypothesis that
   file introduced and that Adjunction/GAFT.v and Adjunction/SAFT.v consume,
   is [PreservesLimitCone] quantified over all shapes, up to repackaging a
   [Limit] record as a cone together with its universal property: the two
   bridges below carry no proof, and both round trips hold by [eq_refl]
   (the two [Type]s are not themselves convertible, one binding [Limit G]
   where the other binds a cone and an [IsLimitCone]).  So GAFT and SAFT
   already speak the general vocabulary under an older name.

   Second, the created lift lies over an ARBITRARY downstairs limit [L] on
   the nose — [comma_strict_apex] and [comma_strict_legs] are [eq_refl] for
   every [L], not merely for the one a [Complete C] happens to choose.  That
   is the generalization this file's header previously deferred: [Limit.v]
   now takes [Ldiag] as a section parameter instead of computing it as
   [HC J Gdiag], so [comma_limit] is parameterized by the limit it is built
   from and the projection lands on that limit definitionally.  The exported
   type of [Comma_Complete] is unchanged by the move — it simply supplies
   [HC J (Gdiag K)] as the parameter — so Adjunction/GAFT.v and
   Adjunction/SAFT.v are untouched.

   On the house rule that morphisms are compared with [≈]: [comma_strict_legs]
   writes [=] between morphisms, and it does so because both sides are the
   SAME term — the witness is [eq_refl].  It records Mac Lane's [F σ = τ] at
   full strength, which is strictly stronger than the [≈] the class asks
   for; every proof below uses [≈].  (An earlier revision said
   [comma_strict_legs] was "the one statement here" of that shape; measured
   at this revision there are FOUR in this file — the later three being
   [comma_limit_at_legs], [comma_prod_leg_strict] and
   [comma_equalizer_leg_strict] — and a fifth, [coslice_lift_legs], in
   Construction/Slice/Creation.v, each likewise [eq_refl] on one term.) *)

(* What follows the strictness readbacks was added for Mac Lane §V.6's
   Lemma 1 and Exercise 1 (book pp. 121-125) and, through
   Construction/Slice/Creation.v, §V.1 Exercise 1 (book p. 112); the same
   ground is Riehl §3.4 Proposition 8 in its limit half (printed p. 106),
   §4.7 Lemma 2 (printed p. 174) and the exercise asking for that lemma's
   direct argument (printed p. 180).  Three things were missing.

   First, the hypothesis was too strong.  Mac Lane's lemma assumes only
   that [U] preserve the limits of the shapes at issue — products and
   equalizers, in Theorem 2's proof — while [PreservesImageLimit]
   quantifies over every shape and every diagram at once, and the two
   per-shape clauses Theorem 2 consumes are not derivable from the sections
   of Construction/Comma/Limit.v, whose [HU] is a total function over
   shapes.  [comma_limit_at] re-derives that whole construction from
   [PreservesLimitCone (Gdiag K) U], the hypothesis at the ONE base diagram
   of the ONE [K] at hand, and it does so ADDITIVELY: Construction/Comma/Limit.v
   is not touched, because NINE [.v] files and nine planning or documentation
   files cite it at fifteen distinct line numbers at master (measured with
   [grep -rloE 'Comma/Limit\.v:[0-9]+'] over [--include='*.v'] and
   [--include='*.md']); the count is ten [.v] files from the previous commit
   on, the tenth being Construction/Slice/Creation.v, which that commit
   added, and one of the nine is this file itself, so EIGHT other files
   carry the constraint.  The price is
   about a hundred lines of re-derivation with the original tactic scripts.

   The two-sided analogue landed first and is not superseded:
   Construction/Arrow/Limit.v:378's [comma_proj_StrictlyCreatesLimit]
   already gives strict creation for [comma_proj : (S ↓ T) ⟶ A ∏ B] from a
   per-diagram hypothesis of the same shape.  The functors differ — [Snd ◯
   comma_proj] and [comma_proj2] are different records — and there is no
   [StrictlyCreatesLimit_compose], so the re-derivation here is not
   avoidable, but the idea is that file's.

   Second, the creation was not strict.  [comma_CreatesLimit]'s
   [creates_lift] DISCARDS the cone it is handed and returns the lift of the
   fixed [L], related to that cone only by the [ConeIso] its second field
   supplies; so its apex is not the given cone's apex, and
   Test/ProbeCommaCreation438.v's negative n5 records the refusal against
   the control that the new lift is accepted.  [comma_StrictlyCreatesLimit]
   builds the lift from [Build_Limit N HN] — the given cone repackaged —
   rather than from a fixed [L], so both [StrictLift] fields are [eq_refl]
   and [reflexivity] at EVERY limiting cone downstairs.  That is Mac Lane's
   [F a = x] and [F σ = τ] in full, and [comma_CreatesLimit_at] then carries
   no [L] argument at all.  [comma_strict_apex] and [comma_strict_legs]
   above do not say this: they speak about [comma_limit HU K L] directly,
   not about what [creates_lift] returns when handed some other cone.

   Third, the two shapes.  The equalizers clause is the per-diagram
   construction read at [Parallel], which costs nothing because [Parallel]
   leaves its hom universe free.  The products clause is stated
   ELEMENTARILY over [Structure/Limit/Product.v]'s [IsIndexedProduct]
   rather than over a discrete shape, because that is the form that can be
   instantiated at an arbitrary FAMILY: a functor out of [DiscreteCat A]
   that eliminates the shape's [x = y] into a hom pins both categories to
   [Category@{_ Set Set}], and is refused over a generic [C] with
   "universe inconsistency: Cannot enforce Set = ..." (probe negative n2) —
   the tree's own [DiscreteCat_Functor] (Instance/Discrete.v:59) prints as
   [DiscreteCat@{u Set Set} A ⟶ C] for that reason, and a hand-rolled
   eliminator is refused identically, so the pin belongs to the ELIMINATION
   and not to any one constant.  It does not belong to [DiscreteCat]
   either, whose hom and proof universes are free
   ([DiscreteCat@{o h p} : Type@{o} → Category@{o h p}]) — which is why
   [comma_CreatesAllLimits] and its instance [comma_CreatesProducts] below
   are formable and axiom-free over a generic [C] and [D], and why they are
   not vacuous: a CONSTANT discrete diagram eliminates nothing and is
   formable, so the class applies to it.  This is the trap the
   Construction/Comma/Special.v bullet of docs/INDEX.md already records for
   [DiscreteCat_Functor], sighted here one step earlier.

   Three of issue #438's substantive claims about the tree are FALSE as of
   this file's parent, and are recorded here because the issue text will
   outlive the commit.  Read them TREE-WIDE: two of the three are written
   in the issue as statements about Construction/Comma/Limit.v, and of THAT
   file they are still true — what falsifies them is this file, which
   landed after the issue was written.  "Creation proper is not stated" —
   [comma_CreatesLimit] above states it.  "The uniqueness/reflection clause
   is absent" — [comma_creates_reflect] is the reflection clause, and
   uniqueness is Structure/Limit/Creation.v's [creates_lift_unique] applied
   to it, though only up to cone isomorphism (see the NOT DELIVERED list).
   "No lemma asserts that the projection of the constructed limit is the
   given one" — [comma_strict_apex] and [comma_strict_legs] assert exactly
   that, by [eq_refl], for an arbitrary downstairs limit.  A fourth is half
   true:
   comma limits sit under an all-shapes [Complete C] oracle only for
   [Comma_Complete] (Construction/Comma/Limit.v:247); [comma_limit] (:240)
   has taken its downstairs limit as a parameter since commit 28ee6e54.
   Seven of the issue's line citations are stale, all of them by the two
   lines that commit added or by later drift: [comma_limit] is :240 not
   :238, [Comma_Complete] :247 not :245, [apex_obj] :161 not :159,
   [apex_leg] :165 not :163, [right_adjoint_PreservesImageLimit] :266 not
   :264, [Comma_Complete_right_adjoint] :273 not :271, and [adj_id] is
   Instance/Adjoints.v:70, not :42 (:42 is prose).  Its citation of
   [PreservesImageLimit] at :110 is correct, and its LIBRARY-DEFECT item —
   that Construction/Comma.v:99-100 and Construction/Comma/Limit.v:32-33
   claim creation where only existence is proved — was already resolved by
   this file's first commit, as the paragraph above records.

   Measured.  This file's [.glob] declares 42 heads (38 [def], 4 [prf]) and
   no [Program] obligation, nine of them from the first commit; with
   Construction/Slice/Creation.v's 30 that is 72 constants, all carried by
   [make print-assumptions] and all reporting "Closed under the global
   context".  Closure goes from 35 modules excluding self to 38, and the
   three added are EXACTLY the three new [Require]s
   (Structure/Limit/Product, Structure/Equalizer, Instance/Parallel) — none
   brings anything else with it, and neither creation class needed a
   [Require] at all — while Adjunction/Representability/Sets.v stays at 99,
   all three having been in its closure already.  Four files require this
   one: that one and Construction/Slice/Creation.v in the library, and the
   two probes.  Construction/Slice/Creation.v closes over 52 and the probe
   over 58.  Zero collisions over the 72 heads and the probe's declared
   names (whole-word [grep -rlw] over [*.v], instrument-checked at [Full],
   [comma_limit] and [Coslice_Proj]); the only other-file hits are two USES
   of [Continuous_PreservesImageLimit] in Adjunction/Representability/Sets.v
   and one prose mention of [comma_CreatesLimit] at Construction/Arrow/Limit.v:97,
   with no second declaration anywhere.  Renaming each of the 72 names in
   turn, in the file that DECLARES it and nowhere else, then recompiling
   this file, the satellite and the probe in order: 71 stop the probe, every
   one of those on a positive line and none inside a refutation, and the
   72nd ([comma_StrictlyCreatesLimit]) stops the satellite first, at the
   line that consumes it — nothing survives a rename, so no guard here is
   vacuous.  [make todo] grows by seven, the probe's seven refutation lines,
   and neither library file contributes a hit.

   Across the two files thirteen definitions close with [Defined] — two of
   them from this file's first commit — and seven with [Qed].  Flipping each
   [Defined] alone to [Qed] in a copy of the whole file: FOUR stop the file
   itself ([comma_at_apex_leg], [comma_at_med], [comma_prod_proj], and the
   satellite's [coslice_lift_leg], each needed to reduce by a later
   definition), TWO stop the probe ([comma_StrictlyCreatesLimit] and
   [Coslice_Proj_StrictlyCreatesLimit], whose strict-lift readbacks are
   [eq_refl]), and SEVEN compile through with every readback intact
   ([comma_at_ump], [comma_reflect_at], [comma_IsIndexedProduct],
   [coslice_reflect_at], [coslice_lift_ump], and the two pre-existing
   [comma_creates_reflect] and [comma_CreatesLimit]).  Those stay
   transparent because they are data — universal properties, limiting-cone
   witnesses, a record inhabitant — matching the [Defined] of [umed] and
   [comma_ump] beside them; that their flip is not load-bearing is
   disclosed, not claimed away.

   NOT DELIVERED here.  No weakening of [Comma_Complete]'s exported type,
   so Adjunction/GAFT.v and Adjunction/SAFT.v are untouched; no per-shape
   completeness class, the products and equalizers clauses being single
   statements rather than instances of a shape-indexed family; no
   INSTANTIATION of [comma_CreatesProducts] at an arbitrary FAMILY over a
   generic [C], for the elimination reason above — the class is shipped and
   the probe applies it to a constant discrete diagram, but a diagram built
   from a family is refused; no ON-THE-NOSE
   uniqueness of the lift, Mac Lane's "exactly one pair" — what is
   available is [creates_lift_unique]'s [ConeIso], and
   Structure/Limit/Creation.v says in terms why uniqueness cannot be a
   field of the class in a setoid setting; no finiteness anywhere, the
   index of the products clause being an arbitrary [Type]; no creation by
   [comma_proj1], which nothing in the tree addresses; and no colimit dual,
   which issue #438 scopes out along with Riehl's connected-colimit half.
   Strict creation for a PLAIN coslice projection IS delivered, in
   Construction/Slice/Creation.v — an earlier revision of this list said it
   was blocked, on the false premise that no unconditioned coslice
   projection existed. *)

(** ** [PreservesImageLimit] is cone-level preservation at every shape *)

Definition PreservesImageLimit_Continuous
  {C D : Category} {U : C ⟶ D} (H : @PreservesImageLimit C D U) :
  ContinuousFunctor U :=
  fun J K N HN => H J K (@Build_Limit J C K N HN).

Definition Continuous_PreservesImageLimit
  {C D : Category} {U : C ⟶ D} (H : ContinuousFunctor U) :
  @PreservesImageLimit C D U :=
  fun J K L => H J K (@limit_cone _ _ _ L) (limit_limitcone L).

(** ** The reflection clause *)

Section CommaReflect.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context (HU : @PreservesImageLimit C D U).
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).

(* The cone with apex [d] over [U ◯ (comma_proj2 ◯ K)] read off the comma
   data of K.  This is the general-diagram analogue of [base_cone]
   (Construction/Comma/Limit.v:146), restated because that one is fixed to
   the chosen [Gdiag]. *)

Lemma rbase_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[U] (fmap[comma_proj2 ◯ K] f) ∘ `2 (K x) ≈ `2 (K y).
Proof using Type.
  symmetry.
  transitivity (`2 (K y) ∘ id[d]).
  - rewrite id_right; reflexivity.
  - exact (`2 (fmap[K] f)).
Qed.

Definition rbase_cone : Cone (U ◯ (comma_proj2 ◯ K)) :=
  @Build_Cone J D (U ◯ (comma_proj2 ◯ K)) d
    (@Build_ACone J D d (U ◯ (comma_proj2 ◯ K))
       (fun j => `2 (K j)) (@rbase_coherence)).

(* A cone over K whose C-projection is limiting is itself limiting.  The
   C-component of the mediator is given by the projected cone; the comma
   component is the triangle over [d], and that triangle is forced by
   uniqueness of the mediator into the image limit — which is exactly what
   [PreservesImageLimit] supplies. *)

Definition comma_creates_reflect (M : Cone K)
  (HM : IsLimitCone (FCone comma_proj2 M)) : IsLimitCone M.
Proof using HU.
  intro N.
  pose (L := @Build_Limit J C (comma_proj2 ◯ K) (FCone comma_proj2 M) HM).
  destruct (HM (FCone comma_proj2 N)) as [w Hw Hwu].
  assert (Hsq : (`2 vertex_obj[M]) ∘ id[d]
                  ≈ fmap[U] w ∘ `2 vertex_obj[N]).
  { rewrite id_right.
    apply (limit_med_eq (image_is_alimit HU L) rbase_cone).
    - intro j.
      change (fmap[U] (cone_leg (FCone comma_proj2 M) j) ∘ (`2 vertex_obj[M])
                ≈ `2 (K j)).
      symmetry.
      exact (comma_square (cone_leg M j)).
    - intro j.
      change (fmap[U] (cone_leg (FCone comma_proj2 M) j)
                ∘ (fmap[U] w ∘ `2 vertex_obj[N]) ≈ `2 (K j)).
      rewrite comp_assoc, <- fmap_comp.
      rewrite (Hw j).
      symmetry.
      exact (comma_square (cone_leg N j)). }
  unshelve refine {| unique_obj := ((ttt, w); Hsq) |}.
  - intro j; split.
    + now destruct (fst (`1 (cone_leg N j))).
    + exact (Hw j).
  - intros [[u1 u2] Hu] Hv; split.
    + simpl; destruct u1; reflexivity.
    + apply Hwu.
      intro j.
      exact (snd (Hv j)).
Defined.

End CommaReflect.

(** ** The instance *)

Section CommaCreates.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context (HU : @PreservesImageLimit C D U).
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).

(* An ARBITRARY limit of the base diagram downstairs.  This used to be the
   chosen [Ldiag HC K] coming from a [Complete C]; making it a parameter is
   what upgrades the strictness statements below from "at the chosen limit"
   to "at every limit". *)
Context (L : Limit (Gdiag K)).

(* The image of the comma limit cone IS that downstairs limit cone, by
   conversion. *)

Definition comma_image_limitcone :
  IsLimitCone (FCone comma_proj2 (@limit_cone _ _ _ (comma_limit HU K L)))
  := fun N => @ump_limit _ _ _ _ (limit_is_alimit L) N.

Definition comma_CreatesLimit : CreatesLimit K comma_proj2.
Proof using HU L.
  unshelve refine
    {| creates_lift := fun _ _ => @limit_cone _ _ _ (comma_limit HU K L) |}.
  - intros N HN.
    exact (limitcone_iso comma_image_limitcone HN).
  - exact (comma_creates_reflect HU K).
Defined.

End CommaCreates.

(** ** Strictness at EVERY limit: apex and legs on the nose *)

(* These now quantify over an arbitrary downstairs limit [L] rather than the
   one chosen by a [Complete C].  The witnesses are still [eq_refl]: the
   comma limit is BUILT from [L], so the projection lands on [L]'s apex and
   legs definitionally, whichever limit [L] is.  This is Mac Lane's [F σ = τ]
   at full strength, and it is what the header of this file previously
   deferred as a separate proposal. *)

Definition comma_strict_apex {C D : Category} {U : C ⟶ D} {d : D}
  (HU : @PreservesImageLimit C D U)
  {J : Category} (K : J ⟶ (=(d) ↓ U)) (L : Limit (Gdiag K)) :
  comma_proj2 (vertex_obj[comma_limit HU K L]) = vertex_obj[L]
  := eq_refl.

Definition comma_strict_legs {C D : Category} {U : C ⟶ D} {d : D}
  (HU : @PreservesImageLimit C D U)
  {J : Category} (K : J ⟶ (=(d) ↓ U)) (L : Limit (Gdiag K)) (j : J) :
  fmap[comma_proj2] (cone_leg (comma_limit HU K L) j)
    = limit_leg (limit_is_alimit L) j := eq_refl.

(** ** The same construction from a PER-DIAGRAM hypothesis *)

(* Mac Lane's Lemma (§V.6, book p. 121) assumes only that [U] preserve the
   limits of the shapes at issue — products and equalizers, in the proof of
   Theorem 2 — whereas [PreservesImageLimit] quantifies over every shape and
   every diagram at once.  The section below re-derives the construction of
   Construction/Comma/Limit.v from the single hypothesis

     [PreservesLimitCone (Gdiag K) U]

   for the one base diagram of the one [K] at hand.  Nothing in
   Construction/Comma/Limit.v is changed or re-proved: [base_cone], [wmed],
   [qcone], [comma_square] and [image_acone] are reused verbatim and the
   tactic scripts are the originals.  The only edit is at the one place the
   all-shapes hypothesis was consumed, [image_is_alimit HU L], which becomes
   [comma_at_image]. *)

Section CommaCreateAt.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).
Context (HK : PreservesLimitCone (Gdiag K) U).
Context (L : Limit (Gdiag K)).

Definition comma_at_image : IsALimit (U ◯ Gdiag K) (U L) :=
  @Build_IsALimit J D (U ◯ Gdiag K) (U L) (image_acone L)
    (HK (@limit_cone _ _ _ L) (limit_limitcone L)).

Definition comma_at_phi : d ~{D}~> U L :=
  limit_med comma_at_image (base_cone K).

Lemma comma_at_phi_commutes (j : J) :
  fmap[U] (limit_leg (limit_is_alimit L) j) ∘ comma_at_phi ≈ `2 (K j).
Proof. exact (limit_med_commutes comma_at_image (base_cone K) j). Qed.

Definition comma_at_apex_obj : (=(d) ↓ U) := ((ttt, vertex_obj[L]); comma_at_phi).

Definition comma_at_apex_leg (j : J) : comma_at_apex_obj ~{=(d) ↓ U}~> K j.
Proof.
  unshelve refine ((ttt, limit_leg (limit_is_alimit L) j); _).
  change (`2 (K j) ∘ id[d]
          ≈ fmap[U] (limit_leg (limit_is_alimit L) j) ∘ comma_at_phi).
  rewrite id_right.
  symmetry.
  exact (comma_at_phi_commutes j).
Defined.

Lemma comma_at_apex_coherence {x y : J} (f : x ~{J}~> y) :
  fmap[K] f ∘ comma_at_apex_leg x ≈ comma_at_apex_leg y.
Proof.
  split.
  - reflexivity.
  - exact (limit_leg_coherence (limit_is_alimit L) f).
Qed.

Definition comma_at_apex_cone : Cone K :=
  @Build_Cone J (=(d) ↓ U) K comma_at_apex_obj
    (@Build_ACone J (=(d) ↓ U) comma_at_apex_obj K comma_at_apex_leg
       (@comma_at_apex_coherence)).

Definition comma_at_med (N : Cone K) :
  vertex_obj[N] ~{=(d) ↓ U}~> comma_at_apex_obj.
Proof.
  unshelve refine ((ttt, wmed K L N); _).
  change (comma_at_phi ∘ id[d] ≈ fmap[U] (wmed K L N) ∘ `2 vertex_obj[N]).
  rewrite id_right.
  apply (limit_med_eq comma_at_image (base_cone K)).
  - exact (limit_med_commutes comma_at_image (base_cone K)).
  - intro j.
    change (fmap[U] (limit_leg (limit_is_alimit L) j)
              ∘ (fmap[U] (wmed K L N) ∘ `2 vertex_obj[N]) ≈ `2 (K j)).
    unfold wmed.
    rewrite comp_assoc, <- fmap_comp.
    rewrite (limit_med_commutes (limit_is_alimit L) (qcone K N) j).
    symmetry.
    exact (comma_square (cone_leg N j)).
Defined.

Definition comma_at_ump (N : Cone K) :
  ∃! u : vertex_obj[N] ~{=(d) ↓ U}~> comma_at_apex_obj,
    ∀ j : J, comma_at_apex_leg j ∘ u ≈ cone_leg N j.
Proof.
  unshelve refine {| unique_obj := comma_at_med N |}.
  - intro j; split.
    + now destruct (fst (`1 (cone_leg N j))).
    + exact (limit_med_commutes (limit_is_alimit L) (qcone K N) j).
  - intros v Hv; split.
    + now destruct (fst (`1 v)).
    + unfold wmed.
      apply (limit_med_unique (limit_is_alimit L) (qcone K N)).
      intro j.
      exact (snd (Hv j)).
Defined.

Definition comma_limit_at : Limit K :=
  @Build_Limit J (=(d) ↓ U) K comma_at_apex_cone comma_at_ump.

(* The projection lands on [L] on the nose, exactly as [comma_strict_apex]
   and [comma_strict_legs] do for the all-shapes construction. *)

Definition comma_limit_at_apex :
  comma_proj2 (vertex_obj[comma_limit_at]) = vertex_obj[L] := eq_refl.

Definition comma_limit_at_legs (j : J) :
  fmap[comma_proj2] (cone_leg comma_limit_at j)
    = limit_leg (limit_is_alimit L) j := eq_refl.

End CommaCreateAt.

(** ** The reflection clause, per diagram *)

Section CommaReflectAt.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).
Context (HK : PreservesLimitCone (Gdiag K) U).

(* [comma_creates_reflect] above with the all-shapes [HU] weakened to [HK];
   the script is that proof's, with [image_is_alimit HU L] replaced by
   [comma_at_image K HK L]. *)

Definition comma_reflect_at (M : Cone K)
  (HM : IsLimitCone (FCone comma_proj2 M)) : IsLimitCone M.
Proof using HK.
  intro N.
  pose (L := @Build_Limit J C (comma_proj2 ◯ K) (FCone comma_proj2 M) HM).
  destruct (HM (FCone comma_proj2 N)) as [w Hw Hwu].
  assert (Hsq : (`2 vertex_obj[M]) ∘ id[d]
                  ≈ fmap[U] w ∘ `2 vertex_obj[N]).
  { rewrite id_right.
    apply (limit_med_eq (comma_at_image K HK L) (rbase_cone K)).
    - intro j.
      change (fmap[U] (cone_leg (FCone comma_proj2 M) j) ∘ (`2 vertex_obj[M])
                ≈ `2 (K j)).
      symmetry.
      exact (comma_square (cone_leg M j)).
    - intro j.
      change (fmap[U] (cone_leg (FCone comma_proj2 M) j)
                ∘ (fmap[U] w ∘ `2 vertex_obj[N]) ≈ `2 (K j)).
      rewrite comp_assoc, <- fmap_comp.
      rewrite (Hw j).
      symmetry.
      exact (comma_square (cone_leg N j)). }
  unshelve refine {| unique_obj := ((ttt, w); Hsq) |}.
  - intro j; split.
    + now destruct (fst (`1 (cone_leg N j))).
    + exact (Hw j).
  - intros [[u1 u2] Hu] Hv; split.
    + simpl; destruct u1; reflexivity.
    + apply Hwu.
      intro j.
      exact (snd (Hv j)).
Defined.

End CommaReflectAt.

(** ** Strict creation *)

(* [comma_CreatesLimit] above is creation in the [CreatesLimit] sense: its
   [creates_lift] returns the lift of the FIXED [L] it was given, related to
   the cone it is handed only up to [ConeIso].  Mac Lane's lemma and Riehl
   §3.4.7 ask for more — that the lift lie over the GIVEN cone on the nose —
   and [Structure/Limit/Creation.v]'s [StrictLift] is the record that says
   so.  The lift below is therefore built from [Build_Limit N HN], the given
   cone repackaged as a limit, rather than from a fixed [L]; both strictness
   fields are then [eq_refl] and [reflexivity], for EVERY limiting cone
   downstairs.  Test/ProbeCommaCreation438.v pins the difference: the shipped
   [creates_lift]'s apex is refused against [vertex_obj[N]] (negative n5)
   where this one is accepted (its paired control). *)

Section CommaStrictCreate.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {J : Category}.
Context (K : J ⟶ (=(d) ↓ U)).
Context (HK : PreservesLimitCone (Gdiag K) U).

Definition comma_strict_lift (N : Cone (comma_proj2 ◯ K)) (HN : IsLimitCone N) :
  StrictLift K comma_proj2 N :=
  @Build_StrictLift J (=(d) ↓ U) C K comma_proj2 N
    (comma_limit_at K HK (@Build_Limit J C (Gdiag K) N HN))
    eq_refl
    (fun x => reflexivity _).

Definition comma_StrictlyCreatesLimit : StrictlyCreatesLimit K comma_proj2.
Proof using HK.
  unshelve refine {| screates := comma_strict_lift |}.
  - intros N HN.
    exact (limit_limitcone
             (comma_limit_at K HK (@Build_Limit J C (Gdiag K) N HN))).
  - exact (comma_reflect_at K HK).
Defined.

(* Creation with no [L] argument at all, and with the lift over the given
   cone rather than over a chosen one. *)

Definition comma_CreatesLimit_at : CreatesLimit K comma_proj2 :=
  StrictlyCreatesLimit_CreatesLimit comma_StrictlyCreatesLimit.

End CommaStrictCreate.

(** ** Products, elementarily *)

(* Mac Lane's Theorem 2 consumes the lemma at two shapes only, products and
   equalizers.  The products clause is stated here over
   [Structure/Limit/Product.v]'s [IsIndexedProduct] rather than over a
   discrete shape, and that is a considered choice, not a convenience:
   [Gdiag] identifies the shape's hom and proof universes with [C]'s, and
   [DiscreteCat A]'s hom is an equality in [Prop] which minimizes to [Set],
   so [Gdiag (DiscreteCat_Functor F)] pins BOTH categories to
   [Category@{_ Set Set}].  Test/ProbeCommaCreation438.v's negative n2
   records the refusal ("Cannot enforce Set = ...").  The elementary form
   below is universe-clean over a generic [C] and [D], and it is the form
   Mac Lane's proof actually uses. *)

Section CommaProducts.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context {A : Type}.
Context (F : A → (=(d) ↓ U)).

Definition comma_prod_fam (a : A) : C := comma_proj2 (F a).

Context (p : C).
Context (proj : ∀ a : A, p ~{C}~> comma_prod_fam a).
Context (HP : IsIndexedProduct comma_prod_fam p proj).

(* The per-shape preservation hypothesis at its most elementary: [U] carries
   THIS indexed product to an indexed product. *)
Context (HU : IsIndexedProduct (fun a => U (comma_prod_fam a)) (U p)
                (fun a => fmap[U] (proj a))).

Definition comma_prod_phi : d ~{D}~> U p :=
  unique_obj (iprod_desc HU (fun a => `2 (F a))).

Lemma comma_prod_phi_commutes (a : A) :
  fmap[U] (proj a) ∘ comma_prod_phi ≈ `2 (F a).
Proof using Type.
  exact (unique_property (iprod_desc HU (fun a => `2 (F a))) a).
Qed.

Definition comma_prod_apex : (=(d) ↓ U) := ((ttt, p); comma_prod_phi).

Definition comma_prod_proj (a : A) : comma_prod_apex ~{=(d) ↓ U}~> F a.
Proof using Type.
  unshelve refine ((ttt, proj a); _).
  change (`2 (F a) ∘ id[d] ≈ fmap[U] (proj a) ∘ comma_prod_phi).
  rewrite id_right.
  symmetry.
  exact (comma_prod_phi_commutes a).
Defined.

Definition comma_IsIndexedProduct :
  IsIndexedProduct F comma_prod_apex comma_prod_proj.
Proof using HP HU.
  constructor.
  intros c pi.
  destruct (iprod_desc HP (fun a => snd (`1 (pi a)))) as [w Hw Hwu].
  assert (Hsq : comma_prod_phi ∘ id[d] ≈ fmap[U] w ∘ `2 c).
  { rewrite id_right.
    unfold comma_prod_phi.
    apply (uniqueness (iprod_desc HU (fun a => `2 (F a)))).
    intro a.
    rewrite comp_assoc, <- fmap_comp, (Hw a).
    symmetry.
    exact (comma_square (pi a)). }
  unshelve refine {| unique_obj := ((ttt, w); Hsq) |}.
  - intro a; split.
    + now destruct (fst (`1 (pi a))).
    + exact (Hw a).
  - intros [[u1 u2] Hu] Hv; split.
    + simpl; destruct u1; reflexivity.
    + apply Hwu.
      intro a.
      exact (snd (Hv a)).
Defined.

Definition comma_prod_apex_strict : comma_proj2 comma_prod_apex = p := eq_refl.

Definition comma_prod_leg_strict (a : A) :
  fmap[comma_proj2] (comma_prod_proj a) = proj a := eq_refl.

End CommaProducts.

(** ** Equalizers *)

(* [Structure/Equalizer.v:127] defines [Equalizer F] as [Limit F] for
   [F : Parallel ⟶ C], so this clause is the per-diagram construction read
   at the walking-parallel-pair shape; [Parallel] leaves its hom universe
   free, so unlike the discrete shape it costs nothing. *)

Section CommaEqualizers.

Context {C D : Category}.
Context {U : C ⟶ D}.
Context {d : D}.
Context (K : Parallel ⟶ (=(d) ↓ U)).
Context (HK : PreservesLimitCone (Gdiag K) U).
Context (E : Equalizer (Gdiag K)).

Definition comma_equalizer_at : Equalizer K := comma_limit_at K HK E.

Definition comma_equalizer_apex_strict :
  comma_proj2 (vertex_obj[comma_equalizer_at]) = vertex_obj[E] := eq_refl.

Definition comma_equalizer_leg_strict (j : Parallel) :
  fmap[comma_proj2] (cone_leg comma_equalizer_at j)
    = limit_leg (limit_is_alimit E) j := eq_refl.

Definition comma_StrictlyCreatesEqualizers :
  StrictlyCreatesLimit K comma_proj2 := comma_StrictlyCreatesLimit K HK.

End CommaEqualizers.

(** ** The shape-indexed creation classes *)

(* Under the ALL-SHAPES [PreservesImageLimit] the per-diagram theorem above
   is available at every diagram at once, so [Structure/Limit/Creation.v]'s
   two classes both follow, by the same term.  [comma_CreatesAllLimits] is
   the strongest of the three statements here and the other two are its
   instances: [CreatesAllLimits_CreatesProducts] reads it at
   [J := DiscreteCat A], and [comma_CreatesProducts] is exactly that.

   An earlier revision of this header said reaching the products clause
   through [CreatesProducts] "would import that pin", and that was wrong.
   [Gdiag K] is formable for an abstract [K : DiscreteCat A ⟶ (=(d) ↓ U)],
   because [Compose] unifies the shape's hom universe with [C]'s before
   minimization, and neither class carries [Set] in its block.  What IS
   refused is a functor OUT OF [DiscreteCat A] that eliminates the shape's
   [x = y] into a hom: [DiscreteCat_Functor] (Instance/Discrete.v:59) prints
   as [DiscreteCat@{u Set Set} A ⟶ C], and a hand-rolled eliminator is
   refused with the same "Cannot enforce Set = ..." (probe negative n2),
   even at a concrete base such as [C = D = Sets] with [U = Id].  So the pin
   belongs to the elimination, not to [DiscreteCat], whose hom and proof
   universes are free.  The classes are NOT vacuous: a CONSTANT discrete
   diagram needs no elimination and is formable over a generic [C], with
   [comma_CreatesProducts] applying to it — Test/ProbeCommaCreation438.v
   ships that witness.  The elementary [IsIndexedProduct] clause above is
   kept because it takes the family directly, which is the form Mac Lane's
   Theorem 2 consumes. *)

Definition comma_CreatesAllLimits {C D : Category} {U : C ⟶ D} {d : D}
  (HU : @PreservesImageLimit C D U) :
  @CreatesAllLimits (=(d) ↓ U) C comma_proj2 :=
  fun J K => StrictlyCreatesLimit_CreatesLimit
               (comma_StrictlyCreatesLimit K
                  (fun N HN => HU _ (Gdiag K) (@Build_Limit _ _ (Gdiag K) N HN))).

Definition comma_CreatesProducts {C D : Category} {U : C ⟶ D} {d : D}
  (HU : @PreservesImageLimit C D U) :
  @CreatesProducts (=(d) ↓ U) C comma_proj2 :=
  CreatesAllLimits_CreatesProducts (comma_CreatesAllLimits HU).

(* Mac Lane's own completeness step.  Construction/Comma/Limit.v's
   [Comma_Complete] builds each limit of the comma category directly; the
   book instead observes that the projection CREATES limits and reads
   completeness off that.  Both routes are now available, and this one is
   his — it is [creates_limits_Complete] at [comma_CreatesAllLimits], and it
   costs no [Require] here.  [Comma_Complete]'s exported type is untouched,
   and [Adjunction/GAFT.v] still consumes that one, so nothing downstream
   moves; issue #436's request to route the argument through the creation
   result is answered here rather than by rewriting [GAFT]. *)

Definition comma_Complete_via_creation {C D : Category} {U : C ⟶ D} {d : D}
  (HU : @PreservesImageLimit C D U) (comp : @Complete C) :
  @Complete (=(d) ↓ U) :=
  creates_limits_Complete comma_proj2 comp (comma_CreatesAllLimits HU).

(** ** The three names issue #438's Verification block audits *)

(* That block runs [Print Assumptions] on [comma_creates_products],
   [comma_creates_equalizers] and [comma_proj_creates_limits].  None of the
   three was a name in the tree, and the three statements above carry names
   of their own that say which shape and which strength is meant, so the
   issue's names are given here as aliases with their binders written out —
   the commands then run as the issue writes them.

   An alias can minimize its universes differently from the constant it
   names, and these three do, so the difference is measured rather than
   assumed.  Under [Set Printing Universes] each alias prints with FEWER
   universe variables than its original — [comma_proj_creates_limits] 27
   against [comma_StrictlyCreatesLimit]'s 33, [comma_creates_equalizers] 23
   against [comma_equalizer_at]'s 32, [comma_creates_products] 11 against
   [comma_IsIndexedProduct]'s 16 — because the equations the originals carry
   in their constraint blocks, [u0 = u2] identifying [C]'s hom-and-proof
   universe with [D]'s in all three, with two, four and one more besides, are
   solved
   into the aliases' binders instead: every alias binder reads
   [C : Category@{_ h h}] and [D : Category@{_ h h}] with ONE [h], and no
   alias block carries an equation at all.  No block on either side mentions
   [Set].  That each alias IS the constant it names, and not merely an
   inhabitant of the same type, is pinned by three [eq_refl] readbacks in
   Test/ProbeCommaCreation438.v. *)

Definition comma_proj_creates_limits {C D : Category} {U : C ⟶ D} {d : D}
  {J : Category} (K : J ⟶ (=(d) ↓ U))
  (HK : PreservesLimitCone (Gdiag K) U) :
  StrictlyCreatesLimit K comma_proj2 := comma_StrictlyCreatesLimit K HK.

Definition comma_creates_equalizers {C D : Category} {U : C ⟶ D} {d : D}
  (K : Parallel ⟶ (=(d) ↓ U)) (HK : PreservesLimitCone (Gdiag K) U)
  (E : Equalizer (Gdiag K)) : Equalizer K := comma_equalizer_at K HK E.

Definition comma_creates_products {C D : Category} {U : C ⟶ D} {d : D}
  {A : Type} (F : A → (=(d) ↓ U)) (p : C)
  (proj : ∀ a : A, p ~{C}~> comma_prod_fam F a)
  (HP : IsIndexedProduct (comma_prod_fam F) p proj)
  (HU : IsIndexedProduct (fun a => U (comma_prod_fam F a)) (U p)
          (fun a => fmap[U] (proj a))) :
  IsIndexedProduct F (comma_prod_apex F p proj HU) (comma_prod_proj F p proj HU)
  := comma_IsIndexedProduct F p proj HP HU.
