Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Instance.Fun.
Require Import Category.Monad.Adjunction.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Monad.Comparison.
Require Import Category.Monad.Monadicity.BeckObjects.
Require Import Category.Monad.Monadicity.Crude.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Limit.Preservation.

Generalizable All Variables.

(** * Beck's monadicity theorem, precise form

    nLab:      https://ncatlab.org/nlab/show/monadicity+theorem
    Wikipedia: https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem

    Fix an adjunction F ⊣ U with F : D ⟶ C, its induced monad T = U ◯ F
    on D ([Adjunction_Induced_Monad], Monad/Comparison.v, with ret = η
    and join = U ε F held transparent), and the Eilenberg–Moore
    comparison K = [EM_Comparison] : C ⟶ D^T.  Beck's precise monadicity
    theorem singles out the monadic adjunctions: K is an equivalence of
    categories whenever U creates coequalizers of U-split pairs —
    parallel pairs in C whose U-image carries a split coequalizer in D
    (Structure/Coequalizer/Split.v).

    ** Creation, in the isomorphism-invariant sense

    [CreatesUSplitCoequalizers] renders "U creates coequalizers of
    U-split pairs" in two clauses:

    - [create_coeq] (existence): every U-split pair has a coequalizer
      upstairs whose U-image agrees with the given split coequalizer up
      to a packaged comparison isomorphism i with i ∘ U e ≈ scoeq_e;

    - [create_coeq_reflects] (uniqueness): every cofork upstairs that
      lies over the given split coequalizer, up to such a compatible
      isomorphism, is itself a coequalizer upstairs.

    The second clause is the uniqueness half of creation, phrased in the
    strongest form the theorem can consume.  Mac Lane's strict definition
    demands a unique on-the-nose lift of the colimiting cocone and that
    this lift be colimiting; in a setoid-based library, where downstairs
    data can only be matched up to isomorphism, the non-evil rendering
    asks instead that every iso-compatible lift be colimiting.  The
    customary reading "the created data are unique up to compatible
    isomorphism" follows as the corollary [create_coeq_unique], because
    any two such lifts are coequalizers of the same pair and so mediate
    through each other (compare [coequalizer_unique]).

    ** Conservativity is derived, not assumed

    Classical statements of the precise theorem carry no separate
    conservativity hypothesis, and none is needed here: creation of
    U-split coequalizers already makes U reflect isomorphisms
    ([creates_split_reflects_isos]).  If U h is invertible, then the
    U-image of the identical pair (id, id) is split-coequalized by U h
    itself, with section (U h)⁻¹; the reflection clause then exhibits h
    as a coequalizer of (id, id) upstairs, and descending id through it
    produces a two-sided inverse of h.  Consequently [beck_monadicity]
    takes only the adjunction and the creation instance — the
    [ReflectsIsos] input of the crude theorem (Monadicity/Crude.v) is
    manufactured, not assumed.

    ** The theorem

    [beck_monadicity] instantiates the crude architecture with created
    rather than chosen coequalizers.  For an algebra (d, α), the
    canonical presentation ε_{F d}, F α upstairs has as its U-image the
    canonical pair μ_d, T α, which is split-coequalized by α itself
    ([canonical_split], Monadicity/BeckObjects.v) — definitionally so,
    because the induced monad's join transparently reads U ε F.
    [create_coeq] at this splitting provides the quasi-inverse G on
    objects, and the downstairs coequalizer that drives every comparison
    map is recovered by transporting the split coequalizer along the
    packaged isomorphism ([coequalizer_along_iso]) instead of by the
    crude preservation hypothesis.  From there the lemma stack of
    Crude.v repeats with the same proofs; its generically stated pieces
    ([crude_pair_l], [crude_pair_r], [crude_alg_unit],
    [crude_hom_square], [crude_alpha_cofork], [crude_unit_alpha],
    [crude_unit_cofork], and the naturality lemmas of
    Monad/Comparison.v) are reused directly.

    ** The converse

    [monadic_creates] packages [em_forget_creates_split]
    (Monadicity/BeckObjects.v) into the class: for any monad T, the
    Eilenberg–Moore forgetful functor U^T = [EM_Forget] creates
    coequalizers of U^T-split pairs.  The existence clause is the
    created algebra with the identity comparison isomorphism; the
    reflection clause descends through the split coequalizer downstairs
    and cancels the split epimorphism T e₀ to check that the descended
    arrow is again an algebra homomorphism.  Transporting this converse
    along the equivalence K, so that an arbitrary functor U that has a
    left adjoint with invertible comparison inherits the creation
    property (closing the loop to a single "monadic iff creates"
    equivalence), is deliberately left to a later development: the
    Eilenberg–Moore statement is the mathematical core, and the
    transport is pure plumbing along [EquivalenceOfCategories]. *)

(** ** Transport of an elementary coequalizer along an isomorphism

    If e is a coequalizer of f, g at q and an isomorphism i : q' ≅ q
    carries a map e' onto e (to i ∘ e' ≈ e), then e' is a coequalizer of
    the same pair at q'.  This is the glue between a created
    coequalizer's packaged comparison isomorphism and the elementary
    universal property consumed by the Beck argument. *)

Lemma coequalizer_along_iso {C : Category} {x y : C} (f g : x ~> y)
  {q q' : C} (e : y ~> q) (E : IsCoequalizer f g q e)
  (i : q' ≅ q) (e' : y ~> q') (Hi : to i ∘ e' ≈ e) :
  IsCoequalizer f g q' e'.
Proof.
  assert (He' : e' ≈ from i ∘ e).
  { rewrite <- Hi.
    rewrite comp_assoc.
    rewrite (iso_from_to i).
    now rewrite id_left. }
  unshelve refine {| cofork := _ ; coeq_desc := _ |}.
  - (* e' coforks the pair, since e does and i is monic *)
    rewrite He'.
    rewrite <- !comp_assoc.
    now rewrite (cofork E).
  - intros z h Hh.
    unshelve eapply Build_Unique.
    + (* descend through e, then precompose the comparison *)
      exact (unique_obj (coeq_desc E h Hh) ∘ to i).
    + rewrite <- comp_assoc.
      rewrite Hi.
      exact (unique_property (coeq_desc E h Hh)).
    + (* uniqueness: conjugate a competitor back through the iso *)
      intros v Hv.
      assert (Hv' : (v ∘ from i) ∘ e ≈ h).
      { rewrite <- comp_assoc.
        rewrite <- He'.
        exact Hv. }
      rewrite (uniqueness (coeq_desc E h Hh) (v ∘ from i) Hv').
      rewrite <- comp_assoc.
      rewrite (iso_from_to i).
      now rewrite id_right.
Defined.

(** ** Creation of coequalizers of U-split pairs

    The two clauses are discussed in the header: [create_coeq] lifts the
    split coequalizer to a coequalizer upstairs, with the agreement of
    the U-image packaged as a comparison isomorphism; and
    [create_coeq_reflects] — the uniqueness clause, in its strongest
    consumable form — recognizes every iso-compatible lift as a
    coequalizer upstairs. *)

Class CreatesUSplitCoequalizers {C D : Category} (U : C ⟶ D) := {
  create_coeq {x y : C} (f g : x ~> y)
    (S : SplitCoequalizer (fmap[U] f) (fmap[U] g)) :
    ∃ (q : C) (e : y ~> q),
      IsCoequalizer f g q e ∧
      (∃ i : @Isomorphism D (U q) (scoeq_obj S),
         to i ∘ fmap[U] e ≈ scoeq_e S);

  create_coeq_reflects {x y : C} (f g : x ~> y)
    (S : SplitCoequalizer (fmap[U] f) (fmap[U] g))
    (q : C) (e : y ~> q)
    (He : e ∘ f ≈ e ∘ g)
    (i : @Isomorphism D (U q) (scoeq_obj S))
    (Hi : to i ∘ fmap[U] e ≈ scoeq_e S) :
    IsCoequalizer f g q e
}.

(** Uniqueness of created data, in the customary form: any two
    iso-compatible lifts of the same split coequalizer are isomorphic,
    compatibly with the coequalizing maps.  Both lifts are coequalizers
    of the pair by the reflection clause, so each descends the other and
    the round trips descend the identity. *)

Corollary create_coeq_unique {C D : Category} {U : C ⟶ D}
  (CR : CreatesUSplitCoequalizers U) {x y : C} (f g : x ~> y)
  (S : SplitCoequalizer (fmap[U] f) (fmap[U] g))
  {q1 q2 : C} (e1 : y ~> q1) (e2 : y ~> q2)
  (He1 : e1 ∘ f ≈ e1 ∘ g) (He2 : e2 ∘ f ≈ e2 ∘ g)
  (i1 : @Isomorphism D (U q1) (scoeq_obj S))
  (Hi1 : to i1 ∘ fmap[U] e1 ≈ scoeq_e S)
  (i2 : @Isomorphism D (U q2) (scoeq_obj S))
  (Hi2 : to i2 ∘ fmap[U] e2 ≈ scoeq_e S) :
  ∃ j : q1 ≅ q2, to j ∘ e1 ≈ e2.
Proof.
  pose proof (@create_coeq_reflects C D U CR x y f g S q1 e1 He1 i1 Hi1)
    as E1.
  pose proof (@create_coeq_reflects C D U CR x y f g S q2 e2 He2 i2 Hi2)
    as E2.
  unshelve eexists.
  - unshelve refine
      {| to   := unique_obj (coeq_desc E1 e2 (cofork E2))
       ; from := unique_obj (coeq_desc E2 e1 (cofork E1)) |}.
    + (* to ∘ from ≈ id, by descent uniqueness over e2 *)
      transitivity (unique_obj (coeq_desc E2 e2 (cofork E2))).
      * symmetry.
        apply (uniqueness (coeq_desc E2 e2 (cofork E2))).
        rewrite <- comp_assoc.
        rewrite (unique_property (coeq_desc E2 e1 (cofork E1))).
        exact (unique_property (coeq_desc E1 e2 (cofork E2))).
      * apply (uniqueness (coeq_desc E2 e2 (cofork E2))).
        apply id_left.
    + (* from ∘ to ≈ id, by descent uniqueness over e1 *)
      transitivity (unique_obj (coeq_desc E1 e1 (cofork E1))).
      * symmetry.
        apply (uniqueness (coeq_desc E1 e1 (cofork E1))).
        rewrite <- comp_assoc.
        rewrite (unique_property (coeq_desc E1 e2 (cofork E2))).
        exact (unique_property (coeq_desc E2 e1 (cofork E1))).
      * apply (uniqueness (coeq_desc E1 e1 (cofork E1))).
        apply id_left.
  - exact (unique_property (coeq_desc E1 e2 (cofork E2))).
Qed.

(** ** Creation makes U conservative

    The splitting used below: when U h is invertible, U h itself
    split-coequalizes the U-image of the identical pair (id, id) — the
    section of e := U h is (U h)⁻¹ and the section of the first leg is
    the identity.  Kept transparent so that its coequalizing map is
    U h on the nose for the reflection clause. *)

Definition iso_identical_split {C D : Category} (U : C ⟶ D)
  {x y : C} (h : x ~> y) (I : IsIsomorphism (fmap[U] h)) :
  SplitCoequalizer (fmap[U] (@id C x)) (fmap[U] (@id C x)).
Proof.
  unshelve refine
    {| scoeq_obj := U y
     ; scoeq_e   := fmap[U] h
     ; scoeq_s   := @two_sided_inverse D _ _ _ I
     ; scoeq_t   := id |}.
  - (* law 1: both legs are U id *)
    reflexivity.
  - (* law 2: the inverse splits U h *)
    exact (@is_right_inverse D _ _ _ I).
  - (* law 3: the identity splits U id *)
    rewrite fmap_id.
    apply id_left.
  - (* law 4: U id ∘ id ≈ (U h)⁻¹ ∘ U h, both sides being id *)
    rewrite fmap_id.
    rewrite id_left.
    symmetry.
    exact (@is_left_inverse D _ _ _ I).
Defined.

(** A functor that creates coequalizers of U-split pairs reflects
    isomorphisms.  Given h with U h invertible, the reflection clause at
    [iso_identical_split] recognizes h as a coequalizer of (id, id);
    descending id through it yields the inverse, whose other triangle is
    epi-cancellation of h. *)

Lemma creates_split_reflects_isos {C D : Category} (U : C ⟶ D)
  (CR : CreatesUSplitCoequalizers U) : ReflectsIsos U.
Proof.
  constructor.
  intros x y h I.
  assert (He : h ∘ @id C x ≈ h ∘ @id C x) by reflexivity.
  assert (Hi : to (@iso_id D (U y)) ∘ fmap[U] h
                 ≈ scoeq_e (iso_identical_split U h I)).
  { simpl.
    apply id_left. }
  pose proof (@create_coeq_reflects C D U CR x x (@id C x) (@id C x)
                (iso_identical_split U h I) y h He iso_id Hi) as E.
  assert (Hfork : @id C x ∘ @id C x ≈ @id C x ∘ @id C x) by reflexivity.
  pose proof (coeq_desc E (@id C x) Hfork) as d.
  unshelve refine {| two_sided_inverse := unique_obj d |}.
  - (* h ∘ h⁻¹ ≈ id: cancel the epimorphism h *)
    apply (@epic _ _ _ _ (coequalizer_epic _ _ E)).
    rewrite <- comp_assoc.
    rewrite (unique_property d).
    rewrite id_right.
    now rewrite id_left.
  - (* h⁻¹ ∘ h ≈ id: the descent triangle itself *)
    exact (unique_property d).
Qed.

Section BeckMonadicity.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).
Context (CR : CreatesUSplitCoequalizers U).

Local Notation HM := (Adjunction_Induced_Monad A).
Local Notation EM := (@EilenbergMoore D (U ◯ F) HM).
Local Notation K := (EM_Comparison A).

(** Conservativity of U, manufactured from the creation instance. *)

Definition beck_reflects : ReflectsIsos U :=
  creates_split_reflects_isos U CR.

(** ** The canonical presentation and its splitting downstairs

    For an algebra x = (d, α), the presentation pair upstairs is
    ε_{F d}, F α ([crude_pair_l]/[crude_pair_r] of Monadicity/Crude.v).
    Its U-image is definitionally the canonical pair μ_d, T α of the
    algebra — the induced monad's join reads U ε F transparently — and
    that pair is split-coequalized by α itself: [canonical_split] of
    Monadicity/BeckObjects.v is exactly the U-splitting that the
    creation instance consumes. *)

Definition beck_split (x : EM) :
  SplitCoequalizer (fmap[U] (crude_pair_l A x))
                   (fmap[U] (crude_pair_r A x)) :=
  @canonical_split D (U ◯ F) HM (`1 x) (`2 x).

(** ** The quasi-inverse on objects: the created coequalizer *)

Definition beck_coeq (x : EM) :
  ∃ (q : C) (e : F (`1 x) ~{C}~> q),
    IsCoequalizer (crude_pair_l A x) (crude_pair_r A x) q e ∧
    (∃ i : @Isomorphism D (U q) (`1 x),
       to i ∘ fmap[U] e ≈ t_alg[`2 x]) :=
  @create_coeq C D U CR _ _ (crude_pair_l A x) (crude_pair_r A x)
    (beck_split x).

Definition beck_G_obj (x : EM) : C := `1 (beck_coeq x).

Definition beck_e (x : EM) : F (`1 x) ~{C}~> beck_G_obj x :=
  `1 (`2 (beck_coeq x)).

Definition beck_is_coeq (x : EM) :
  IsCoequalizer (crude_pair_l A x) (crude_pair_r A x)
    (beck_G_obj x) (beck_e x) :=
  fst (`2 (`2 (beck_coeq x))).

(* The packaged comparison isomorphism of the created coequalizer, and
   its compatibility triangle with the canonical splitting. *)
Definition beck_iso (x : EM) :
  @Isomorphism D (U (beck_G_obj x)) (`1 x) :=
  `1 (snd (`2 (`2 (beck_coeq x)))).

Definition beck_iso_e (x : EM) :
  to (beck_iso x) ∘ fmap[U] (beck_e x) ≈ t_alg[`2 x] :=
  `2 (snd (`2 (`2 (beck_coeq x)))).

(* The cofork law of the created coequalizer, in unfolded form. *)
Lemma beck_cofork (x : EM) :
  beck_e x ∘ @counit _ _ _ _ A (F (`1 x))
    ≈ beck_e x ∘ fmap[F] (t_alg[`2 x]).
Proof. exact (cofork (beck_is_coeq x)). Qed.

Definition beck_e_epic (x : EM) : Epic (beck_e x) :=
  coequalizer_epic _ _ (beck_is_coeq x).

(** ** The quasi-inverse on morphisms: descent

    Identical to the crude development, with the created coequalizer in
    place of the chosen one; the commuting square of a homomorphism is
    the reused [crude_hom_square]. *)

Lemma beck_G_map_cofork {x y : EM} (h : x ~{EM}~> y) :
  (beck_e y ∘ fmap[F] (t_alg_hom[h])) ∘ @counit _ _ _ _ A (F (`1 x))
    ≈ (beck_e y ∘ fmap[F] (t_alg_hom[h])) ∘ fmap[F] (t_alg[`2 x]).
Proof.
  rewrite <- (comp_assoc (beck_e y) (fmap[F] (t_alg_hom[h]))
                (@counit _ _ _ _ A (F (`1 x)))).
  rewrite <- (comp_assoc (beck_e y) (fmap[F] (t_alg_hom[h]))
                (fmap[F] (t_alg[`2 x]))).
  rewrite <- (adj_counit_natural A (fmap[F] (t_alg_hom[h]))).
  rewrite (comp_assoc (beck_e y) (@counit _ _ _ _ A (F (`1 y)))
             (fmap[F] (fmap[U] (fmap[F] (t_alg_hom[h]))))).
  rewrite (beck_cofork y).
  rewrite <- (comp_assoc (beck_e y) (fmap[F] (t_alg[`2 y]))
                (fmap[F] (fmap[U] (fmap[F] (t_alg_hom[h]))))).
  rewrite <- (@fmap_comp D C F _ _ _ (t_alg[`2 y])
                (fmap[U] (fmap[F] (t_alg_hom[h])))).
  rewrite <- (crude_hom_square A h).
  rewrite (@fmap_comp D C F _ _ _ (t_alg_hom[h]) (t_alg[`2 x])).
  reflexivity.
Qed.

Definition beck_G_desc {x y : EM} (h : x ~{EM}~> y) :
  ∃! u : beck_G_obj x ~{C}~> beck_G_obj y,
    u ∘ beck_e x ≈ beck_e y ∘ fmap[F] (t_alg_hom[h]) :=
  coeq_desc (beck_is_coeq x) (beck_e y ∘ fmap[F] (t_alg_hom[h]))
    (beck_G_map_cofork h).

Definition beck_G_map {x y : EM} (h : x ~{EM}~> y) :
  beck_G_obj x ~{C}~> beck_G_obj y :=
  unique_obj (beck_G_desc h).

Definition beck_G_map_commutes {x y : EM} (h : x ~{EM}~> y) :
  beck_G_map h ∘ beck_e x ≈ beck_e y ∘ fmap[F] (t_alg_hom[h]) :=
  unique_property (beck_G_desc h).

(** Functoriality of the descent, by descent uniqueness. *)

Lemma beck_G_map_respects {x y : EM} (h k : x ~{EM}~> y) (E : h ≈ k) :
  beck_G_map h ≈ beck_G_map k.
Proof.
  apply (uniqueness (beck_G_desc h)).
  rewrite (beck_G_map_commutes k).
  apply compose_respects.
  - reflexivity.
  - apply fmap_respects.
    symmetry.
    exact E.
Qed.

Lemma beck_G_map_id (x : EM) : beck_G_map (@id EM x) ≈ id.
Proof.
  apply (uniqueness (beck_G_desc (@id EM x))).
  change (id ∘ beck_e x ≈ beck_e x ∘ fmap[F] (@id D (`1 x))).
  rewrite fmap_id.
  rewrite id_left.
  now rewrite id_right.
Qed.

Lemma beck_G_map_comp {x y z : EM}
  (h : y ~{EM}~> z) (k : x ~{EM}~> y) :
  beck_G_map (h ∘ k) ≈ beck_G_map h ∘ beck_G_map k.
Proof.
  apply (uniqueness (beck_G_desc (h ∘ k))).
  rewrite <- (comp_assoc (beck_G_map h) (beck_G_map k) (beck_e x)).
  rewrite (beck_G_map_commutes k).
  rewrite (comp_assoc (beck_G_map h) (beck_e y)
             (fmap[F] (t_alg_hom[k]))).
  rewrite (beck_G_map_commutes h).
  rewrite <- (comp_assoc (beck_e z) (fmap[F] (t_alg_hom[h]))
                (fmap[F] (t_alg_hom[k]))).
  rewrite <- (@fmap_comp D C F _ _ _ (t_alg_hom[h]) (t_alg_hom[k])).
  reflexivity.
Qed.

(** The quasi-inverse functor G : D^T ⟶ C. *)

Definition Beck_Inverse : EM ⟶ C :=
  @Build_Functor EM C
    beck_G_obj
    (fun x y h => beck_G_map h)
    (fun x y h k E => beck_G_map_respects h k E)
    (fun x => beck_G_map_id x)
    (fun x y z h k => beck_G_map_comp h k).

(** ** Downstairs: the U-image coequalizer, by transport

    Where the crude proof invoked preservation, the created coequalizer
    carries its own downstairs comparison: transporting the canonical
    splitting along the packaged isomorphism exhibits U (G (d, α)) as a
    coequalizer of the pair U ε_{F d}, U (F α), coequalized by U e. *)

Definition beck_U_coeq (x : EM) :
  IsCoequalizer
    (fmap[U] (@counit _ _ _ _ A (F (`1 x))))
    (fmap[U] (fmap[F] (t_alg[`2 x])))
    (U (beck_G_obj x)) (fmap[U] (beck_e x)) :=
  coequalizer_along_iso
    (fmap[U] (crude_pair_l A x)) (fmap[U] (crude_pair_r A x))
    (t_alg[`2 x])
    (split_coequalizer_is_coequalizer _ _ (beck_split x))
    (beck_iso x) (fmap[U] (beck_e x)) (beck_iso_e x).

Definition beck_Ue_epic (x : EM) : Epic (fmap[U] (beck_e x)) :=
  coequalizer_epic _ _ (beck_U_coeq x).

(* The comparison map U (G (d, α)) ~> d: descend α through U e.  The
   cofork hypothesis is the reused [crude_alpha_cofork] — the algebra
   action law, reversed. *)
Definition beck_to_desc (x : EM) :
  ∃! u : U (beck_G_obj x) ~{D}~> `1 x,
    u ∘ fmap[U] (beck_e x) ≈ t_alg[`2 x] :=
  coeq_desc (beck_U_coeq x) (t_alg[`2 x]) (crude_alpha_cofork A x).

Definition beck_to (x : EM) : U (beck_G_obj x) ~{D}~> `1 x :=
  unique_obj (beck_to_desc x).

Definition beck_to_e (x : EM) :
  beck_to x ∘ fmap[U] (beck_e x) ≈ t_alg[`2 x] :=
  unique_property (beck_to_desc x).

(* The inverse comparison d ~> U (G (d, α)): the split coequalizer's
   descent of U e through α, i.e. U e ∘ η_d. *)
Definition beck_from (x : EM) : `1 x ~{D}~> U (beck_G_obj x) :=
  fmap[U] (beck_e x) ∘ @unit _ _ _ _ A (`1 x).

(* Restricting [beck_from] along α recovers U e: slide η across α by
   naturality ([crude_unit_alpha]), trade U (F α) for U ε under U e (the
   U-image of the cofork law), and close with the zig-zag identity. *)
Lemma beck_from_alpha (x : EM) :
  beck_from x ∘ t_alg[`2 x] ≈ fmap[U] (beck_e x).
Proof.
  unfold beck_from.
  rewrite <- (comp_assoc (fmap[U] (beck_e x))
                (@unit _ _ _ _ A (`1 x)) (t_alg[`2 x])).
  rewrite (crude_unit_alpha A x).
  rewrite (comp_assoc (fmap[U] (beck_e x))
             (fmap[U] (fmap[F] (t_alg[`2 x])))
             (@unit _ _ _ _ A (U (F (`1 x))))).
  rewrite <- (@fmap_comp C D U _ _ _ (beck_e x)
                (fmap[F] (t_alg[`2 x]))).
  rewrite <- (beck_cofork x).
  rewrite (@fmap_comp C D U _ _ _ (beck_e x)
             (@counit _ _ _ _ A (F (`1 x)))).
  rewrite <- (comp_assoc (fmap[U] (beck_e x))
                (fmap[U] (@counit _ _ _ _ A (F (`1 x))))
                (@unit _ _ _ _ A (U (F (`1 x))))).
  rewrite (@fmap_counit_unit _ _ _ _ A (F (`1 x))).
  now rewrite id_right.
Qed.

(** The two comparisons are mutually inverse. *)

Lemma beck_to_from (x : EM) : beck_to x ∘ beck_from x ≈ id.
Proof.
  unfold beck_from.
  rewrite (comp_assoc (beck_to x) (fmap[U] (beck_e x))
             (@unit _ _ _ _ A (`1 x))).
  rewrite (beck_to_e x).
  exact (crude_alg_unit A x).
Qed.

Lemma beck_from_to (x : EM) : beck_from x ∘ beck_to x ≈ id.
Proof.
  apply (@epic _ _ _ _ (beck_Ue_epic x)).
  rewrite <- (comp_assoc (beck_from x) (beck_to x)
                (fmap[U] (beck_e x))).
  rewrite (beck_to_e x).
  rewrite (beck_from_alpha x).
  now rewrite id_left.
Qed.

(** ** The counit of the equivalence: K (G (d, α)) ≅ (d, α) in D^T *)

Lemma beck_from_commutes (x : EM) :
  beck_from x ∘ t_alg[`2 x]
    ≈ fmap[U] (@counit _ _ _ _ A (beck_G_obj x))
        ∘ fmap[U] (fmap[F] (beck_from x)).
Proof.
  rewrite (beck_from_alpha x).
  unfold beck_from.
  rewrite (@fmap_comp D C F _ _ _ (fmap[U] (beck_e x))
             (@unit _ _ _ _ A (`1 x))).
  rewrite (@fmap_comp C D U _ _ _ (fmap[F] (fmap[U] (beck_e x)))
             (fmap[F] (@unit _ _ _ _ A (`1 x)))).
  rewrite (comp_assoc (fmap[U] (@counit _ _ _ _ A (beck_G_obj x)))
             (fmap[U] (fmap[F] (fmap[U] (beck_e x))))
             (fmap[U] (fmap[F] (@unit _ _ _ _ A (`1 x))))).
  rewrite <- (@fmap_comp C D U _ _ _
                (@counit _ _ _ _ A (beck_G_obj x))
                (fmap[F] (fmap[U] (beck_e x)))).
  rewrite (adj_counit_natural A (beck_e x)).
  rewrite (@fmap_comp C D U _ _ _ (beck_e x)
             (@counit _ _ _ _ A (F (`1 x)))).
  rewrite <- (comp_assoc (fmap[U] (beck_e x))
                (fmap[U] (@counit _ _ _ _ A (F (`1 x))))
                (fmap[U] (fmap[F] (@unit _ _ _ _ A (`1 x))))).
  rewrite <- (@fmap_comp C D U _ _ _
                (@counit _ _ _ _ A (F (`1 x)))
                (fmap[F] (@unit _ _ _ _ A (`1 x)))).
  rewrite (@counit_fmap_unit _ _ _ _ A (`1 x)).
  rewrite fmap_id.
  now rewrite id_right.
Qed.

(* The homomorphism (d, α) ~> K (G (d, α)) carried by [beck_from]. *)
Definition beck_counit_hom_inv (x : EM) :
  x ~{EM}~> K (beck_G_obj x) :=
  @Build_TAlgebraHom D (U ◯ F) HM (`1 x) (U (beck_G_obj x))
    (`2 x) (EM_Comparison_Algebra A (beck_G_obj x))
    (beck_from x) (beck_from_commutes x).

(* Its carrier is invertible, transparently. *)
Definition beck_from_is_iso (x : EM) : IsIsomorphism (beck_from x) :=
  {| two_sided_inverse := beck_to x
   ; is_right_inverse  := beck_from_to x
   ; is_left_inverse   := beck_to_from x |}.

(* The inverse homomorphism K (G (d, α)) ~> (d, α), by the conjugation
   argument [em_iso_inverse_hom] of BeckObjects.v — conservativity of
   U^T, kept transparent so its carrier is [beck_to] on the nose. *)
Definition beck_counit_hom (x : EM) :
  K (beck_G_obj x) ~{EM}~> x :=
  @em_iso_inverse_hom D (U ◯ F) HM x (K (beck_G_obj x))
    (beck_counit_hom_inv x) (beck_from_is_iso x).

Definition beck_counit_component (x : EM) :
  @Isomorphism EM (K (beck_G_obj x)) x :=
  @Build_Isomorphism EM (K (beck_G_obj x)) x
    (beck_counit_hom x) (beck_counit_hom_inv x)
    (beck_to_from x) (beck_from_to x).

(* Conjugation coherence of the counit cell, on carriers: cancel the
   epimorphism U e, contract the two descent triangles, and close with
   the commuting square of h. *)
Lemma beck_counit_coherence {x y : EM} (h : x ~{EM}~> y) :
  fmap[U] (beck_G_map h)
    ≈ (beck_from y ∘ t_alg_hom[h]) ∘ beck_to x.
Proof.
  apply (@epic _ _ _ _ (beck_Ue_epic x)).
  rewrite <- (comp_assoc (beck_from y ∘ t_alg_hom[h]) (beck_to x)
                (fmap[U] (beck_e x))).
  rewrite (beck_to_e x).
  rewrite <- (comp_assoc (beck_from y) (t_alg_hom[h]) (t_alg[`2 x])).
  rewrite (crude_hom_square A h).
  rewrite (comp_assoc (beck_from y) (t_alg[`2 y])
             (fmap[U] (fmap[F] (t_alg_hom[h])))).
  rewrite (beck_from_alpha y).
  rewrite <- (@fmap_comp C D U _ _ _ (beck_G_map h) (beck_e x)).
  rewrite <- (@fmap_comp C D U _ _ _ (beck_e y)
                (fmap[F] (t_alg_hom[h]))).
  rewrite (beck_G_map_commutes h).
  reflexivity.
Qed.

Definition beck_equivalence_counit : K ◯ Beck_Inverse ≈ Id[EM].
Proof.
  exists (fun x => beck_counit_component x).
  intros x y h.
  exact (beck_counit_coherence h).
Defined.

(** ** The unit of the equivalence: c ≅ G (K c) in C

    The counit ε_c coforks the presentation of the comparison algebra
    K c = (U c, U ε_c) — the reused [crude_unit_cofork] — and therefore
    descends to a mediator θ_c out of the created coequalizer G (K c). *)

Definition beck_unit_desc (c : C) :
  ∃! u : beck_G_obj (K c) ~{C}~> c,
    u ∘ beck_e (K c) ≈ @counit _ _ _ _ A c :=
  coeq_desc (beck_is_coeq (K c)) (@counit _ _ _ _ A c)
    (crude_unit_cofork A c).

Definition beck_theta (c : C) : beck_G_obj (K c) ~{C}~> c :=
  unique_obj (beck_unit_desc c).

Definition beck_theta_e (c : C) :
  beck_theta c ∘ beck_e (K c) ≈ @counit _ _ _ _ A c :=
  unique_property (beck_unit_desc c).

(* Downstairs, U θ_c is the comparison map of the algebra K c: both
   descend U ε_c through U e, so the epimorphism U e identifies them. *)
Lemma beck_U_theta (c : C) :
  fmap[U] (beck_theta c) ≈ beck_to (K c).
Proof.
  apply (@epic _ _ _ _ (beck_Ue_epic (K c))).
  rewrite (beck_to_e (K c)).
  rewrite <- (@fmap_comp C D U _ _ _ (beck_theta c) (beck_e (K c))).
  rewrite (beck_theta_e c).
  reflexivity.
Qed.

Lemma beck_U_theta_from (c : C) :
  fmap[U] (beck_theta c) ∘ beck_from (K c) ≈ id.
Proof.
  rewrite (beck_U_theta c).
  exact (beck_to_from (K c)).
Qed.

Lemma beck_from_U_theta (c : C) :
  beck_from (K c) ∘ fmap[U] (beck_theta c) ≈ id.
Proof.
  rewrite (beck_U_theta c).
  exact (beck_from_to (K c)).
Qed.

Definition beck_theta_U_iso (c : C) :
  IsIsomorphism (fmap[U] (beck_theta c)) :=
  {| two_sided_inverse := beck_from (K c)
   ; is_right_inverse  := beck_U_theta_from c
   ; is_left_inverse   := beck_from_U_theta c |}.

(* The derived conservativity reflects the invertibility upstairs. *)
Definition beck_theta_iso (c : C) : IsIsomorphism (beck_theta c) :=
  @reflects_iso C D U beck_reflects _ _ (beck_theta c)
    (beck_theta_U_iso c).

Definition beck_theta_inv (c : C) : c ~{C}~> beck_G_obj (K c) :=
  @two_sided_inverse C _ _ (beck_theta c) (beck_theta_iso c).

Lemma beck_theta_theta_inv (c : C) :
  beck_theta c ∘ beck_theta_inv c ≈ id.
Proof.
  exact (@is_right_inverse C _ _ (beck_theta c) (beck_theta_iso c)).
Qed.

Definition beck_unit_component (c : C) : c ≅ beck_G_obj (K c) :=
  @Build_Isomorphism C c (beck_G_obj (K c))
    (beck_theta_inv c) (beck_theta c)
    (@is_left_inverse C _ _ (beck_theta c) (beck_theta_iso c))
    (@is_right_inverse C _ _ (beck_theta c) (beck_theta_iso c)).

(* Naturality of θ: cancel the epimorphism e, contract the descent
   triangles of θ and of G (K f), and finish by counit naturality. *)
Lemma beck_theta_natural {x y : C} (f : x ~{C}~> y) :
  f ∘ beck_theta x ≈ beck_theta y ∘ beck_G_map (fmap[K] f).
Proof.
  apply (@epic _ _ _ _ (beck_e_epic (K x))).
  rewrite <- (comp_assoc f (beck_theta x) (beck_e (K x))).
  rewrite (beck_theta_e x).
  rewrite <- (comp_assoc (beck_theta y) (beck_G_map (fmap[K] f))
                (beck_e (K x))).
  rewrite (beck_G_map_commutes (fmap[K] f)).
  rewrite (comp_assoc (beck_theta y) (beck_e (K y))
             (fmap[F] (t_alg_hom[fmap[K] f]))).
  rewrite (beck_theta_e y).
  symmetry.
  exact (adj_counit_natural A f).
Qed.

(* Conjugation coherence of the unit cell. *)
Lemma beck_unit_coherence {x y : C} (f : x ~{C}~> y) :
  f ≈ (beck_theta y ∘ beck_G_map (fmap[K] f)) ∘ beck_theta_inv x.
Proof.
  rewrite <- (beck_theta_natural f).
  rewrite <- (comp_assoc f (beck_theta x) (beck_theta_inv x)).
  rewrite (beck_theta_theta_inv x).
  now rewrite id_right.
Qed.

Definition beck_equivalence_unit : Id[C] ≈ Beck_Inverse ◯ K.
Proof.
  exists (fun c => beck_unit_component c).
  intros x y f.
  exact (beck_unit_coherence f).
Defined.

(** ** Beck's precise monadicity theorem

    No conservativity hypothesis appears: it is derived from creation
    by [creates_split_reflects_isos], as in the classical statement. *)

Definition beck_monadicity : EquivalenceOfCategories (EM_Comparison A) :=
  {| quasi_inverse      := Beck_Inverse
   ; equivalence_counit := beck_equivalence_counit
   ; equivalence_unit   := beck_equivalence_unit |}.

End BeckMonadicity.

(** * The converse: the Eilenberg–Moore forgetful functor creates

    [em_forget_creates_split] of Monadicity/BeckObjects.v, repackaged
    into the class.  The existence clause returns the created algebra
    with the identity comparison isomorphism.  The reflection clause is
    proved directly: a cofork of algebras lying over the splitting up to
    a compatible isomorphism i descends downstairs through the split
    coequalizer, the descended arrow is conjugated back through i, its
    homomorphism square follows by cancelling the split epimorphism
    T e₀, and descent uniqueness downstairs pins the mediator. *)

Section MonadicCreates.

Context {D : Category}.
Context (T : D ⟶ D).
Context `{H : @Monad D T}.

Local Notation EMT := (@EilenbergMoore D T H).

(** ** The existence clause *)

Lemma em_create_iso_triangle {a b : EMT} (f g : a ~{EMT}~> b)
  (S : SplitCoequalizer (t_alg_hom[f]) (t_alg_hom[g])) :
  id ∘ t_alg_hom[created_hom T f g S (em_forget_creates_split T f g S)]
    ≈ scoeq_e S.
Proof.
  rewrite id_left.
  apply (created_hom_carrier T f g S (em_forget_creates_split T f g S)).
Qed.

Definition em_create_coeq {a b : EMT} (f g : a ~{EMT}~> b)
  (S : SplitCoequalizer (fmap[EM_Forget T] f) (fmap[EM_Forget T] g)) :
  ∃ (q : EMT) (e : b ~{EMT}~> q),
    IsCoequalizer f g q e ∧
    (∃ i : @Isomorphism D (fobj[EM_Forget T] q) (scoeq_obj S),
       to i ∘ fmap[EM_Forget T] e ≈ scoeq_e S).
Proof.
  exists (scoeq_obj S;
          created_alg T f g S (em_forget_creates_split T f g S)).
  exists (created_hom T f g S (em_forget_creates_split T f g S)).
  split.
  - exact (created_coequalizes T f g S (em_forget_creates_split T f g S)).
  - exists iso_id.
    exact (em_create_iso_triangle f g S).
Defined.

(** ** The reflection clause *)

Section EMReflect.

Context {a b : EMT}.
Context (f g : a ~{EMT}~> b).
Context (S : SplitCoequalizer (t_alg_hom[f]) (t_alg_hom[g])).
Context {q : EMT}.
Context (e : b ~{EMT}~> q).
Context (He : e ∘ f ≈ e ∘ g).
Context (i : @Isomorphism D (`1 q) (scoeq_obj S)).
Context (Hi : to i ∘ t_alg_hom[e] ≈ scoeq_e S).

(* The carrier of e, read back through the comparison isomorphism. *)
Lemma em_reflect_e0 : t_alg_hom[e] ≈ from i ∘ scoeq_e S.
Proof using All.
  rewrite <- Hi.
  rewrite comp_assoc.
  rewrite (iso_from_to i).
  now rewrite id_left.
Qed.

(* e₀ is a split epimorphism, with section s ∘ to i. *)
Lemma em_reflect_e0_split :
  t_alg_hom[e] ∘ (scoeq_s S ∘ to i) ≈ id.
Proof using All.
  rewrite em_reflect_e0.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (scoeq_e S) (scoeq_s S) (to i)).
  rewrite (scoeq_law2 S).
  rewrite id_left.
  exact (iso_from_to i).
Qed.

Definition em_reflect_Te0_epic : Epic (fmap[T] (t_alg_hom[e])) :=
  fmap_split_epic T (t_alg_hom[e]) (scoeq_s S ∘ to i)
    em_reflect_e0_split.

Section EMReflectDesc.

Context {z : EMT}.
Context (h : b ~{EMT}~> z).
Context (Hh : h ∘ f ≈ h ∘ g).

(* Descent downstairs, through the split coequalizer. *)
Definition em_reflect_desc0 :
  ∃! u : scoeq_obj S ~{D}~> `1 z, u ∘ scoeq_e S ≈ t_alg_hom[h] :=
  split_coeq_desc S (t_alg_hom[h]) Hh.

(* The mediating carrier, conjugated back through the comparison. *)
Definition em_reflect_desc_carrier : `1 q ~{D}~> `1 z :=
  unique_obj em_reflect_desc0 ∘ to i.

Lemma em_reflect_desc_triangle :
  em_reflect_desc_carrier ∘ t_alg_hom[e] ≈ t_alg_hom[h].
Proof using All.
  unfold em_reflect_desc_carrier.
  rewrite <- comp_assoc.
  rewrite Hi.
  exact (unique_property em_reflect_desc0).
Qed.

(* The descended carrier is an algebra homomorphism: both sides of its
   square restrict along the split epimorphism T e₀ to h₀ ∘ β. *)
Lemma em_reflect_desc_commutes :
  em_reflect_desc_carrier ∘ t_alg[`2 q]
    ≈ t_alg[`2 z] ∘ fmap[T] em_reflect_desc_carrier.
Proof using All.
  apply (@epic _ _ _ _ em_reflect_Te0_epic).
  rewrite <- !comp_assoc.
  rewrite <- (@t_alg_hom_commutes _ _ _ _ _ _ _ e).
  rewrite <- fmap_comp.
  rewrite em_reflect_desc_triangle.
  rewrite <- (@t_alg_hom_commutes _ _ _ _ _ _ _ h).
  rewrite comp_assoc.
  rewrite em_reflect_desc_triangle.
  reflexivity.
Qed.

Definition em_reflect_desc_hom : q ~{EMT}~> z :=
  @Build_TAlgebraHom D T H (`1 q) (`1 z) (`2 q) (`2 z)
    em_reflect_desc_carrier em_reflect_desc_commutes.

(* Uniqueness on carriers: a competitor, conjugated through the
   comparison, is a downstairs descent of h₀, so the split
   coequalizer's uniqueness clause identifies the two. *)
Lemma em_reflect_desc_unique (v : q ~{EMT}~> z)
  (Hv : t_alg_hom[v] ∘ t_alg_hom[e] ≈ t_alg_hom[h]) :
  em_reflect_desc_carrier ≈ t_alg_hom[v].
Proof using All.
  assert (Hv' : (t_alg_hom[v] ∘ from i) ∘ scoeq_e S ≈ t_alg_hom[h]).
  { rewrite <- comp_assoc.
    rewrite <- em_reflect_e0.
    exact Hv. }
  unfold em_reflect_desc_carrier.
  rewrite (uniqueness em_reflect_desc0 (t_alg_hom[v] ∘ from i) Hv').
  rewrite <- comp_assoc.
  rewrite (iso_from_to i).
  now rewrite id_right.
Qed.

End EMReflectDesc.

Definition em_reflect_is_coeq : IsCoequalizer f g q e.
Proof using All.
  unshelve refine {| cofork := He ; coeq_desc := _ |}.
  intros z h Hh.
  unshelve eapply Build_Unique.
  - exact (em_reflect_desc_hom h Hh).
  - exact (em_reflect_desc_triangle h Hh).
  - intros v Hv.
    exact (em_reflect_desc_unique h Hh v Hv).
Defined.

End EMReflect.

(** The converse of Beck's theorem, at the terminal resolution: U^T
    creates coequalizers of U^T-split pairs. *)

Theorem monadic_creates : CreatesUSplitCoequalizers (EM_Forget T).
Proof.
  unshelve refine {| create_coeq := _ ; create_coeq_reflects := _ |}.
  - intros a b f g S.
    exact (em_create_coeq f g S).
  - intros a b f g S q e He i Hi.
    exact (em_reflect_is_coeq f g S e He i Hi).
Defined.

End MonadicCreates.
