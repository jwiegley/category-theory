Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Monad.Adjunction.
Require Import Category.Monad.Algebra.
Require Import Category.Monad.Eilenberg.Moore.
Require Import Category.Monad.Eilenberg.Moore.Adjunction.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Coequalizer.Split.
Require Import Category.Structure.Coequalizer.Reflexive.
Require Import Category.Structure.Limit.Preservation.

Generalizable All Variables.

(** * Beck objects: split forks, conservativity, created coequalizers

    nLab:      https://ncatlab.org/nlab/show/monadicity+theorem
    Wikipedia: https://en.wikipedia.org/wiki/Beck%27s_monadicity_theorem

    Fix a monad (T, η, μ) = (T, ret, join) on a category D, with
    Eilenberg–Moore category D^T (Monad/Eilenberg/Moore.v) and forgetful
    functor U^T = [EM_Forget] (Monad/Eilenberg/Moore/Adjunction.v).  This
    file assembles the three Eilenberg–Moore ingredients that drive
    Beck's monadicity theorem; the theorem itself consumes them through
    the comparison functor.

    1. [canonical_split]: every T-algebra (a, α) is presented by free
       data — the parallel pair μ_a, T α : T (T a) ⇉ T a is coequalized
       by α itself, and the coequalizer is split by the sections η_a and
       η_{T a}.  The order of the pair matters: law 3 of a split
       coequalizer asks the *first* leg to retract the section η_{T a},
       which is the monad unit law μ ∘ η_{T a} ≈ id, so μ_a comes first;
       the second leg T α composes with η_{T a} to η_a ∘ α by naturality
       of η, which is exactly law 4.  [canonical_reflexive] records that
       the same pair is also reflexive, with common section T η_a.

    2. [em_forget_reflects_isos]: U^T is conservative.  An algebra
       homomorphism whose underlying arrow is invertible is itself
       invertible: the inverse arrow is again an algebra homomorphism,
       obtained by conjugating the commuting square with the inverse on
       both sides.

    3. [em_forget_creates_split]: U^T creates coequalizers of U^T-split
       pairs.  Given f, g : (a, α) ⇉ (b, β) in D^T whose underlying pair
       has a split coequalizer e : b ~> q in D, the object q carries a
       unique T-algebra action γ making e an algebra homomorphism, and
       that homomorphism coequalizes f, g in D^T.  The action γ is the
       descent of e ∘ β through T e — legitimate because split
       coequalizers are absolute (Structure/Coequalizer/Split.v), so T
       and T ∘ T both preserve the given split fork — and its algebra
       laws follow by cancelling the split epimorphisms T e and T (T e).
       The whole package is the record [CreatedSplitCoequalizer]. *)

Section BeckObjects.

Context {D : Category}.
Context (T : D ⟶ D).
Context `{H : @Monad D T}.

(** ** The canonical split presentation of an algebra

    For an algebra (a, α), the fork

        μ_a, T α : T (T a) ⇉ T a  --α-->  a

    is a split coequalizer: α coforks the pair (the associativity law
    [t_action], read backwards), η_a splits α (the unit law [t_id]),
    η_{T a} splits μ_a (the monad law [join_ret]), and T α ∘ η_{T a}
    computes η_a ∘ α (naturality [fmap_ret] of the unit). *)

Definition canonical_split {a : D} (α : TAlgebra T a) :
  SplitCoequalizer (@join D T H a) (fmap[T] (t_alg[α])).
Proof.
  unshelve refine
    {| scoeq_obj := a
     ; scoeq_e   := t_alg[α]
     ; scoeq_s   := ret
     ; scoeq_t   := ret |}.
  - (* law 1: α ∘ μ ≈ α ∘ T α, i.e. [t_action] reversed *)
    symmetry.
    apply (@t_action D T H a α).
  - (* law 2: α ∘ η ≈ id, i.e. [t_id] *)
    apply (@t_id D T H a α).
  - (* law 3: μ ∘ η_{T a} ≈ id, i.e. [join_ret] *)
    apply join_ret.
  - (* law 4: T α ∘ η_{T a} ≈ η_a ∘ α, naturality of η reversed *)
    symmetry.
    apply fmap_ret.
Defined.

(** The same canonical pair is reflexive: T η_a is a common section,
    by the monad law [join_fmap_ret] on the μ side and functoriality
    over the unit law [t_id] on the T α side. *)

Definition canonical_reflexive {a : D} (α : TAlgebra T a) :
  ReflexivePair (@join D T H a) (fmap[T] (t_alg[α])).
Proof.
  unshelve refine {| refl_section := fmap[T] ret |}.
  - (* μ ∘ T η ≈ id *)
    apply join_fmap_ret.
  - (* T α ∘ T η ≈ T (α ∘ η) ≈ T id ≈ id *)
    rewrite <- fmap_comp.
    rewrite (@t_id D T H a α).
    apply fmap_id.
Defined.

(** ** A functor sends split epis to epis

    The image under T of a morphism with a right inverse is again a
    split epi, hence epic.  Used below to cancel T e and T (T e). *)

Lemma fmap_split_epic {x y : D} (p : x ~> y) (s : y ~> x)
  (Hps : p ∘ s ≈ id) : Epic (fmap[T] p).
Proof.
  apply retractions_are_epic.
  exists (fmap[T] s).
  rewrite <- fmap_comp.
  rewrite Hps.
  apply fmap_id.
Qed.

(** ** The forgetful functor reflects isomorphisms

    Let h : (a, α) ~> (b, β) be an algebra homomorphism with underlying
    arrow h₀ and suppose h₀ has a two-sided inverse k in D.  Then k is
    itself an algebra homomorphism (b, β) ~> (a, α):

        k ∘ β ≈ k ∘ β ∘ T (h₀ ∘ k)          (h₀ ∘ k ≈ id)
              ≈ k ∘ (β ∘ T h₀) ∘ T k
              ≈ k ∘ (h₀ ∘ α) ∘ T k          (square for h, reversed)
              ≈ (k ∘ h₀) ∘ α ∘ T k
              ≈ α ∘ T k.                    (k ∘ h₀ ≈ id)

    The two inverse laws upstairs are then the ones downstairs, since
    hom-equivalence in D^T is hom-equivalence of underlying arrows.  The
    proof below runs the chain backwards, cancelling the split epi T h₀
    on the right. *)

Lemma em_iso_inverse_commutes {x y : EilenbergMoore T}
  (h : x ~{EilenbergMoore T}~> y)
  (I : IsIsomorphism (t_alg_hom[h])) :
  @two_sided_inverse D _ _ _ I ∘ t_alg[`2 y]
    ≈ t_alg[`2 x] ∘ fmap[T] (@two_sided_inverse D _ _ _ I).
Proof.
  apply (@epic _ _ _ _
           (fmap_split_epic (t_alg_hom[h]) (@two_sided_inverse D _ _ _ I)
              (@is_right_inverse D _ _ _ I))).
  rewrite <- !comp_assoc.
  rewrite <- (@t_alg_hom_commutes _ _ _ _ _ _ _ h).
  rewrite <- fmap_comp.
  rewrite (@is_left_inverse D _ _ _ I).
  rewrite fmap_id.
  rewrite id_right.
  rewrite comp_assoc.
  rewrite (@is_left_inverse D _ _ _ I).
  apply id_left.
Qed.

(** The inverse arrow, packaged as a morphism of D^T. *)

Definition em_iso_inverse_hom {x y : EilenbergMoore T}
  (h : x ~{EilenbergMoore T}~> y)
  (I : IsIsomorphism (t_alg_hom[h])) :
  y ~{EilenbergMoore T}~> x :=
  {| t_alg_hom := @two_sided_inverse D _ _ _ I
   ; t_alg_hom_commutes := em_iso_inverse_commutes h I |}.

(** U^T is conservative.  Note that [fmap[EM_Forget T] h] is
    definitionally [t_alg_hom[h]], so the hypothesis hands us exactly an
    inverse of the underlying arrow, and the inverse laws upstairs hold
    by the same equations downstairs. *)

#[export] Instance em_forget_reflects_isos : ReflectsIsos (EM_Forget T).
Proof.
  constructor.
  intros x y h I.
  unshelve refine {| two_sided_inverse := em_iso_inverse_hom h I |}.
  - exact (@is_right_inverse D _ _ _ I).
  - exact (@is_left_inverse D _ _ _ I).
Qed.

(** ** Creation of coequalizers of split pairs

    Fix algebra homomorphisms f, g : (a, α) ⇉ (b, β) and a split
    coequalizer [SC] of their underlying pair in D, with object q,
    coequalizing map e : b₀ ~> q, and sections s and t.  We manufacture
    the unique algebra structure on q for which e is a homomorphism, and
    show the resulting homomorphism coequalizes f, g in D^T. *)

Section CreatedCoequalizers.

Context {a b : EilenbergMoore T}.
Context (f g : a ~{EilenbergMoore T}~> b).
Context (SC : SplitCoequalizer (t_alg_hom[f]) (t_alg_hom[g])).

(** Split coequalizers are absolute, so T preserves this one. *)

Definition beck_image_split :
  SplitCoequalizer (fmap[T] (t_alg_hom[f])) (fmap[T] (t_alg_hom[g])) :=
  functor_preserves_split T (t_alg_hom[f]) (t_alg_hom[g]) SC.

(** The three split epimorphisms we cancel against: e itself, T e (the
    coequalizing map of the preserved fork), and T (T e). *)

Lemma beck_e_epic : Epic (scoeq_e SC).
Proof.
  apply retractions_are_epic.
  exists (scoeq_s SC).
  apply (scoeq_law2 SC).
Qed.

Definition beck_fmap_e_epic : Epic (fmap[T] (scoeq_e SC)) :=
  fmap_split_epic (scoeq_e SC) (scoeq_s SC) (scoeq_law2 SC).

Definition beck_fmap_fmap_e_epic :
  Epic (fmap[T] (fmap[T] (scoeq_e SC))) :=
  fmap_split_epic (fmap[T] (scoeq_e SC)) (fmap[T] (scoeq_s SC))
    (scoeq_law2 beck_image_split).

(** e ∘ β coforks the T-image pair: push β through the commuting
    squares of f and g, then use the cofork law of [SC] under e. *)

Lemma beck_image_cofork :
  (scoeq_e SC ∘ t_alg[`2 b]) ∘ fmap[T] (t_alg_hom[f])
    ≈ (scoeq_e SC ∘ t_alg[`2 b]) ∘ fmap[T] (t_alg_hom[g]).
Proof.
  rewrite <- !comp_assoc.
  rewrite <- (@t_alg_hom_commutes _ _ _ _ _ _ _ f).
  rewrite <- (@t_alg_hom_commutes _ _ _ _ _ _ _ g).
  rewrite !comp_assoc.
  rewrite (scoeq_law1 SC).
  reflexivity.
Qed.

(** The created action: descend e ∘ β through the preserved coequalizer
    T e.  Its defining triangle γ ∘ T e ≈ e ∘ β is [created_action_sq]. *)

Definition beck_action_desc :
  ∃! u : T (scoeq_obj SC) ~{D}~> scoeq_obj SC,
    u ∘ fmap[T] (scoeq_e SC) ≈ scoeq_e SC ∘ t_alg[`2 b] :=
  split_coeq_desc beck_image_split (scoeq_e SC ∘ t_alg[`2 b])
    beck_image_cofork.

Definition created_action : T (scoeq_obj SC) ~{D}~> scoeq_obj SC :=
  unique_obj beck_action_desc.

Definition created_action_sq :
  created_action ∘ fmap[T] (scoeq_e SC) ≈ scoeq_e SC ∘ t_alg[`2 b] :=
  unique_property beck_action_desc.

(** Unit law for γ: precompose with the epi e, slide η past e by
    naturality, contract γ ∘ T e, then use the unit law of β. *)

Lemma created_action_t_id : created_action ∘ ret ≈ id.
Proof.
  apply (@epic _ _ _ _ beck_e_epic).
  rewrite <- comp_assoc.
  rewrite fmap_ret.
  rewrite comp_assoc.
  rewrite created_action_sq.
  rewrite <- comp_assoc.
  rewrite (@t_id D T H _ (`2 b)).
  rewrite id_right.
  rewrite id_left.
  reflexivity.
Qed.

(** Associativity law for γ: both sides agree after precomposition with
    the epi T (T e) — the left leg contracts γ ∘ T e twice, the right
    leg slides μ past T (T e) by naturality and contracts once; what
    remains is the associativity law of β under e. *)

Lemma created_action_t_action :
  created_action ∘ fmap[T] created_action ≈ created_action ∘ join.
Proof.
  apply (@epic _ _ _ _ beck_fmap_fmap_e_epic).
  rewrite <- !comp_assoc.
  rewrite <- fmap_comp.
  rewrite created_action_sq.
  rewrite fmap_comp.
  rewrite join_fmap_fmap.
  rewrite !comp_assoc.
  rewrite created_action_sq.
  rewrite <- !comp_assoc.
  rewrite (@t_action D T H _ (`2 b)).
  reflexivity.
Qed.

(** The created algebra (q, γ), and e as an algebra homomorphism into
    it.  Its carrier is definitionally the coequalizing map e. *)

Definition created_algebra : @TAlgebra D T H (scoeq_obj SC) :=
  {| t_alg    := created_action
   ; t_id     := created_action_t_id
   ; t_action := created_action_t_action |}.

Lemma created_e_commutes :
  scoeq_e SC ∘ t_alg[`2 b] ≈ created_action ∘ fmap[T] (scoeq_e SC).
Proof.
  symmetry.
  apply created_action_sq.
Qed.

Definition created_e_hom :
  b ~{EilenbergMoore T}~> (scoeq_obj SC; created_algebra) :=
  @Build_TAlgebraHom D T H (`1 b) (scoeq_obj SC) (`2 b) created_algebra
    (scoeq_e SC) created_e_commutes.

(** Descent upstairs.  A homomorphism h coforking f, g has a coforking
    carrier, hence descends through e downstairs; the descended arrow is
    itself a homomorphism, seen by cancelling the epi T e: both sides of
    its square restrict along T e to h₀ ∘ β. *)

Lemma created_desc_is_alg_hom (z : EilenbergMoore T)
  (h : b ~{EilenbergMoore T}~> z)
  (Hh : t_alg_hom[h] ∘ t_alg_hom[f] ≈ t_alg_hom[h] ∘ t_alg_hom[g]) :
  unique_obj (split_coeq_desc SC (t_alg_hom[h]) Hh) ∘ created_action
    ≈ t_alg[`2 z]
        ∘ fmap[T] (unique_obj (split_coeq_desc SC (t_alg_hom[h]) Hh)).
Proof.
  apply (@epic _ _ _ _ beck_fmap_e_epic).
  rewrite <- !comp_assoc.
  rewrite created_action_sq.
  rewrite <- fmap_comp.
  rewrite (unique_property (split_coeq_desc SC (t_alg_hom[h]) Hh)).
  rewrite comp_assoc.
  rewrite (unique_property (split_coeq_desc SC (t_alg_hom[h]) Hh)).
  apply (@t_alg_hom_commutes _ _ _ _ _ _ _ h).
Qed.

Definition created_desc_hom (z : EilenbergMoore T)
  (h : b ~{EilenbergMoore T}~> z)
  (Hh : t_alg_hom[h] ∘ t_alg_hom[f] ≈ t_alg_hom[h] ∘ t_alg_hom[g]) :
  ((scoeq_obj SC; created_algebra) : EilenbergMoore T)
    ~{EilenbergMoore T}~> z :=
  @Build_TAlgebraHom D T H (scoeq_obj SC) (`1 z) created_algebra (`2 z)
    (unique_obj (split_coeq_desc SC (t_alg_hom[h]) Hh))
    (created_desc_is_alg_hom z h Hh).

(** The universal property upstairs: since hom-equivalence and
    composition in D^T are those of D on carriers, the triangle and the
    uniqueness clause are exactly the ones of the split coequalizer
    downstairs, transported along [created_desc_hom]. *)

Definition created_is_coequalizer :
  IsCoequalizer f g (scoeq_obj SC; created_algebra) created_e_hom.
Proof.
  unshelve refine {| cofork := _ ; coeq_desc := _ |}.
  - (* e coforks f, g upstairs since it does downstairs *)
    exact (scoeq_law1 SC).
  - intros z h Hh.
    unshelve refine {| unique_obj := created_desc_hom z h Hh |}.
    + (* the triangle is the one downstairs *)
      exact (unique_property (split_coeq_desc SC (t_alg_hom[h]) Hh)).
    + (* uniqueness on carriers is uniqueness downstairs *)
      intros v Hv.
      exact (uniqueness (split_coeq_desc SC (t_alg_hom[h]) Hh)
               (t_alg_hom[v]) Hv).
Defined.

(** Uniqueness of the created action: any algebra structure on q making
    e a homomorphism satisfies the defining triangle of γ, so descent
    uniqueness identifies the two actions. *)

Lemma created_algebra_unique (alg' : @TAlgebra D T H (scoeq_obj SC)) :
  scoeq_e SC ∘ t_alg[`2 b] ≈ t_alg[alg'] ∘ fmap[T] (scoeq_e SC) →
  t_alg[alg'] ≈ t_alg[created_algebra].
Proof.
  intros Halg.
  symmetry.
  apply (uniqueness beck_action_desc).
  symmetry.
  exact Halg.
Qed.

(** The record a consumer of creation receives: the algebra on the
    coequalizer object, the coequalizing homomorphism with its carrier
    pinned to e, the coequalizer property upstairs, and uniqueness of
    the algebra structure. *)

Record CreatedSplitCoequalizer : Type := {
  created_alg : @TAlgebra D T H (scoeq_obj SC);
  created_hom : b ~{EilenbergMoore T}~> (scoeq_obj SC; created_alg);
  created_hom_carrier : t_alg_hom[created_hom] ≈ scoeq_e SC;
  created_coequalizes :
    IsCoequalizer f g (scoeq_obj SC; created_alg) created_hom;
  created_alg_unique (alg' : @TAlgebra D T H (scoeq_obj SC)) :
    scoeq_e SC ∘ t_alg[`2 b] ≈ t_alg[alg'] ∘ fmap[T] (scoeq_e SC) →
    t_alg[alg'] ≈ t_alg[created_alg]
}.

Theorem em_forget_creates_split : CreatedSplitCoequalizer.
Proof.
  unshelve refine
    {| created_alg := created_algebra
     ; created_hom := created_e_hom |}.
  - (* the carrier of the created homomorphism is e on the nose *)
    reflexivity.
  - exact created_is_coequalizer.
  - exact created_algebra_unique.
Defined.

End CreatedCoequalizers.

End BeckObjects.
