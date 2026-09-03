Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.Topos.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Topos.
Require Import Category.Instance.FinSet.Powerset.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Proset.Monotone.
Require Import Category.Instance.Powerset.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.

Generalizable All Variables.

(** * The power set of a finite set, ordered by inclusion, COMPUTING

    Seven Sketches (Fong and Spivak, "An Invitation to Applied Category
    Theory") §1.2.2 Examples 50 and 51 and §1.4.3 Examples 117 and 118.
    There is no page image for that book here, so the clauses are quoted
    from the catalog issue's own transcription: the power sets of the
    zero-, one- and two-element sets with their inclusion orders drawn
    out, and then the apples-and-buckets function with its preimage, its
    direct image and its dual image evaluated at named subsets.

    nLab: https://ncatlab.org/nlab/show/power+set
    nLab: https://ncatlab.org/nlab/show/subobject+classifier
    nLab: https://ncatlab.org/nlab/show/power+object

    ** WHAT IS DELIVERED, WITH GRADES

    (A) A decidable bounded quantifier pair, [fin_allb] and [fin_anyb],
        with both halves of each specification.  Neither name occurs
        anywhere else in the tree; the three existing [Fin.t]
        enumerations ([all_fins] in Instance/Matr/Determinant.v,
        [fin_enum] in Instance/FinSet/Skeleton.v, [all_fin] in
        Instance/FinSet/Pushout.v) enumerate a LIST, which is a heavier
        instrument than a fold to [bool] and, in the first case, sits in
        a module whose closure is far larger than this file's.

    (B) [finpow_le], its [PreOrder], and [FinSubsets n], the power set of
        the n-element set as a thin category over Instance/Proset.v's
        [Proset].  The objects are EXACTLY the [finpow n] codes
        ([FinSubsets_obj_is_code], [eq_refl]), so the three counts of
        Example 50 are [finpow 0 = 1], [finpow 1 = 2], [finpow 2 = 4],
        all by [eq_refl].  The orders are exhibited: at n = 1 the two
        codes [empty1]/[full1] with the one inclusion inhabited and its
        converse refuted; at n = 2 the four codes with all FIVE
        non-identity inclusions inhabited and BOTH incomparabilities
        refuted ([sub2_01_not_le_10], [sub2_10_not_le_01]), so
        [FinSubsets 2] is provably not a chain -- which is what
        distinguishes the power set of a two-element set from an
        arbitrary four-element order.  Every one of these is [eq_refl] or
        [discriminate], because [finpow_mem] is a decidable test; its
        [Subsets] cousin over an arbitrary Prop-valued predicate could
        not be enumerated constructively at all.

    (C) The comparison with Instance/Powerset.v: [finpow_to_subset] turns
        a code into a Prop-valued subset of the discrete setoid
        [Powerset_Prop_fin_object n], monotone and ORDER-REFLECTING, so
        [FinSubsetsToSubsets n : FinSubsets n ⟶ Subsets _] is proved
        [Full] -- order reflection is exactly what [Full] spends.
        [FinSubsetsToSubsets_Faithful] is shipped beside it but carries
        NO content: the source is thin, so [f ≈ g] there is [True] and
        every functor out of [FinSubsets n] is faithful by the same
        one-line proof.  Essential surjectivity is NOT claimed: it would
        decide an arbitrary Prop-valued predicate.

    (D) [FinSet_Pow_one : Pow 1 = 2] by [eq_refl] -- the missing member of
        Instance/FinSet/Topos.v's [FinSet_Pow_zero]/[FinSet_Pow_two]
        family, which lives here rather than there.  The GENERAL form
        [finpow_is_topos_Pow] is NOT new: Instance/FinSet/Powerset.v:509
        already proves [Pow n = finpow n] for open [n], and it is cited,
        not duplicated.

    (E) The INTERNAL inclusion order on the power object at [FinSet]:
        [finpow_subseteq] as a [bool] and
        [internal_subseteq n : Pow n × Pow n ~{FinSet}~> Ω] as an arrow
        of the category, with [internal_subseteq_spec] proving the
        internal test EQUIVALENT to the external order [finpow_le] -- so
        the two readings agree, not merely correspond.  The general-topos
        internal inclusion is NOT delivered, and the obstruction is
        measured rather than guessed: it would be the equalizer of the
        first projection against the composite of an internal
        conjunction with the two evaluations, and the tree HAS NO
        internal conjunction on Ω: no constant anywhere has type
        [Ω × Ω ~> Ω], and the characteristic map of ⟨truth, truth⟩
        appears nowhere.  Read that measurement at its scope -- the word
        "meet" DOES occur in Structure/Topos.v:101, but as prose
        describing what a Lawvere-Tierney topology is, not as a
        constant.

    (F) Example 118, evaluated.  [apples : 3 ~> 2] puts two apples in
        bucket 0 and one in bucket 1.  [finpow_preimage] is
        Instance/FinSet/Powerset.v:159's [finpow_map] under a name that
        says what it is ([finpow_preimage_is_finpow_map], [eq_refl] --
        the inverse image on codes was ALREADY the arrow action of
        [FinPowerset], and nothing is rebuilt); [finpow_image] and
        [finpow_dual] are new.  Six [eq_refl] evaluations at closed
        inputs chosen so the three operations VISIBLY differ: at {0} the
        image is {0} while the dual is empty (apple 1 is missing), at
        {0,1} both are {0}.  Example 117's left half -- the preimage has
        a LEFT adjoint -- is [finpow_image_preimage_galois]; its right
        half, the dual image as a RIGHT adjoint, is #384's and is NOT
        built here.  The EVALUATIONS of [finpow_dual] are this file's;
        the adjunction it satisfies is not.

    ** WHAT IS NOT DELIVERED

    The dual-image adjunction (#384).  The general-topos internal
    inclusion, for the measured reason above.  No isomorphism between
    [FinSubsets n] and [Subsets (Powerset_Prop_fin_object n)] (only the
    full and faithful comparison).  No link between [finpow_subseteq] and
    [sub_le] on [SubObj n] through [FinSet_Sub_powerset]/[finpow_codec]:
    that would need the classifier round trip carried across the
    subobject setoid, which is a further construction and is only
    cross-referenced.  No [Cartesian]/[Complete] structure on
    [FinSubsets], which would be Instance/Powerset.v's development
    repeated over codes.

    ** UNIVERSES

    [FinSubsets@{u}] carries a [Set] BOUND from [Fin.t n : Set], not an
    identification; everything mentioning [Powerset_Prop_obj] inherits
    [Set < o] from the donor as usual.  Measured per constant in the
    report.

    ** TRANSPARENCY

    [finpow_to_subset] MUST be [Defined] -- measured by flipping it to
    [Qed], which breaks the file, its predicate being read through by
    the two monotonicity lemmas.  [FinSubsetsToSubsets_Full] and the
    inline [FinSubsetsToSubsets_Faithful] each compile as [Qed] and are
    [Defined] for uniformity -- three [Defined]s in this file.

    ** REGISTRATION

    Nothing here is an [Instance]. *)

(* ------------------------------------------------------------------------ *)
(** ** (A) Bounded decidable quantifiers over [Fin.t] *)

Fixpoint fin_allb (n : nat) : (Fin.t n → bool) → bool :=
  match n with
  | O    => fun _ => true
  | S m  => fun g => andb (g Fin.F1) (fin_allb m (fun i => g (Fin.FS i)))
  end.

Fixpoint fin_anyb (n : nat) : (Fin.t n → bool) → bool :=
  match n with
  | O    => fun _ => false
  | S m  => fun g => orb (g Fin.F1) (fin_anyb m (fun i => g (Fin.FS i)))
  end.

Lemma fin_allb_forall (n : nat) (g : Fin.t n → bool) :
  fin_allb n g = true → ∀ i : Fin.t n, g i = true.
Proof.
  induction n as [| m IH]; intros H i.
  - exact (Fin.case0 (fun _ => g i = true) i).
  - simpl in H.
    apply Bool.andb_true_iff in H; destruct H as [H1 H2].
    refine (Fin.caseS' i (fun j => g j = true) H1 _).
    intro j; exact (IH (fun p => g (Fin.FS p)) H2 j).
Qed.

Lemma fin_forall_allb (n : nat) (g : Fin.t n → bool) :
  (∀ i : Fin.t n, g i = true) → fin_allb n g = true.
Proof.
  induction n as [| m IH]; intro H; simpl.
  - reflexivity.
  - apply Bool.andb_true_iff; split.
    + exact (H Fin.F1).
    + exact (IH (fun p => g (Fin.FS p)) (fun p => H (Fin.FS p))).
Qed.

Lemma fin_anyb_exists (n : nat) (g : Fin.t n → bool) :
  fin_anyb n g = true → ∃ i : Fin.t n, g i = true.
Proof.
  induction n as [| m IH]; intro H; simpl in H.
  - discriminate H.
  - (* [orb_true_elim] lands in [sumbool], which -- unlike
       [orb_true_iff]'s [or] -- may be eliminated into the [Type]-valued
       [∃] the conclusion uses. *)
    destruct (Bool.orb_true_elim _ _ H) as [H1 | H1].
    + exists Fin.F1; exact H1.
    + destruct (IH (fun p => g (Fin.FS p)) H1) as [j Hj].
      exists (Fin.FS j); exact Hj.
Qed.

Lemma fin_exists_anyb (n : nat) (g : Fin.t n → bool) (i : Fin.t n) :
  g i = true → fin_anyb n g = true.
Proof.
  induction n as [| m IH]; intro H.
  - exact (Fin.case0 (fun _ => fin_anyb 0 g = true) i).
  - simpl; apply Bool.orb_true_iff.
    revert H.
    refine (Fin.caseS' i (fun j => g j = true → _) _ _).
    + intro H; left; exact H.
    + intros j H; right.
      exact (IH (fun p => g (Fin.FS p)) j H).
Qed.

(* Membership reads a boolean back through [fin_of_bool] on the nose. *)
Lemma finpow_mem_of_bool (b : bool) : fin_eqb (fin_of_bool b) fin_true = b.
Proof. destruct b; reflexivity. Qed.

(* ------------------------------------------------------------------------ *)
(** ** (B) The inclusion order on codes, and the thin category *)

Definition finpow_le {n : nat} (S T : Fin.t (finpow n)) : Prop :=
  ∀ i : Fin.t n, finpow_mem S i = true → finpow_mem T i = true.

Definition finpow_le_preorder (n : nat) : PreOrder (@finpow_le n) :=
  {| PreOrder_Reflexive  := fun S i Hi => Hi
   ; PreOrder_Transitive :=
       fun S T U HST HTU i Hi => HTU i (HST i Hi) |}.

(* A decidable order needs no argument: [fin_allb] settles every one of
   the four codes' comparisons by computation. *)
Lemma finpow_le_of_allb (n : nat) (S T : Fin.t (finpow n)) :
  fin_allb n (fun i => implb (finpow_mem S i) (finpow_mem T i)) = true →
  finpow_le S T.
Proof.
  intros H i Hi.
  pose proof (fin_allb_forall n
    (fun j => implb (finpow_mem S j) (finpow_mem T j)) H i) as Hj.
  cbv beta in Hj.
  rewrite Hi in Hj; exact Hj.
Qed.

Definition FinSubsets@{u} (n : nat) : Category@{Set u u} :=
  Proset@{Set u} (finpow_le_preorder n).

Example FinSubsets_obj_is_code@{u} (n : nat) :
  obj[FinSubsets@{u} n] = Fin.t (finpow n) := eq_refl.

Example FinSubsets_hom_is_finpow_le@{u} (n : nat)
  (S T : FinSubsets@{u} n) :
  (S ~{FinSubsets@{u} n}~> T) = finpow_le S T := eq_refl.

(** ** Example 50: the three small power sets, counted and drawn *)

Example finpow_zero_count : finpow 0 = 1%nat := eq_refl.
Example finpow_one_count  : finpow 1 = 2%nat := eq_refl.
Example finpow_two_count  : finpow 2 = 4%nat := eq_refl.

(* n = 1: the two subsets of a one-element set. *)
Definition empty1 : Fin.t (finpow 1) := fin_tabulate (fun _ => fin_false).
Definition full1  : Fin.t (finpow 1) := fin_tabulate (fun _ => fin_true).

Example empty1_at_0 : finpow_mem empty1 Fin.F1 = false := eq_refl.
Example full1_at_0  : finpow_mem full1  Fin.F1 = true  := eq_refl.

Definition empty1_le_full1 : finpow_le empty1 full1 :=
  finpow_le_of_allb 1 empty1 full1 eq_refl.

Lemma full1_not_le_empty1 : finpow_le full1 empty1 → False.
Proof. intro H; discriminate (H Fin.F1 eq_refl). Qed.

(* n = 2: the four subsets of a two-element set, and the square. *)
Definition sub2_00 : Fin.t (finpow 2) := fin_tabulate (fun _ => fin_false).
Definition sub2_10 : Fin.t (finpow 2) :=
  fin_tabulate (fun i => match i with
                         | Fin.F1 => fin_true
                         | _      => fin_false
                         end).
Definition sub2_01 : Fin.t (finpow 2) :=
  fin_tabulate (fun i => match i with
                         | Fin.F1 => fin_false
                         | _      => fin_true
                         end).
Definition sub2_11 : Fin.t (finpow 2) := fin_tabulate (fun _ => fin_true).

Example sub2_10_at_0 : finpow_mem sub2_10 Fin.F1 = true := eq_refl.
Example sub2_10_at_1 :
  finpow_mem sub2_10 (Fin.FS Fin.F1) = false := eq_refl.
Example sub2_01_at_0 : finpow_mem sub2_01 Fin.F1 = false := eq_refl.
Example sub2_01_at_1 :
  finpow_mem sub2_01 (Fin.FS Fin.F1) = true := eq_refl.

(* The five non-identity inclusions of the square. *)
Definition sub2_00_le_10 : finpow_le sub2_00 sub2_10 :=
  finpow_le_of_allb 2 sub2_00 sub2_10 eq_refl.
Definition sub2_00_le_01 : finpow_le sub2_00 sub2_01 :=
  finpow_le_of_allb 2 sub2_00 sub2_01 eq_refl.
Definition sub2_00_le_11 : finpow_le sub2_00 sub2_11 :=
  finpow_le_of_allb 2 sub2_00 sub2_11 eq_refl.
Definition sub2_10_le_11 : finpow_le sub2_10 sub2_11 :=
  finpow_le_of_allb 2 sub2_10 sub2_11 eq_refl.
Definition sub2_01_le_11 : finpow_le sub2_01 sub2_11 :=
  finpow_le_of_allb 2 sub2_01 sub2_11 eq_refl.

(* ... and the two incomparabilities that make it a square and not a
   chain. *)
Lemma sub2_01_not_le_10 : finpow_le sub2_01 sub2_10 → False.
Proof. intro H; discriminate (H (Fin.FS Fin.F1) eq_refl). Qed.

Lemma sub2_10_not_le_01 : finpow_le sub2_10 sub2_01 → False.
Proof. intro H; discriminate (H Fin.F1 eq_refl). Qed.

(* ------------------------------------------------------------------------ *)
(** ** (C) The comparison with the Prop-valued power set *)

Definition finpow_to_subset@{o +} (n : nat) (S : Fin.t (finpow n)) :
  carrier (Powerset_Prop_obj@{o} (Powerset_Prop_fin_object@{o} n)).
Proof.
  unshelve refine
    (@Build_SetoidMorphism@{o o o}
       (Fin.t n) (is_setoid (Powerset_Prop_fin_object@{o} n))
       Prop (is_setoid Powerset_Prop_truth@{o})
       (fun i => finpow_mem S i = true) _).
  intros i j Hij; rewrite Hij; split; exact (fun h => h).
Defined.

(* Monotone, and ORDER-REFLECTING: both directions are the same
   implication read through the definition of [finpow_to_subset]. *)
Lemma finpow_to_subset_mono@{o} (n : nat) (S T : Fin.t (finpow n)) :
  finpow_le S T →
  subset_le (finpow_to_subset@{o} n S) (finpow_to_subset@{o} n T).
Proof. intros H i Hi; exact (H i Hi). Qed.

Lemma finpow_to_subset_reflects@{o} (n : nat) (S T : Fin.t (finpow n)) :
  subset_le (finpow_to_subset@{o} n S) (finpow_to_subset@{o} n T) →
  finpow_le S T.
Proof. intros H i Hi; exact (H i Hi). Qed.

Definition finpow_subset_MonotoneFun@{o +} (n : nat) :
  @MonotoneFun _ (@finpow_le n) _
    (@subset_le@{o} (Powerset_Prop_fin_object@{o} n)) :=
  {| mono_map  := finpow_to_subset@{o} n
   ; mono_pres := finpow_to_subset_mono@{o} n |}.

Definition FinSubsetsToSubsets@{o u +} (n : nat) :
  FinSubsets@{u} n ⟶ Subsets@{o u} (Powerset_Prop_fin_object@{o} n) :=
  Functor_of_monotone (finpow_le_preorder n)
    (subset_le_preorder@{o} (Powerset_Prop_fin_object@{o} n))
    (finpow_subset_MonotoneFun n).

Definition FinSubsetsToSubsets_Faithful@{o u +} (n : nat) :
  Faithful (FinSubsetsToSubsets@{o u} n).
Proof. constructor; intros x y f g _; exact I. Defined.

Definition FinSubsetsToSubsets_Full@{o u +} (n : nat) :
  Full (FinSubsetsToSubsets@{o u} n).
Proof.
  unshelve econstructor.
  - intros x y g; exact (finpow_to_subset_reflects n x y g).
  - intros x y g; exact I.
Defined.

(* ------------------------------------------------------------------------ *)
(** ** (D) The power object at 1 *)

(* The missing member of Instance/FinSet/Topos.v's family: [Pow 0 = 1] and
   [Pow 2 = 4] are there, [Pow 1 = 2] is here.  The GENERAL statement
   [finpow_is_topos_Pow] is Instance/FinSet/Powerset.v:509 and is cited,
   not duplicated. *)
Example FinSet_Pow_one : @Pow FinSet FinSet_Topos 1%nat = 2%nat := eq_refl.

Example FinSet_Omega_is_two :
  @Ω FinSet FinSet_Terminal FinSet_Classifier = 2%nat := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** (E) The internal inclusion order on the power object *)

Definition finpow_subseteq {n : nat} (S T : Fin.t (finpow n)) : bool :=
  fin_allb n (fun i => implb (finpow_mem S i) (finpow_mem T i)).

Lemma finpow_subseteq_iff (n : nat) (S T : Fin.t (finpow n)) :
  finpow_subseteq S T = true ↔ finpow_le S T.
Proof.
  split.
  - exact (finpow_le_of_allb n S T).
  - intro H.
    apply fin_forall_allb; intro i.
    destruct (finpow_mem S i) eqn:HS; simpl.
    + exact (H i HS).
    + reflexivity.
Qed.

(* The underlying function, stated over [finpow] so that the implicit
   arguments of [fin_unpair] are the codes and not the (convertible, but
   syntactically distinct) [Pow] applications.  That distinction is not
   cosmetic: without it, the two occurrences of
   [finpow_subseteq (fst (fin_unpair p)) (snd (fin_unpair p))] in the
   theorem below carry different implicits and no rewrite matches. *)
Definition finpow_subseteq_fn (n : nat)
  (p : Fin.t (finpow n * finpow n)) : Fin.t 2 :=
  fin_of_bool (finpow_subseteq (fst (fin_unpair p)) (snd (fin_unpair p))).

(* The internal order as an ARROW of [FinSet], from the product of the
   power object with itself to Ω. *)
Definition internal_subseteq (n : nat) :
  @product_obj FinSet FinSet_Cartesian
    (@Pow FinSet FinSet_Topos n) (@Pow FinSet FinSet_Topos n)
  ~{FinSet}~> @Ω FinSet FinSet_Terminal FinSet_Classifier :=
  finpow_subseteq_fn n.

Example internal_subseteq_is_fn (n : nat)
  (p : Fin.t (finpow n * finpow n)) :
  internal_subseteq n p = finpow_subseteq_fn n p := eq_refl.

(* THE INTERNAL TEST IS THE EXTERNAL ORDER. *)
Theorem internal_subseteq_spec (n : nat)
  (p : Fin.t (finpow n * finpow n)) :
  internal_subseteq n p = fin_true
    ↔ finpow_le (fst (fin_unpair p)) (snd (fin_unpair p)).
Proof.
  change (internal_subseteq n p) with (finpow_subseteq_fn n p).
  unfold finpow_subseteq_fn.
  (* Generalize the boolean first, so that destructing it rewrites the
     goal and the biconditional together. *)
  generalize (finpow_subseteq_iff n (fst (fin_unpair p))
                (snd (fin_unpair p))).
  destruct (finpow_subseteq (fst (fin_unpair p)) (snd (fin_unpair p)));
    intro Hiff.
  - split; [ intros _; exact (fst Hiff eq_refl) | intros _; reflexivity ].
  - split.
    + intro Hc; discriminate Hc.
    + intro Hle; discriminate (snd Hiff Hle).
Qed.

(* Non-vacuity: the internal test computes, and separates. *)
Example internal_subseteq_true :
  internal_subseteq 2 (fin_pair sub2_10 sub2_11) = fin_true := eq_refl.

Example internal_subseteq_false :
  internal_subseteq 2 (fin_pair sub2_10 sub2_01) = fin_false := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** (F) Example 118: apples and buckets, evaluated *)

(* Two apples in bucket 0, one apple in bucket 1. *)
Definition apples : 3%nat ~{FinSet}~> 2%nat :=
  fun i => match i with
           | Fin.F1        => Fin.F1
           | Fin.FS Fin.F1 => Fin.F1
           | _             => Fin.FS Fin.F1
           end.

Example apples_at_0 : apples Fin.F1 = Fin.F1 := eq_refl.
Example apples_at_1 : apples (Fin.FS Fin.F1) = Fin.F1 := eq_refl.
Example apples_at_2 :
  apples (Fin.FS (Fin.FS Fin.F1)) = Fin.FS Fin.F1 := eq_refl.

(* The preimage on codes ALREADY EXISTS: it is [finpow_map], the arrow
   action of [FinPowerset].  Named, not rebuilt. *)
Definition finpow_preimage {m n : nat} (f : Fin.t n → Fin.t m)
  (T : Fin.t (finpow m)) : Fin.t (finpow n) := finpow_map f T.

Example finpow_preimage_is_finpow_map {m n : nat}
  (f : Fin.t n → Fin.t m) (T : Fin.t (finpow m)) :
  finpow_preimage f T = finpow_map f T := eq_refl.

(* The direct image: bucket j is occupied when SOME apple in S lands in
   it. *)
Definition finpow_image {m n : nat} (f : Fin.t n → Fin.t m)
  (S : Fin.t (finpow n)) : Fin.t (finpow m) :=
  fin_tabulate (fun j : Fin.t m =>
    fin_of_bool
      (fin_anyb n (fun i => andb (fin_eqb (f i) j) (finpow_mem S i)))).

(* The dual image: bucket j is occupied when EVERY apple landing in it is
   already in S.  The EVALUATIONS are this file's; the adjunction it
   satisfies is #384's and is not built here. *)
Definition finpow_dual {m n : nat} (f : Fin.t n → Fin.t m)
  (S : Fin.t (finpow n)) : Fin.t (finpow m) :=
  fin_tabulate (fun j : Fin.t m =>
    fin_of_bool
      (fin_allb n (fun i => implb (fin_eqb (f i) j) (finpow_mem S i)))).

Lemma finpow_image_mem {m n : nat} (f : Fin.t n → Fin.t m)
  (S : Fin.t (finpow n)) (j : Fin.t m) :
  finpow_mem (finpow_image f S) j
    = fin_anyb n (fun i => andb (fin_eqb (f i) j) (finpow_mem S i)).
Proof.
  unfold finpow_mem, finpow_image.
  rewrite fin_apply_tabulate.
  apply finpow_mem_of_bool.
Qed.

Lemma finpow_dual_mem {m n : nat} (f : Fin.t n → Fin.t m)
  (S : Fin.t (finpow n)) (j : Fin.t m) :
  finpow_mem (finpow_dual f S) j
    = fin_allb n (fun i => implb (fin_eqb (f i) j) (finpow_mem S i)).
Proof.
  unfold finpow_mem, finpow_dual.
  rewrite fin_apply_tabulate.
  apply finpow_mem_of_bool.
Qed.

(** ** The six evaluations *)

(* The apples: {0} and {0,1} of the three. *)
Definition apple0 : Fin.t (finpow 3) :=
  fin_tabulate (fun i => match i with
                         | Fin.F1 => fin_true
                         | _      => fin_false
                         end).
Definition apple01 : Fin.t (finpow 3) :=
  fin_tabulate (fun i => match i with
                         | Fin.F1        => fin_true
                         | Fin.FS Fin.F1 => fin_true
                         | _             => fin_false
                         end).

(* Two preimages: the buckets {0} and {1} pulled back to apples. *)
Example preimage_bucket0 :
  finpow_preimage apples sub2_10 = apple01 := eq_refl.

Example preimage_bucket1 :
  finpow_preimage apples sub2_01
    = fin_tabulate (fun i : Fin.t 3 =>
        match i with
        | Fin.F1        => fin_false
        | Fin.FS Fin.F1 => fin_false
        | _             => fin_true
        end) := eq_refl.

(* Two direct images. *)
Example image_apple0 : finpow_image apples apple0 = sub2_10 := eq_refl.
Example image_apple01 : finpow_image apples apple01 = sub2_10 := eq_refl.

(* Two dual images: at {0} the dual is EMPTY, because bucket 0 also holds
   apple 1, which is missing; at {0,1} it is {0}.  This is where the
   dual image visibly differs from the direct image. *)
Example dual_apple0 : finpow_dual apples apple0 = sub2_00 := eq_refl.
Example dual_apple01 : finpow_dual apples apple01 = sub2_10 := eq_refl.

Example image_ne_dual_at_apple0 :
  finpow_image apples apple0 = finpow_dual apples apple0 → False.
Proof. intro H; discriminate H. Qed.

(* ------------------------------------------------------------------------ *)
(** ** Example 117, left half: the preimage has a left adjoint *)

Section FinGalois.

Context {m n : nat}.
Context (f : Fin.t n → Fin.t m).

Lemma finpow_image_mono (S T : Fin.t (finpow n)) :
  finpow_le S T → finpow_le (finpow_image f S) (finpow_image f T).
Proof.
  intros H j Hj.
  rewrite finpow_image_mem in Hj |- *.
  destruct (fin_anyb_exists n _ Hj) as [i Hi].
  apply Bool.andb_true_iff in Hi; destruct Hi as [Hfi HSi].
  refine (fin_exists_anyb n _ i _).
  apply Bool.andb_true_iff; split; [ exact Hfi | exact (H i HSi) ].
Qed.

Lemma finpow_preimage_mono (S T : Fin.t (finpow m)) :
  finpow_le S T → finpow_le (finpow_preimage f S) (finpow_preimage f T).
Proof.
  intros H i Hi.
  unfold finpow_preimage in *.
  rewrite finpow_map_mem in Hi |- *.
  exact (H (f i) Hi).
Qed.

Lemma finpow_image_transpose_to (S : Fin.t (finpow n))
  (T : Fin.t (finpow m)) :
  finpow_le (finpow_image f S) T → finpow_le S (finpow_preimage f T).
Proof.
  intros H i Hi.
  unfold finpow_preimage; rewrite finpow_map_mem.
  refine (H (f i) _).
  rewrite finpow_image_mem.
  refine (fin_exists_anyb n _ i _).
  apply Bool.andb_true_iff; split; [ apply fin_eqb_refl | exact Hi ].
Qed.

Lemma finpow_image_transpose_from (S : Fin.t (finpow n))
  (T : Fin.t (finpow m)) :
  finpow_le S (finpow_preimage f T) → finpow_le (finpow_image f S) T.
Proof.
  intros H j Hj.
  rewrite finpow_image_mem in Hj.
  destruct (fin_anyb_exists n _ Hj) as [i Hi].
  apply Bool.andb_true_iff in Hi; destruct Hi as [Hfi HSi].
  pose proof (H i HSi) as Hp.
  unfold finpow_preimage in Hp; rewrite finpow_map_mem in Hp.
  rewrite <- (fin_eqb_eq _ _ Hfi); exact Hp.
Qed.

Definition finpow_image_preimage_galois :
  GaloisConnection (@finpow_le n) (@finpow_le m) :=
  {| gal_l := finpow_image f
   ; gal_r := finpow_preimage f
   ; gal_mono_l := finpow_image_mono
   ; gal_mono_r := finpow_preimage_mono
   ; gal_to   := finpow_image_transpose_to
   ; gal_from := finpow_image_transpose_from |}.

Definition FinDirectImage@{u} : FinSubsets@{u} n ⟶ FinSubsets@{u} m :=
  GaloisFunctor_l (finpow_le_preorder n) (finpow_le_preorder m)
    finpow_image_preimage_galois.

Definition FinInverseImage@{u} : FinSubsets@{u} m ⟶ FinSubsets@{u} n :=
  GaloisFunctor_r (finpow_le_preorder n) (finpow_le_preorder m)
    finpow_image_preimage_galois.

Definition finpow_image_preimage_adjunction :
  FinDirectImage ⊣ FinInverseImage :=
  GaloisAdjunction (finpow_le_preorder n) (finpow_le_preorder m)
    finpow_image_preimage_galois.

End FinGalois.

Example fin_direct_image_obj (S : Fin.t (finpow 3)) :
  fobj[FinDirectImage apples] S = finpow_image apples S := eq_refl.

Example fin_inverse_image_obj (T : Fin.t (finpow 2)) :
  fobj[FinInverseImage apples] T = finpow_map apples T := eq_refl.
