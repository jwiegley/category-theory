(** * Compact Hausdorff spaces, and the creation of limits

    Mac Lane, Categories for the Working Mathematician, 2nd ed., §V.1
    Exercise 2 (book p. 112, `maclane:V.1:ex2`): the underlying-set functor
    on compact Hausdorff spaces creates limits.  nLab:
    https://ncatlab.org/nlab/show/compact+Hausdorff+space and
    https://ncatlab.org/nlab/show/created+limit.  The classical argument
    has three parts: the product topology on a product of compact
    Hausdorff spaces is compact (Tychonoff) and Hausdorff; a continuous
    bijection from a compact space to a Hausdorff space is a homeomorphism,
    so any other compact Hausdorff topology making the projections
    continuous coincides with the product one; and the two together make
    the lift of a limit unique and limiting.  This file delivers what the
    library's topology can carry of that argument, MEASURES where the rest
    stops, and names the stopping points precisely.

    THREE PREMISES OF THE ISSUE ARE STALE, each re-measured.  The issue's
    "Current state" says there is no category of spaces, no compactness,
    no Hausdorff property and no creation notion.  All four exist:
    [Top] is Instance/Top.v (#259); [IsCompact], [IsHausdorff],
    [CompactHausdorff_Subcategory], [CompactHausdorffSpaces] and
    [CompactHausdorff_Full] are Instance/Top.v:895-968, whose own header
    at :951-955 scopes out exactly the theory asked for here as "out of
    scope for this file"; and [CreatesLimit] is Structure/Limit/Creation.v
    (#406).  So the issue's pinned name [CompHaus] is an ALIAS of an
    existing category, not a construction, and the substance of the
    exercise is the three parts above.

    WHAT IS DELIVERED.
    (A) [CompHaus : Category := CompactHausdorffSpaces], read back at
        [eq_refl]; its inclusion [CompHaus_Incl := Incl Top
        CompactHausdorff_Subcategory] with [CompHaus_Incl_Full] and
        [CompHaus_Incl_Faithful]; the underlying-set functor
        [CompHaus_Forget := Top_Forget ◯ CompHaus_Incl : CompHaus ⟶ Sets]
        with [CompHaus_Forget_Faithful].
    (B) THE BIJECTION THEOREM, constructively and honestly.  For
        [f : X ~{Top}~> Y] with a setoid inverse [g] ([f ∘ g] and [g ∘ f]
        pointwise the identity), [X] compact and [Y] Hausdorff:
        [inverse_open_of_decidable U HU dU : IsOpen Y (fun y => U (g y))]
        for every open [U] of [X] that is DECIDABLE ([dU : ∀ x, U x + ¬U
        x]); [inverse_continuous_of_decidable dec : Continuous Y X g] when
        every open of [X] is; and [compact_hausdorff_bijection_iso dec :
        X ≅[Top] Y].  The decidability is exactly where the classical
        argument decides membership: it covers [X] by [U] together with
        the [f]-preimages of Hausdorff-separating opens around [f c] for
        the points [c] OUTSIDE [U] ([sep_cover_covers], where [dU] decides
        membership; [nbhd_inside] uses it a second time, to decide [U (g
        y')] before deriving the contradiction), takes the finite subcover
        [IsCompact] hands over as
        a list, and intersects the matching separating opens around the
        target point ([nbhd]); that finite intersection is the required
        neighbourhood, and the union of these over the points of the
        preimage is the preimage ([inverse_open_of_decidable]).  [List.In],
        a [Prop], is eliminated only into [False] ([finite_inter_In_False]).
        [IsHausdorff] enters through [sep_nonequal], where [f c ≈ y0] for
        [c] outside [U] would put [c ≈ g y0] inside it — no double-negation
        elimination is needed, contrary to a worry recorded at
        Instance/Top/Kolmogorov.v:224-238 for the Hausdorff ⟹ T0 direction.
        CAVEAT, disclosed and not claimed necessary: [dec] for ALL opens
        holds for no INHABITED space in the tree — [Discrete_Top]'s opens
        are all the [≈]-respecting predicates ([discrete_open],
        Instance/Top.v:292), so [dec] there is decidability of every such
        predicate — while the empty space [Empty_Top] (Instance/Top.v:471)
        satisfies it vacuously and does instantiate both theorems (measured
        by an audit); so the per-open lemma is the form with non-vacuous
        content, and the probe applies it at the one-point space with the
        identity and the whole open.
    (C) THE TRUNCATED PRODUCT TOPOLOGY, the furthest formable point of the
        Tychonoff half.  [Top] has no products: the natural product
        openness predicate — an existential over opens of the two factors —
        lives one universe above the points and is REFUSED at the space's
        level (Test/ProbeCoproduct.v N9, Instance/Top/Homotopy.v:86-97).
        Instance/Top/Coproduct.v:90-99 names one escape hatch it did not
        try, the impredicative truncation [Powerset_squash] of
        Instance/Sets/Powerset.v.  It is tried here: [sq_open W] is "[W]
        respects [≈], and every point of [W] has a SQUASHED box datum
        ([sq_boxdata], a [Type@{o1}] with [o < o1]) inside [W]"; the squash
        is a [Prop], so [sq_open : (sq_carrier → Type@{o}) → Type@{o}] fits,
        and [Top_sq_product X Y : TopSpace@{o}] closes all five topology
        fields (unions and intersections of squashed boxes by [sq_squash_map]
        and [sq_squash_pair]).  Its projections [Top_sq_fst], [Top_sq_snd]
        are continuous (a box [U × whole]).  WHAT STOPS, compiled in the
        probe: the pairing [sq_fork_map f g] exists on points, but its
        continuity would eliminate the squash into the [Type]-valued
        [IsOpen Z] — refused, the eliminator's motive must be a [Prop]
        ("Cannot enforce o <= Prop"), while eliminating into [True] is
        accepted; and the other route, a union over ALL boxes inside [W],
        is refused because [sq_boxdata] sits at [o1] and [open_union]
        indexes at [o].  So [Top_sq_product] has projections but no
        universal property is ESTABLISHED here: the two routes tried are
        refused, and it is not shown that every encoding is refused
        (Instance/Top/Coproduct.v:85-97 records the same over-read in an
        earlier draft of its own header) — and its compactness (Tychonoff)
        is NOT attempted: its finite subcovers would be [Type]-level data
        extracted from squashed boxes, so it is expected behind the same
        wall by the same argument, asserted rather than compiled. This is a
        measured refinement of Coproduct.v's note: the truncated encoding
        elaborates AND yields a space, and the wall moves to the fork.
    (D) CREATION.  Two facts, one positive and one conditional:
        - The issue's pinned statement [CreatesLimit K CompHaus_Forget] IS
          FORMABLE, for a diagram [K] out of any shape [J] (the probe checks
          it, with [J : Category] left to inference). A survey read
          Instance/Top/Forgetful.v:315-336 as saying it is not, and that note's
          own last sentence did generalize its stratification claim to
          [Top_Forget] by name — false there, since [Top_Forget] lands in
          [Sets@{h so}], whose hom level is [Top]'s own, so the limit-cone
          predicates apply on both sides; the sentence is corrected in place,
          line-neutrally, in this commit. What is NOT delivered is its proof:
          [creates_lift] must produce a COMPACT HAUSDORFF apex over an
          arbitrary limiting cone of setoids, which is Tychonoff plus the
          Hausdorff property of the lift, and [creates_reflect] must make the
          mediator continuous into the lifted topology, which is the fork wall
          of (C).
        - The generic lemma Construction/Subcategory/Creation.v adds — a FULL
          subcategory whose objects are CLOSED under the ambient limits is
          created into by its inclusion ([sub_CreatesLimit], [sub_Complete]) —
          is applied at [CompactHausdorff_Subcategory] as
          [CompHaus_Incl_CreatesLimit closed K] and [CompHaus_Complete_of
          closed HT], CONDITIONALS on [closed : ClosedUnderLimits
          CompactHausdorff_Subcategory] and [HT : Complete Top]. Both
          hypotheses are unwitnessed in the tree: [Top] has no limits beyond
          [Top_Terminal] to be closed under, and no [Top_Complete] exists. They
          are the statements the exercise's conclusion would follow from,
          stated at the inclusion, not at the forgetful functor.

    NOT DELIVERED, in the issue's own terms.  (a) Tychonoff at ANY index
    generality — not even the binary product has its universal property
    (see (C)); (c) the PROOF of [CreatesLimit K CompHaus_Forget] (see
    (D)); (d) [CompHaus_Complete] unconditionally (the conditional
    [CompHaus_Complete_of] is what stands); a [Cartesian Top]; compactness
    of a SUBSET ([IsCompact] is whole-space); the closed-map form of (B);
    any necessity result for [dec]; any witness of [ClosedUnderLimits], or
    an inhabited witness of [dec] for all opens; and nothing registered as
    an [Instance]
    ([CompHaus_Forget_Faithful] and [CompHaus_Incl_Faithful] are lemmas,
    following Structure/Limit/Creation.v:125-128's discipline for creation
    witnesses).  The Stone–Čech adjoint and the ultrafilter monad, the
    reasons the roster lists this category (Instance/Roster.v:158-169),
    remain as that note leaves them.

    UNIVERSES, MEASURED OFF BOTH BINDER AND BLOCK OVER ALL 48 CONSTANTS
    OF THIS FILE (and the 9 of Construction/Subcategory/Creation.v).
    ZERO word-bounded [Set] in any of the 57 blocks.  The truncated-product
    constants are the small ones: [Top_sq_product@{o o1} : TopSpace@{o} →
    TopSpace@{o} → TopSpace@{o}] with the single named bound [o < o1] (the
    box datum's level) plus stdlib caps; [Top_sq_fst@{o o1 u}] adds [Top]'s
    hom level [o < u].  The bijection constants carry two block equations:
    [u3 = u1] (the two list universes, [finite_inter]'s and the
    subcover's, on [sep_subcover_covers], [nbhd_inside] — printed there as
    [u1 = u3] —,
    [inverse_open_of_decidable], [inverse_continuous_of_decidable],
    [compact_hausdorff_bijection_iso]) and [u9 = u8] (the open's level is
    the carrier's, on the last two); the forty-three others carry NONE.
    In Creation.v, [sub_lift], [sub_lift_apex], [sub_lift_leg],
    [sub_cone_iso] and [sub_CreatesLimit] carry five equations — [u0 = u11]
    identifies the ambient hom universe with the shape's
    (Structure/Limit/Preservation.v's [IsLimitCone] pin, inherited) and
    [u0 = u13] with [Sub]'s ([Compose] types its three categories at one
    hom universe, so [Incl C S ◯ K] imposes it — an audit isolated the two
    causes), and [u5 = u12], [u6 = u14], [u9 = u10] identify the closure
    hypothesis' quantified shape and [Sub] levels with the diagram's: the
    hypothesis is consumed at the diagram's own universe instance —
    [sub_ReflectsLimitCone] carries the first two only, and
    [ClosedUnderLimits], [sub_CreatesAllLimits], [sub_Complete] none.

    COUNTS.  57/57 constants (48 here: 24 [Definition], 20 [Lemma], 2
    [Theorem], 1 [Example], 1 [Fixpoint]; 9 there: 7 [Definition], 2
    [Example]) closed under the global context with ZERO [Axioms:] lines,
    all in the [make print-assumptions] gate FULLY QUALIFIED; no [Program]
    anywhere.  Seven [Defined]-terminated proofs, FIVE load-bearing by
    flipping each alone to [Qed] and recompiling both files and the probe:
    [Top_sq_product] (this file stops at [sq_fst_continuous]'s statement,
    which needs the product's carrier to unfold), [sq_fst_map] and
    [sq_snd_map] (the projections' continuity proofs unfold the morphism
    field), [compact_hausdorff_bijection_iso] (the probe's readback of its
    forward map), and Creation.v's [sub_lift] (its own [eq_refl] readbacks
    [sub_lift_apex]/[sub_lift_leg]); [sq_fork_map] and [sub_cone_iso] flip
    with everything green and are kept [Defined] by the data convention.
    Closure 52 modules excluding self — Construction/Subcategory/Creation.v
    costs 10 at the margin (it brings Theory/Equivalence/Limit.v),
    Instance/Sets/Powerset.v 3, Instance/Top/Forgetful.v 1, each of the
    other sixteen [Category.*] [Require]s 0 (nineteen in all, each dropped
    alone); Creation.v's own closure is 35 (Theory/Equivalence/Limit.v
    costs 10, Structure/Limit/Creation.v 3, Construction/Subcategory.v 1,
    the other eight 0).  Zero collisions over the 57 names (the
    section-local cover constants are prefixed [sep_] because the bare
    words [cover]/[subcover] occur in prose across the tree).

    Test/ProbeCompHaus413.v mirrors this file's [Require] list and carries
    5 refutation commands = 1 instrument check + 4 negatives of THREE kinds
    told apart by their messages — N1 and N2 both say "universe
    inconsistency", and are told apart by "expected to have type Prop"
    against "because o < …": N1 SORT/TYPING (the fork's continuity by
    eliminating the squash into [IsOpen Z]: "has type Type while it is
    expected to have type Prop", with the clause "Cannot enforce o <=
    Prop"; control: elimination into [True] accepted), N2 UNIVERSE (the
    union over all boxes: the index's level strictly above [o]; control: a
    union indexed by the points accepted), N3 TYPING ([CompHaus_Forget]
    ascribed at [CompHaus ⟶ Top], a plain has-type mismatch) and N4 TYPING
    ([compact_hausdorff_bijection_iso] without [dec] ascribed at [X ≅ Y]:
    it still has a function type) — each stripped ONE AT A TIME in a copy
    of the whole file and compiled alone with its error read; the POSITIVE
    formability of [CreatesLimit K CompHaus_Forget]; readbacks at [eq_refl]
    of the alias, the inclusion's object map, both projections on points,
    the isomorphism's forward map and the generic lift's apex and legs;
    the one-point non-vacuity of (B); guard coverage measured mechanically
    under the plain tokenization (comment-stripped, every identifier token
    inside a refutation command other than the keywords and the wildcard):
    31 identifiers inside, 29 also outside, the two exceptions exhaustively
    the instrument's absent name and the bound variable [z] of N1's lambda;
    rename-simulated 7/7 over the target constants the negatives name, each
    rename applied in THIS file only and every break landing on a [Check]
    line of the probe, none inside a refutation command.  [make todo] grows
    by 5 lines, ALL the probe's refutation commands; this file and
    Creation.v contribute ZERO. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Subcategory.Creation.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Coq.Lists.List.

Generalizable All Variables.

(** * The category, under the issue's name *)

Definition CompHaus : Category := CompactHausdorffSpaces.

Example CompHaus_is_CompactHausdorffSpaces :
  CompHaus = CompactHausdorffSpaces := eq_refl.

Definition CompHaus_Incl : CompHaus ⟶ Top :=
  Incl Top CompactHausdorff_Subcategory.

Lemma CompHaus_Incl_Full : Functor.Full CompHaus_Incl.
Proof. exact (Full_Implies_Full_Functor Top _ CompactHausdorff_Full). Qed.

Lemma CompHaus_Incl_Faithful : Functor.Faithful CompHaus_Incl.
Proof. exact (Incl_Faithful Top _). Qed.

(** * A continuous bijection from a compact space to a Hausdorff space *)

Section Bijection.
Context {X Y : TopSpace} (f : X ~{Top}~> Y)
        (g : SetoidMorphism (top_carrier Y) (top_carrier X))
        (Hfg : ∀ y : Y, continuous_map f (g y) ≈ y)
        (Hgf : ∀ x : X, g (continuous_map f x) ≈ x)
        (HX : IsCompact X) (HY : IsHausdorff Y).

(* Finite intersections of a list-indexed family of opens of [Y]. *)
Fixpoint finite_inter {I : Type} (B : I → Y → Type) (l : list I) : Y → Type :=
  match l with
  | nil => fun _ => poly_unit
  | cons i l' => fun y => (B i y ∧ finite_inter B l' y)%type
  end.

Lemma finite_inter_open {I : Type} (B : I → Y → Type)
  (HB : ∀ i, IsOpen Y (B i)) (l : list I) : IsOpen Y (finite_inter B l).
Proof using.
  induction l; simpl.
  - apply open_whole.
  - apply open_inter; [apply HB | exact IHl].
Qed.

Lemma finite_inter_all {I : Type} (B : I → Y → Type) (l : list I) (y : Y) :
  (∀ i, B i y) → finite_inter B l y.
Proof using.
  induction l; simpl; intro H.
  - exact ttt.
  - split; [apply H | exact (IHl H)].
Qed.

(* The one use of [List.In], a [Prop], eliminated only into [False]. *)
Lemma finite_inter_In_False {I : Type} (B : I → Y → Type) (l : list I)
  (y : Y) :
  finite_inter B l y → ∀ i, In i l → (B i y → False) → False.
Proof using.
  induction l; simpl; intros H i Hi nb.
  - exact Hi.
  - destruct Hi as [e | Hi].
    + subst; exact (nb (fst H)).
    + exact (IHl (snd H) i Hi nb).
Qed.

Section Open.
Context (U : X → Type) (HU : IsOpen X U)
        (dU : ∀ x : X, U x + (U x → False)).

(* The complement of [U], as a type of points. *)
Definition compl_pts : Type := { c : X & U c → False }.

Section Point.
Context (y0 : Y) (hy0 : U (g y0)).

Lemma sep_nonequal (c : compl_pts) : continuous_map f (`1 c) ≈ y0 → False.
Proof using Hgf HU hy0.
  intro e. apply (`2 c).
  apply (open_proper X U HU (g y0) (`1 c)).
  - rewrite <- (Hgf (`1 c)). apply (proper_morphism g). symmetry. exact e.
  - exact hy0.
Qed.

Definition sepA (c : compl_pts) : Y → Type := `1 (HY _ y0 (sep_nonequal c)).
Definition sepB (c : compl_pts) : Y → Type :=
  `1 (`2 (HY _ y0 (sep_nonequal c))).

Lemma sepA_open (c : compl_pts) : IsOpen Y (sepA c).
Proof using. exact (fst (fst (`2 (`2 (HY _ y0 (sep_nonequal c)))))). Qed.
Lemma sepB_open (c : compl_pts) : IsOpen Y (sepB c).
Proof using. exact (snd (fst (`2 (`2 (HY _ y0 (sep_nonequal c)))))). Qed.
Lemma sepA_at (c : compl_pts) : sepA c (continuous_map f (`1 c)).
Proof using. exact (fst (fst (snd (`2 (`2 (HY _ y0 (sep_nonequal c))))))). Qed.
Lemma sepB_at (c : compl_pts) : sepB c y0.
Proof using. exact (snd (fst (snd (`2 (`2 (HY _ y0 (sep_nonequal c))))))). Qed.
Lemma sep_disjoint (c : compl_pts) (z : Y) : sepA c z → sepB c z → False.
Proof using. exact (snd (snd (`2 (`2 (HY _ y0 (sep_nonequal c))))) z). Qed.

(* The sep_cover of [X]: the preimages of the separating opens, plus [U]. *)
Definition sep_cover_idx : Type := (compl_pts + poly_unit)%type.
Definition sep_cover (i : sep_cover_idx) : X → Type :=
  match i with
  | inl c => fun x => sepA c (continuous_map f x)
  | inr _ => U
  end.

(* This is where membership in [U] is decided. *)
Lemma sep_cover_covers : Covers sep_cover (fun _ => poly_unit).
Proof using HU dU f.
  split.
  - intros [c | u]; simpl.
    + exact (continuity f (sepA c) (sepA_open c)).
    + exact HU.
  - intro x; split.
    + intros _. destruct (dU x) as [u | n].
      * exists (inr ttt); exact u.
      * exists (inl (x; n)); exact (sepA_at (x; n)).
    + intros _; exact ttt.
Qed.

Definition sep_subcover : list sep_cover_idx :=
  `1 (HX sep_cover_idx sep_cover sep_cover_covers).
Definition sep_subcover_covers :
  ∀ x : X, ∃ i : sep_cover_idx, (In i sep_subcover ∧ sep_cover i x)%type :=
  `2 (HX sep_cover_idx sep_cover sep_cover_covers).

(* The [Y]-side family: the separating opens around [y0]; nothing for [U]. *)
Definition sep_fam (i : sep_cover_idx) : Y → Type :=
  match i with
  | inl c => sepB c
  | inr _ => fun _ => poly_unit
  end.

Definition nbhd : Y → Type := finite_inter sep_fam sep_subcover.

Lemma nbhd_open : IsOpen Y nbhd.
Proof using.
  apply finite_inter_open. intros [c | u]; simpl.
  - exact (sepB_open c).
  - exact (open_whole Y).
Qed.

Lemma nbhd_at : nbhd y0.
Proof using.
  apply finite_inter_all. intros [c | u]; simpl.
  - exact (sepB_at c).
  - exact ttt.
Qed.

Lemma nbhd_inside (y' : Y) : nbhd y' → U (g y').
Proof using Hfg HU dU.
  intro hn. destruct (dU (g y')) as [u | n]; [exact u | exfalso].
  destruct (sep_subcover_covers (g y')) as [i [Hin w]].
  destruct i as [c | u]; simpl in w.
  - refine (finite_inter_In_False sep_fam sep_subcover y' hn (inl c) Hin _).
    intro b. apply (sep_disjoint c y').
    + apply (open_proper Y (sepA c) (sepA_open c)
               (continuous_map f (g y')) y').
      * exact (Hfg y').
      * exact w.
    + exact b.
  - exact (n w).
Qed.

End Point.

Theorem inverse_open_of_decidable : IsOpen Y (fun y => U (g y)).
Proof using Hfg Hgf HU HX HY dU f g.
  apply (open_respects Y
           (fun y => { yp : { y0 : Y & U (g y0) } & nbhd (`1 yp) (`2 yp) y })).
  - intro y; split.
    + intros [yp hn]. exact (nbhd_inside (`1 yp) (`2 yp) y hn).
    + intro v. exists (y; v). exact (nbhd_at y v).
  - apply (open_union Y { y0 : Y & U (g y0) }
             (fun yp => nbhd (`1 yp) (`2 yp))).
    intro yp. exact (nbhd_open (`1 yp) (`2 yp)).
Qed.

End Open.

Theorem inverse_continuous_of_decidable
  (dec : ∀ U : X → Type, IsOpen X U → ∀ x : X, U x + (U x → False)) :
  Continuous Y X g.
Proof using Hfg Hgf HX HY f g.
  intros U HU. exact (inverse_open_of_decidable U HU (dec U HU)).
Qed.

Definition compact_hausdorff_bijection_iso
  (dec : ∀ U : X → Type, IsOpen X U → ∀ x : X, U x + (U x → False)) :
  X ≅[Top] Y.
Proof using Hfg Hgf HX HY f g.
  unshelve refine
    {| to := f
     ; from := Build_ContinuousMorphism Y X g
                 (inverse_continuous_of_decidable dec) |}.
  - intro y; simpl. exact (Hfg y).
  - intro x; simpl. exact (Hgf x).
Defined.

End Bijection.

(** * The truncated product topology: the furthest formable point of (a) *)

Section SquashProduct.

Universe o o1.
Constraint o < o1.
Context (X Y : TopSpace@{o}).

Definition sq_carrier : SetoidObject@{o o} := {|
  carrier := (carrier (top_carrier X) * carrier (top_carrier Y))%type;
  is_setoid := prod_setoid
|}.

(* A box around [p] inside [W]: opens of the factors, data at level [o1]. *)
Definition sq_boxdata (W : sq_carrier → Type@{o}) (p : sq_carrier) :
  Type@{o1} :=
  { U : carrier (top_carrier X) → Type@{o} &
  { V : carrier (top_carrier Y) → Type@{o} &
    (IsOpen X U ∧ IsOpen Y V ∧ U (fst p) ∧ V (snd p)
       ∧ (∀ q : sq_carrier, U (fst q) → V (snd q) → W q))%type } }.

(* Squashed into a [Prop], the box datum fits at level [o]. *)
Definition sq_open (W : sq_carrier → Type@{o}) : Type@{o} :=
  ((∀ x y : sq_carrier, x ≈ y → W x → W y)
   ∧ (∀ p : sq_carrier, W p → Powerset_squash@{o1} (sq_boxdata W p)))%type.

Lemma sq_squash_map {A B : Type@{o1}} (f : A → B) :
  Powerset_squash@{o1} A → Powerset_squash@{o1} B.
Proof using. intros s Q k; exact (s Q (fun a => k (f a))). Qed.

Lemma sq_squash_pair {A B : Type@{o1}} :
  Powerset_squash@{o1} A → Powerset_squash@{o1} B →
  Powerset_squash@{o1} (A * B)%type.
Proof using.
  intros a b Q k; exact (a Q (fun x => b Q (fun y => k (x, y)))).
Qed.

Definition Top_sq_product : TopSpace@{o}.
Proof using X Y.
  unshelve refine {| top_carrier := sq_carrier; IsOpen := sq_open |}.
  - (* open_respects *)
    intros U V H [Hp Hb]; split.
    + intros x y e u. apply (fst (H y)). apply (Hp x y e). apply (snd (H x)).
      exact u.
    + intros p v. apply (sq_squash_map (A := sq_boxdata U p)).
      * intros [U0 [V0 [oU [oV [u0 [v0 inside]]]]]].
        exists U0; exists V0. repeat split; try assumption.
        intros q0 a0 b0. apply (fst (H q0)). exact (inside q0 a0 b0).
      * apply Hb. apply (snd (H p)). exact v.
  - (* open_proper *)
    intros U [Hp _] x y e u. exact (Hp x y e u).
  - (* open_union *)
    intros I U HU; split.
    + intros x y e [i u]. exists i. exact (fst (HU i) x y e u).
    + intros p [i u]. apply (sq_squash_map (A := sq_boxdata (U i) p)).
      * intros [U0 [V0 [oU [oV [u0 [v0 inside]]]]]].
        exists U0; exists V0. repeat split; try assumption.
        intros q0 a0 b0. exists i. exact (inside q0 a0 b0).
      * exact (snd (HU i) p u).
  - (* open_whole *)
    split.
    + intros; exact ttt.
    + intros p _. apply Powerset_squash_intro.
      exists (fun _ => poly_unit); exists (fun _ => poly_unit).
      repeat split; try exact ttt; try apply open_whole.
  - (* open_inter *)
    intros U V [HpU HbU] [HpV HbV]; split.
    + intros x y e [u v]. split; [exact (HpU x y e u) | exact (HpV x y e v)].
    + intros p [u v].
      apply (sq_squash_map (A := (sq_boxdata U p * sq_boxdata V p)%type)).
      * intros [[U0 [V0 [oU0 [oV0 [u0 [v0 in0]]]]]]
                [U1 [V1 [oU1 [oV1 [u1 [v1 in1]]]]]]].
        exists (fun a => (U0 a ∧ U1 a)%type);
        exists (fun b => (V0 b ∧ V1 b)%type).
        split; [apply open_inter; assumption |].
        split; [apply open_inter; assumption |].
        split; [split; assumption |].
        split; [split; assumption |].
        intros q0 [a0 a1] [b0 b1].
        split; [exact (in0 q0 a0 b0) | exact (in1 q0 a1 b1)].
      * apply sq_squash_pair; [exact (HbU p u) | exact (HbV p v)].
Defined.

Definition sq_fst_map : SetoidMorphism sq_carrier (top_carrier X).
Proof using X Y.
  unshelve notypeclasses refine {| morphism := fun p : sq_carrier => fst p |}.
  intros u v Huv; exact (fst Huv).
Defined.

Definition sq_snd_map : SetoidMorphism sq_carrier (top_carrier Y).
Proof using X Y.
  unshelve notypeclasses refine {| morphism := fun p : sq_carrier => snd p |}.
  intros u v Huv; exact (snd Huv).
Defined.

Lemma sq_fst_continuous : Continuous Top_sq_product X sq_fst_map.
Proof using X Y.
  intros U HU; split.
  - intros x y [e _] u. exact (open_proper X U HU (fst x) (fst y) e u).
  - intros p u. apply Powerset_squash_intro.
    exists U; exists (fun _ => poly_unit).
    repeat split; try assumption; try apply open_whole; try exact ttt.
    intros q0 a0 _; exact a0.
Qed.

Lemma sq_snd_continuous : Continuous Top_sq_product Y sq_snd_map.
Proof using X Y.
  intros V HV; split.
  - intros x y [_ e] v. exact (open_proper Y V HV (snd x) (snd y) e v).
  - intros p v. apply Powerset_squash_intro.
    exists (fun _ => poly_unit); exists V.
    repeat split; try assumption; try apply open_whole; try exact ttt.
    intros q0 _ b0; exact b0.
Qed.

Definition Top_sq_fst : Top_sq_product ~{Top}~> X :=
  Build_ContinuousMorphism Top_sq_product X sq_fst_map sq_fst_continuous.

Definition Top_sq_snd : Top_sq_product ~{Top}~> Y :=
  Build_ContinuousMorphism Top_sq_product Y sq_snd_map sq_snd_continuous.

(* The pairing exists at the level of setoids; its CONTINUITY is what the
   probe pins as refused. *)
Definition sq_fork_map {Z : TopSpace@{o}}
  (f : Z ~{Top}~> X) (g : Z ~{Top}~> Y) :
  SetoidMorphism (top_carrier Z) sq_carrier.
Proof using X Y.
  unshelve notypeclasses refine
    {| morphism := fun z => (continuous_map f z, continuous_map g z) |}.
  intros u v Huv; split.
  - exact (proper_morphism (continuous_map f) u v Huv).
  - exact (proper_morphism (continuous_map g) u v Huv).
Defined.

End SquashProduct.

(** * The forgetful functor, and creation *)

Definition CompHaus_Forget := Top_Forget ◯ CompHaus_Incl.

Lemma CompHaus_Forget_Faithful : Functor.Faithful CompHaus_Forget.
Proof.
  constructor; intros X Y h k E.
  apply (@fmap_inj _ _ _ CompHaus_Incl_Faithful X Y h k).
  apply (@fmap_inj _ _ _ Top_Forget_Faithful _ _ _ _).
  exact E.
Qed.

(* Creation by the INCLUSION, from the generic lemma, under closure of the
   compact Hausdorff predicate under the limits of [Top]. *)
Definition CompHaus_Incl_CreatesLimit
  (closed : ClosedUnderLimits CompactHausdorff_Subcategory)
  {J : Category} (K : J ⟶ CompHaus) : CreatesLimit K CompHaus_Incl :=
  sub_CreatesLimit CompactHausdorff_Subcategory CompactHausdorff_Full closed K.

Definition CompHaus_Complete_of
  (closed : ClosedUnderLimits CompactHausdorff_Subcategory)
  (HT : @Complete Top) : @Complete CompHaus :=
  sub_Complete CompactHausdorff_Subcategory CompactHausdorff_Full closed HT.
