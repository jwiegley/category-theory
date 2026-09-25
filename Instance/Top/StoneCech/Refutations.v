Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Structure.WellPowered.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.CompHaus.
Require Import Category.Instance.Top.StoneCech.
Require Import Category.Adjunction.GAFT.
Require Import Category.Adjunction.SAFT.
Require Import Category.Adjunction.SAFT.Characterization.
Require Import Coq.Lists.List.

Generalizable All Variables.

(* Why the adjoint functor theorems give no Stone–Čech over [Top]

   Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
   §V.2 Proposition 3, book p. 114 (maclane:V.2:prop3), Freyd's theorem
   that a small complete category is a preorder, consumed through
   Structure/Complete/Freyd.v; §V.6 and §V.8 as in the header of
   Instance/Top/StoneCech.v, which this file completes.
   nLab: https://ncatlab.org/nlab/show/complete+small+category
   nLab: https://ncatlab.org/nlab/show/Stone-Cech+compactification

   BACKGROUND.  Freyd's observation (Structure/Complete/Freyd.v's header):
   were a category with products indexed by its own arrow collection K to
   carry two distinct parallel arrows, the 2^K choices between them would
   give 2^K arrows into the K-fold power, more than the K arrows there are.
   So completeness in the book's sense is a property of LARGE categories,
   and the adjoint functor theorems ask for it at shapes the size of the
   homs.  Instance/Top/StoneCech.v's header explains why [Top] and
   [CompHaus] are small at their own hom universe: their homs sit strictly
   above the points (o < h), and a whole space is a [TopSpace@{o}] of type
   [Type@{o+1}], at or below h.  This file turns that into theorems.
   Nothing here is an axiom.  Informative excluded middle ([IEM],
   Instance/Sets/Classifier/OneLevel.v) and arrow indices ([ArrowIndex],
   Structure/Complete/Freyd.v) are hypotheses; [IEM] holds classically,
   and under it an [ArrowIndex] exists ([canonical_ArrowIndex] of
   [ObjDecEq_of_IEM]).

   WHAT IS REFUTED.
   (1) Completeness.  [CompHaus_not_complete]: given an [ArrowIndex] of
       [CompHaus] at shape universe [s], [Complete@{r s h c} CompHaus] is
       false.  The two points [sc_pt_bool true] and [sc_pt_bool false] of
       the two-point discrete space are told apart by evaluation at the
       point ([sc_eval_pt]), constructively, and Freyd's core
       [freyd_no_separated_pair] refutes the power of [Bool_CH] at the index
       that completeness supplies ([complete_iprod]).
       [CompHaus_not_complete_IEM]: under [IEM], at every shape universe
       with [c <= s] and [h <= s], which includes the one GAFT uses at
       [CompHaus_Forget] (all four universes [h]) and every one SAFT uses at
       [CompHaus_Incl] with the tree's well-powering (see (3)), at the
       instances COVERAGE records.
       [Top_not_complete] and [Top_not_complete_IEM]: the same for [Top], at
       every [s] with [h <= s], so the hypothesis [HT : Complete Top] of
       Instance/Top/CompHaus.v's [CompHaus_Complete_of] is refuted at those
       shapes as well (that file's (D) carries the correction).
       [CompHaus_ArrowIndex_of_Top]: an arrow index of [Top] at [s] is one
       of [CompHaus] at [s], at every universe [c >= h] of its objects
       (About), because [Sub]'s homs are [Top]'s paired with [True] and the
       index never mentions an object.  Through it, applied to
       [canonical_ArrowIndex] of [Top], [CompHaus_not_complete_IEM_below]
       refutes [Complete@{r s h c} CompHaus] under [IEM] at every shape
       universe with [h <= s], the shapes below the objects included, and
       [CompHaus_not_complete_IEM_above] is its case at GAFT's shape
       [Complete@{h h h c}] with the objects at or above the homs.  COVERAGE
       below records which instances each form reaches.
   (2) The adjunction at [CompHaus_Forget].
       [large_universal_arrow_refuted]: there is no universal arrow from
       the arrow-index set [KSet AI], at the hom universe, to
       [CompHaus_Forget].  The unique extensions along it of the maps
       φ : K → bool are arrows from the universal object to [Bool_CH],
       each encoded as an element of K; reading them back at the unit
       gives a surjection K → (K → bool), which Freyd.v's
       [freyd_cantor_bool] refutes.  [StoneCech_adjunction_refuted_IEM]:
       under [IEM], at the instance with the objects of [CompHaus] at its
       hom universe [h], no functor [F : Sets@{h s} ⟶ CompHaus] is left
       adjoint to [CompHaus_Forget], which is the type
       [GAFT_CompHaus_only_complete] concludes.
       [StoneCech_adjunction_refuted_IEM_above]: the same at every object
       universe [c] at or above [h], at the instances COVERAGE records,
       through [CompHaus_ArrowIndex_of_Top]; below [h] the adjunction is
       not formable, [CompHaus_Forget] carrying [h <= c] (About).  The
       universal arrows at SMALL sets are untouched:
       Instance/Top/StoneCech.v's [StoneCech_finite] builds them at every
       finitely enumerable setoid at the points' universe; the refutation
       needs a set at the hom universe, and the domain [Sets@{h s}] of any
       left adjoint to [CompHaus_Forget] contains one.  The §V.8 adjunction
       at [CompHaus_Incl] is NOT refuted, and classically it holds: the
       domain [Top@{h o}] of a left adjoint to the inclusion has its
       points at [o], strictly below [h], so it offers no object as large
       as the arrow collection and the argument does not apply.  Only
       SAFT's route to that adjunction is vacuous, by (3).
   (3) The vacuity pairs, each consuming ONE completeness hypothesis twice:
       [GAFT_CompHaus_IEM_vacuous] ([GAFT_CompHaus_only_complete] against
       [CompHaus_not_complete_IEM]), and [SAFT_Incl_vacuous] and
       [SAFT_Incl_IEM_vacuous] (Adjunction/SAFT/Characterization.v's
       [SAFT_wellpowered] at [CompHaus_Incl], against the refutation by an
       index or by [IEM]).  The SAFT side's reduction is recorded as well:
       [CompHaus_WellPowered] is Structure/WellPowered.v's [trivial_small]
       at [CompHaus] (a category whose objects fit at its hom universe is
       well-powered by the trivial index), and [SAFT_CompHaus_Incl] is SAFT
       at the inclusion with well-poweredness discharged, three hypotheses
       remaining: completeness, continuity and a cogenerator.  Discharging
       it forces [c = h] (a block equation, measured by About with [c] and
       [h] named separately; Test/ProbeStoneCech455.v pins its
       consequences), so every shape universe SAFT accepts there satisfies
       [c <= s] and [h <= s], and (1)'s [IEM] form covers it at the
       instances COVERAGE records.  [SAFT_CompHaus_Incl] is a conditional
       at more instances than those: it is accepted with the proof slot
       below the objects' universe, and with the fourteenth and fifteenth
       slots below the points' universe, where every refutation here is
       refused (measured by #455's review), and there its completeness
       premise stays classically false, the objects' points still sitting
       at [o] (a meta-argument; NOT DELIVERED).  The two halves of the
       equation have different sources.  [c <= h] is
       [CompHaus_WellPowered]'s: Structure/WellPowered.v's [WellPowered]
       declares the objects at or below its index, and [trivial_small]
       indexes at the hom universe.  [h <= c] is the inclusion's, under ANY
       well-powering: [CompHaus_Incl] carries it (About), and SAFT at the
       inclusion with a well-powering hypothesis is refused at [c < h] as
       well (the probe's N19).  Under a well-powering other than
       [CompHaus_WellPowered] the shape can lie below the objects, and
       [SAFT_Incl_IEM_vacuous_below] covers that: it consumes (1)'s
       [CompHaus_not_complete_IEM_below], at every shape universe SAFT
       accepts at the inclusion, at the instances COVERAGE records.  On
       the GAFT side, [taut_sols] fits GAFT
       only with the objects at [h] (the probe's N9), so
       [GAFT_CompHaus_IEM_vacuous_above] takes the solution sets as a
       hypothesis and pairs GAFT at [CompHaus_Forget] against
       [CompHaus_not_complete_IEM_above] at every object universe at or
       above the homs.
   (4) An obstruction with no hypothesis beyond completeness (no [IEM],
       no arrow index).  [big_inj] and [big_inj_injective]: from
       [Complete@{r s h c} CompHaus] alone, an injection of
       [obj[CompHaus] → bool] into the points of a single space, the power
       of [Bool_CH] over all objects.  The index is the object type of the
       very category [comp] is about: the local definition [C := CompHaus]
       ties the two, and the block carries [c <= s].  Written with
       [obj[CompHaus]] in both places instead, the two elaborate at
       separate instances and the block has no [c <= s] (measured by
       About; Test/ProbeStoneCech455.v pins its consequences), so the
       index could be
       the objects of a smaller [CompHaus].  In a set-theoretic model
       where the points' universe is a Grothendieck universe V_κ, every
       inhabited set in V_κ, carried with the total equivalence, is a
       compact Hausdorff space (compact by one index, separated
       vacuously), so there are at least κ objects, while the points of
       one space form a set below κ; by Cantor no such injection exists,
       and [Complete@{r s h c} CompHaus] is false there.  That is a
       meta-argument, not a theorem of this file: the tree has no cardinal
       arithmetic, and the injection is what is proved.
   (5) The cogenerator premise.  [CompHaus_cogenerator_stable_DNE]: any
       [Cogenerator CompHaus] (Adjunction/SAFT.v) whose members have
       ¬¬-stable equality of points yields double-negation elimination for
       every proposition.  The gadget is [YP_CH P], the two-point discrete
       space whose equality is [x = y ∨ P] ([sc_YP]), compact and Hausdorff
       with no hypothesis ([Discrete_CH] of [sc_yp_FinEnum]).  Under ¬¬P the
       cogenerator cannot tell the identity of [YP_CH P] from the constant
       map [sc_yp_const], so the two agree, and at the point [false] that
       agreement is [P].  It is the [CompHaus] analogue of
       Instance/Mod/Cogenerator.v's [cogenerator_stable_DNE] for [Ab]
       (#454), and it reads the same way: classically it refutes nothing,
       but an axiom-free cogenerating family with ¬¬-stable members, the
       interval among the candidates, would prove DNE.
       [CompHaus_point_separator_stable_DNE] is the case of a single
       space: a [K] whose maps separate the points of EVERY compact
       Hausdorff space, which is the premise of Instance/Top/StoneCech.v's
       [KSeparated_of_unit_injective], yields the same principle when its
       points have ¬¬-stable equality, by the same gadget at the points
       [true] and [false] of [YP_CH P].

   STRENGTHS.  (1) and (2) end in [False], except
   [CompHaus_ArrowIndex_of_Top], which is data whose decoding law is [≈]
   of arrows; (3) are pairs whose second component is [False]; (4)
   concludes Leibniz equality of two boolean families at every object
   from [≈] of their images; both theorems of (5) conclude
   ∀ P : Prop, ¬¬P → P.

   UNIVERSES, measured with [Set Printing Universes. About …], stdlib
   bounds left out; [o] the points, [h] the homs, [c] the objects of
   [CompHaus], [s] and [r] a shape and its limit, [e] the level of [IEM].

     CompHaus_not_complete@{r s c h …} :
       ArrowIndex@{s c h} CompHaus → ¬ Complete@{r s h c}
       (* s <= r, h <= r: nothing ties s to c *)
     CompHaus_not_complete_IEM@{e r s c h …} :
       IEM@{e} → ¬ Complete@{r s h c}     (* c <= s, h <= s, s <= r *)
     Top_not_complete_IEM@{e r s h o} :
       IEM@{e} → ¬ Complete@{r s h h} Top@{h o}   (* o < h <= s <= r *)
     StoneCech_adjunction_refuted_IEM@{e h s …} :
       IEM@{e} → ¬ ∃ F : Sets@{h s} ⟶ CompHaus, F ⊣ CompHaus_Forget
       (* h < s; CompHaus's objects at h *)
     CompHaus_ArrowIndex_of_Top@{s h o c …} :
       ArrowIndex@{s h h} Top@{h o} → ArrowIndex@{s c h} CompHaus
       (* o < h <= c; CompHaus's Top slot at h *)
     CompHaus_not_complete_IEM_below@{e r s c h o …} :
       IEM@{e} → ¬ Complete@{r s h c}  (* o < h, h <= s <= r, h <= c *)
     CompHaus_not_complete_IEM_above@{e h c …} :
       IEM@{e} → ¬ Complete@{h h h c}     (* h <= c *)
     StoneCech_adjunction_refuted_IEM_above@{e h s o c …} :
       IEM@{e} → ¬ ∃ F : Sets@{h s} ⟶ CompHaus, F ⊣ CompHaus_Forget
       (* o < h < s, h <= c; CompHaus's objects at c *)
     big_inj_injective@{r s c h …} : let C := CompHaus in
       ∀ (comp : Complete@{r s h c}) (phi psi : obj[C] → bool), …
       (* c <= s, s <= r *)

   [IEM@{e}] is free of the category's universes: a decider for [x = y],
   a [Prop], fits any level.  A word-bounded [Set] occurs in none of the
   33 readbacks of this file.

   COVERAGE, measured by applying each [IEM] form at instances of
   [CompHaus] written out slot by slot, the order of the named universes
   declared; Test/ProbeStoneCech455.v pins the boundaries below with
   refusals (N10, N12, N20-N22) and positive controls beside them.
   [CompHaus] carries fifteen universes.  Besides [c] and [h], four matter
   here: the third, [t], the hom universe of the [Top@{t o}] of which it
   is a full subcategory ([t <= c], [t <= h]); the fourth, [p], the
   universe of the proof that a space is compact Hausdorff ([p <= c]);
   and the fourteenth and fifteenth, the universes of the separating
   opens of the Hausdorff proof (Instance/Top.v's [IsHausdorff], whose
   opens are predicates at those universes).  [CompHaus_Forget] and
   [CompHaus_Incl] set [t] to [h] (About), so every statement about
   either functor has [t = h].
     - The adjunction at [CompHaus_Forget] is not formable at [c < h]
       ([CompHaus_Forget] carries [h <= c], About).  At [c = h] both
       [StoneCech_adjunction_refuted_IEM] and
       [StoneCech_adjunction_refuted_IEM_above] apply; at [c > h] only the
       latter (the former is refused there, N12).
     - [Complete@{r s h c} CompHaus]: [CompHaus_not_complete_IEM] applies
       at every [s] with [c <= s] and [h <= s], at every [t];
       [CompHaus_not_complete_IEM_below] at every [s] with [h <= s], at
       [t = h] (so [h <= c]); [CompHaus_not_complete_IEM_above] at GAFT's
       shape, [r = s = h], at [t = h].  Together they reach every [s] with
       [h <= s] except, at an instance with [t < h < c], the shapes below
       [c] (N21).  At [s < h] no [IEM] form here applies; the index forms
       of (1) apply wherever an index at [s] is given.
     - The vacuity pairs follow their refutations:
       [GAFT_CompHaus_IEM_vacuous] at [c = h] and
       [GAFT_CompHaus_IEM_vacuous_above] at every [c >= h];
       [SAFT_Incl_IEM_vacuous] at [c <= s] and
       [SAFT_Incl_IEM_vacuous_below] at every [s] that SAFT accepts at the
       inclusion ([h <= s]).
     - Every form, the older ones included, applies only at [p = c]: the
       blocks of [CompHaus_not_complete], [large_universal_arrow_refuted]
       and the helper [sc_pt_bool] set the proof slot to the objects'
       universe (About), and at [p < c] every application tried is
       refused (N20 for the adjunction).
     - And every form, the index forms included, applies only where the
       fourteenth and fifteenth slots are the points' universe [o], which
       [Bool_CH] and [Point_CH] take from [Discrete_Hausdorff@{h o}]: the
       blocks of [CompHaus_not_complete], [large_universal_arrow_refuted]
       and [sc_pt_bool] set both slots to [o] (About).  Below [o] the
       adjunction's type and the completeness hypothesis are still
       formed, and every application tried is refused (measured by #455's
       review; N22 for [StoneCech_adjunction_refuted_IEM_above], beside
       its control at [o]).

   NON-VACUITY.  [IEM] is classically true, so (1) and (2) refute their
   statements, each at the instances COVERAGE records, in every classical
   model; the [ArrowIndex] forms apply to [canonical_ArrowIndex] of any
   [ObjDecEq CompHaus], or, through [CompHaus_ArrowIndex_of_Top], of any
   [ObjDecEq Top], which is how the [IEM] forms are proved.  (3)'s
   conditionals are accepted with their hypotheses bound, and closed.
   (4) needs only the completeness hypothesis.  The premises of (5) are
   met by no family and no space in the tree, and are met classically
   ([0,1], by Urysohn).

   NOT DELIVERED.  A refutation of completeness with neither an index nor
   [IEM]: thinness of a small complete category is not constructively
   provable (Structure/Complete/Freyd.v's header).  The cardinal argument
   of (4) as a theorem.  Any refutation at an instance whose proof slot
   [p] lies below its object universe, or whose fourteenth and fifteenth
   slots, the Hausdorff proof's opens, lie below the points' universe
   [o], and one of completeness at an instance with [t < h < c] at a
   shape below [c] (COVERAGE); classically those instances are false as
   well, the objects' points still sitting at [o] (a meta-argument).
   #455's review measured what a draft of this paragraph denied: that
   something is refuted at an instance of [CompHaus] whose object
   universe [c] lies above its hom universe [h], that an arrow index at
   [h] does not need the object type itself to fit at [h], and that
   SAFT's completeness premise at [CompHaus_Incl], under a well-powering
   other than [CompHaus_WellPowered] and at a shape universe below the
   objects', is refuted as well, the draft reading the [IEM] form's
   [c <= s] as a limit.  An arrow index of [CompHaus] needs only one of
   [Top], whose objects fit at [h] ([CompHaus_ArrowIndex_of_Top]), [IEM]
   supplies that one through [Top]'s [canonical_ArrowIndex], and
   [StoneCech_adjunction_refuted_IEM_above],
   [CompHaus_not_complete_IEM_above], [CompHaus_not_complete_IEM_below]
   and [SAFT_Incl_IEM_vacuous_below] are those refutations.  What the
   draft measured stands as the scope of the two older constants,
   which apply [canonical_ArrowIndex] to [CompHaus]'s own objects:
   [StoneCech_adjunction_refuted_IEM] is refused applied at
   [CompHaus : Category@{c h h}] under [h < c] ("universe
   inconsistency: Cannot enforce c = h because h < c"), and
   [CompHaus_not_complete_IEM] is refused at GAFT's shape
   [Complete@{h h h c}], needing [c <= s].  Anything over the
   Prop-valued re-encoding (#1328), and Stone–Čech itself (#1329).
   CORRECTION (#458): the re-run of this file's completeness refutations
   over the Prop-valued [PTopCat] is Instance/Top/Complete/Refutations.v's
   and their colimit duals are Instance/Top/Cocomplete/Refutations.v's,
   with [Top_not_cocomplete_Freyd] there the dual of [Top_not_complete]
   here; [PCompHaus] and Stone–Čech stay with #1328 and #1329.  And
   Instance/Top/Complete/Refutations.v carries [Top_not_complete_IEM]
   and [CompHaus_not_complete_IEM_below] below the hom universe, where
   COVERAGE records that no [IEM] form here applies, to every shape
   universe strictly above the points: [Top_not_complete_below_IEM] and
   [CompHaus_not_complete_below_IEM], through an arrow index of [Top]
   moved between hom universes ([Top_ArrowIndex_transport]).

   COUNTS.  33 constants here (18 [Definition], 4 [Lemma], 11 [Theorem]),
   all closed under the global context by their fully qualified names,
   [Print Module] listing exactly these 33.  One proof ends [Defined], and
   it is load-bearing: flipping [sc_phi_map] alone to [Qed], the proof of
   [large_universal_arrow_refuted] is refused.  Closure 153 modules
   excluding self: Instance/Sets/Classifier/OneLevel.v costs 15 at the
   margin ([IEM] lives there), Structure/Complete/Freyd.v 11,
   Adjunction/SAFT/Characterization.v 3, Instance/Top/StoneCech.v 1, each
   of the other fifteen [Category.*] [Require]s 0 (each dropped alone). *)

(** * The two points of the discrete two-point space *)

Definition sc_pt_bool@{o +} (b : bool) : Point_CH ~{CompHaus}~> Bool_CH :=
  (top_point Bool_Discrete@{o} b; I).

Definition sc_eval_pt@{c h +}
  (f : Point_CH ~{CompHaus : Category@{c h h}}~> Bool_CH) : bool :=
  continuous_map (`1 f) ttt.

Lemma sc_eval_pt_resp@{c h +}
  (u v : Point_CH ~{CompHaus : Category@{c h h}}~> Bool_CH) :
  u ≈ v → sc_eval_pt u = sc_eval_pt v.
Proof. intro H. exact (H ttt). Qed.

(** * Completeness at the hom universe is refuted (Freyd's core) *)

Theorem CompHaus_not_complete@{r s c h +}
  (AI : ArrowIndex@{s c h} CompHaus)
  (comp : @Complete@{r s h c} CompHaus) : False.
Proof.
  exact (freyd_no_separated_pair AI (sc_pt_bool true) (sc_pt_bool false) _ _
           (complete_iprod comp (fun _ : ai_index AI => Bool_CH))
           sc_eval_pt sc_eval_pt_resp eq_refl eq_refl).
Qed.

(* Informative excluded middle decides equality of objects. *)
Definition ObjDecEq_of_IEM@{e c h +} (E : IEM@{e}) (C : Category@{c h h}) :
  ObjDecEq C :=
  fun x y => match E (x = y) with
             | inl e => left e
             | inr n => right n
             end.

Theorem CompHaus_not_complete_IEM@{e r s c h +} (E : IEM@{e})
  (comp : @Complete@{r s h c} CompHaus) : False.
Proof.
  exact (CompHaus_not_complete
           (canonical_ArrowIndex (ObjDecEq_of_IEM E CompHaus)) comp).
Qed.

Theorem Top_not_complete@{r s h o +} (AI : ArrowIndex@{s h h} Top@{h o})
  (comp : @Complete@{r s h h} Top@{h o}) : False.
Proof.
  exact (freyd_no_separated_pair AI
           (top_point Bool_Discrete true) (top_point Bool_Discrete false) _ _
           (complete_iprod comp (fun _ : ai_index AI => Bool_Discrete))
           (fun h => continuous_map h ttt) (fun u v H => H ttt)
           eq_refl eq_refl).
Qed.

Theorem Top_not_complete_IEM@{e r s h o +} (E : IEM@{e})
  (comp : @Complete@{r s h h} Top@{h o}) : False.
Proof.
  exact (Top_not_complete
           (canonical_ArrowIndex (ObjDecEq_of_IEM E Top)) comp).
Qed.

(** * Above the hom universe: an arrow index transported from [Top] *)

(* The homs of the full subcategory are [Top]'s paired with [True]
   ([Sub]), so an arrow index of [Top] indexes the arrows of [CompHaus] at
   every universe of its objects at or above the homs: the index never
   mentions them. *)
Definition CompHaus_ArrowIndex_of_Top@{s h o c +}
  (AIT : ArrowIndex@{s h h} Top@{h o}) :
  ArrowIndex@{s c h} (CompHaus : Category@{c h h}) :=
  @Build_ArrowIndex (CompHaus : Category@{c h h}) (ai_index AIT)
    (fun x y f => ai_enc AIT (`1 f))
    (fun x y m d => (ai_dec AIT m (`1 d); I))
    (fun x y f d => ai_dec_enc AIT (`1 f) (`1 d)).

Theorem CompHaus_not_complete_IEM_below@{e r s c h o +} (E : IEM@{e})
  (comp : @Complete@{r s h c} (CompHaus : Category@{c h h})) : False.
Proof.
  exact (CompHaus_not_complete
           (CompHaus_ArrowIndex_of_Top
              (canonical_ArrowIndex@{s h h} (ObjDecEq_of_IEM E Top@{h o})))
           comp).
Qed.

Theorem CompHaus_not_complete_IEM_above@{e h c +} (E : IEM@{e})
  (comp : @Complete@{h h h c} (CompHaus : Category@{c h h})) : False.
Proof. exact (CompHaus_not_complete_IEM_below E comp). Qed.

(** * The adjunction itself is refuted: a universal arrow at a large set *)

(* The arrow index of [CompHaus], as a setoid with Leibniz equality. *)
Definition KSet@{s c h +} (AI : ArrowIndex@{s c h} CompHaus) :
  SetoidObject@{s s} :=
  {| carrier := ai_index AI; is_setoid := eq_Setoid (ai_index AI) |}.

Definition sc_phi_map@{c h +} (AI : ArrowIndex@{h c h} CompHaus)
  (phi : ai_index AI → bool) :
  KSet AI ~{Sets}~> CompHaus_Forget Bool_CH.
Proof.
  unshelve refine {| morphism := phi |}.
  all: intros a b e; simpl in *; destruct e; reflexivity.
Defined.

Theorem large_universal_arrow_refuted@{c h +}
  (AI : ArrowIndex@{h c h} CompHaus)
  (UA : UniversalArrow (C:=Sets) (KSet AI) CompHaus_Forget) : False.
Proof.
  pose (pm := sc_phi_map AI).
  pose (ext := fun phi => unique_obj (ump_universal_arrows UA (pm phi))).
  pose (dflt := ext (fun _ => true)).
  pose (Fam := fun k i =>
         continuous_map (`1 (ai_dec AI k dflt)) (@arrow _ _ _ _ UA i) : bool).
  apply (freyd_cantor_bool Fam).
  intro phi. exists (ai_enc AI (ext phi)). intro i.
  unfold Fam.
  rewrite (ai_dec_enc AI (ext phi) dflt (@arrow _ _ _ _ UA i)).
  pose proof (unique_property (ump_universal_arrows UA (pm phi)) i) as H.
  simpl in H. symmetry. exact H.
Qed.

Theorem StoneCech_adjunction_refuted_IEM@{e h s +} (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget }) : False.
Proof.
  pose (AI := canonical_ArrowIndex (ObjDecEq_of_IEM E CompHaus)).
  exact (large_universal_arrow_refuted AI
           (universal_arrow_of_adjunction (`2 A) (KSet AI))).
Qed.

(* The same at every object universe at or above the homs, through the
   index of [Top]. *)
Theorem StoneCech_adjunction_refuted_IEM_above@{e h s o c +} (E : IEM@{e})
  (A : { F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
       & F ⊣ CompHaus_Forget }) : False.
Proof.
  pose (AI := CompHaus_ArrowIndex_of_Top
                (canonical_ArrowIndex (ObjDecEq_of_IEM E Top@{h o}))).
  exact (large_universal_arrow_refuted AI
           (universal_arrow_of_adjunction (`2 A) (KSet AI))).
Qed.

(** * GAFT and SAFT consume the refuted hypothesis *)

Definition GAFT_CompHaus_IEM_vacuous@{e h s +} (E : IEM@{e})
  (comp : @Complete@{h h h h} CompHaus) :
  ({ F : Sets@{h s} ⟶ CompHaus & F ⊣ CompHaus_Forget } * False)%type :=
  (GAFT_CompHaus_only_complete comp, CompHaus_not_complete_IEM E comp).

(* With the objects at or above the homs [taut_sols] no longer fits GAFT,
   so the solution sets are a hypothesis. *)
Definition GAFT_CompHaus_IEM_vacuous_above@{e h s c +} (E : IEM@{e})
  (comp : @Complete@{h h h c} (CompHaus : Category@{c h h}))
  (sols : ∀ d : obj[Sets@{h s}], SolutionSet CompHaus_Forget d) :
  ({ F : Sets@{h s} ⟶ (CompHaus : Category@{c h h})
     & F ⊣ CompHaus_Forget } * False)%type :=
  (GAFT CompHaus_Forget comp CompHaus_Forget_PreservesImageLimit sols,
   CompHaus_not_complete_IEM_above E comp).

Definition CompHaus_WellPowered@{c h t +} :
  WellPowered@{c h h h t} (CompHaus : Category@{c h h}) :=
  trivial_small CompHaus.

(* SAFT at the inclusion, well-poweredness discharged: three hypotheses
   remain, and the completeness one is refuted under [IEM] at the
   instances COVERAGE records. *)
Definition SAFT_CompHaus_Incl@{s h +} (comp : @Complete@{s s h h} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl) (G : Cogenerator CompHaus) :
  { F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } :=
  SAFT_wellpowered CompHaus_Incl comp cont G CompHaus_WellPowered.

Definition SAFT_Incl_vacuous@{s c h +} (AI : ArrowIndex@{s c h} CompHaus)
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  (SAFT_wellpowered CompHaus_Incl comp cont G WP,
   CompHaus_not_complete AI comp).

Definition SAFT_Incl_IEM_vacuous@{e s c h +} (E : IEM@{e})
  (comp : @Complete@{s s h c} CompHaus)
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  (SAFT_wellpowered CompHaus_Incl comp cont G WP,
   CompHaus_not_complete_IEM E comp).

(* The same at every shape universe SAFT accepts at the inclusion, the
   shapes below the objects included. *)
Definition SAFT_Incl_IEM_vacuous_below@{e s c h +} (E : IEM@{e})
  (comp : @Complete@{s s h c} (CompHaus : Category@{c h h}))
  (cont : @PreservesImageLimit _ _ CompHaus_Incl)
  (G : Cogenerator CompHaus) (WP : WellPowered CompHaus) :
  ({ F : Top ⟶ CompHaus & F ⊣ CompHaus_Incl } * False)%type :=
  (SAFT_wellpowered CompHaus_Incl comp cont G WP,
   CompHaus_not_complete_IEM_below E comp).

(** * The classical-model obstruction, with no hypothesis beyond completeness *)

(* The index is the object type of the category [comp] is about: the local
   definition [C] makes the two one instance. *)
Definition big_inj@{r s c h +} (C := CompHaus : Category@{c h h})
  (comp : @Complete@{r s h c} C) (phi : obj[C] → bool) :
  top_carrier (`1 (complete_iprod_obj comp (fun _ : obj[C] => Bool_CH))) :=
  continuous_map
    (`1 (unique_obj
           (iprod_desc (complete_iprod comp (fun _ : obj[C] => Bool_CH))
              (fun j => sc_pt_bool (phi j))))) ttt.

Lemma big_inj_injective@{r s c h +} (C := CompHaus : Category@{c h h})
  (comp : @Complete@{r s h c} C) (phi psi : obj[C] → bool) :
  big_inj comp phi ≈ big_inj comp psi → ∀ j, phi j = psi j.
Proof.
  intros E j.
  pose proof (unique_property
    (iprod_desc (complete_iprod comp (fun _ : obj[C] => Bool_CH))
       (fun j => sc_pt_bool (phi j))) j ttt) as Hp.
  pose proof (unique_property
    (iprod_desc (complete_iprod comp (fun _ : obj[C] => Bool_CH))
       (fun j => sc_pt_bool (psi j))) j ttt) as Hq.
  simpl in Hp, Hq.
  pose proof (proper_morphism
    (continuous_map
       (`1 (complete_iprod_proj comp (fun _ : obj[C] => Bool_CH) j)))
    _ _ E) as Hm.
  simpl in Hm.
  rewrite <- Hp, <- Hq. exact Hm.
Qed.

(** * A cogenerator of CompHaus with stable members gives DNE *)

(* The two-point space whose points are identified exactly when [P]. *)
Definition sc_yp_equiv@{o +} (P : Prop) (x y : bool) : Type@{o} :=
  (x = y \/ P).

Lemma sc_yp_equiv_Equivalence@{o +} (P : Prop) :
  Equivalence (sc_yp_equiv@{o} P).
Proof.
  unfold sc_yp_equiv; constructor.
  - intro x; left; reflexivity.
  - intros x y [e|p]; [left; symmetry; exact e | right; exact p].
  - intros x y z [e1|p] [e2|p2]; [left; congruence | right | right | right];
      assumption.
Qed.

Definition sc_YP@{o +} (P : Prop) : SetoidObject@{o o} :=
  {| carrier := bool;
     is_setoid := {| equiv := sc_yp_equiv P;
                     setoid_equiv := sc_yp_equiv_Equivalence P |} |}.

Lemma sc_yp_FinEnum@{o +} (P : Prop) :
  FinEnum (sc_YP P : SetoidObject@{o o}).
Proof.
  exists (true :: false :: nil). intros [|].
  - exists true. split; [left; reflexivity | left; reflexivity].
  - exists false. split; [right; left; reflexivity | left; reflexivity].
Qed.

Definition YP_CH@{o +} (P : Prop) : CompHaus :=
  Discrete_CH (sc_YP P : SetoidObject@{o o}) (sc_yp_FinEnum P).

Definition sc_yp_const@{o +} (P : Prop) : YP_CH P ~{CompHaus}~> YP_CH P :=
  (Build_ContinuousMorphism (Discrete_Top@{o o} (sc_YP P))
     (Discrete_Top (sc_YP P))
     (const_morphism (sc_YP P) (sc_YP P) true)
     (fun U _ => open_const (Discrete_Top (sc_YP P)) (U true)); I).

Theorem CompHaus_cogenerator_stable_DNE@{k c h +}
  (G : Cogenerator@{k c h} CompHaus)
  (stable : ∀ j (a b : top_carrier (`1 (cog_obj G j))),
              ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P → P.
Proof.
  intros P nnP.
  assert (H : (@id CompHaus (YP_CH P)) ≈ sc_yp_const P).
  { apply (cog_separates G).
    intros j k b; simpl.
    apply stable; intro Hne.
    apply nnP; intro HP.
    apply Hne.
    apply (proper_morphism (continuous_map (`1 k))).
    right; exact HP. }
  destruct (H false) as [e|p]; [discriminate | exact p].
Qed.

(* The case of a single space: a [K] that separates the points of every
   compact Hausdorff space, the premise of Instance/Top/StoneCech.v's
   [KSeparated_of_unit_injective], costs the same when its points have
   ¬¬-stable equality. *)
Theorem CompHaus_point_separator_stable_DNE@{c h +}
  (K : (CompHaus : Category@{c h h}))
  (sepK : ∀ (Y : (CompHaus : Category@{c h h})) (p q : top_carrier (`1 Y)),
            (∀ k : Y ~{CompHaus}~> K,
               continuous_map (`1 k) p ≈ continuous_map (`1 k) q) → p ≈ q)
  (stable : ∀ a b : top_carrier (`1 K), ((a ≈ b → False) → False) → a ≈ b) :
  ∀ P : Prop, ~~P → P.
Proof.
  intros P nnP.
  destruct (sepK (YP_CH P) true false) as [e|p]; [| discriminate | exact p].
  intro k. apply stable. intro Hne. apply nnP. intro HP. apply Hne.
  apply (proper_morphism (continuous_map (`1 k))). right. exact HP.
Qed.
