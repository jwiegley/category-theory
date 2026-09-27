Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Complete.
Require Import Category.Structure.Complete.Freyd.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Comma.Limit.
Require Import Category.Construction.Reflective.
Require Import Category.Adjunction.GAFT.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Classifier.OneLevel.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Subspace.TypeValued.
Require Import Category.Instance.Top.StoneCech.
Require Import Category.Instance.Top.StoneCech.Refutations.
Require Import Category.Instance.Top.Complete.Refutations.

Generalizable All Variables.

(** * Hausdorff spaces over the Type-valued [Top] *)

(* Mac Lane, "Categories for the Working Mathematician", 2nd ed. (GTM 5),
     §V.9, book p. 135 (PDF p. 144), read from the page image,
     Proposition 2 (catalog id maclane:V.9:prop2): the inclusion
     Haus → Top has a left adjoint H, "obtained by the adjoint functor
     theorem".  The statement over Instance/Top/Prop.v's [PTopCat] is
     Instance/Top/Hausdorff.v's; this file records what holds over
     Instance/Top.v's Type-valued [Top].
   Riehl, "Category Theory in Context", §4.7, printed p. 180 (PDF p. 200),
     read from the page image, Exercise 4.7.ii (riehl:4.7:exii), the same
     reflector "by Theorem 4.7.3"
   nLab:      https://ncatlab.org/nlab/show/Hausdorff+space

   BACKGROUND.  Instance/Top.v's [Top@{h o}] has Type-valued opens, and
   its homs sit strictly above its points ([o < h]; that file's header,
   point 2).  Its Hausdorff subcategory, [HausdorffSpaces], is defined
   by the classical negative axiom [IsHausdorff], which Mac Lane uses
   without defining it (book p. 158, §VI.9), and whose separating opens
   are data.  The completeness of [CompHaus], the premise the adjoint
   functor theorem needs there, is refuted under informative excluded
   middle (Instance/Top/Complete/Refutations.v's
   [CompHaus_not_complete_below_IEM], through Instance/Top/StoneCech/
   Refutations.v's [CompHaus_ArrowIndex_of_Top]).  The same argument
   with the compactness clause dropped reaches Haus.  The direct
   reflection below, [TopT2_Reflective], is onto another subcategory,
   [TSepSub tprem_T2], the spaces of the positive and truncated T2; it
   needs no completeness and no solution set, and is not walled, once
   the separation premise alone is a proposition.

   THE DIRECT REFLECTION.  A premise [TSepPremise] reads a proposition
   off a family of Type-valued opens; [tprem_T2] is nLab's constructive
   Hausdorff premise with the meeting point truncated
   ([inhabited { z & U z * V z }]), and [TSep prem X] says that it forces
   the points' equality.  [TSepQuot] is the intersection-of-separating-
   relations quotient of Instance/Top/Separation.v, built on
   Instance/Top/Subspace/TypeValued.v's [TQuot]; [TSepLaws] asks two laws
   ([tl_pull], [tl_equiv]).  [TSep_Reflective] assembles the reflection
   by universal arrows, and [TopT2_Reflective] is the largest Hausdorff
   quotient over [Top].  [IsHausdorff_TSep2_nn]: Instance/Top.v's
   [IsHausdorff] gives this T2 only under a double negation.

   THE ADJOINT FUNCTOR THEOREM AT Haus ⟶ Top.  [GAFT_TopHaus] states
   Adjunction/GAFT.v's [GAFT] at [Incl Top Hausdorff_Subcategory]; it is
   accepted.  [TopHaus_not_complete] is Freyd's argument
   (Structure/Complete/Freyd.v's [freyd_no_separated_pair]) at
   [HausdorffSpaces], with the two points of [Bool_Discrete] as the
   separated pair, both spaces Hausdorff at every universe of the
   predicate and of its separating opens ([tophaus_bool_hausdorff],
   [tophaus_point_hausdorff], whose opens are propositions; Instance/Top/
   StoneCech.v's [Discrete_Hausdorff] separates by the opens [z ≈ x],
   which sit at the points' universe); [TopHaus_ArrowIndex_of_Top]
   restricts an arrow index of [Top] to [HausdorffSpaces]; and
   [TopHaus_not_complete_below_IEM] feeds it the index that
   Instance/Top/Complete/Refutations.v's [Top_ArrowIndex_transport]
   carries from Instance/Top/StoneCech/Refutations.v's
   [ObjDecEq_of_IEM].  So [GAFT_TopHaus_vacuous]: under [IEM], the
   hypotheses of [GAFT_TopHaus] cannot all hold, at every universe
   instance of [GAFT_TopHaus] (UNIVERSES, below).

   STRENGTHS.  No [eq_refl] readback is claimed.  One [Defined], counted
   by token ([tsep_universal]), by the data convention: flipped alone to
   [Qed] in a scratch copy, every readback of this file, of
   Instance/Top/Separation.v, of Instance/Top/Hausdorff.v and of
   Test/ProbeHausdorff461.v stays accepted.  17 [Qed], counted by token.
   Every constant is closed under the global context ([Print
   Assumptions] on each); [IEM] is a hypothesis of the two refutations,
   never an axiom.

   UNIVERSES, read by [About] under [Set Printing Universes] on all 48
   constants of this file's [Print Module] listing (the record
   constructor [Build_TSepLaws] among them; no [Program] obligation).
     - The premise, the laws and the quotient's relation and setoid:
       [@{o}], empty blocks; [TSepPremise@{o}]'s sort is
       [Type@{max(Set+1,o+1)}], the relations it returns being
       Prop-valued.
       [TSepQuot] and [TSepQuot_sep] add the caps
       [o <= projections.u0], [o <= projections.u1], [TQuot]'s own.
     - The mediator ([tsep_ker] through [tsep_med]): [@{o u}] with
       [o < u], the hom universe of [ContinuousMorphism@{u u0}], whose
       block is [u0 < u].
     - [TSepSub], [TSep_Full]: [@{o h}] with [o < h], [Top]'s own;
       [TSepSpaces] and the reflection's constants add [h < u], the
       auxiliary of Construction/Subcategory.v's [Sub] above the hom
       universe, and [<=]-related auxiliaries; the strict stdlib cap
       [o < Projections.u0] is first carried by [tsep_universal].
       [TopT2_Reflective@{o h u u0 u1 u2}]: [o < h], [h < u], nothing
       mentions [Set].
     - [IsHausdorff_TSep2_nn@{o u u0 u1}]: [IsHausdorff]'s own four
       universes and bounds.
     - [tophaus_bool_hausdorff@{t p q o}], [tophaus_point_hausdorff]:
       [IsHausdorff]'s block ([p < t], [q < t], [p <= o], [q <= o],
       [o <= t]).  [TopHaus_Bool], [TopHaus_Point], [tophaus_pt_bool]:
       the nine universes of [HausdorffSpaces] named, [@{c hh h t s a o p
       q}] (its objects and homs, [Top]'s homs, the predicate, two
       auxiliaries, the points, the two opens), and exactly the eleven
       constraints of [HausdorffSpaces]'s own block.
       [TopHaus_not_complete@{r s c hh h t sh a o p q}] adds [s <= r] and
       [hh <= r], [Complete]'s own.  [TopHaus_not_complete_below_IEM]
       reads [HausdorffSpaces] with its homs at [Top]'s, [h], and its
       objects at any [c] with [h <= c]: [TopHaus_not_complete]'s
       constraints at [hh := h], and [o < s].
     - [GAFT_TopHaus_vacuous@{e h o u u0 u1 u2 u3 u4 u6}]: the hypotheses
       are written at [GAFT_TopHaus]'s own instance, nine of its ten
       universes named (the tenth occurs in no hypothesis), and the
       [About] block carries every constraint of [GAFT_TopHaus]'s and
       adds only eight stdlib caps, each of the form [h <= _] or [o <= _]
       on a stdlib universe (compared by script).  In particular the
       objects of the Hausdorff subcategory sit at any [u4] with
       [h <= u4], its predicate at any [u] with [o <= u <= u4], and its
       separating opens at any [u2], [u3] below [u] and at or below [o].
       Test/ProbeHausdorff461.v pins this with the constraint list closed
       by strict inequalities, so that no equation among them can be
       inferred: [p461_vacuous_apart] reads the theorem with the objects
       strictly above [h], the predicate strictly between [o] and [h] and
       the opens strictly below [o], and [p461_not_complete_above] the
       refutation of completeness with the objects strictly above [h].
       The two spaces' own lemmas are what reach opens below the points:
       [Discrete_Hausdorff] read there is refused, that file's N11
       ("Cannot enforce o = p because p < o"), where
       [tophaus_bool_hausdorff] is accepted ([p461_bool_opens_below]).
     - No block carries an equation.  A word count of [Set] over the
       [About] output of the 48 constants reads 1, [TSepPremise]'s
       sort.

   NOT DELIVERED.  The reflector over [Top] by [GAFT] (vacuous under
   [IEM], above; without [IEM] neither obtained nor refuted); a
   reflection of [HausdorffSpaces], the subcategory of the negative
   form, by any route; [GAFT] at [TSepSub tprem_T2]; T0 and T1 over
   [Top] beyond Instance/Top/Kolmogorov.v's T0 reflection; a comparison
   of [TopT2_Reflective] with Instance/Top/Hausdorff.v's reflector
   across the two encodings; completeness of [TSepSpaces]; Exercises 4
   and 5 over [Top]. *)

(** ** Separation premises with Type-valued opens *)

(* Only the premise is truncated to a proposition; the opens stay
   Type-valued, as in Instance/Top.v. *)
Definition TSepPremise@{o} :=
  ∀ S : Type@{o}, ((S → Type@{o}) → Type@{o}) → S → S → Prop.

(* T2: every open about the first point meets every open about the second,
   the meeting point truncated. *)
Definition tprem_T2@{o} : TSepPremise@{o} :=
  fun S O x y => ∀ U V, O U → O V → U x → V y →
    inhabited { z : S & (U z * V z)%type }.

Definition TSep@{o} (prem : TSepPremise@{o}) (X : TopSpace@{o}) : Type@{o} :=
  ∀ x y : X, prem _ (IsOpen X) x y → x ≈ y.

Record TSepLaws@{o} (prem : TSepPremise@{o}) : Prop := {
  tl_pull : ∀ (S S' : Type@{o}) (f : S → S') (O : (S → Type@{o}) → Type@{o})
      (O' : (S' → Type@{o}) → Type@{o}),
      (∀ W, O' W → O (fun s => W (f s))) →
      ∀ x y, prem S O x y → prem S' O' (f x) (f y);
  tl_equiv : ∀ (X : TopSpace@{o}) (x y : X), x ≈ y → prem _ (IsOpen X) x y
}.

Lemma tprem_T2_laws@{o} : TSepLaws@{o} tprem_T2@{o}.
Proof.
  constructor.
  - intros S S' f O O' sub x y H W1 W2 H1 H2 w1 w2.
    destruct (H _ _ (sub W1 H1) (sub W2 H2) w1 w2) as [[z [a b]]].
    exact (inhabits (f z; (a, b))).
  - intros X x y e U V HU HV u v.
    exact (inhabits (y; (open_proper X U HU x y e u, v))).
Qed.

(** ** The largest separated quotient *)

Section TQuotient.

Universe o.

Variable prem : TSepPremise@{o}.
Variable L : TSepLaws@{o} prem.

Context (X : TopSpace@{o}).

Local Notation P := (carrier (top_carrier X)).

Definition tsep_qopen (R : P → P → Prop) (U : P → Type@{o}) : Type@{o} :=
  (IsOpen X U * (∀ a b, R a b → U a → U b))%type.

Definition TSepRel (R : P → P → Prop) : Prop :=
  (∀ a, R a a) /\ (∀ a b, R a b → R b a) /\
  (∀ a b c, R a b → R b c → R a c) /\
  (∀ a b : P, a ≈ b → R a b) /\
  (∀ a b, prem P (tsep_qopen R) a b → R a b).

Definition tsepeq (a b : P) : Prop := ∀ R, TSepRel R → R a b.

Lemma tsepeq_refl (a : P) : tsepeq a a.
Proof. intros R HR. exact (proj1 HR a). Qed.

Lemma tsepeq_sym (a b : P) : tsepeq a b → tsepeq b a.
Proof. intros e R HR. exact (proj1 (proj2 HR) a b (e R HR)). Qed.

Lemma tsepeq_trans (a b c : P) : tsepeq a b → tsepeq b c → tsepeq a c.
Proof.
  intros e1 e2 R HR.
  exact (proj1 (proj2 (proj2 HR)) a b c (e1 R HR) (e2 R HR)).
Qed.

Lemma tsepeq_of_equiv (a b : P) : a ≈ b → tsepeq a b.
Proof. intros e R HR. exact (proj1 (proj2 (proj2 (proj2 HR))) a b e). Qed.

Definition tsep_setoid : SetoidObject@{o o} :=
  {| carrier := P;
     is_setoid := {| equiv := tsepeq;
                     setoid_equiv := Build_Equivalence tsepeq tsepeq_refl
                                       tsepeq_sym tsepeq_trans |} |}.

Definition tsep_q :
  @SetoidMorphism@{o o o} _ (is_setoid (top_carrier X)) _
    (is_setoid tsep_setoid) :=
  @Build_SetoidMorphism _ (is_setoid (top_carrier X)) _ (is_setoid tsep_setoid)
    (fun x => x) tsepeq_of_equiv.

Definition TSepQuot : TopSpace@{o} := TQuot X tsep_setoid tsep_q.

Lemma TSepQuot_sep : TSep prem TSepQuot.
Proof using L.
  intros x y H R HR.
  apply (proj2 (proj2 (proj2 (proj2 HR)))).
  apply (tl_pull _ L P P (fun s => s) (IsOpen TSepQuot) (tsep_qopen R));
    [|exact H].
  intros U [HU HsU]. split.
  - intros t t' e u. exact (HsU t t' (e R HR) u).
  - exact HU.
Qed.

Section TMed.

Context (H : TopSpace@{o}) (HH : TSep prem H) (f : ContinuousMorphism X H).

Definition tsep_ker (a b : P) : Prop :=
  prem _ (IsOpen H) (continuous_map f a) (continuous_map f b).

Lemma tsep_ker_to (a b : P) :
  tsep_ker a b → continuous_map f a ≈ continuous_map f b.
Proof using HH. exact (HH _ _). Qed.

Lemma tsep_ker_of (a b : P) :
  continuous_map f a ≈ continuous_map f b → tsep_ker a b.
Proof using L. exact (tl_equiv _ L H _ _). Qed.

Lemma tsep_ker_TSepRel : TSepRel tsep_ker.
Proof using L HH.
  refine (conj _ (conj _ (conj _ (conj _ _)))).
  - intro a. apply tsep_ker_of. reflexivity.
  - intros a b e. apply tsep_ker_of. symmetry. exact (tsep_ker_to a b e).
  - intros a b c e1 e2. apply tsep_ker_of.
    transitivity (continuous_map f b);
      [exact (tsep_ker_to _ _ e1)|exact (tsep_ker_to _ _ e2)].
  - intros a b e. apply tsep_ker_of.
    exact (proper_morphism (continuous_map f) a b e).
  - intros a b Hp. unfold tsep_ker.
    apply (tl_pull _ L P _ (fun s => continuous_map f s)
             (tsep_qopen tsep_ker) (IsOpen H)); [|exact Hp].
    intros W HW. split.
    + exact (continuity f W HW).
    + intros a' b' e u.
      exact (open_proper H W HW _ _ (tsep_ker_to a' b' e) u).
Qed.

Lemma tsep_med_resp (a b : P) :
  tsepeq a b → continuous_map f a ≈ continuous_map f b.
Proof using L HH.
  intro e. exact (tsep_ker_to a b (e tsep_ker tsep_ker_TSepRel)).
Qed.

Definition tsep_med_setoid :
  @SetoidMorphism@{o o o} _ (is_setoid tsep_setoid) _
    (is_setoid (top_carrier H)) :=
  @Build_SetoidMorphism _ (is_setoid tsep_setoid) _ (is_setoid (top_carrier H))
    (fun a => continuous_map f a) tsep_med_resp.

Definition tsep_med : ContinuousMorphism TSepQuot H :=
  tquot_desc X tsep_setoid tsep_q H f tsep_med_setoid
    (fun x => reflexivity (continuous_map f x)).

End TMed.

End TQuotient.

Section TReflection.

Universes o h.
Constraint o < h.

Variable prem : TSepPremise@{o}.
Variable L : TSepLaws@{o} prem.

Definition TSepSub : Subcategory@{h h o h} Top@{h o} :=
  @Build_Subcategory@{h h o h} Top@{h o}
    (fun X => TSep prem X)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition TSepSpaces : Category := Sub Top@{h o} TSepSub.

Lemma TSep_Full : Construction.Subcategory.Full Top@{h o} TSepSub.
Proof. intros x y ox oy g; exact I. Qed.

Definition TSepObj (X : Top@{h o}) : TSepSpaces :=
  (TSepQuot prem X; TSepQuot_sep prem L X).

Definition tsep_proj (X : Top@{h o}) :
  X ~{Top@{h o}}~> Incl Top@{h o} TSepSub (TSepObj X) :=
  tquot_proj X (tsep_setoid prem X) (tsep_q prem X).

Definition tsep_universal (X : Top@{h o}) :
  ∀ (d : TSepSpaces) (f : X ~{Top@{h o}}~> Incl Top@{h o} TSepSub d),
    ∃! g : TSepObj X ~{TSepSpaces}~> d,
      f ≈ fmap[Incl Top@{h o} TSepSub] g ∘ tsep_proj X.
Proof using L.
  intros d f.
  unshelve eexists.
  - exact (tsep_med prem L X (`1 d) (`2 d) f; I).
  - intro x; simpl; reflexivity.
  - intros g Hg x; simpl. exact (Hg x).
Defined.

Definition tsep_ua (X : Top@{h o}) :
  @UniversalArrow Top@{h o} TSepSpaces X (Incl Top@{h o} TSepSub) :=
  @universal_arrow_from_UMP Top@{h o} TSepSpaces X (Incl Top@{h o} TSepSub)
    (TSepObj X) (tsep_proj X) (tsep_universal X).

Definition TSep_reflector : Top@{h o} ⟶ TSepSpaces :=
  LeftAdjointFunctorFromUniversalArrows (Incl Top@{h o} TSepSub) tsep_ua.

Definition TSep_adj : TSep_reflector ⊣ Incl Top@{h o} TSepSub :=
  AdjunctionFromUniversalArrows (Incl Top@{h o} TSepSub) tsep_ua.

Definition TSep_Reflective : Reflective TSepSub :=
  @Build_Reflective Top@{h o} TSepSub TSep_Full TSep_reflector TSep_adj.

End TReflection.

(* The direct Hausdorff reflection over the Type-valued [Top]. *)
Definition TopT2_Reflective@{o h +| o < h +} :
  Reflective (TSepSub@{o h} tprem_T2@{o}) :=
  TSep_Reflective tprem_T2 tprem_T2_laws.

(* Instance/Top.v's [IsHausdorff], the classical negative form, gives this
   T2 only under a double negation. *)
Lemma IsHausdorff_TSep2_nn@{o +} (X : TopSpace@{o}) (HX : IsHausdorff X)
  (x y : X) : tprem_T2 _ (IsOpen X) x y → ¬ ¬ inhabited (x ≈ y).
Proof.
  intros Hp Hne.
  destruct (HX x y (fun e => Hne (inhabits e))) as [U [V [[HU HV] [[u v] Hd]]]].
  destruct (Hp U V HU HV u v) as [[z [a b]]].
  exact (Hd z a b).
Qed.

(** ** The adjoint functor theorem at the Type-valued inclusion *)

(* The two-point discrete space and the point are Hausdorff at every
   universe of the predicate and of the separating opens, the opens used
   being propositions.  Instance/Top/StoneCech.v's [Discrete_Hausdorff]
   separates by the opens [z ≈ x], which sit at the points' universe. *)
Lemma tophaus_bool_hausdorff@{t p q o +| p < t, q < t, p <= o, q <= o,
    o <= t +} : IsHausdorff@{t p q o} Bool_Discrete@{o}.
Proof.
  intros x y nxy.
  exists (fun z : bool => z = x). exists (fun z : bool => z = y).
  refine ((_, _), ((_, _), _)); simpl.
  - intros u v Huv Hu. simpl in Huv. congruence.
  - intros u v Huv Hu. simpl in Huv. congruence.
  - reflexivity.
  - reflexivity.
  - intros z Hx Hy. apply nxy. simpl. congruence.
Qed.

Lemma tophaus_point_hausdorff@{t p q o +| p < t, q < t, p <= o, q <= o,
    o <= t +} : IsHausdorff@{t p q o} Point_Top@{o}.
Proof. intros x y nxy. destruct x, y. destruct (nxy (reflexivity _)). Qed.

(* The universes of [HausdorffSpaces]: [c], [hh] its objects and homs; [h]
   and [o] those of [Top]; [t] the predicate [IsHausdorff]; [p], [q] its
   separating opens; [s], [a] auxiliaries of the subcategory. *)
Definition TopHaus_Bool@{c hh h t s a o p q +} :
  HausdorffSpaces@{c hh h t s a o p q} :=
  (Bool_Discrete@{o}; tophaus_bool_hausdorff@{t p q o}).

Definition TopHaus_Point@{c hh h t s a o p q +} :
  HausdorffSpaces@{c hh h t s a o p q} :=
  (Point_Top@{o}; tophaus_point_hausdorff@{t p q o}).

Definition tophaus_pt_bool@{c hh h t s a o p q +} (b : bool) :
  TopHaus_Point@{c hh h t s a o p q}
    ~{HausdorffSpaces@{c hh h t s a o p q}}~>
  TopHaus_Bool@{c hh h t s a o p q} :=
  (top_point Bool_Discrete@{o} b; I).

(* #455's arrow index of [Top], restricted to the Hausdorff spaces. *)
Definition TopHaus_ArrowIndex_of_Top@{s h o c +}
  (AIT : ArrowIndex@{s h h} Top@{h o}) :
  ArrowIndex@{s c h} (HausdorffSpaces : Category@{c h h}) :=
  @Build_ArrowIndex (HausdorffSpaces : Category@{c h h}) (ai_index AIT)
    (fun x y f => ai_enc AIT (`1 f))
    (fun x y m d => (ai_dec AIT m (`1 d); I))
    (fun x y f d => ai_dec_enc AIT (`1 f) (`1 d)).

(* Freyd's argument: a complete category with an arrow index is thin, and
   the two points of [Bool_Discrete] are two arrows out of the point. *)
Theorem TopHaus_not_complete@{r s c hh h t sh a o p q +}
  (AI : ArrowIndex@{s c hh} HausdorffSpaces@{c hh h t sh a o p q})
  (comp : @Complete@{r s hh c} HausdorffSpaces@{c hh h t sh a o p q}) :
  False.
Proof.
  exact (freyd_no_separated_pair AI (tophaus_pt_bool true)
           (tophaus_pt_bool false) _ _
           (complete_iprod comp (fun _ : ai_index AI => TopHaus_Bool))
           (fun f => continuous_map (`1 f) ttt) (fun u v H => H ttt)
           eq_refl eq_refl).
Qed.

Theorem TopHaus_not_complete_below_IEM@{e r s c h t sh a o p q +| o < h,
    o < s, h <= c +} (E : IEM@{e})
  (comp : @Complete@{r s h c} HausdorffSpaces@{c h h t sh a o p q}) :
  False.
Proof.
  exact (TopHaus_not_complete
           (TopHaus_ArrowIndex_of_Top
              (Top_ArrowIndex_transport@{s o s h}
                 (canonical_ArrowIndex
                    (ObjDecEq_of_IEM E Top@{h o} : ObjDecEq Top@{s o}))))
           comp).
Qed.

(* [GAFT] at the Type-valued inclusion is formable ... *)
Definition GAFT_TopHaus@{h o +| o < h +}
  (comp : @Complete (Sub Top@{h o} Hausdorff_Subcategory))
  (cont : @PreservesImageLimit _ _ (Incl Top@{h o} Hausdorff_Subcategory))
  (sols : ∀ X : Top@{h o},
      SolutionSet (Incl Top@{h o} Hausdorff_Subcategory) X) :
  { H : Top@{h o} ⟶ Sub Top@{h o} Hausdorff_Subcategory &
    H ⊣ Incl Top@{h o} Hausdorff_Subcategory } :=
  GAFT (Incl Top@{h o} Hausdorff_Subcategory) comp cont sols.

(* ... and vacuous under informative excluded middle: its completeness
   premise is refuted.  The hypotheses are those of [GAFT_TopHaus] at
   every one of its universe instances. *)
Theorem GAFT_TopHaus_vacuous@{e h o u u0 u1 u2 u3 u4 u6 +| o < h, h < u1,
    h < u6, u2 < u, u3 < u, u2 <= o, u3 <= o, o <= u, u <= u4, h <= u4,
    u0 <= h, u4 <= u6 +} (E : IEM@{e})
  (comp : @Complete@{h h h u4}
            (Sub@{h h u u0 u4 h u1} Top@{h o}
               Hausdorff_Subcategory@{h u0 o u u2 u3}))
  (cont : @PreservesImageLimit@{u4 h h h u6 h u1 h} _ _
            (Incl@{h h u u0 u4 u1} Top@{h o}
               Hausdorff_Subcategory@{h u0 o u u2 u3}))
  (sols : ∀ X : Top@{h o},
      SolutionSet@{h h u4 h}
        (Incl@{h h u u0 u4 u1} Top@{h o}
           Hausdorff_Subcategory@{h u0 o u u2 u3}) X) :
  False.
Proof.
  pose proof (GAFT_TopHaus@{h o u u0 u1 u2 u3 u4 _ u6} comp cont sols) as _.
  exact (TopHaus_not_complete_below_IEM E comp).
Qed.
