Require Import Coq.Reals.Rdefinitions.
Require Import Coq.Reals.Raxioms.
Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Rbasic_fun.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.Rseries.
Require Import Coq.Reals.SeqProp.
Require Import Coq.Reals.Rcomplete.
Require Import Coq.micromega.Lra.
Require Import Coq.ZArith.ZArith.

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Subcategory.
Require Import Category.Instance.Sets.

Generalizable All Variables.

Open Scope R_scope.

(** * Metric spaces, isometries, and the complete ones *)

(* nLab:      https://ncatlab.org/nlab/show/metric+space
   nLab:      https://ncatlab.org/nlab/show/complete+metric+space
   nLab:      https://ncatlab.org/nlab/show/Cauchy+sequence
   Wikipedia: https://en.wikipedia.org/wiki/Metric_space
   Wikipedia: https://en.wikipedia.org/wiki/Complete_metric_space
   Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              GTM 5, §III.1, printed pp. 56-57 (PDF pp. 65-66) — the
              construction this file and Instance/Met/Completion.v serve
   Book:      Fong & Spivak, "Seven Sketches in Compositionality",
              §2.3.3, Definition 2.51, printed pp. 59-60 (PDF pp. 71-72) —
              the four axioms, transcribed below
   Book:      Bishop, "Foundations of Constructive Analysis", McGraw-Hill
              1967 — the constructive discipline the moduli below follow
   Paper:     Lawvere, "Metric spaces, generalized logic, and closed
              categories", Rend. Sem. Mat. Fis. Milano 43, 1973 — the
              ROAD NOT TAKEN here; see the scope note

   ON THE CITATIONS.  No book was opened for this file, and nothing below
   quotes one; every claim about what a printed source says is a paraphrase,
   and the paraphrases of Mac Lane are taken from the in-tree book
   inventory rather than from the text.  Specifically: the §III.1 reading
   used below — "the category of metric spaces and metric-preserving
   functions (necessarily injective)", with the completion as a universal
   arrow to the inclusion of the complete ones — is
   doc/plan/books/maclane/inventory/III.json's entry
   [maclane:III.1:construction3] (book p. 56, PDF pp. 65-66), and the §IV.3
   contrast is that inventory's [maclane:IV.3:construction1] (book p. 92),
   whose summary of Mac Lane's reflective-subcategory example says "metric
   spaces with uniformly continuous maps".  The Fong & Spivak page numbers
   come from doc/plan/books/seven-sketches/pagemap.md.  A reader checking
   this file against the printed books should expect the wording to differ.

   A metric space is a set of points together with a numerical distance
   between them.  The notion is Fréchet's: his 1906 thesis "Sur quelques
   points du calcul fonctionnel" isolated what he called an *écart* — a
   symmetric, vanishing-on-the-diagonal, triangle-obeying function of two
   points — precisely so that convergence arguments from analysis could be
   run on spaces whose points are functions rather than numbers.  Hausdorff's
   "Grundzüge der Mengenlehre" (1914) named the resulting object the
   *metrischer Raum* and made it the backbone of general topology; the
   separation clause (distance zero forces equality), which Fréchet had
   assumed, is exactly what distinguishes a metric from the pseudometrics
   and the generalized distances that came later.

   COMPLETION is older than the general definition, and is the reason the
   general definition was worth making.  Cantor's 1872 construction of the
   real numbers takes Cauchy sequences of rationals and identifies two of
   them when their difference tends to zero; Hausdorff observed that the
   same recipe applies verbatim to any metric space and manufactures a
   complete space containing it.  What Mac Lane adds in §III.1 is the
   observation that the recipe is not a recipe at all but a UNIVERSAL
   PROPERTY: the embedding of a space into its completion is a universal
   arrow to the inclusion of complete spaces, so the completion is
   determined up to a unique isomorphism by a factorization property and
   not by the sequences used to build it.  That is Instance/Met/Completion.v.

   THIS FILE is the base: the four axioms, the category, and the complete
   ones as a full subcategory.

   TWO NAMES THAT ARE NOT THIS ONE.

   (1) [CauchyComplete] (Construction/Karoubi/Universal.v:416) is a synonym
       of [IdempotentsSplit] — CATEGORICAL Cauchy completeness, the property
       that every idempotent of a category splits.  It is a same-name trap
       and has nothing to do with the metric completeness defined here.  The
       shared word is not an accident (Lawvere's enriched reading, below,
       makes the two instances of one notion) but nothing in this file or in
       Instance/Met/Completion.v is stated in terms of it, and no theorem
       here is imported from there.  [MComplete] below is the metric notion.

   (2) LAWVERE GENERALIZED METRIC SPACES.  Lawvere's 1973 paper reads a
       metric space as a category enriched in the poset [0,∞] with addition
       as the tensor — dropping symmetry and separation, which are the two
       axioms that have no enriched counterpart.  In-tree that reading
       appears only as prose, in the background essays of
       Theory/Profunctor.v, Construction/Enriched.v, Instance/Poset.v,
       Instance/Two.v and Construction/Karoubi.v.  This file does NOT take
       that road: [MetricSpace] below is a record with a distance FUNCTION
       and Fong & Spivak's four axioms, not an [Enriched] instance, and no
       attempt is made here to identify the two presentations.  A metric
       space in this file is symmetric and separated, so it is not a
       Lawvere metric space and the enriched machinery would not apply to
       it unchanged.

   THE CODOMAIN OF THE DISTANCE is the standard library's [R].  The choice
   is forced rather than stylistic, and the header of
   Instance/Met/Completion.v gives the argument in full; in one line, the
   distance between two Cauchy sequences is the LIMIT of the distances
   between their terms, so a codomain that is not closed under limits of
   its own Cauchy sequences cannot host the completion, and the universal
   arrow would not be statable.  [Q] is not closed under such limits.  What
   is machine-checked is the forcing half — Completion.v's
   [cdist_spec]/[cdist_unique] show the completion's distance IS that limit
   and is pinned by it — while the ℚ-specific half is classical folklore
   (√2) and is labelled as ARGUED, not proved, in that file's header.

   THE AXIOM FOOTPRINT of this file is measured per constant, not sampled.
   Mentioning [R] costs nothing (the type is a definition), but any real
   ARITHMETIC costs the two standard-library axioms [sig_forall_dec] and
   [functional_extensionality_dep], and COMPLETENESS of the reals costs
   [sig_not_dec] on top.  Exactly two constants here reach for completeness:
   [R_Metric_MComplete] and the [CMet] object [R_CMet] built from it, both
   through [R_complete].  Everything else carries at most the two, and
   [R_Setoid] and [Nat_Setoid] are closed under the global context.
   Instance/Met/Completion.v, which builds the completion, necessarily
   carries all three on most of its constants; Instance/Met/Extended.v
   carries none of [sig_not_dec] at all.

   NON-NEGATIVITY IS NOT AN AXIOM HERE.  Fong & Spivak put it in the
   codomain, writing d : X × X → ℝ≥0 and then listing four conditions.  This
   file takes the codomain to be all of [R] and lists the same four
   conditions; [dist_nonneg] below then DERIVES 0 ≤ d(x,y) from them, so
   nothing is lost and the record carries one field fewer.

   THE ARROWS ARE ISOMETRIES.  Mac Lane's §III.1 says "metric spaces and
   metric-preserving functions", with the parenthetical "(necessarily
   injective)", so the arrows are the distance-PRESERVING maps
   d(fx,fy) = d(x,y) — not the short maps d(fx,fy) ≤ d(x,y), and not the
   continuous or uniformly continuous ones.  His parenthetical is
   [isometry_injective] below, proved rather than assumed, and
   [Met_all_Monic] draws the categorical consequence.  The choice matters
   for the universal property and the reader should know that Mac Lane
   himself uses a DIFFERENT category one chapter later: the §IV.3 example of
   a reflective subcategory takes metric spaces with UNIFORMLY CONTINUOUS
   maps ([maclane:IV.3:construction1]).  Both categories have the completion
   as a universal arrow — the extension of a uniformly continuous map to the
   completion is the classical statement, and an isometry is in particular
   uniformly continuous — but they are different categories with different
   hom-sets, and NO comparison between them is built here.  This file
   formalizes the §III.1 one, which is the one the issue names.

   WHAT IS DELIVERED HERE: the record [MetricSpace] (four axioms), the
   derived non-negativity and injectivity lemmas, the category [Met], a
   reusable constructor [Metric_of_injection] and the concrete spaces
   [R_Metric], [Point_Metric] and [Harmonic], the Cauchy/convergence/
   completeness vocabulary, the full subcategory [CMet] of complete spaces
   with its inclusion, the completeness of [R_Metric] and [Point_Metric],
   and the proof that [Harmonic] is NOT complete.

   WHAT IS NOT DELIVERED HERE: any limit, colimit, monoidal or enriched
   structure on [Met]; the identification of [Met] with a subcategory of
   [Top] (the metric topology is not built); short maps, uniformly
   continuous maps, or any category of metric spaces other than the
   isometric one.  The completion itself is Instance/Met/Completion.v and
   extended metric spaces are Instance/Met/Extended.v. *)

(** ** A missing standard-library step *)

(* [Rabs_no_R0] states the contrapositive; the standard library has no
   direct form, and the round trip through it needs the decidability of
   equality on [R] ([Req_dec], itself a consequence of [total_order_T]). *)
Lemma Rabs_zero_inv (r : R) : Rabs r = 0 → r = 0.
Proof.
  intro Hr.
  destruct (Req_dec r 0) as [Hz | Hnz]; [ exact Hz |].
  now apply Rabs_no_R0 in Hnz.
Qed.

(** ** The four axioms *)

(* Fong & Spivak, Definition 2.51, clause for clause.  [dist_proper] is the
   setoid bookkeeping that a Bishop-set presentation needs and that a
   set-level presentation does not state: the distance must not distinguish
   points the carrier's own equality has already identified.  Equality of
   distances is Coq's [=] because distances are real numbers, not morphisms;
   the `≈`-never-`=` discipline of this library governs its HOMS, and the
   hom-setoid of [Met] below is pointwise `≈` in the standard way. *)
Record MetricSpace@{o} := {
  met_carrier :> SetoidObject@{o o};      (* the setoid of points *)

  dist : met_carrier → met_carrier → R;   (* the distance *)

  (* the distance respects the carrier's own equality *)
  dist_proper : ∀ x x' y y', x ≈ x' → y ≈ y' → dist x y = dist x' y';

  (* (a) zero self-distance *)
  dist_refl : ∀ x, dist x x = 0;

  (* (b) separation *)
  dist_separates : ∀ x y, dist x y = 0 → x ≈ y;

  (* (c) symmetry *)
  dist_sym : ∀ x y, dist x y = dist y x;

  (* (d) the triangle inequality *)
  dist_triangle : ∀ x y z, dist x z <= dist x y + dist y z
}.

Arguments dist {X} _ _ : rename.
Arguments dist_proper {X} _ _ _ _ _ _ : rename.
Arguments dist_refl {X} _ : rename.
Arguments dist_separates {X} _ _ _ : rename.
Arguments dist_sym {X} _ _ : rename.
Arguments dist_triangle {X} _ _ _ : rename.

(** ** What the four axioms already give *)

(* Non-negativity, which Fong & Spivak build into the codomain: run the
   triangle inequality from x to x through y, then use symmetry and the
   vanishing diagonal to read 0 ≤ 2 d(x,y). *)
Lemma dist_nonneg {X : MetricSpace} (x y : X) : 0 <= dist x y.
Proof.
  pose proof (dist_triangle x y x) as H.
  rewrite (dist_refl x), (dist_sym y x) in H.
  lra.
Qed.

(* The converse of [dist_separates]: equal points are at distance zero.
   This is [dist_proper] against [dist_refl], and it is used constantly. *)
Lemma dist_eq_zero {X : MetricSpace} (x y : X) : x ≈ y → dist x y = 0.
Proof.
  intro Hxy.
  rewrite (dist_proper x x y x (reflexivity x) (symmetry Hxy)).
  apply dist_refl.
Qed.

(* Distance vanishes exactly on the diagonal of the carrier's own equality:
   the two separation clauses packaged together. *)
Lemma dist_zero_iff {X : MetricSpace} (x y : X) : dist x y = 0 ↔ x ≈ y.
Proof.
  split.
  - apply dist_separates.
  - apply dist_eq_zero.
Qed.

(* The quadrilateral (or "four-point") inequality: distances differ by no
   more than their endpoints do.  This is the estimate that makes the
   distance function itself uniformly continuous, and it is what
   Instance/Met/Completion.v runs on — it is the reason the sequence of
   distances between two Cauchy sequences is itself Cauchy. *)
Lemma dist_quadrilateral {X : MetricSpace} (x x' y y' : X) :
  Rabs (dist x y - dist x' y') <= dist x x' + dist y y'.
Proof.
  apply Rabs_le; split.
  - pose proof (dist_triangle x' x y') as H1.
    pose proof (dist_triangle x y y') as H2.
    rewrite (dist_sym x' x) in H1.
    lra.
  - pose proof (dist_triangle x x' y) as H1.
    pose proof (dist_triangle x' y' y) as H2.
    rewrite (dist_sym y' y) in H2.
    lra.
Qed.

(** ** Isometries *)

(* Mac Lane's arrows: maps that PRESERVE the distance.  The underlying map
   is a [SetoidMorphism], so it already respects the two carriers'
   equalities; distance preservation is the extra metric condition.  This is
   the same layering [Top] uses for continuity (Instance/Top.v). *)
Record Isometry (X Y : MetricSpace) := {
  isometry_map :> SetoidMorphism (met_carrier X) (met_carrier Y);
  isometry_dist : ∀ x y : X, dist (isometry_map x) (isometry_map y) = dist x y
}.

Arguments isometry_map {X Y} _.
Arguments isometry_dist {X Y} _ _ _.

(* Mac Lane's parenthetical "(necessarily injective)", proved.  If two
   points have equal images then their images are at distance zero, so the
   points are, so they are equal.  Note where each axiom enters:
   [dist_eq_zero] on the codomain, [isometry_dist] to transport, and
   [dist_separates] on the domain. *)
Lemma isometry_injective {X Y : MetricSpace} (f : Isometry X Y) (x y : X) :
  isometry_map f x ≈ isometry_map f y → x ≈ y.
Proof.
  intro Hf.
  apply dist_separates.
  rewrite <- (isometry_dist f x y).
  now apply dist_eq_zero.
Qed.

(** ** The category Met *)

(* The hom-setoid compares only the map part, pointwise up to the
   codomain's `≈`; the distance-preservation witness is not compared.  Two
   isometries that agree on points are the same arrow of [Met], whatever
   proofs they carry — the extensional discipline of [SetoidMorphism_equiv],
   and what makes [Met] a category with no proof-irrelevance axiom. *)
Definition Isometry_equiv {X Y : MetricSpace} : crelation (Isometry X Y) :=
  fun f g => ∀ x : X, isometry_map f x ≈ isometry_map g x.

Arguments Isometry_equiv {X Y} _ _ /.

#[export]
Program Instance Isometry_Setoid {X Y : MetricSpace} :
  Setoid (Isometry X Y) := {| equiv := Isometry_equiv |}.
Next Obligation.
  constructor.
  - intros f x; reflexivity.
  - intros f g Hfg x; symmetry; exact (Hfg x).
  - intros f g h Hfg Hgh x; transitivity (isometry_map g x).
    + exact (Hfg x).
    + exact (Hgh x).
Qed.

Definition met_id {X : MetricSpace} : Isometry X X := {|
  isometry_map  := setoid_morphism_id;
  isometry_dist := fun x y => eq_refl
|}.

Definition met_compose {X Y Z : MetricSpace}
           (g : Isometry Y Z) (f : Isometry X Y) : Isometry X Z := {|
  isometry_map  := setoid_morphism_compose g f;
  isometry_dist := fun x y =>
    eq_trans (isometry_dist g (f x) (f y)) (isometry_dist f x y)
|}.

Lemma met_compose_respects {X Y Z : MetricSpace} :
  Proper (equiv ==> equiv ==> equiv) (@met_compose X Y Z).
Proof.
  intros g1 g2 Hg f1 f2 Hf x; simpl.
  rewrite (Hg (isometry_map f1 x)).
  apply proper_morphism, Hf.
Qed.

(* The category of metric spaces and metric-preserving maps.  The category
   laws hold pointwise on the map parts exactly as in [Sets]; the
   distance-preservation witnesses play no part, the hom-setoid ignoring
   them. *)
Program Definition Met : Category := {|
  obj     := MetricSpace;
  hom     := Isometry;
  homset  := @Isometry_Setoid;
  id      := @met_id;
  compose := @met_compose;

  compose_respects := @met_compose_respects
|}.

(* Every arrow of [Met] is monic — the categorical shadow of Mac Lane's
   parenthetical.  This makes [Met] a rather rigid category and is worth
   saying out loud: it is NOT a claim that [Met] is balanced, and no
   converse is proved here. *)
Lemma Met_all_Monic {X Y : Met} (f : X ~> Y) : Monic f.
Proof.
  constructor; intros z g1 g2 Hg x.
  exact (isometry_injective f (isometry_map g1 x) (isometry_map g2 x) (Hg x)).
Qed.

(* The forgetful functor to setoids.  It is faithful by construction: the
   hom-setoid of [Met] IS pointwise `≈` of the underlying maps, so
   faithfulness is the identity implication, exactly as
   Construction/Subcategory.v's [Incl_Faithful] is. *)
Program Definition Met_Forget : Met ⟶ Sets := {|
  fobj := met_carrier;
  fmap := fun _ _ f => isometry_map f
|}.

Lemma Met_Forget_Faithful : Faithful Met_Forget.
Proof. constructor; intros x y f g H; exact H. Qed.

(** ** Building metric spaces *)

(* Every injection into the reals is a metric.  This is the cheapest source
   of concrete examples and it is used three times below.  The two
   hypotheses are exactly the two halves of "[f] is injective on the
   setoid": [f_proper] makes the distance well defined, [f_injective] is
   what buys separation. *)
Section OfInjection.

(* The five lemmas below genuinely depend on the section variables; [Lib.v]
   sets [Default Proof Using "Type"], which would discard them.  Same
   reason, same remedy, as Instance/Top/Interval.v:24. *)
Local Set Default Proof Using "All".

Context (A : SetoidObject).
Context (f : A → R).
Context (f_proper : ∀ x y : A, x ≈ y → f x = f y).
Context (f_injective : ∀ x y : A, f x = f y → x ≈ y).

Let inj_dist (x y : A) : R := Rabs (f x - f y).

Lemma inj_proper : ∀ x x' y y', x ≈ x' → y ≈ y' → inj_dist x y = inj_dist x' y'.
Proof.
  intros a b c d Hab Hcd; unfold inj_dist.
  now rewrite (f_proper _ _ Hab), (f_proper _ _ Hcd).
Qed.

Lemma inj_refl : ∀ x, inj_dist x x = 0.
Proof.
  intro a; unfold inj_dist.
  replace (f a - f a) with 0 by ring.
  exact Rabs_R0.
Qed.

Lemma inj_separates : ∀ x y, inj_dist x y = 0 → x ≈ y.
Proof.
  intros a b Hab; unfold inj_dist in Hab.
  apply f_injective, Rminus_diag_uniq.
  now apply Rabs_zero_inv.
Qed.

Lemma inj_sym : ∀ x y, inj_dist x y = inj_dist y x.
Proof. intros a b; apply Rabs_minus_sym. Qed.

Lemma inj_triangle : ∀ x y z, inj_dist x z <= inj_dist x y + inj_dist y z.
Proof.
  intros a b c; unfold inj_dist.
  replace (f a - f c) with ((f a - f b) + (f b - f c)) by ring.
  apply Rabs_triang.
Qed.

Definition Metric_of_injection : MetricSpace :=
  {| met_carrier    := A;
     dist           := inj_dist;
     dist_proper    := inj_proper;
     dist_refl      := inj_refl;
     dist_separates := inj_separates;
     dist_sym       := inj_sym;
     dist_triangle  := inj_triangle |}.

End OfInjection.

Arguments Metric_of_injection A f f_proper f_injective : clear implicits.

(* The real line.  Its carrier is [R] under Leibniz equality. *)
Definition R_Setoid : SetoidObject :=
  {| carrier := R; is_setoid := {| equiv := @eq R |} |}.

Definition R_Metric : MetricSpace :=
  Metric_of_injection R_Setoid (fun r => r)
    (fun x y H => H) (fun x y H => H).

(* Distance on [R_Metric] is the absolute difference, by conversion.  This
   is the [eq_refl] exception: it is a statement about definitional
   unfolding, not about `≈`. *)
Example R_Metric_dist (x y : R_Metric) : dist x y = Rabs (x - y) := eq_refl.

(* The one-point space, over the singleton setoid [Sets_Terminal] uses.
   Everything is at distance zero from everything, and separation holds
   because the carrier has one element. *)
Definition Point_Metric : MetricSpace :=
  {| met_carrier    := unit_setoid_object;
     dist           := fun _ _ => 0;
     dist_proper    := fun _ _ _ _ _ _ => eq_refl;
     dist_refl      := fun _ => eq_refl;
     dist_separates := fun x y _ =>
       match x, y with ttt, ttt => reflexivity ttt end;
     dist_sym       := fun _ _ => eq_refl;
     dist_triangle  := fun _ _ _ => Rplus_le_le_0_compat 0 0 (Rle_refl 0) (Rle_refl 0) |}.

(** ** A concrete incomplete space *)

(* The harmonic space: the natural numbers, with n placed at 1/(n+1) on the
   real line.  It is a metric space by [Metric_of_injection], it is NOT
   complete ([Harmonic_not_MComplete] below), and its completion adds
   exactly the missing limit point 0 — which is what makes
   Instance/Met/Completion.v's non-vacuity witness concrete rather than
   nominal.  The carrier is [nat] itself, so no subsetoid machinery is
   needed anywhere. *)
Definition harm (n : nat) : R := / (INR n + 1).

Lemma harm_pos (n : nat) : 0 < harm n.
Proof.
  apply Rinv_0_lt_compat.
  pose proof (pos_INR n); lra.
Qed.

Lemma harm_injective (m n : nat) : harm m = harm n → m = n.
Proof.
  unfold harm; intro H.
  pose proof (pos_INR m); pose proof (pos_INR n).
  assert (INR m + 1 = INR n + 1) as H'.
  { rewrite <- (Rinv_inv (INR m + 1)), <- (Rinv_inv (INR n + 1)).
    now rewrite H. }
  apply INR_eq; lra.
Qed.

Definition Nat_Setoid : SetoidObject :=
  {| carrier := nat; is_setoid := {| equiv := @eq nat |} |}.

Definition Harmonic : MetricSpace :=
  Metric_of_injection Nat_Setoid harm
    (fun x y H => f_equal harm H)
    (fun x y H => harm_injective x y H).

(** ** Cauchy sequences, limits, completeness *)

(* THE MODULUS IS DATA.  This library's `∃` is [sigT] (Lib/Foundation.v:61,
   66), so [MCauchy] below is TYPE-valued and a Cauchy sequence hands out
   its threshold N as a function of ε rather than merely asserting that one
   exists.  That is not decoration: Instance/Met/Completion.v proves the
   completion complete by a diagonal argument that CONSUMES one threshold
   per index, and extracting a sequence of thresholds from a sequence of
   Prop-level existentials is countable choice.  With the modulus as data no
   choice principle is used anywhere in this development.

   The reading is Bishop's, and it is worth being precise about its
   strength: "every sequence PRESENTED WITH A MODULUS converges" is
   constructively weaker than the classical "every Cauchy sequence
   converges", the two being interderivable only via countable choice.
   [MComplete] is the former.  No claim is made here that the two agree.

   THE DIRECTION MATTERS, in both places the notion is used.  Because
   [MComplete] is the WEAKER property, PROVING it — as
   [Completion_MComplete] does — is the weaker positive statement, while
   REFUTING it — as [Harmonic_not_MComplete] does — is the STRONGER negative
   one: the witnessing sequence [fun n => n] carries an explicit modulus
   ([harm_seq_MCauchy]), so the harmonic space is incomplete already in this
   restricted sense and therefore in the classical sense as well.

   Note also that the BODY of each `∃` is a Prop ([Rlt] is Prop-valued), so
   a threshold, once produced, may be shown to work by any Prop-level
   reasoning whatever — which is how [R_Metric_MComplete] below bridges to
   the standard library's Prop-valued [Un_cv]. *)

Definition MCauchy (X : MetricSpace) (u : nat → X) : Type :=
  ∀ eps : R, 0 < eps →
    ∃ N : nat, ∀ m n : nat, (N <= m)%nat → (N <= n)%nat → dist (u m) (u n) < eps.

Definition MConverges (X : MetricSpace) (u : nat → X) (l : X) : Type :=
  ∀ eps : R, 0 < eps →
    ∃ N : nat, ∀ n : nat, (N <= n)%nat → dist (u n) l < eps.

Definition MComplete (X : MetricSpace) : Type :=
  ∀ u : nat → X, MCauchy X u → ∃ l : X, MConverges X u l.

(* Limits are unique up to the carrier's own equality.  This is where
   separation earns its place among the axioms: without it a sequence could
   converge to two genuinely different points. *)
Lemma MConverges_unique {X : MetricSpace} (u : nat → X) (l l' : X) :
  MConverges X u l → MConverges X u l' → l ≈ l'.
Proof.
  intros Hl Hl'.
  apply dist_separates.
  (* 0 ≤ d(l,l') and d(l,l') < ε for every ε > 0, hence d(l,l') = 0. *)
  assert (∀ eps : R, 0 < eps → dist l l' < eps) as Hsmall.
  { intros eps Heps.
    destruct (Hl (eps / 2) ltac:(lra)) as [N1 HN1].
    destruct (Hl' (eps / 2) ltac:(lra)) as [N2 HN2].
    pose (n := Nat.max N1 N2).
    specialize (HN1 n (Nat.le_max_l N1 N2)).
    specialize (HN2 n (Nat.le_max_r N1 N2)).
    pose proof (dist_triangle l (u n) l') as Htri.
    rewrite (dist_sym l (u n)) in Htri.
    lra. }
  pose proof (dist_nonneg l l') as Hpos.
  destruct (Rle_lt_or_eq_dec 0 (dist l l') Hpos) as [Hlt | Heq].
  - exfalso. specialize (Hsmall (dist l l') Hlt). lra.
  - now symmetry.
Qed.

(* A convergent sequence is Cauchy.  The Cauchy modulus is produced from the
   convergence modulus at ε/2 — data from data, no choice. *)
Lemma MConverges_MCauchy {X : MetricSpace} (u : nat → X) (l : X) :
  MConverges X u l → MCauchy X u.
Proof.
  intros Hl eps Heps.
  destruct (Hl (eps / 2) ltac:(lra)) as [N HN].
  exists N; intros m n Hm Hn.
  pose proof (dist_triangle (u m) l (u n)) as Htri.
  rewrite (dist_sym l (u n)) in Htri.
  pose proof (HN m Hm) as H1.
  pose proof (HN n Hn) as H2.
  lra.
Qed.

(* An isometry carries Cauchy sequences to Cauchy sequences and limits to
   limits, on the nose: the ε and the threshold are unchanged, because the
   distances themselves are unchanged.  Both are used by the completion's
   universal property. *)
Lemma isometry_MCauchy {X Y : MetricSpace} (f : Isometry X Y) (u : nat → X) :
  MCauchy X u → MCauchy Y (fun n => isometry_map f (u n)).
Proof.
  intros Hu eps Heps.
  destruct (Hu eps Heps) as [N HN].
  exists N; intros m n Hm Hn.
  rewrite (isometry_dist f (u m) (u n)).
  now apply HN.
Qed.

Lemma isometry_MConverges {X Y : MetricSpace} (f : Isometry X Y)
      (u : nat → X) (l : X) :
  MConverges X u l → MConverges Y (fun n => isometry_map f (u n)) (isometry_map f l).
Proof.
  intros Hu eps Heps.
  destruct (Hu eps Heps) as [N HN].
  exists N; intros n Hn.
  rewrite (isometry_dist f (u n) l).
  now apply HN.
Qed.

(** ** The full subcategory of complete spaces *)

(* Written with [Build_Subcategory] rather than [Program] for the reason
   Construction/Subcategory/Terminal.v gives: obligations discharged by
   [Qed] are opaque to the unifier, and [shom] here has to reduce. *)
Definition CompleteSpaces : Subcategory Met :=
  @Build_Subcategory Met
    (fun X => MComplete X)              (* the complete spaces *)
    (fun _ _ _ _ _ => True)             (* full: every isometry is kept *)
    (fun _ _ _ _ _ _ _ _ _ _ => I)      (* closed under composition *)
    (fun _ _ => I).                     (* closed under identities *)

Definition CMet : Category := Sub Met CompleteSpaces.

Definition CMet_Incl : CMet ⟶ Met := Incl Met CompleteSpaces.

Definition CMet_Full : Construction.Subcategory.Full Met CompleteSpaces :=
  fun _ _ _ _ _ => I.

Definition CMet_Incl_Faithful : Faithful CMet_Incl :=
  Incl_Faithful Met CompleteSpaces.

Definition CMet_Incl_Full : Functor.Full CMet_Incl :=
  Full_Implies_Full_Functor Met CompleteSpaces CMet_Full.

(* Note that an object of [CMet] is a space TOGETHER WITH a chosen
   completeness witness, [MComplete] being proof-relevant data (it computes
   limits).  Two witnesses for one space give distinct but isomorphic
   objects of [CMet]; that is [Full_membership_iso]
   (Construction/Subcategory.v) and is the standard situation for full
   subcategories in this library, not a defect of this one. *)

(** ** Complete and incomplete witnesses *)

(* The one-point space is complete: every sequence converges to the point,
   with threshold 0. *)
Definition Point_Metric_MComplete : MComplete Point_Metric :=
  fun u _ => (ttt; fun eps Heps => (0%nat; fun n _ => Heps)).

(* The real line is complete.  The limit comes from the standard library's
   [R_complete]; the CONVERGENCE MODULUS is produced here from the Cauchy
   modulus at ε/2, which is data, and the inequality it has to satisfy is a
   Prop and so may be argued with the Prop-valued [Un_cv] that [R_complete]
   returns.  This is the bridge the header describes. *)
Lemma R_Metric_MComplete : MComplete R_Metric.
Proof.
  intros u Hu.
  (* The standard library's Cauchy criterion, from our modulus. *)
  assert (Cauchy_crit u) as Hcc.
  { intros eps Heps.
    destruct (Hu eps ltac:(lra)) as [N HN].
    exists N; intros n m Hn Hm.
    unfold R_dist.
    exact (HN n m Hn Hm). }
  destruct (R_complete u Hcc) as [l Hl].
  exists l; intros eps Heps.
  destruct (Hu (eps / 2) ltac:(lra)) as [N HN].
  exists N; intros n Hn.
  (* |u n - l| ≤ |u n - u m| + |u m - l| for a suitable m ≥ N chosen by the
     Prop-level convergence; the goal is a Prop, so this is legitimate. *)
  destruct (Hl (eps / 2) ltac:(lra)) as [M HM].
  pose (m := Nat.max N M).
  assert (R_dist (u m) l < eps / 2) as H1 by (apply HM; apply Nat.le_max_r).
  assert (dist (u n) (u m) < eps / 2) as H2
      by (apply HN; [ exact Hn | apply Nat.le_max_l ]).
  pose proof (dist_triangle (X:=R_Metric) (u n) (u m) l) as Htri.
  unfold R_dist in H1.
  change (dist (X:=R_Metric) (u m) l) with (Rabs (u m - l)) in *.
  lra.
Qed.

(* [CMet] is inhabited, twice over. *)
Definition R_CMet : CMet := (R_Metric; R_Metric_MComplete).
Definition Point_CMet : CMet := (Point_Metric; Point_Metric_MComplete).

(** ** The harmonic space is not complete *)

(* An archimedean modulus, as DATA: [up] is a function, and [archimed] is
   the Prop that certifies it. *)
Definition harm_mod (eps : R) : nat := Z.to_nat (up (/ eps)).

Lemma harm_antitone (m n : nat) : (m <= n)%nat → harm n <= harm m.
Proof.
  intro Hmn; unfold harm.
  apply Rinv_le_contravar.
  - pose proof (pos_INR m); lra.
  - apply Rplus_le_compat_r, le_INR, Hmn.
Qed.

Lemma harm_mod_spec (eps : R) : 0 < eps → harm (harm_mod eps) < eps.
Proof.
  intro Heps.
  assert (0 < / eps) as Hinv by (apply Rinv_0_lt_compat, Heps).
  destruct (archimed (/ eps)) as [Hup _].
  assert (0 <= up (/ eps))%Z as Hnn.
  { apply le_IZR; simpl; lra. }
  assert (INR (harm_mod eps) = IZR (up (/ eps))) as Heq.
  { unfold harm_mod. rewrite INR_IZR_INZ, Z2Nat.id by exact Hnn. reflexivity. }
  unfold harm; rewrite Heq.
  (* / eps < IZR (up (/eps)) < IZR (up (/eps)) + 1, so the reciprocal is < eps. *)
  assert (/ eps < IZR (up (/ eps)) + 1) as Hlt by lra.
  apply (Rmult_lt_reg_l (IZR (up (/ eps)) + 1)); [ lra |].
  rewrite Rinv_r by lra.
  apply (Rmult_lt_reg_r (/ eps)); [ exact Hinv |].
  rewrite Rmult_1_l, Rmult_assoc, Rinv_r by lra.
  lra.
Qed.

(* Past index 2l+1 the harmonic sequence has dropped below half of harm l.
   Used both here and, in Instance/Met/Completion.v, to show that the class
   of the identity sequence is not in the image of the embedding. *)
Lemma harm_half (l n : nat) : (2 * l + 1 <= n)%nat → harm n <= harm l / 2.
Proof.
  intro Hn.
  transitivity (harm (2 * l + 1)); [ now apply harm_antitone |].
  unfold harm.
  rewrite plus_INR, mult_INR.
  replace (INR 2 * INR l + INR 1 + 1) with (2 * (INR l + 1)) by (simpl; lra).
  rewrite Rinv_mult.
  pose proof (pos_INR l); lra.
Qed.

(* The identity sequence of the harmonic space is Cauchy. *)
Lemma harm_seq_MCauchy : MCauchy Harmonic (fun n => n).
Proof.
  intros eps Heps.
  exists (harm_mod eps); intros m n Hm Hn.
  pose proof (harm_mod_spec eps Heps) as Hsmall.
  pose proof (harm_antitone _ _ Hm) as Hm'.
  pose proof (harm_antitone _ _ Hn) as Hn'.
  pose proof (harm_pos m); pose proof (harm_pos n).
  change (Rabs (harm m - harm n) < eps).
  apply Rabs_def1; lra.
Qed.

(* ... and it has no limit in the space.  Every point k sits at 1/(k+1) > 0,
   while the sequence runs down to 0; taking ε = 1/(2(k+1)) and an index
   past 2k+1 separates them. *)
Lemma harm_seq_no_limit (l : Harmonic) :
  MConverges Harmonic (fun n => n) l → False.
Proof.
  intro Hl.
  pose proof (harm_pos l) as Hlpos.
  destruct (Hl (harm l / 2) ltac:(lra)) as [N HN].
  pose (n := Nat.max N (2 * l + 1)).
  assert (N <= n)%nat as Hn by apply Nat.le_max_l.
  specialize (HN n Hn).
  change (Rabs (harm n - harm l) < harm l / 2) in HN.
  pose proof (harm_half l n (Nat.le_max_r N (2 * l + 1))) as Hsmall.
  pose proof (harm_pos n).
  rewrite Rabs_left1 in HN by lra.
  lra.
Qed.

Lemma Harmonic_not_MComplete : MComplete Harmonic → False.
Proof.
  intro Hc.
  destruct (Hc (fun n => n) harm_seq_MCauchy) as [l Hl].
  exact (harm_seq_no_limit l Hl).
Qed.
