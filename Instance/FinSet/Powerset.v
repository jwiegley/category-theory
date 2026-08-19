Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Subobject.
Require Import Category.Theory.Subobject.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.SubobjectClassifier.
Require Import Category.Structure.SubobjectClassifier.Natural.
Require Import Category.Structure.Topos.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Product.
Require Import Category.Instance.FinSet.Closed.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Topos.
Require Import Category.Theory.Universal.Element.

Require Import Coq.Vectors.Fin.

Generalizable All Variables.

(** * The contravariant power-set functor on skeletal [FinSet], computably *)

(* nLab:      https://ncatlab.org/nlab/show/universal+element
   nLab:      https://ncatlab.org/nlab/show/subobject+classifier
   Wikipedia: https://en.wikipedia.org/wiki/Power_set

   Mac Lane asks (CWM 2nd ed., §III.1, Exercise 2, printed p. 59) for a
   universal element of the contravariant power-set functor, and the
   classical answer is the pair ⟨2, {1}⟩.  Riehl states the same example
   (Category Theory in Context, 2nd ed., §2.3 Example 2.3.6, printed
   p. 68) with the emphasis that the universal element is the SUBSET
   {⊤} ∈ P(Ω), an element of the functor's VALUE at Ω, and not the POINT
   ⊤ ∈ Ω, the isomorphism sending f : A ⟶ Ω to the subset f⁻¹(⊤) ⊆ A.
   Awodey runs the correspondence for Sets (Category Theory, §5.3
   Example 5.14, printed pp. 104-106), where the punchline is that it is
   NATURAL in the object.

   ATTRIBUTION.  The section-and-page coordinates above, and the one-line
   summaries of what those passages contain, are reproduced from the
   catalogue entry of the issue this file answers
   (jwiegley/category-theory#311, items maclane:III.1:ex2,
   riehl:2.3:example6, awodey:5.3:example14); the printed texts were not
   consulted while writing the file, so every statement here about their
   content is the issue's characterization rather than a reading of the
   books.  The mathematics stands on its own proofs.

   WHY THIS FILE EXISTS ALONGSIDE Instance/Sets/Powerset/Universal.v.
   That file answers the same exercise over [Sets], where a subset of A
   is a [Prop]-valued predicate on A and is therefore, by construction,
   already a map A ⟶ Ω; the correspondence there is genuine but its
   content is thin, being the single equivalence "membership in {⊤}
   detects truth".  Here nothing is definitional: the power set of the
   n-element set is the 2^n-element set, subsets are ELEMENTS of it, and
   the passage between a subset and its characteristic map is the digit
   codec of Instance/FinSet/Closed.v.  Both round trips of that codec hold
   at LEIBNIZ equality ([fin_apply_tabulate], [fin_tabulate_apply]), which
   is what lets the universal property below be proved without a single
   setoid manoeuvre, and lets the whole correspondence COMPUTE — the
   acceptance tests at the end are [eq_refl] on closed data.

   WHAT THIS FILE DELIVERS, AND AT WHICH STRENGTH.

     (1) [FinPowerset : FinSet^op ⟶ FinSet] — the contravariant power-set
         functor INSIDE [FinSet], object action n ↦ 2^n, arrow action the
         inverse image.  Both functor laws close at Leibniz equality of
         codes through [fin_tabulate_apply] and [fin_apply_tabulate];
         [FinSet]'s hom-setoid is pointwise [=] ([fun_setoid]), so those
         are the honest statements, not weakenings.

     (2) [FinPowerset_Sets : FinSet^op ⟶ Sets] — the same functor read
         into [Sets], which is the shape [AUniversalElement] requires of
         its [H].  [finpowerset_sets_agrees] records by [eq_refl] that the
         two have the same arrow action, so (2) is (1) retyped and not a
         second construction.

     (3) [FinPowerset_universal_element] — Mac Lane's §III.1 clause, the
         pair ⟨2, {⊤}⟩, through Theory/Universal/Element.v's
         [AUniversalElement].  The universal element is
         [finpow_truth_subset : Fin.t 4], an element of P(2), NOT the
         point [fin_true : Fin.t 2]; the two have different types, and
         Test/ProbePowersetUniversal.v pins the substitution as a type
         error against a positive control.

     (4) Riehl's preimage description, PROVED and not merely asserted:
         [finpow_fmap_is_preimage] says that the i-th digit of
         [P k {⊤}] is [k i] itself, so [finpow_preimage_iff] reads off
         that i belongs to [P k {⊤}] exactly when [k i] is [fin_true] —
         that is, that the functor's action on k applied to the universal
         element IS k⁻¹(⊤).  [finpow_preimage_of_truth] collects the
         digits: pulling {⊤} back along k returns the CODE of k.

     (5) [FinSet_Sub_natural] — Awodey's naturality clause instantiated at
         [FinSet_Classifier]: the subobject presheaf of [FinSet] is
         naturally isomorphic to [Hom(─, 2)].  This is
         Structure/SubobjectClassifier/Natural.v applied, not reproved.

     (6) [FinSet_Sub_powerset] — the two are joined:
         [Sub ≅ FinPowerset_Sets] in [[FinSet^op, Sets]].  So on [FinSet]
         the power-set functor of (2) and the subobject functor of
         Theory/Subobject/Functor.v are the same presheaf, naturally.  The
         middle term is [Hom(─,2)] and the second leg is the codec.

   THE PRIOR ART, measured against the parent commit rather than restated
   from the issue.  There was no [Instance/FinSet/PowerSet.v] and no
   power-set functor of any kind over [FinSet]; the only power-set
   functors over a Sets-like category at one level were the four in
   Instance/Sets/Powerset.v, none of them contravariant at a single
   universe level (Instance/Concrete.v:295's [Rel_Powerset : Rel ⟶ Sets]
   is a fifth, but it is COVARIANT and out of [Rel], so it bears on
   neither), and no universal
   element was stated for any of them.  Instance/Sets/Powerset/Universal.v
   carries the fuller correction, including why the issue's "no power-set
   functor" reading of the prior art would be wrong.

     (7) [finpow_is_topos_Pow] — the object action AGREES with
         Structure/Topos.v's internal power object [Pow a := Ω ^ a] at
         [FinSet_Topos], by [eq_refl].  ([exponent_obj m n] of
         [FinSet_Closed] is [n ^ m], so [Ω ^ n] at Ω = 2 is [2 ^ n].)

   WHAT IS NOT DELIVERED.  No claim is made that [FinPowerset] is a monad.
   [finpow_is_topos_Pow] identifies the OBJECT actions with the internal
   power object and nothing further: no comparison morphism is built, and
   the internal version has no arrow action to compare with — that is
   exactly the gap Instance/Sets/Powerset.v's header records about
   [Structure/Topos.v:129].  Nothing here is stated for a general topos,
   and the [Sub ≅ FinPowerset_Sets] comparison lives in [[FinSet^op, Sets]]
   rather than inside [FinSet]. *)

(* ------------------------------------------------------------------------ *)
(** ** The power set of a finite set, and the inverse image *)

(* The power set of the n-element set is the 2^n-element set: a subset is a
   digit string, one binary digit per element.  The codec
   [fin_tabulate] / [fin_apply] of Instance/FinSet/Closed.v is exactly the
   passage between such a string and the characteristic function it
   encodes, so no new encoding is introduced here. *)

Definition finpow (n : nat) : nat := Nat.pow 2 n.

(* Membership, as a decidable test: i belongs to the subset coded by S when
   the i-th digit of S is [fin_true].  ([fin_true] is [Fin.F1] and
   [fin_false] is [Fin.FS Fin.F1] — Instance/FinSet/Classifier.v's
   convention, adopted here unchanged so that the classifier connection
   below needs no translation.) *)
Definition finpow_mem {n : nat} (S : Fin.t (finpow n)) (i : Fin.t n) : bool :=
  fin_eqb (fin_apply S i) fin_true.

(* The inverse image: the subset of the domain whose i-th digit is the digit
   of S at [f i]. *)
Definition finpow_map {m n : nat} (f : Fin.t n → Fin.t m)
  (S : Fin.t (finpow m)) : Fin.t (finpow n) :=
  fin_tabulate (fun i : Fin.t n => fin_apply S (f i)).

Lemma finpow_map_mem {m n : nat} (f : Fin.t n → Fin.t m)
  (S : Fin.t (finpow m)) (i : Fin.t n) :
  finpow_mem (finpow_map f S) i = finpow_mem S (f i).
Proof. unfold finpow_mem, finpow_map; now rewrite fin_apply_tabulate. Qed.

(* The two functor laws.  Both are Leibniz equations between codes, which
   is exactly the pointwise [=] that [FinSet]'s hom-setoid IS (see the
   header note above: [fun_setoid] over the discrete [Fin_Setoid]), not a
   strengthening of it, and each is one rewrite with a codec round trip. *)

Lemma finpow_map_id {n : nat} (S : Fin.t (finpow n)) :
  finpow_map (fun i : Fin.t n => i) S = S.
Proof. unfold finpow_map; apply fin_tabulate_apply. Qed.

Lemma finpow_map_comp {m n p : nat}
  (f : Fin.t n → Fin.t m) (g : Fin.t p → Fin.t n) (S : Fin.t (finpow m)) :
  finpow_map (fun i => f (g i)) S = finpow_map g (finpow_map f S).
Proof.
  unfold finpow_map.
  apply fin_tabulate_ext; intro i.
  now rewrite fin_apply_tabulate.
Qed.

Lemma finpow_map_ext {m n : nat} (f g : Fin.t n → Fin.t m)
  (H : ∀ i, f i = g i) (S : Fin.t (finpow m)) :
  finpow_map f S = finpow_map g S.
Proof. unfold finpow_map; apply fin_tabulate_ext; intro i; now rewrite H. Qed.

(* ------------------------------------------------------------------------ *)
(** ** The functor, twice *)

(* Inside [FinSet].  An arrow x ~> y of [FinSet^op] is an arrow y ~> x of
   [FinSet], so the action on it lands where it should. *)
Program Definition FinPowerset : FinSet^op ⟶ FinSet := {|
  fobj := finpow ;
  fmap := fun x y (f : x ~{FinSet^op}~> y) => finpow_map f
|}.
Next Obligation. repeat intro; now apply finpow_map_ext. Qed.
Next Obligation. now apply finpow_map_id. Qed.
Next Obligation. now apply finpow_map_comp. Qed.

(* ... and into [Sets], which is what [AUniversalElement] needs of its
   functor.  The carrier setoid is the discrete one on [Fin.t (2^n)]; it is
   Instance/Sets/Powerset.v's universe-polymorphic [Powerset_Prop_fin_object]
   rather than a third private copy of the same three-line record. *)
Program Definition FinPowerset_Sets : FinSet^op ⟶ Sets := {|
  fobj := fun n => Powerset_Prop_fin_object (finpow n) ;
  fmap := fun x y (f : x ~{FinSet^op}~> y) =>
            {| morphism := finpow_map f |}
|}.
Next Obligation.
  (* [exact] rather than [apply]: the goal is a projection out of a record
     literal, which [apply]'s unifier declines to reduce here. *)
  repeat intro; exact (finpow_map_ext x0 y0 H x1).
Qed.
Next Obligation. now apply finpow_map_id. Qed.
Next Obligation. now apply finpow_map_comp. Qed.

(* The two carry the same arrow action, by [eq_refl] — the convertibility
   exception, flagged as such.  So (2) is (1) retyped. *)
Example finpowerset_sets_agrees {x y : FinSet} (f : x ~{FinSet^op}~> y)
  (S : Fin.t (finpow x)) :
  fmap[FinPowerset_Sets] f S = fmap[FinPowerset] f S := eq_refl.

Example finpowerset_obj (n : nat) : fobj[FinPowerset] n = Nat.pow 2 n := eq_refl.

Example finpowerset_two : fobj[FinPowerset] 2%nat = 4%nat := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Ω, the point ⊤, and the SUBSET {⊤} *)

(* The truth-value object of [FinSet_Classifier] is 2, and its point is
   [fin_true].  The universal element is NOT that point: it is the subset
   {⊤} ⊆ 2, an element of P(2) = 4, namely the digit string whose
   [fin_true] digit is [fin_true] and whose [fin_false] digit is
   [fin_false] — that is, the code of the identity function on 2. *)

Definition finpow_truth_point : Fin.t 2 := fin_true.

Definition finpow_truth_subset : Fin.t (finpow 2) :=
  fin_tabulate (fun i : Fin.t 2 => i).

(* It really is {⊤}: ⊤ is in it and ⊥ is not, by computation. *)
Example finpow_truth_has_true :
  finpow_mem finpow_truth_subset fin_true = true := eq_refl.

Example finpow_truth_lacks_false :
  finpow_mem finpow_truth_subset fin_false = false := eq_refl.

(* ... and the digit at j is j itself, for every j — the general form of the
   two computations above, which is what the universal property consumes. *)
Lemma finpow_truth_digit (j : Fin.t 2) : fin_apply finpow_truth_subset j = j.
Proof. unfold finpow_truth_subset; apply fin_apply_tabulate. Qed.

(* ------------------------------------------------------------------------ *)
(** ** Mac Lane's §III.1 universal element ⟨2, {⊤}⟩ *)

(* THE PREIMAGE DESCRIPTION, PROVED FIRST, because it is what makes the
   universal property mean what Riehl says it means: the action of the
   functor on k, applied to {⊤}, is the preimage k⁻¹(⊤). *)

Lemma finpow_fmap_is_preimage {n : nat} (k : Fin.t n → Fin.t 2)
  (i : Fin.t n) :
  fin_apply (finpow_map k finpow_truth_subset) i = k i.
Proof.
  unfold finpow_map; rewrite fin_apply_tabulate; apply finpow_truth_digit.
Qed.

Lemma finpow_preimage_iff {n : nat} (k : Fin.t n → Fin.t 2) (i : Fin.t n) :
  finpow_mem (finpow_map k finpow_truth_subset) i = fin_eqb (k i) fin_true.
Proof. unfold finpow_mem; now rewrite finpow_fmap_is_preimage. Qed.

(* Pulling {⊤} back along k recovers the code of k on the nose — this is the
   preimage law with the digits collected, and it is the whole universal
   property once [fin_tabulate]/[fin_apply] are known to be inverse. *)
Lemma finpow_preimage_of_truth {n : nat} (k : Fin.t n → Fin.t 2) :
  finpow_map k finpow_truth_subset = fin_tabulate k.
Proof.
  unfold finpow_map; apply fin_tabulate_ext; intro i; apply finpow_truth_digit.
Qed.

(* Mac Lane's clause at D := FinSet^op and H := FinPowerset_Sets: for every
   object n and every subset S of n there is a UNIQUE arrow
   k : 2 ~{FinSet^op}~> n — that is, a unique function n → 2 — with
   k⁻¹(⊤) = S.  The witness is [fin_apply S], the characteristic function
   read off the digit string. *)
Program Definition FinPowerset_universal_element :
  @AUniversalElement (FinSet^op) FinPowerset_Sets 2%nat := {|
  aue_elem := finpow_truth_subset ;
  aue_universal := fun n S => {| unique_obj := fin_apply S |}
|}.
Next Obligation.
  rewrite finpow_preimage_of_truth; apply fin_tabulate_apply.
Qed.
Next Obligation.
  (* Uniqueness.  [Program] has already substituted S by k⁻¹(⊤) and
     introduced the point, so the goal IS the preimage law. *)
  apply finpow_fmap_is_preimage.
Qed.

(* The element of the pair is {⊤} and the mediating arrow of a subset is its
   characteristic function, both by [eq_refl]. *)
Example finpow_aue_elem :
  @aue_elem (FinSet^op) FinPowerset_Sets 2%nat FinPowerset_universal_element
    = finpow_truth_subset := eq_refl.

Example finpow_aue_med (n : nat) (S : Fin.t (finpow n)) :
  unique_obj (@aue_universal (FinSet^op) FinPowerset_Sets 2%nat
                FinPowerset_universal_element n S)
    = fin_apply S := eq_refl.

(* The representation, through the Yoneda-FREE route of
   Theory/Universal/Element.v.  (The Yoneda route is unavailable at [Sets]
   for universe reasons recorded in Instance/Sets/Powerset/Universal.v; it
   is not taken here either, so that both files go the same way and the
   comparison between them is not confounded.) *)
Definition FinPowerset_representation :
  @Curried_Hom (FinSet^op) 2%nat
    ≅[[(FinSet^op), Sets]] FinPowerset_Sets :=
  ue_representation FinPowerset_Sets 2%nat FinPowerset_universal_element.

Example finpow_representation_to_is_preimage (n : nat)
  (k : n ~{FinSet}~> 2%nat) :
  transform (to FinPowerset_representation) n k
    = finpow_map k finpow_truth_subset := eq_refl.

Definition FinPowerset_Representable : Representable FinPowerset_Sets :=
  Representable_of_UniversalElement
    (UniversalElement_of_AUniversalElement FinPowerset_universal_element).

Example finpow_repr_obj :
  @repr_obj (FinSet^op) FinPowerset_Sets FinPowerset_Representable = 2%nat
  := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** Awodey's naturality clause at [FinSet_Classifier] *)

(* Structure/SubobjectClassifier/Natural.v applied — nothing is reproved.
   [Ω] of [FinSet_Classifier] is 2 on the nose, so the target is literally
   [Hom(─, 2)]. *)
Definition FinSet_Sub_natural :
  @Isomorphism ([(FinSet^op), Sets])
    (@Sub FinSet FinSet_Pullbacks) (@Curried_CoHom FinSet 2%nat)
  := @Sub_classifier_natural FinSet FinSet_Terminal FinSet_Pullbacks
       FinSet_Classifier.

Definition FinSet_Sub_Representable : Representable (@Sub FinSet FinSet_Pullbacks)
  := @Sub_Representable FinSet FinSet_Terminal FinSet_Pullbacks
       FinSet_Classifier.

Example FinSet_Sub_repr_obj :
  @repr_obj (FinSet^op) (@Sub FinSet FinSet_Pullbacks) FinSet_Sub_Representable
    = 2%nat := eq_refl.

(* ------------------------------------------------------------------------ *)
(** ** The subobject presheaf of [FinSet] IS the power-set functor *)

(* The codec, as a natural isomorphism [Hom(─,2) ≅ FinPowerset_Sets].  Its
   naturality is one application of [fin_apply_tabulate]; both round trips
   are the codec's own Leibniz equations. *)

(* The two naturality equations of the codec, isolated so that the seven
   obligations below — six of which reach a [Next Obligation] — can be
   discharged by one tactic that tries each in both
   orientations — [Program] emits them in an order that is not worth
   predicting, and a mis-guessed order is the only thing a hand-written list
   would be recording. *)

Lemma codec_natural_to {m n : nat} (f : Fin.t n → Fin.t m)
  (k : Fin.t m → Fin.t 2) :
  finpow_map f (fin_tabulate k) = fin_tabulate (fun i => k (f i)).
Proof.
  unfold finpow_map; apply fin_tabulate_ext; intro i.
  now rewrite fin_apply_tabulate.
Qed.

Lemma codec_natural_from {m n : nat} (f : Fin.t n → Fin.t m)
  (S : Fin.t (finpow m)) (i : Fin.t n) :
  fin_apply (finpow_map f S) i = fin_apply S (f i).
Proof. unfold finpow_map; now rewrite fin_apply_tabulate. Qed.

Local Ltac codec :=
  simpl; repeat intro;
  first [ exact (codec_natural_from _ _ _)
        | symmetry; exact (codec_natural_from _ _ _)
        | exact (codec_natural_to _ _)
        | symmetry; exact (codec_natural_to _ _)
        | apply fin_tabulate_apply
        | symmetry; apply fin_tabulate_apply
        | apply fin_apply_tabulate
        | symmetry; apply fin_apply_tabulate
        | apply fin_tabulate_ext; assumption
        | symmetry; apply fin_tabulate_ext; assumption
        | subst; reflexivity
        | reflexivity ].

Program Definition finpow_codec :
  @Isomorphism ([(FinSet^op), Sets])
    (@Curried_CoHom FinSet 2%nat) FinPowerset_Sets := {|
  to   := {| transform := fun n => {| morphism := fun k : Fin.t n -> Fin.t 2 =>
                                        fin_tabulate k |} |} ;
  from := {| transform := fun n => {| morphism := fun S : Fin.t (finpow n) =>
                                        fin_apply S |} |}
|}.
Next Obligation. codec. Qed.
Next Obligation. codec. Qed.
Next Obligation. codec. Qed.
Next Obligation. codec. Qed.
Next Obligation. codec. Qed.
Next Obligation. codec. Qed.

(* THE CAPSTONE.  Subobjects of a finite set are its subsets, naturally. *)
Definition FinSet_Sub_powerset :
  @Isomorphism ([(FinSet^op), Sets])
    (@Sub FinSet FinSet_Pullbacks) FinPowerset_Sets :=
  iso_compose finpow_codec FinSet_Sub_natural.

(* ------------------------------------------------------------------------ *)
(** ** Non-vacuity: the correspondence computing on a concrete subset *)

(* The subset {0, 2} ⊆ 3, as a digit string. *)
Definition finpow_sub02 : Fin.t (finpow 3) :=
  fin_tabulate (fun i : Fin.t 3 =>
    match i with
    | Fin.F1 => fin_true
    | Fin.FS Fin.F1 => fin_false
    | _ => fin_true
    end).

(* Its three membership digits, by computation. *)
Example finpow_sub02_at_0 : finpow_mem finpow_sub02 Fin.F1 = true := eq_refl.
Example finpow_sub02_at_1 :
  finpow_mem finpow_sub02 (Fin.FS Fin.F1) = false := eq_refl.
Example finpow_sub02_at_2 :
  finpow_mem finpow_sub02 (Fin.FS (Fin.FS Fin.F1)) = true := eq_refl.

(* The mediating arrow produced by the universal property is its
   characteristic function, and it takes the expected values — computed
   through the class accessor, not through [fin_apply] directly, so what is
   being checked is the universal element and not the codec. *)
Definition finpow_char02 : Fin.t 3 → Fin.t 2 :=
  unique_obj (@aue_universal (FinSet^op) FinPowerset_Sets 2%nat
                FinPowerset_universal_element 3%nat finpow_sub02).

Example finpow_char02_at_0 : finpow_char02 Fin.F1 = fin_true := eq_refl.
Example finpow_char02_at_1 :
  finpow_char02 (Fin.FS Fin.F1) = fin_false := eq_refl.
Example finpow_char02_at_2 :
  finpow_char02 (Fin.FS (Fin.FS Fin.F1)) = fin_true := eq_refl.

(* The round trip: the preimage of {⊤} along that characteristic map is the
   subset again, by computation on closed data. *)
Example finpow_round02 :
  finpow_map finpow_char02 finpow_truth_subset = finpow_sub02 := eq_refl.

(* A DEGENERACY EXCLUDED BY PROOF: distinct subsets have distinct
   characteristic maps, so the correspondence is not collapsing anything.
   The witness is {0,2} against the EMPTY subset. *)
Definition finpow_empty : Fin.t (finpow 3) :=
  fin_tabulate (fun _ : Fin.t 3 => fin_false).

Example finpow_empty_has_nothing (i : Fin.t 3) :
  finpow_mem finpow_empty i = false.
Proof. unfold finpow_mem, finpow_empty; now rewrite fin_apply_tabulate. Qed.

Example finpow_sub02_ne_empty : finpow_sub02 = finpow_empty → False.
Proof. discriminate. Qed.

Example finpow_chars_distinct :
  fin_apply finpow_sub02 = fin_apply finpow_empty → False.
Proof.
  intro Heq.
  assert (H0 : fin_apply finpow_sub02 Fin.F1 = fin_apply finpow_empty Fin.F1)
    by now rewrite Heq.
  discriminate H0.
Qed.

(* A SECOND DEGENERACY EXCLUDED: the functor's action genuinely MOVES
   subsets, so it is not the identity in disguise.  Along the constant map
   at 0 the inverse image of {0,2} is all of 3 — every i has [const0 i = 0],
   which is in the subset — and the inverse image of the empty subset is
   empty, so the two are separated. *)
Definition finpow_const0 : Fin.t 3 → Fin.t 3 := fun _ => Fin.F1.

Example finpow_inverse_of_sub02_is_full :
  finpow_map finpow_const0 finpow_sub02
    = fin_tabulate (fun _ : Fin.t 3 => fin_true) := eq_refl.

Example finpow_inverse_of_empty_is_empty :
  finpow_map finpow_const0 finpow_empty = finpow_empty := eq_refl.

Example finpow_inverse_moves :
  finpow_map finpow_const0 finpow_sub02 = finpow_sub02 → False.
Proof. discriminate. Qed.

(* ------------------------------------------------------------------------ *)
(** ** The internal power object *)

(* Structure/Topos.v defines the power object of a topos as the exponential
   [Pow a := Ω ^ a], an assignment on OBJECTS with no action on morphisms —
   the gap Instance/Sets/Powerset.v's header records.  At [FinSet_Topos]
   its object action is this file's, on the nose: [exponent_obj m n] is
   [n ^ m], so [Ω ^ n] at Ω = 2 is [2 ^ n], which is [finpow n].  What
   [FinPowerset] adds over it is the arrow action; no comparison morphism
   is claimed, because there is nothing on the other side to compare. *)

Example finpow_is_topos_Pow (n : nat) :
  @Pow FinSet FinSet_Topos n = finpow n := eq_refl.

(* This numeric instance is the pre-existing [FinSet_Pow_two]
   (Instance/FinSet/Topos.v:52) restated; the general [finpow_is_topos_Pow]
   above is what is new here. *)
Example finpow_topos_Pow_two :
  @Pow FinSet FinSet_Topos 2%nat = 4%nat := eq_refl.
