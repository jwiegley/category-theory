Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Quotient.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(* Lib.v sets [Default Proof Using "Type"], which keeps only the section
   variables occurring in a statement.  Every statement below mentions the
   section's R, HR and HC only THROUGH [sets_part_pred] and [SetsParts],
   which are section-local definitions and so do not register as syntactic
   occurrences; "All" is the precedent of Theory/EckmannHilton.v:110 and
   Theory/Category/Monoid.v:919. *)
#[local] Set Default Proof Using "All".

(** * The quotient as a set of parts *)

(* nLab:      https://ncatlab.org/nlab/show/partition
   nLab:      https://ncatlab.org/nlab/show/quotient+set
   Wikipedia: https://en.wikipedia.org/wiki/Equivalence_class
   Wikipedia: https://en.wikipedia.org/wiki/Partition_of_a_set

   Fong and Spivak, "Seven Sketches in Compositionality", §1.2.1
   definition 1.21 (printed p. 10): the quotient of a set by an
   equivalence relation IS the set of PARTS of the corresponding
   partition.  Instance/Sets/Quotient.v gives the other presentation --
   the same carrier under a coarser equality -- and this file builds the
   book's and compares the two.

   The comparison is not a formality, and the whole interest of the file
   is in what it costs.  Three separate things are true, and they are
   kept apart below because conflating any two of them would misstate the
   result.

   (1) THE UNTRUNCATED CLASS OBJECT DOES NOT EXIST AT THE RIGHT LEVEL.
       In this library `≈` is [crelation]-valued, so the class of a is
       naturally the TYPE-valued predicate x ↦ R a x.  But
       [obj[Sets@{o so}]] is [SetoidObject@{o o}], which identifies a
       setoid's carrier and relation universes, and
       [carrier A → Type@{o}] has type [Type@{o+1}].  So the untruncated
       class object is not an object of the [Sets] that A lives in; it is
       one of the next [Sets] up.  This is a genuine universe
       inconsistency and Test/ProbeSetsQuotient.v pins it, with two
       positive controls -- the truncated carrier at the same level, and
       the untruncated one a level up.  It is the same wall
       Instance/Sets/Powerset.v (#227) reports for [Powerset_obj], met
       from the other side, and this file's [SetsParts] uses that file's
       [Powerset_Prop_obj] rather than rebuilding a subset object.

   (2) TRUNCATION MAKES THE OBJECT EXIST, AND CLASSIFICATION STILL
       HOLDS -- UP TO TRUNCATION.  Taking the class of a to be
       x ↦ ‖R a x‖, with [Powerset_squash] the impredicative truncation
       Powerset.v already uses, puts the class object back at the level
       of the carrier.  [sets_part_of] is then available under EXACTLY
       the hypotheses the quotient itself takes -- R an equivalence,
       coarser than `≈` -- with no stability assumed; and it is
       surjective ([sets_part_of_surjective]) and separates points up to
       truncation ([sets_part_of_squash]).  What is NOT available is the
       last step out of the truncation, since ‖R a b‖ is a [Prop] and
       R a b need not be.

   (3) THE HYPOTHESIS THAT CLOSES THE GAP IS EXACTLY THE CONCLUSION.
       [SquashStable R] -- that ‖R x y‖ implies R x y -- gives the
       isomorphism ([sets_partition_iso]); and conversely injectivity of
       [sets_part_of] gives back [SquashStable R]
       ([partition_stability_is_the_conclusion] -- the name is prefixed
       because the tree already carries TWO constants called
       [stability_is_the_conclusion], at Instance/Grp/Epi.v:1143 and
       Instance/Field.v:318).  So no cheaper hypothesis exists,
       which is the discipline Instance/Grp/Epi.v and Instance/Field.v
       use for their constructive stratifications.  A [Prop]-valued R is
       squash-stable ([prop_rel_squash_stable]), by instantiating the
       impredicative quantifier at R x y itself; and Seven Sketches'
       classical setting is exactly the [Prop]-valued one, so the book's
       identification is recovered there with nothing extra assumed. *)

(* Two presentations of a quotient, and why a library has to choose

   Text:  Fong and Spivak, "Seven Sketches in Compositionality", CUP
          2019, §1.2.1
   Text:  Bishop, "Foundations of Constructive Analysis", McGraw-Hill 1967
   Paper: Hofstra and Warren, "Combinatorial realizability models of type
          theory", APAL 164(10) 2013
   Paper: Barthe, Capretta, Pons, "Setoids in type theory", JFP 13(2) 2003

   Classically the two presentations are interchangeable and textbooks
   move between them without comment: a quotient is a set of classes, and
   a class is named by any of its members.  What breaks the symmetry in
   type theory is that "the set of classes" is a set of SUBSETS, and the
   power set is a universe-raising operation, while "the same set with a
   coarser equality" raises nothing.  The library's design (stated at
   Instance/Sets.v:66) takes the second reading for exactly this reason,
   and every quotient in the tree follows it -- the hom-congruence
   quotient of Construction/Quotient.v, the group and module quotients of
   Instance/Grp/Quotient.v and Instance/Mod/Quotient.v, and
   Instance/Sets/Quotient.v.

   The class reading is nevertheless not a mere alternative notation, and
   this file is where the difference is visible.  It survives at all only
   because [Prop] is impredicative in Coq, so a truncated subset stays at
   the level of the carrier; and once truncated it cannot be untruncated,
   so the passage back to a representative is the step that has to be
   paid for.  Payment is [SquashStable], and Fong and Spivak's setting
   pays it for free by working with [Prop]-valued relations throughout.

   One thing this file does NOT do is decide whether the setoid reading
   is "the right one".  It shows what each costs and where they agree. *)

(* WHAT IS DELIVERED

   * [sets_part_pred], the truncated class of an element as an object of
     Instance/Sets/Powerset.v's [Powerset_Prop_obj A] -- a `≈`-respecting
     [Prop]-valued predicate, so a subset of A in that file's sense, not a
     new notion of subset invented here.

   * That the classes are a PARTITION, proved rather than assumed:
     [sets_part_mem_self] (every element lies in its own class) and
     [sets_part_shared_elem] (two classes sharing an element are equal).

   * [SetsParts A R], the set of parts, and [sets_part_of], the class map
     out of the coarsening quotient.  Both take the quotient's own two
     hypotheses and NOTHING MORE -- in particular no stability -- and
     [sets_part_of] is surjective and separates up to truncation.

   * [SquashStable] and the three results that pin it: it suffices
     ([sets_partition_iso], an isomorphism in [Sets]), it is necessary
     ([partition_stability_is_the_conclusion], a biconditional against injectivity
     of [sets_part_of]), and it is free for a [Prop]-valued relation
     ([prop_rel_squash_stable]).

   * [SetsPartsProp A R], the object with the class-hood witness itself
     truncated -- literally a sub-setoid of [Powerset_Prop_obj A], with no
     representative carried -- together with the comparison map
     [sets_parts_forget].  This is included because it, and not
     [SetsParts], is what "the set of parts" says when read strictly, and
     because the difference between the two is exactly the constructive
     content.

   WHAT IS NOT DELIVERED

   * NO INVERSE TO [sets_parts_forget].  Recovering a representative from
     a truncated existence witness is large elimination out of [Prop],
     which is not available; no impossibility is proved here either, and
     in particular no theorem says that no OTHER map back exists.  The
     statement is that this map is not invertible by the evident
     candidate.

   * NO CLAIM THAT [SquashStable] IS UNAVOIDABLE FOR SOME OTHER
     PRESENTATION.  [partition_stability_is_the_conclusion] is about [sets_part_of];
     it says nothing about class maps built differently.

   * NO UNTRUNCATED CLASS OBJECT, at any level.  The one-level-up object
     is exhibited only inside Test/ProbeSetsQuotient.v, as the positive
     control for the universe measurement, and nothing is built over it.

   * NO PARTITION AS A FIRST-CLASS STRUCTURE.  There is no record of
     "partitions of A", no inverse assignment from partitions to
     relations, and hence no bijection between the two -- Seven Sketches'
     §1.2.1 sets that correspondence up, and only the direction from a
     relation to its parts is formalized here.

   STATUS: axiom-free.  36 named constants, no [Program] obligations, all
   reporting "Closed under the global context"; the Makefile's
   [print-assumptions] target audits fourteen of them. *)

Section Partition.

Context {A : SetoidObject}.
Context (R : crelation (carrier A)).
Context (HR : Equivalence R).
Context (HC : SetoidCoarser R).

(** ** The class of an element, as a subset *)

(* The truncated class.  [Powerset_squash] (Instance/Sets/Powerset.v) is
   the impredicative truncation ∀ Q : Prop, (A → Q) → Q; applying it is
   what keeps the predicate [Prop]-valued and hence keeps the whole
   construction at the carrier's universe. *)
Definition sets_part_pred (a : carrier A) : carrier (Powerset_Prop_obj A).
Proof.
  unshelve refine
    (@Build_SetoidMorphism (carrier A) (is_setoid A) Prop
       (is_setoid Powerset_Prop_truth)
       (fun x => Powerset_squash (R a x)) _).
  intros x x' Hxx'; split; intros H Q k; apply H; intro w; apply k.
  - transitivity x; [ exact w | exact (HC x x' Hxx') ].
  - transitivity x'; [ exact w | exact (HC x' x (symmetry Hxx')) ].
Defined.

(* Membership in one's own class, and the class of an R-related element:
   the two facts that make the classes a partition. *)
Lemma sets_part_mem_self (a : carrier A) : sets_part_pred a a.
Proof. exact (Powerset_squash_intro (Equivalence_Reflexive a)). Qed.

Lemma sets_part_mem_of (a x : carrier A) (w : R a x) : sets_part_pred a x.
Proof. exact (Powerset_squash_intro w). Qed.

(* Two classes that share an element are equal.  This is the second half
   of "the classes partition A"; note that the shared element's
   membership witnesses arrive truncated, and the conclusion is an
   equality of [Prop]-valued predicates, so both are eliminated into a
   [Prop] and no untruncation is needed. *)
Lemma sets_part_shared_elem (a b c : carrier A)
  (Ha : sets_part_pred a c) (Hb : sets_part_pred b c) :
  @equiv _ (Powerset_Prop_obj A) (sets_part_pred a) (sets_part_pred b).
Proof.
  intro x; split; intro H.
  - apply Ha; intro wac; apply Hb; intro wbc; apply H; intro wax; clear H.
    apply Powerset_squash_intro.
    transitivity a; [ | exact wax ].
    transitivity c; [ exact wbc | exact (symmetry wac) ].
  - apply Ha; intro wac; apply Hb; intro wbc; apply H; intro wbx; clear H.
    apply Powerset_squash_intro.
    transitivity b; [ | exact wbx ].
    transitivity c; [ exact wac | exact (symmetry wbc) ].
Qed.

(* Classes of R-related elements coincide. *)
Lemma sets_part_pred_respects (a b : carrier A) (w : R a b) :
  @equiv _ (Powerset_Prop_obj A) (sets_part_pred a) (sets_part_pred b).
Proof.
  exact (sets_part_shared_elem a b b (sets_part_mem_of a b w)
           (sets_part_mem_self b)).
Qed.

(** ** The set of parts, with a representative carried *)

(* An element is a subset of A together with an element it is the class
   of.  The representative is DATA -- the library's `∃` is [sigT] -- and
   the setoid IGNORES it, comparing only the subsets.  That is what makes
   this the set of parts rather than the set of pointed parts, and it is
   also exactly what makes the map back to the coarsening quotient
   writable at all; [SetsPartsProp] below is the same object with the
   representative truncated away, and there the EVIDENT map back -- take
   the representative -- cannot be written, since that would be large
   elimination out of [Prop].  Nothing here says no OTHER map back
   exists. *)
Definition sets_parts_carrier : Type :=
  { P : carrier (Powerset_Prop_obj A)
      & { a : carrier A & @equiv _ (Powerset_Prop_obj A) P (sets_part_pred a) } }.

Definition sets_parts_equiv : crelation sets_parts_carrier :=
  fun S T => @equiv _ (Powerset_Prop_obj A) (`1 S) (`1 T).

Lemma sets_parts_equivalence : Equivalence sets_parts_equiv.
Proof.
  unfold sets_parts_equiv; constructor.
  - intro S; reflexivity.
  - intros S T H; now symmetry.
  - intros S T U H1 H2; now transitivity (`1 T).
Qed.

Definition SetsParts : SetoidObject :=
  {| carrier := sets_parts_carrier ;
     is_setoid := {| equiv := sets_parts_equiv ;
                     setoid_equiv := sets_parts_equivalence |} |}.

(** ** The class map *)

(* Defined for an ARBITRARY [crelation]-valued R: no stability is needed
   to send an element to its class. *)
(* The class of [a], with [a] itself as the carried representative. *)
Definition sets_part_elt (a : carrier A) : sets_parts_carrier.
Proof.
  unshelve refine
    (existT (fun P : carrier (Powerset_Prop_obj A) =>
               { b : carrier A
                   & @equiv _ (Powerset_Prop_obj A) P (sets_part_pred b) })
       (sets_part_pred a)
       (existT (fun b : carrier A =>
                  @equiv _ (Powerset_Prop_obj A) (sets_part_pred a)
                    (sets_part_pred b)) a _)).
  reflexivity.
Defined.

Definition sets_part_of : SetsQuotient A R HR ~{Sets}~> SetsParts.
Proof.
  unshelve refine
    (@Build_SetoidMorphism (carrier A) (is_setoid (SetsQuotient A R HR))
       sets_parts_carrier (is_setoid SetsParts) sets_part_elt _).
  intros a b w; exact (sets_part_pred_respects a b w).
Defined.

(* Every part is the class of its own representative, so [sets_part_of]
   is surjective -- and the preimage is produced, not merely asserted to
   exist. *)
Lemma sets_part_of_surjective (S : carrier SetsParts) :
  @equiv _ SetsParts (sets_part_of (`1 (`2 S))) S.
Proof.
  intro x; split; intro H.
  - exact (proj2 (`2 (`2 S) x) H).
  - exact (proj1 (`2 (`2 S) x) H).
Qed.

(* ... and it separates points UP TO TRUNCATION.  Evaluating the equality
   of classes at [a] turns reflexivity of R into ‖R b a‖, and symmetry
   inside the truncation gives ‖R a b‖; the last step out is what is not
   available. *)
Lemma sets_part_of_squash (a b : carrier A)
  (H : @equiv _ SetsParts (sets_part_of a) (sets_part_of b)) :
  Powerset_squash (R a b).
Proof.
  assert (Hba : Powerset_squash (R b a))
    by exact (proj1 (H a) (sets_part_mem_self a)).
  intros Q k; apply Hba; intro w; apply k; exact (symmetry w).
Qed.

(** ** The hypothesis that closes the gap, and that it is the conclusion *)

Definition SquashStable : Type :=
  ∀ x y : carrier A, Powerset_squash (R x y) → R x y.

(* A [Prop]-valued relation is squash-stable: instantiate the
   impredicative quantifier at the proposition itself. *)
Lemma prop_rel_squash_stable (Rp : carrier A -> carrier A -> Prop)
  (HRel : ∀ x y : carrier A, R x y ↔ Rp x y) : SquashStable.
Proof.
  intros x y H.
  apply (snd (HRel x y)).
  exact (H (Rp x y) (fun w => fst (HRel x y) w)).
Qed.

(* Stability is exactly injectivity of the class map.  Backwards is
   [sets_part_of_squash]; forwards, a truncated R x y already forces the
   two classes to agree, because the goal at each point is a [Prop] and
   so the truncation may be eliminated into it. *)
Lemma squash_stable_injective (HS : SquashStable) (a b : carrier A)
  (H : @equiv _ SetsParts (sets_part_of a) (sets_part_of b)) : R a b.
Proof. exact (HS a b (sets_part_of_squash a b H)). Qed.

(* Two moves inside the truncation, isolated so that the statements are
   about [Powerset_squash] rather than about [sets_part_of]'s first
   projection -- which spares every use site a reduction step.  Both are
   eliminations of a truncation into a [Prop] goal, which is exactly what
   impredicative truncation permits. *)
Lemma squash_rel_sym (x y : carrier A) (H : Powerset_squash (R x y)) :
  Powerset_squash (R y x).
Proof. intros Q k; apply H; intro w; apply k; exact (symmetry w). Qed.

Lemma squash_rel_shift (x y z : carrier A) (H : Powerset_squash (R x y))
  (Hz : Powerset_squash (R x z)) : Powerset_squash (R y z).
Proof.
  intros Q k; apply H; intro wxy; apply Hz; intro wxz; apply k.
  transitivity x; [ exact (symmetry wxy) | exact wxz ].
Qed.

Lemma injective_squash_stable
  (Hinj : ∀ a b : carrier A,
     @equiv _ SetsParts (sets_part_of a) (sets_part_of b) → R a b) :
  SquashStable.
Proof.
  intros x y H.
  apply Hinj.
  intro z; split; intro Hz.
  - exact (squash_rel_shift x y z H Hz).
  - exact (squash_rel_shift y x z (squash_rel_sym x y H) Hz).
Qed.

Theorem partition_stability_is_the_conclusion :
  SquashStable ↔
  (∀ a b : carrier A,
     @equiv _ SetsParts (sets_part_of a) (sets_part_of b) → R a b).
Proof.
  split.
  - exact squash_stable_injective.
  - exact injective_squash_stable.
Qed.

(** ** Seven Sketches §1.2.1: the two presentations agree *)

Definition sets_part_rep (HS : SquashStable) :
  SetsParts ~{Sets}~> SetsQuotient A R HR.
Proof.
  unshelve refine
    (@Build_SetoidMorphism sets_parts_carrier (is_setoid SetsParts)
       (carrier A) (is_setoid (SetsQuotient A R HR))
       (fun S => `1 (`2 S)) _).
  intros S T HST.
  apply (squash_stable_injective HS).
  assert (Hpred : @equiv _ (Powerset_Prop_obj A)
                    (sets_part_pred (`1 (`2 S))) (sets_part_pred (`1 (`2 T)))).
  { transitivity (`1 S); [ symmetry; exact (`2 (`2 S)) | ].
    transitivity (`1 T); [ exact HST | exact (`2 (`2 T)) ]. }
  exact Hpred.
Defined.

(* THE STATEMENT: the coarsening quotient and the set of parts are
   isomorphic in [Sets], under stability and nothing else. *)
Definition sets_partition_iso (HS : SquashStable) :
  @Isomorphism Sets (SetsQuotient A R HR) SetsParts.
Proof.
  unshelve refine {| to := sets_part_of ; from := sets_part_rep HS |}.
  - intro S; exact (sets_part_of_surjective S).
  - intro a; exact (Equivalence_Reflexive a).
Defined.

(* The class map is the isomorphism's forward leg on the nose. *)
Example sets_partition_iso_to (HS : SquashStable) :
  to (sets_partition_iso HS) = sets_part_of.
Proof. reflexivity. Qed.

(* ... and the backward leg is "take the carried representative", again
   on the nose. *)
Example sets_partition_iso_from (HS : SquashStable) (S : carrier SetsParts) :
  from (sets_partition_iso HS) S = `1 (`2 S).
Proof. reflexivity. Qed.

(** ** The strict reading: parts with no representative *)

(* "The set of parts" read strictly is a SUB-SETOID of the power set --
   the subsets that are classes -- with no representative attached.  It
   exists at the right universe because the class-hood witness is
   truncated too. *)
Definition sets_parts_prop_carrier : Type :=
  { P : carrier (Powerset_Prop_obj A)
      & Powerset_squash
          { a : carrier A
              & @equiv _ (Powerset_Prop_obj A) P (sets_part_pred a) } }.

Definition sets_parts_prop_equiv : crelation sets_parts_prop_carrier :=
  fun S T => @equiv _ (Powerset_Prop_obj A) (`1 S) (`1 T).

Lemma sets_parts_prop_equivalence : Equivalence sets_parts_prop_equiv.
Proof.
  unfold sets_parts_prop_equiv; constructor.
  - intro S; reflexivity.
  - intros S T H; now symmetry.
  - intros S T U H1 H2; now transitivity (`1 T).
Qed.

Definition SetsPartsProp : SetoidObject :=
  {| carrier := sets_parts_prop_carrier ;
     is_setoid := {| equiv := sets_parts_prop_equiv ;
                     setoid_equiv := sets_parts_prop_equivalence |} |}.

(* Forgetting the representative.  This map exists unconditionally; what
   does not exist is the evident inverse, which would have to produce a
   representative from a truncated existence witness -- large elimination
   out of [Prop].  No impossibility is claimed, only that this candidate
   is unavailable. *)
Definition sets_parts_forget : SetsParts ~{Sets}~> SetsPartsProp.
Proof.
  unshelve refine
    {| morphism := fun S : carrier SetsParts =>
         existT (fun P : carrier (Powerset_Prop_obj A) =>
                   Powerset_squash
                     { a : carrier A
                         & @equiv _ (Powerset_Prop_obj A) P
                             (sets_part_pred a) })
           (`1 S) (Powerset_squash_intro (`2 S)) |}.
  intros S T HST; exact HST.
Defined.

(* It is the identity on the underlying subset, by conversion. *)
Example sets_parts_forget_pred (S : carrier SetsParts) :
  `1 (sets_parts_forget S) = `1 S.
Proof. reflexivity. Qed.

(* The composite class map into the strict object. *)
Definition sets_part_of_prop : SetsQuotient A R HR ~{Sets}~> SetsPartsProp :=
  sets_parts_forget ∘ sets_part_of.

Lemma sets_part_of_prop_surjective (S : carrier SetsPartsProp) :
  Powerset_squash
    { a : carrier A & @equiv _ SetsPartsProp (sets_part_of_prop a) S }.
Proof.
  intros Q k; apply (`2 S); intros [a Ha]; apply k.
  exists a.
  assert (Hsym : @equiv _ (Powerset_Prop_obj A) (sets_part_pred a) (`1 S))
    by (symmetry; exact Ha).
  exact Hsym.
Qed.

End Partition.


(** ** Non-vacuity: the parity quotient, read as a set of parts *)

(* Instance/Sets/Quotient.v's [nat_parity] is [Prop]-valued (an equation
   of booleans), so [prop_rel_squash_stable] discharges the hypothesis
   and the isomorphism is unconditional at it. *)
Definition nat_parity_stable : SquashStable nat_parity.
Proof.
  apply (prop_rel_squash_stable nat_parity nat_parity_Equivalence nat_parity_coarser
           (fun m n => Nat.even m = Nat.even n)).
  intros m n; split; intro H; exact H.
Qed.

Definition nat_parity_partition_iso :
  @Isomorphism Sets NatParity (SetsParts nat_parity nat_parity_Equivalence nat_parity_coarser) :=
  sets_partition_iso nat_parity nat_parity_Equivalence nat_parity_coarser
    nat_parity_stable.

(* The parts genuinely merge and genuinely separate: 0 and 2 have the
   same class, 0 and 1 do not.  The negative goes through the
   isomorphism's own injectivity clause, so it is a statement about the
   PARTS and not about [nat_parity] restated. *)
Lemma nat_parity_parts_merge :
  @equiv _ (SetsParts nat_parity nat_parity_Equivalence nat_parity_coarser)
    (sets_part_of nat_parity nat_parity_Equivalence nat_parity_coarser 0%nat)
    (sets_part_of nat_parity nat_parity_Equivalence nat_parity_coarser 2%nat).
Proof.
  exact (sets_part_pred_respects nat_parity nat_parity_Equivalence
           nat_parity_coarser 0%nat 2%nat eq_refl).
Qed.

Lemma nat_parity_parts_separate :
  @equiv _ (SetsParts nat_parity nat_parity_Equivalence nat_parity_coarser)
    (sets_part_of nat_parity nat_parity_Equivalence nat_parity_coarser 0%nat)
    (sets_part_of nat_parity nat_parity_Equivalence nat_parity_coarser 1%nat)
  → False.
Proof.
  intro H.
  pose proof (squash_stable_injective nat_parity nat_parity_Equivalence
                nat_parity_coarser nat_parity_stable 0%nat 1%nat H) as E.
  discriminate E.
Qed.
