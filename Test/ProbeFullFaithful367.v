(* Boundary probe for issue #367: Mac Lane §IV.3 Theorem 1 and its lemma.

   Targets: Functor/Hom/Transfer.v and Adjunction/FullFaithful.v.  This
   file mirrors BOTH targets' full Require lists, then requires the
   targets themselves, then the extra modules the non-vacuity witnesses
   need.  The short-prefix hazard is real and is what this discipline
   exists to avoid: a probe compiled against fewer imports can fail for a
   missing coercion or a missing reference and look like a clean
   refutation.

   WHY A SEPARATE FILE.  An in-file [Fail] renames in lockstep with the
   constant it guards, so it cannot detect a rename.  Every negative here
   names target constants from OUTSIDE the targets, and every constant a
   negative names also appears outside a [Fail] elsewhere in this file.

   CONTENTS

   - An instrument check: a [Fail Check] on a reference that does not
     exist, so that a [Fail] which passes for the wrong reason is
     visible.
   - SEVEN negatives of THREE kinds, kept lexically apart and told apart
     by the error TEXT rather than by label:
       CONVERSION   ends "cannot unify" between two terms of one type;
       TYPING       a plain "has type ... while it is expected to have
                    type", with no "cannot unify" and no universe clause;
       FORMABILITY  ends "universe inconsistency".
     Each was stripped ONE AT A TIME, with the others left as [Fail], and
     compiled alone; the whole error was read and the place it fires
     confirmed.
   - Positive controls beside each negative.
   - Non-vacuity for one of the two quadrants of Theorem 1, and the
     honest scope of the other.

   NOTE on what "not a Section" can mean.  Theorem 1(ii) is a
   biconditional between [Full U] and the FAMILY (∀ a, Section (ε a)).
   Refuting fullness therefore refutes the FAMILY, not a named component:
   a single ε_a may still split while U is not full.  The two witnesses
   below are stated at exactly that strength and no stronger. *)

(* The Require list of Functor/Hom/Transfer.v. *)
Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Morphisms.
Require Import Category.Functor.Hom.

(* The extra Requires of Adjunction/FullFaithful.v. *)
Require Import Category.Theory.Morphisms.Duality.
Require Import Category.Theory.Adjunction.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Fullness.
Require Import Category.Adjunction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.

(* The two targets. *)
Require Import Category.Functor.Hom.Transfer.
Require Import Category.Adjunction.FullFaithful.

(* Prior art the probe checks against the targets, and the witnesses. *)
Require Import Category.Instance.Coq.Monoid.Free.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.One.
Require Import Category.Functor.Diagonal.
Require Import Category.Instance.Sets.Pointed.
Require Import Category.Theory.Algebra.Monoid.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(* ------------------------------------------------------------------ *)
(** ** Instrument check *)

(* If this ever stops failing, the [Fail]s below are not measuring
   anything. *)

Fail Check probe_367_no_such_reference.

(* ------------------------------------------------------------------ *)
(** ** (1) The transfer transformation against [fmap[Curried_Hom]] *)

Section TransferComparison.

Context {A : Category}.
Context {a b : A}.
Context (f : b ~> a).

(* CONTROL.  The values agree at Leibniz equality, and the two
   transformations agree at [≈] in the functor category.  Both of these
   are the targets' own shipped constants, named here outside any
   [Fail]. *)

Check @hom_transfer.
Check @Curried_Hom.
Check (@hom_transfer_is_fmap_value A a b f).
Check (@hom_transfer_is_fmap A a b f).

Example ctrl_transfer_value (c : A) (h : a ~> c) :
  transform[hom_transfer f] c h
    = transform[fmap[Curried_Hom A] (f : a ~{Opposite A}~> b)] c h
  := eq_refl.

(* NEGATIVE 1 (CONVERSION).  The whole [Transform] record is NOT
   [fmap[Curried_Hom A] f]: [Transform] carries [naturality] and
   [naturality_sym], which the two definitions elaborate as separate
   obligations.  Stripped and compiled alone, this reports
   `The term "eq_refl" has type "hom_transfer f = hom_transfer f" while
   it is expected to have type "hom_transfer f = fmap[A] f" (cannot unify
   "hom_transfer f" and "fmap[A] f")`.  Note the display: the coercion
   [Curried_Hom : Category >-> Functor] makes the functor print as its
   CATEGORY. *)

Fail Example neg1_whole_record :
  hom_transfer f = fmap[Curried_Hom A] (f : a ~{Opposite A}~> b)
  := eq_refl.

(* NEGATIVE 2 (CONVERSION).  Neither is the COMPONENT record, one rung
   lower: a [SetoidMorphism] carries a [proper_morphism] certificate, and
   the two are separately elaborated.  The control above shows the
   underlying values agree, so this locates the difference exactly at the
   certificate — the whole-record failure is not only about naturality. *)

Fail Example neg2_component_record (c : A) :
  transform[hom_transfer f] c
    = transform[fmap[Curried_Hom A] (f : a ~{Opposite A}~> b)] c
  := eq_refl.

(* CONTROL.  The Yoneda-side readback holds at [≈]. *)

Check (@hom_transfer_at_id A a b f).

(* NEGATIVE 3 (CONVERSION).  It does not hold at [eq_refl]: the value is
   `id ∘ f`, and [id_left] is a law field of [Category], so no amount of
   conversion removes it. *)

Fail Example neg3_transfer_at_id :
  transform[hom_transfer f] a id = f := eq_refl.

End TransferComparison.

(* ------------------------------------------------------------------ *)
(** ** (2) Split monic is not plain monic *)

Section SplitVersusMonic.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context `{A : F ⊣ U}.

(* CONTROL.  Theorem 1(ii) delivers a [Section] — the library's split
   monomorphism — and that is what the reviewer check for this issue
   asks for. *)

Check @right_adjoint_full_iff_counit_split_monic.

Definition ctrl_section (HU : Functor.Full U) (a : C) :
  Section (@counit C D F U A a) :=
  fst right_adjoint_full_iff_counit_split_monic HU a.

(* NEGATIVE 4 (TYPING).  [Section] and [Monic] are two different classes,
   so the conclusion of (ii) is not a [Monic] statement even though every
   [Section] is monic ([sections_are_monic]).  Stripped and compiled
   alone, this reports a plain `has type ... while it is expected to have
   type ...` with NO "cannot unify" and no universe clause — the mark
   that separates it from negatives 1-3 and 5. *)

Fail Definition neg4_section_is_not_monic (HU : Functor.Full U) (a : C) :
  Monic (@counit C D F U A a) :=
  fst right_adjoint_full_iff_counit_split_monic HU a.

(* CONTROL that the implication is nevertheless available, by the
   in-tree passage rather than by conversion. *)

Definition ctrl_section_gives_monic (HU : Functor.Full U) (a : C) :
  Monic (@counit C D F U A a) :=
  sections_are_monic _ _ _ (ctrl_section HU a).

End SplitVersusMonic.

(* ------------------------------------------------------------------ *)
(** ** (3) The reflective donor is opaque *)

Section ReflectiveOpacity.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).
Context (x : Sub C S).

(* CONTROL.  Section (G) of the target derives the conclusion of
   Construction/Reflective.v:92 from Theorem 1(iii), and the existing
   lemma is nameable here. *)

Check (@reflective_counit_IsIsomorphism_general C S R x).
Check (@reflective_counit_iso C S R x).
Check (to (@reflective_counit_iso C S R x)).
Check @reflector.
Check @Incl.
Check @reflective_adj.

(* NEGATIVE 5 (CONVERSION).  [reflective_counit_iso] produces DATA and is
   closed with [Qed] (Construction/Reflective.v:115), so its [to] does not
   reduce to the counit although the proof script supplies exactly that.
   Stripped and compiled alone this reports "cannot unify".  The [≈] form
   is unavailable for the same reason and is therefore not shipped
   either: there is nothing to rewrite with. *)

Fail Example neg5_reflective_to_is_counit :
  to (@reflective_counit_iso C S R x)
  = @counit (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) x
  := eq_refl.

End ReflectiveOpacity.

(* ------------------------------------------------------------------ *)
(** ** (4) Universes: what the headlines inherit *)

(* The measurement, for the record: every headline of both targets is
   over categories whose hom and proof universes are identified IN THE
   BINDER (`Category@{u u0 u0}`), and the theorem file's headlines carry
   in addition the single BLOCK equation `u0 = u2`, identifying C's and
   D's hom-and-proof universes.  Neither file has a `Set` in any binder
   or block.  The two probes below isolate a donor for each. *)

Section HomProofDonor.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (u v : Cu).
Context (g : u ~{Cu}~> v).

(* CONTROLS accepted at these very levels: naming a hom, an identity, and
   a composite. *)

Check (u ~{Cu}~> v).
Check (@id Cu u).
Check (g ∘ @id Cu u).
Check @Retraction.

(* NEGATIVE 6 (FORMABILITY).  [Epic] alone identifies hom with proof, so
   it is rejected where the hom and proof universes are declared strictly
   apart.  Stripped and compiled alone it ends "universe inconsistency".
   [Monic], [Section] and [Retraction] are rejected at the same levels;
   they are listed here as further [Fail]s rather than as separate
   numbered negatives, since they measure the same identification. *)

Fail Check (@Epic Cu u v g).
Fail Check (@Monic Cu u v g).
Fail Check (@Section Cu u v g).
Fail Check (@Retraction Cu u v g).

End HomProofDonor.

Section AdjunctionHomDonor.

Universes ao ah bo bh.
Constraint ah < bh.

Context (Cu : Category@{ao ah ah}).
Context (Du : Category@{bo bh bh}).

(* CONTROL accepted at these levels: a functor in the direction the
   constraint allows. *)

Check (Cu ⟶ Du).

(* NEGATIVE 7 (FORMABILITY).  The other direction is rejected, because
   [Functor] forces the source's hom universe below the target's.  So the
   block equation `u0 = u2` on the theorem file's headlines needs no
   appeal to [Adjunction] at all: the mere presence of functors in BOTH
   directions already forces it, and [Adjunction] cannot be tested apart
   from that, since its very type mentions both.  Stripped and compiled
   alone this ends "universe inconsistency". *)

Fail Check (Du ⟶ Cu).

End AdjunctionHomDonor.

(* ------------------------------------------------------------------ *)
(** ** (5) The prior art, checked against the target at one type *)

(* Instance/Coq/Monoid/Free.v:476's [adjunction_counit_epic] already
   proves the forward half of Theorem 1(i) for an ARBITRARY adjunction.
   The target restates it (by a different proof, through the transfer
   lemma) rather than consuming it, because that constant lives in the
   `Instance/Coq` layer.  That the two STATEMENTS are the same is
   machine-checked here: both are ascribed to one type. *)

Section PriorArt.

Context {C : Category}.
Context {D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

Definition ctrl_prior_art_free (HU : Functor.Faithful U) (a : C) :
  Epic (@counit C D F U A a) :=
  adjunction_counit_epic A HU a.

Definition ctrl_prior_art_target (HU : Functor.Faithful U) (a : C) :
  Epic (@counit C D F U A a) :=
  @counit_epic_of_faithful C D F U A HU a.

(* And the two [Retraction] readings of `U ε` agree in type as well:
   Free.v:465 and Fullness.v's whiskered development. *)

Check (@adjunction_counit_underlying_retraction C D F U A).

End PriorArt.

(* ------------------------------------------------------------------ *)
(** ** (6) Non-vacuity, quadrant one: full and NOT faithful *)

(* #368's witness, read through Theorem 1.  [Erase PointedSets] is the
   right adjoint of [zero_erase_adjunction], it is FULL because
   [PointedSets] has a zero object (Fullness.v:785), and it is provably
   NOT faithful (Fullness.v:812).  So by (ii) every counit component
   splits, and by (i) — contrapositive — the counit family is NOT
   componentwise epi.  The second is new content: Fullness.v refutes only
   invertibility of the component at [PointedTwo].

   DEGENERACY, labelled: the target of [Erase] is the terminal category
   [_1], so fullness holds for a reason unrelated to the theorem (every
   hom-set of [_1] is a singleton, and the zero morphism hits it).  What
   the witness exercises is the CONTRAPOSITIVE of (i) and the forward half
   of (ii), not a subtle adjunction. *)

Definition pointed_erase_adj :
  @Diagonal PointedSets _1
    (@initial_obj PointedSets (@zero_initial PointedSets PointedSets_Zero))
  ⊣ Erase PointedSets :=
  zero_erase_adjunction PointedSets_Zero.

Definition pointed_counit_Section (a : PointedSets) :
  Section (@counit PointedSets _1 _ (Erase PointedSets)
             pointed_erase_adj a) :=
  fst (@right_adjoint_full_iff_counit_split_monic PointedSets _1 _
         (Erase PointedSets) pointed_erase_adj)
      (Full_Erase_of_ZeroObject PointedSets_Zero) a.

Lemma pointed_counit_family_not_Epic :
  (∀ a : PointedSets,
      Epic (@counit PointedSets _1 _ (Erase PointedSets)
              pointed_erase_adj a)) → False.
Proof.
  intros H.
  apply Erase_PointedSets_not_Faithful.
  exact (snd (@right_adjoint_faithful_iff_counit_epic PointedSets _1 _
                (Erase PointedSets) pointed_erase_adj) H).
Qed.

(* The pre-existing refutation of invertibility at [PointedTwo], recorded
   beside them so the three readings sit together. *)

Check pointed_counit_not_IsIsomorphism.

(* ------------------------------------------------------------------ *)
(** ** (7) Non-vacuity, quadrant two: faithful and NOT full *)

(* The free-monoid adjunction over [Coq] (Instance/Coq/Monoid/Free.v).
   Its right adjoint is the forgetful functor to [Coq]; it is faithful
   because a monoid morphism there IS a function paired with a property
   and the hom-setoid compares the functions, and it is NOT full because
   a function between underlying sets need not preserve the unit.  By (i)
   every counit component is epi; by (ii) — contrapositive — the counit
   family does NOT split.

   NON-DEGENERACY: the refutation of fullness evaluates the recovered
   homomorphism at the UNIT, where the chosen non-homomorphism
   `fun _ => cons true nil` provably differs from it, so the witness is
   not the empty-hom-set kind. *)

Definition mon_coq_forget : @Mon Coq Coq_Monoidal ⟶ Coq :=
  @Mon_Forget Coq Coq_Monoidal.

Definition free_mon_faithful : Functor.Faithful mon_coq_forget.
Proof. constructor; intros x y f g H; exact H. Qed.

Definition free_mon_counit_Epic (L : @Mon Coq Coq_Monoidal) :
  Epic (@counit (@Mon Coq Coq_Monoidal) Coq FreeMonoid mon_coq_forget
          free_monoid_adjunction L) :=
  fst (@right_adjoint_faithful_iff_counit_epic
         (@Mon Coq Coq_Monoidal) Coq FreeMonoid mon_coq_forget
         free_monoid_adjunction) free_mon_faithful L.

Lemma free_mon_forget_not_Full : Functor.Full mon_coq_forget → False.
Proof.
  intros HFull.
  pose (W := FreeMon bool).
  pose (k := (fun _ : list bool => Datatypes.cons true Datatypes.nil)
             : mon_coq_forget W ~{Coq}~> mon_coq_forget W).
  pose proof (@fmap_sur _ _ mon_coq_forget HFull W W k) as Hs.
  pose proof (hom_mone (@prefmap _ _ mon_coq_forget HFull W W k)) as Hu.
  specialize (Hs (@mone W)).
  simpl in Hs, Hu.
  rewrite Hu in Hs.
  discriminate Hs.
Qed.

Lemma free_mon_counit_family_not_Section :
  (∀ L : @Mon Coq Coq_Monoidal,
      Section (@counit (@Mon Coq Coq_Monoidal) Coq FreeMonoid
                 mon_coq_forget free_monoid_adjunction L)) → False.
Proof.
  intros H.
  apply free_mon_forget_not_Full.
  exact (snd (@right_adjoint_full_iff_counit_split_monic
                (@Mon Coq Coq_Monoidal) Coq FreeMonoid mon_coq_forget
                free_monoid_adjunction) H).
Qed.

(* And the combined reading: by (iii), the counit of this adjunction is
   not a componentwise isomorphism either. *)

Lemma free_mon_counit_family_not_iso :
  (∀ L : @Mon Coq Coq_Monoidal,
      IsIsomorphism (@counit (@Mon Coq Coq_Monoidal) Coq FreeMonoid
                       mon_coq_forget free_monoid_adjunction L)) → False.
Proof.
  intros H.
  apply free_mon_forget_not_Full.
  exact (fst (snd (@right_adjoint_fully_faithful_iff_counit_iso
                     (@Mon Coq Coq_Monoidal) Coq FreeMonoid
                     mon_coq_forget free_monoid_adjunction) H)).
Qed.

(* ------------------------------------------------------------------ *)
(** ** (8) The remaining headline names, checked from outside *)

(* Every target constant that a negative above names appears in a
   succeeding command; these [Check]s cover the rest of the two files'
   headline surface, so that a rename of any of them breaks this file at
   a NON-[Fail] line. *)

Check @hom_transfer_monic_iff_epic.
Check @hom_transfer_epic_iff_section.
Check @hom_transfer_component.
Check @hom_transfer_component_injective_iff.
Check @hom_transfer_component_surjective_iff.
Check @epic_of_hom_transfer_monic.
Check @hom_transfer_monic_of_epic.
Check @section_of_hom_transfer_epic.
Check @hom_transfer_epic_of_section.
Check @Epic_Section_IsIsomorphism.
Check @counit_precomp_is_from_adj_fmap_U.
Check @transfer_at_counit_is_precomp.
Check @fmap_U_is_transfer_then_transpose.
Check @counit_transfer_monic_of_faithful.
Check @counit_epic_of_faithful.
Check @faithful_of_counit_epic.
Check @right_adjoint_faithful_iff_counit_epic.
Check @counit_transfer_epic_of_full.
Check @counit_section_via_transfer.
Check @full_data_of_counit_section.
Check @full_of_counit_section.
Check @right_adjoint_fully_faithful_iff_counit_iso.
Check @from_adj_id_is_counit.
Check @from_adj_epic_of_epic_direct.
Check @from_adj_epic_of_epic.
Check @right_adjoint_faithful_iff_from_adj_epic.
Check @op_counit_is_unit.
Check @op_unit_is_counit.
Check @left_adjoint_faithful_iff_unit_monic.
Check @left_adjoint_full_iff_unit_split_epic.
Check @left_adjoint_fully_faithful_iff_unit_iso.
Check @unit_retract_agrees.
Check @reflective_incl_Full.
Check @reflective_incl_Faithful.
Check @reflective_counit_Isomorphism_general.
Check @reflection_counit_Epic.
