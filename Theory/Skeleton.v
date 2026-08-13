Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Bundled.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Quotient.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.StrictCat.ToCat.
Require Import Equations.Prop.Logic.

Generalizable All Variables.

(** * Skeletons and skeletal categories *)

(* nLab: https://ncatlab.org/nlab/show/skeleton
   Wikipedia: https://en.wikipedia.org/wiki/Skeleton_(category_theory)

   A category is SKELETAL when isomorphic objects are equal, and a SKELETON
   of C is a full subcategory of C containing exactly one object from each
   isomorphism class.  Mac Lane states both (Categories for the Working
   Mathematician, 2nd ed., §IV.4, Definition 3, p. 93), then records that a
   category is equivalent to each of its skeletons (Remark 1, p. 95) and
   asks in Exercise 1 (p. 95) for the two comparison results: any two
   skeletons of one category are isomorphic, and two categories are
   equivalent exactly when their skeletons are isomorphic.  Riehl defines a
   skeleton instead as any skeletal category equivalent to C (Category
   Theory in Context, §1.5, Definition 1.5.16, p. 36); that reading is
   [skeletal_equivalence_is_isomorphism] below, of which the subcategory
   form is a corollary, and her Remark 1.5.17 (pp. 36-37) matches Mac
   Lane's.  She computes examples
   (Example 1.5.18, p. 37).  Awodey asks for the skeletal subcategory and
   for a property invariant under isomorphism of categories but not under
   equivalence (Category Theory, 1st ed., §7.10, Exercises 12 and 11,
   p. 188); skeletality is that property, and both halves are proved in
   Theory/Skeleton/Separation.v.  Fong & Spivak observe that a partial
   order is exactly a skeletal preorder (Seven Sketches in
   Compositionality, §1.2.2, remark 35, p. 13), which is
   [Proset_Skeletal_iff_Antisymmetric] in Instance/Proset/Skeletal.v.

   HYPOTHESES AS DATA (honest reading, per the campaign discipline).  The
   existence of a skeleton is equivalent to the axiom of choice, a caveat
   Theory/Equivalence.v has carried since long before this file, so no
   existence claim is made here: the choice is carried as the record
   [Skeleton], a full subcategory together with, for each object of C, a
   chosen object of that subcategory isomorphic to it and a proof that it is
   the only one.  Every field is load-bearing.  [skel_full] is what makes the
   inclusion full, [skel_rep] and [skel_iso] are the essential surjectivity
   that [skeleton_inclusion_is_equivalence] consumes — the counit of the
   resulting equivalence IS the chosen family, and [skel_reflect_obj] holds by
   [reflexivity] — and [skel_uniq] is what [skeleton_is_skeletal] consumes.
   This is the discipline of Theory/Equivalence.v's [EssentiallySurjective],
   where "there exists a preimage" is replaced by "here is one", and the
   packaging of [SolutionSet] in Adjunction/SAFT.v and [AdamekData] in
   Theory/Adamek.v: a leaner-but-honest hypothesis form that never weakens the
   conclusion.

   WHY [skel_uniq] IS STATED AT THE SIGMA LEVEL.  Its conclusion equates
   objects of [Sub C skel_sub], which are dependent pairs, so it also
   identifies membership proofs.  That is not extra strength imposed for
   convenience.  In a full subcategory two membership proofs for one object
   already give isomorphic objects of [Sub] ([Full_membership_iso],
   Construction/Subcategory.v), so any notion of skeletality for [Sub]
   identifies them anyway; and the weakening is provably unavailable.
   [skeleton0_skeletal_forces_UIP] shows that the carrier-level clause (the
   record [Skeleton0] below) cannot yield [Skeletal (Sub C s0_sub)] without
   entailing UIP for every type, by a free-loop-space countermodel over
   [DiscreteCat] — while [skeleton0_is_skeletal_carrier] shows the carrier
   statement itself survives, which is what makes the separation sharp.  This
   is the house pattern of [arrow_mul_respects_forces_UIP]
   (Theory/Category/Monoid.v) and [Discrete_DiscreteUpToIso_forces_UIP]
   (Instance/Discrete/Reconstruct.v).

   WHY [StrictCat] AND NOT [Cat].  Mac Lane's Exercise 1 and Riehl's Remark
   1.5.17 both say ISOMORPHIC, on the nose.  [Cat]'s hom-setoid is
   [Functor_Setoid] (Instance/Cat.v), i.e. natural isomorphism, so an
   isomorphism in [Cat] between two skeletons says only that they are
   equivalent — which already follows from [skeleton_inclusion_is_equivalence]
   on both sides, with no skeletality used at all.  The discriminating
   statement is [≅[StrictCat]], whose hom-setoid is [Functor_StrictEq_Setoid]
   (Theory/Functor.v), and that is what [skeletons_are_isomorphic] proves.
   [Skeletal_StrictCat_invariant] and
   [skeletality_is_not_equivalence_invariant] (Theory/Skeleton/Separation.v)
   are the two halves that demonstrate the distinction is real.  Note also
   that [skeletons_isomorphic_iff_equivalent] is an iff relative to GIVEN
   skeletons on both sides: it says nothing whatever about categories for
   which no [Skeleton] is supplied, which is the only reading available
   under the no-existence discipline above.

   THE CRUX, AND WHY NO RIGIDITY HYPOTHESIS IS NEEDED.  The two evident
   comparison functors between skeletons are not mutually strict inverses:
   their composite conjugates by an automorphism of the object it sits at, and
   a skeletal category can have plenty of those.  The correction is the
   half-adjoint (adjointification) move of the HoTT book, applied at the level
   of OBJECT TYPES only: from the two object bijections one builds a corrected
   counit [adjointified] satisfying the triangle [half_adjoint_triangle],
   after which the loop that would otherwise have to be collapsed is [eq_refl]
   by construction.  The alternative — assuming object-level UIP on one
   skeleton, in the idiom of [ObjDecEq] (Construction/Quotient.v) — is thereby
   avoided, and the whole file stays free of rigidity hypotheses.  Note also
   that [skel_reflect] is the identity on the OBJECTS of the skeleton
   ([skel_reflect_incl_obj], on the nose) and only naturally isomorphic to the
   identity on morphisms ([skeleton_remark]); the strict statement holds for
   the CORRECTED inverse used in Exercise 1, not for the canonical reflector.

   NON-FUNCTORIALITY, and what is proved instead.  The assignment of a
   skeleton to a category is not known to be functorial, and is expected
   not to be: a functor F : C ⟶ D need not
   carry chosen representatives to chosen representatives, so F has no strict
   lift to the chosen skeletons.  What there is, and what is proved here, is
   the comparison functor [skel_comparison] together with
   [skel_comparison_natural]: the inclusion of the comparison is naturally
   isomorphic to the restriction, which is exactly Riehl's clause, and no
   more.  The pseudofunctor that would package this coherently is out of scope
   for a reason and not for want of effort: [Pseudofunctor]
   (Theory/Bicategory/Pseudofunctor.v) requires a total object assignment from
   categories to skeletal categories, which IS the existence claim this file
   refuses to make, and there is no bicategory of skeletal categories in tree
   (Instance/Cat/Bicategory.v supplies [Cat] only).  The negative half — that
   no strictly functorial choice exists — needs a counterexample and is
   not attempted here.

   SCOPE OF THE IMPORTS.  This is a heavyweight Theory module: stating
   [≅[StrictCat]] needs Instance/StrictCat.v and Instance/StrictCat/ToCat.v,
   the bundled [≃] needs Theory/Equivalence/Bundled.v, the [≅[Fun]] forms
   need Instance/Fun.v, and the forcing countermodel needs
   Instance/Discrete.v's [DiscreteCat].  That is precedented — Theory/
   Equivalence.v already requires Instance/Fun.v and Instance/Cat.v — but it
   is deliberate rather than incidental.  The separating witnesses, which
   would additionally drag Instance/Discrete/Reconstruct.v and
   Instance/Two.v, are kept OFF this cone in Theory/Skeleton/Separation.v,
   the same split rationale Instance/Discrete/Reconstruct.v records for
   itself. *)

(** ** The half-adjoint correction, at the level of object types *)

(* The path algebra needed for [half_adjoint_triangle] below.  These are the
   HoTT-book lemmas for [f_equal] (there written [ap]) and for homotopies,
   proved here by [destruct] on the path so that nothing outside
   Coq.Init.Logic is used.  [f_equal_idmap] has no standard-library name,
   and [ap_ap] is preferred to the standard [f_equal_compose] because it is
   always applied with both functions given explicitly, which is what makes
   it fire against beta-reduced indices. *)

Section HalfAdjoint.
Context {A B : Type}.
Variable f : A → B.
Variable g : B → A.
Variable eta : ∀ a, g (f a) = a.
Variable eps : ∀ b, f (g b) = b.

Lemma f_equal_idmap {X : Type} {x y : X} (p : x = y) :
  f_equal (fun z => z) p = p.
Proof. now destruct p. Qed.

Lemma ap_ap {X Y Z : Type} (u : X → Y) (v : Y → Z) {x y : X} (p : x = y) :
  f_equal v (f_equal u p) = f_equal (fun t => v (u t)) p.
Proof. now destruct p. Qed.

Lemma homotopy_natural {X Y : Type} (u v : X → Y) (H : ∀ x, u x = v x)
      {x y : X} (p : x = y) :
  eq_trans (H x) (f_equal v p) = eq_trans (f_equal u p) (H y).
Proof. destruct p; simpl. now rewrite eq_trans_refl_l. Qed.

Lemma cancel_right {X : Type} {x y z : X} (p q : x = y) (r : y = z) :
  eq_trans p r = eq_trans q r → p = q.
Proof. destruct r; auto. Qed.

Lemma homotopy_id_shift (u : A → A) (H : ∀ x, u x = x) (x : A) :
  H (u x) = f_equal u (H x).
Proof.
  apply (cancel_right _ _ (H x)).
  pose proof (homotopy_natural u (fun z => z) H (H x)) as N.
  rewrite f_equal_idmap in N. now rewrite N.
Qed.

Lemma ap_eta (a : A) :
  f_equal f (eta (g (f a))) = f_equal (fun z => f (g z)) (f_equal f (eta a)).
Proof.
  rewrite (ap_ap f (fun z => f (g z)) (eta a)).
  pose proof (homotopy_id_shift (fun x => g (f x)) eta a) as E1.
  simpl in E1. rewrite E1.
  now rewrite (ap_ap (fun x => g (f x)) f (eta a)).
Qed.

(* The corrected counit.  The raw [eps] satisfies no triangle: [eps (f a)]
   and [f_equal f (eta a)] are two proofs of one object equality, and
   identifying them is exactly what UIP would buy.  [adjointified] repairs
   [eps] so that the triangle holds by path algebra alone. *)

Definition adjointified (b : B) : f (g b) = b :=
  eq_trans (eq_sym (eps (f (g b)))) (eq_trans (f_equal f (eta (g b))) (eps b)).

Lemma half_adjoint_triangle (a : A) : adjointified (f a) = f_equal f (eta a).
Proof.
  unfold adjointified. rewrite ap_eta.
  pose proof (homotopy_natural (fun z => f (g z)) (fun z => z) eps
                (f_equal f (eta a))) as N.
  rewrite f_equal_idmap in N. rewrite <- N.
  rewrite eq_trans_assoc, eq_trans_sym_inv_l.
  now rewrite eq_trans_refl_l.
Qed.

End HalfAdjoint.

(** ** Strict functor equality from a family of object equalities *)

(* [Functor_StrictEq_Setoid] compares functors by a family of object
   equalities together with a transported-morphism condition.  Stating that
   condition with [id_cast] instead of raw [transport] keeps every proof
   below inside the ordinary categorical calculus. *)

Lemma transport_square {D : Category} {a a' b b' : D}
  (p : a = a') (q : b = b') (u : a ~{D}~> b) (v : a' ~{D}~> b') :
  (Logic.transport (fun z => a ~{D}~> z) q u
     ≈ Logic.transport_r (fun z => z ~{D}~> b') p v)
  ↔ (id_cast q ∘ u ≈ v ∘ id_cast p).
Proof.
  destruct p, q; unfold Logic.transport, Logic.transport_r, id_cast; simpl;
    split; intro H; [ now rewrite id_left, id_right | ].
  now rewrite id_left, id_right in H.
Qed.

Definition strict_equiv_of_id_cast_nat
  {C D : Category} (F G : C ⟶ D) (e : ∀ x : C, F x = G x)
  (H : ∀ (x y : C) (f : x ~> y),
         id_cast (e y) ∘ fmap[F] f ≈ fmap[G] f ∘ id_cast (e x)) :
  @equiv _ (@Functor_StrictEq_Setoid C D) F G :=
  existT _ e (fun x y f => snd (transport_square (e x) (e y)
                                  (fmap[F] f) (fmap[G] f)) (H x y f)).

(** ** Skeletal categories *)

(* Mac Lane §IV.4 Definition 3, second half; Riehl Definition 1.5.16.  A
   plain [Definition], not a [Class]: nothing here is registered for
   instance resolution, following Theory/Equivalence.v. *)

Definition Skeletal (C : Category) := ∀ x y : C, x ≅ y → x = y.

(** ** An equivalence between skeletal categories is an isomorphism *)

(* The general lemma, of which Mac Lane's Exercise 1 is a corollary.  The
   quasi-inverse supplied by the equivalence is corrected twice: its action
   on morphisms is replaced by the [prefmap] of a [hom_cast] (so that the
   two composites are strictly, not merely naturally, the identities), and
   its object counit is replaced by [adjointified] (so that no rigidity
   hypothesis is needed). *)

Section SkeletalEquivalence.
Context {A B : Category}.
Variable SA : Skeletal A.
Variable SB : Skeletal B.
Variable F : A ⟶ B.
Variable E : EquivalenceOfCategories F.
#[local] Existing Instance E.
Notation G := (@quasi_inverse A B F E).

Definition F_Full : Category.Theory.Functor.Full F := Equivalence_Full E.
Definition F_Faithful : Faithful F := Equivalence_Faithful E.

Definition eta_ob (a : A) : G (F a) = a :=
  eq_sym (SA a (G (F a)) (@equivalence_unit_at A B F E a)).
Definition eps_ob (b : B) : F (G b) = b :=
  SB (F (G b)) b (@equivalence_counit_at A B F E b).
Definition Eps (b : B) : F (G b) = b :=
  adjointified (fobj[F]) (fobj[G]) eta_ob eps_ob b.

Lemma Eps_triangle (a : A) : Eps (F a) = f_equal (fobj[F]) (eta_ob a).
Proof. apply half_adjoint_triangle. Qed.

#[local] Obligation Tactic := idtac.

Program Definition Finv : B ⟶ A := {|
  fobj := fun b => G b;
  fmap := fun b b' h =>
    prefmap (Full := F_Full) (hom_cast (eq_sym (Eps b)) (eq_sym (Eps b')) h)
|}.
Next Obligation.
  intros b b' h h' Hh.
  apply (fmap_inj (Faithful := F_Faithful)).
  rewrite !(fmap_sur (Full := F_Full)).
  now apply hom_cast_respects.
Qed.
Next Obligation.
  intros b.
  apply (fmap_inj (Faithful := F_Faithful)).
  rewrite (fmap_sur (Full := F_Full)), fmap_id.
  now rewrite hom_cast_id.
Qed.
Next Obligation.
  intros b b' b'' g h.
  apply (fmap_inj (Faithful := F_Faithful)).
  rewrite fmap_comp, !(fmap_sur (Full := F_Full)).
  now rewrite hom_cast_comp.
Qed.

Lemma FFinv_strict :
  @equiv _ (@Functor_StrictEq_Setoid B B) (F ◯ Finv) Id[B].
Proof using All.
  apply (strict_equiv_of_id_cast_nat (F ◯ Finv) Id[B] Eps).
  intros b b' h.
  change (fmap[F ◯ Finv] h)
    with (fmap[F] (prefmap (Full := F_Full)
            (hom_cast (eq_sym (Eps b)) (eq_sym (Eps b')) h))).
  rewrite (fmap_sur (Full := F_Full)).
  rewrite hom_cast_decompose, eq_sym_involutive, !comp_assoc.
  rewrite id_cast_inv_r, id_left.
  reflexivity.
Qed.

(* The [!Eps_triangle] rewrite below is the crux: with the RAW counit the
   goal would carry a loop at the intermediate object that only UIP could
   collapse. *)

Lemma FinvF_strict :
  @equiv _ (@Functor_StrictEq_Setoid A A) (Finv ◯ F) Id[A].
Proof using All.
  apply (strict_equiv_of_id_cast_nat (Finv ◯ F) Id[A] eta_ob).
  intros a b f.
  apply (fmap_inj (Faithful := F_Faithful)).
  rewrite !fmap_comp, !fmap_id_cast.
  change (fmap[Finv ◯ F] f)
    with (prefmap (Full := F_Full)
            (hom_cast (eq_sym (Eps (F a))) (eq_sym (Eps (F b))) (fmap[F] f))).
  rewrite (fmap_sur (Full := F_Full)).
  rewrite hom_cast_decompose, eq_sym_involutive, !Eps_triangle, !comp_assoc.
  rewrite id_cast_inv_r, id_left.
  reflexivity.
Qed.

Definition skeletal_equivalence_is_isomorphism : A ≅[StrictCat] B :=
  @Build_Isomorphism StrictCat A B F Finv FFinv_strict FinvF_strict.

End SkeletalEquivalence.

Arguments skeletal_equivalence_is_isomorphism {A B} SA SB F E.

(** ** "A is a skeleton of C", packaged as data *)

(* Mac Lane §IV.4 Definition 3, first half; Riehl Definition 1.5.16.  The
   uniqueness clause concludes in [Sub C skel_sub], not in C: see the header
   for why that strengthening is necessary rather than convenient.  Note
   also that Lib/Setoid.v's [Unique]/[∃!] must NOT be used here: at object
   level the exported [ob_setoid] makes [≈] mean isomorphism, so [Unique]
   would state a vacuity. *)

Section Skeleton.
Context {C : Category}.

Record Skeleton := {
  skel_sub  : Subcategory C;
  skel_full : Subcategory.Full C skel_sub;
  skel_rep  : C → Sub C skel_sub;
  skel_iso  : ∀ x : C, x ≅ `1 (skel_rep x);
  skel_uniq : ∀ (x : C) (a : Sub C skel_sub), x ≅ `1 a → skel_rep x = a
}.

End Skeleton.

Arguments Skeleton : clear implicits.

Definition skel_cat {C : Category} (S : Skeleton C) : Category :=
  Sub C (skel_sub S).

Definition skel_incl {C : Category} (S : Skeleton C) : skel_cat S ⟶ C :=
  Incl C (skel_sub S).

Section SkeletonTheory.
Context {C : Category}.
Variable S : Skeleton C.

Theorem skeleton_is_skeletal : Skeletal (skel_cat S).
Proof using.
  intros a b i.
  rewrite <- (skel_uniq S `1 a a iso_id).
  apply (skel_uniq S).
  exists (`1 (to i)) (`1 (from i)).
  - exact (iso_to_from i).
  - exact (iso_from_to i).
Qed.

Definition Incl_Full : Functor.Full (skel_incl S) :=
  Full_Implies_Full_Functor C (skel_sub S) (skel_full S).

Program Definition Incl_EssSurj : EssentiallySurjective (skel_incl S) := {|
  eso_obj := skel_rep S;
  eso_iso := fun x => iso_sym (skel_iso S x)
|}.

(* Mac Lane §IV.4 Remark 1, first half: the inclusion of a skeleton is an
   equivalence.  [Defined], so that the reflector below reduces. *)

Theorem skeleton_inclusion_is_equivalence :
  EquivalenceOfCategories (skel_incl S).
Proof using.
  exact (@FF_ESO_Equivalence _ _ (skel_incl S)
           Incl_Full (Incl_Faithful C (skel_sub S)) Incl_EssSurj).
Defined.

Definition skeleton_equivalence : skel_cat S ≃ C :=
  (skel_incl S; skeleton_inclusion_is_equivalence).

(* the reflector, and the two halves of the Remark *)
Definition skel_reflect : C ⟶ skel_cat S :=
  @quasi_inverse _ _ _ skeleton_inclusion_is_equivalence.

Definition skeleton_counit : skel_incl S ◯ skel_reflect ≈ Id[C] :=
  @equivalence_counit _ _ _ skeleton_inclusion_is_equivalence.

Definition skeleton_unit : Id[skel_cat S] ≈ skel_reflect ◯ skel_incl S :=
  @equivalence_unit _ _ _ skeleton_inclusion_is_equivalence.

Corollary skel_reflect_obj (x : C) : skel_reflect x = skel_rep S x.
Proof. reflexivity. Qed.

Corollary skel_reflect_incl_obj (a : skel_cat S) :
  skel_reflect (skel_incl S a) = a.
Proof. exact (skel_uniq S `1 a a iso_id). Qed.

End SkeletonTheory.

Arguments skel_reflect {C} S.

Definition skeleton_counit_iso {C : Category} (S : Skeleton C) :
  skel_incl S ◯ skel_reflect S ≅[Fun] Id[C] :=
  equiv_iso (skeleton_counit S).

Definition skeleton_unit_iso {C : Category} (S : Skeleton C) :
  Id[skel_cat S] ≅[Fun] skel_reflect S ◯ skel_incl S :=
  equiv_iso (skeleton_unit S).

(* Mac Lane §IV.4 Remark 1, in the issue's own orientation.  The second
   component is at OBJECTS only: [skel_reflect S ◯ skel_incl S ≈[StrictCat]
   Id] is not derivable in general for the CANONICAL reflector (it holds in
   degenerate cases such as [Indiscrete_bool_Skeleton]), since it would need a
   normality coherence tying the chosen isomorphism to the chosen equality.
   The strict statement holds instead for the CORRECTED inverse built in
   Exercise 1 below. *)

Definition skeleton_remark {C : Category} (S : Skeleton C) :
  (Id[C] ≅[Fun] skel_incl S ◯ skel_reflect S)
  * (∀ a : skel_cat S, skel_reflect S (skel_incl S a) = a) :=
  (iso_sym (skeleton_counit_iso S), skel_reflect_incl_obj S).

(* THE GROUPOID OF FINITE SETS AND BIJECTIONS is not in tree, and this
   development does not pretend otherwise.  Riehl's Example 1.5.18 computes
   its skeleton — the naturals, with the symmetric groups as automorphism
   groups and no morphisms between distinct numbers — but "the skeleton OF"
   needs the ambient groupoid, and there is none: Construction/Groupoid.v
   supplies only the core [Groupoid C] of a given C, and building the groupoid
   of ALL finite sets over [Sets] would reproduce the universe obstruction
   docs/INHABITATION.md already records for cospans, where [Sets] places its
   objects one universe above its homs.  The skeleton-side facts about
   [Groupoid FinSet] — that it is skeletal, that its off-diagonal hom-sets are
   empty, and that its automorphism monoid at [n] is the group of bijections
   of the canonical n-element set — are each cheap over the
   [hom_monoid]/[GrpObject] of Construction/Deloop.v, but they are statements
   about [Groupoid FinSet], not about a skeleton of anything, and they are
   left for a follow-up rather than stated. *)

(** ** Mac Lane §IV.4 Exercise 1 *)

Definition skeletons_of_equivalent_are_isomorphic
  {C D : Category} (S : Skeleton C) (T : Skeleton D) (Eq : C ≃ D) :
  skel_cat S ≅[StrictCat] skel_cat T :=
  let e : skel_cat S ≃ skel_cat T :=
      Equivalence_trans (skeleton_equivalence S)
        (Equivalence_trans Eq (Equivalence_sym (skeleton_equivalence T))) in
  skeletal_equivalence_is_isomorphism
    (skeleton_is_skeletal S) (skeleton_is_skeletal T) (`1 e) (`2 e).

Definition skeletons_are_isomorphic {C : Category} (S1 S2 : Skeleton C) :
  skel_cat S1 ≅[StrictCat] skel_cat S2 :=
  skeletons_of_equivalent_are_isomorphic S1 S2 (Equivalence_refl C).

Definition strict_iso_to_equivalence {A B : Category}
           (i : A ≅[StrictCat] B) : A ≃ B :=
  (to i;
   @Build_EquivalenceOfCategories A B (to i) (from i)
     (strict_equiv_implies_fun_equiv _ _ (iso_to_from i))
     (symmetry (strict_equiv_implies_fun_equiv _ _ (iso_from_to i)))).

Definition equivalent_of_isomorphic_skeletons
  {C D : Category} (S : Skeleton C) (T : Skeleton D)
  (i : skel_cat S ≅[StrictCat] skel_cat T) : C ≃ D :=
  Equivalence_trans (Equivalence_sym (skeleton_equivalence S))
    (Equivalence_trans (strict_iso_to_equivalence i) (skeleton_equivalence T)).

Definition skeletons_isomorphic_iff_equivalent
  {C D : Category} (S : Skeleton C) (T : Skeleton D) :
  (C ≃ D) ↔ (skel_cat S ≅[StrictCat] skel_cat T) :=
  (skeletons_of_equivalent_are_isomorphic S T,
   equivalent_of_isomorphic_skeletons S T).

(** ** Riehl Remark 1.5.17: the comparison functor along an arbitrary F *)

Definition skel_comparison {C D : Category}
  (S : Skeleton C) (T : Skeleton D) (F : C ⟶ D) : skel_cat S ⟶ skel_cat T :=
  skel_reflect T ◯ (F ◯ skel_incl S).

Theorem skel_comparison_natural {C D : Category}
  (S : Skeleton C) (T : Skeleton D) (F : C ⟶ D) :
  skel_incl T ◯ skel_comparison S T F ≈ F ◯ skel_incl S.
Proof.
  unfold skel_comparison.
  rewrite (fun_equiv_comp_assoc (skel_incl T) (skel_reflect T)
             (F ◯ skel_incl S)).
  rewrite (skeleton_counit T).
  now rewrite (fun_equiv_id_left (F ◯ skel_incl S)).
Qed.

Definition skel_comparison_natural_iso {C D : Category}
  (S : Skeleton C) (T : Skeleton D) (F : C ⟶ D) :
  skel_incl T ◯ skel_comparison S T F ≅[Fun] F ◯ skel_incl S :=
  equiv_iso (skel_comparison_natural S T F).

(** ** Why the uniqueness clause cannot be weakened to carriers *)

Section Skeleton0.
Context {C : Category}.

Record Skeleton0 := {
  s0_sub  : Subcategory C;
  s0_full : Subcategory.Full C s0_sub;
  s0_rep  : C → Sub C s0_sub;
  s0_iso  : ∀ x : C, x ≅ `1 (s0_rep x);
  s0_uniq : ∀ (x : C) (a : Sub C s0_sub), x ≅ `1 a → `1 (s0_rep x) = `1 a
}.

End Skeleton0.
Arguments Skeleton0 : clear implicits.

Theorem skeleton0_is_skeletal_carrier {C : Category} (S : Skeleton0 C)
        (a b : Sub C (s0_sub S)) (i : a ≅ b) : `1 a = `1 b.
Proof.
  rewrite <- (s0_uniq S `1 a a iso_id).
  apply (s0_uniq S).
  exists (`1 (to i)) (`1 (from i)).
  - exact (iso_to_from i).
  - exact (iso_from_to i).
Qed.

(* The countermodel: over a discrete category, select as membership proofs
   the free loop space of each object. *)

Program Definition Loop_Sub (A : Type) : Subcategory (DiscreteCat A) := {|
  sobj := fun x => x = x;
  shom := fun x y ox oy f => True
|}.

Program Definition LoopSkeleton0 (A : Type) : Skeleton0 (DiscreteCat A) := {|
  s0_sub  := Loop_Sub A;
  s0_full := fun x y ox oy f => I;
  s0_rep  := fun x => (x; @eq_refl A x);
  s0_iso  := fun x => iso_id;
  s0_uniq := fun x a f => to f
|}.

Theorem skeleton0_skeletal_forces_UIP
  (K : ∀ (C : Category) (S : Skeleton0 C), Skeletal (Sub C (s0_sub S))) :
  ∀ (A : Type) (x y : A) (p q : x = y), p = q.
Proof.
  intros A.
  assert (loops : ∀ (x : A) (l : x = x), l = eq_refl).
  { intros x l.
    pose proof (K (DiscreteCat A) (LoopSkeleton0 A)
                  (x; @eq_refl A x) (x; l)
                  (Full_sub_iso (DiscreteCat A) (Loop_Sub A)
                     (fun _ _ _ _ _ => I) (@eq_refl A x) l iso_id)) as H.
    exact (match H in _ = w return (`2 w = @eq_refl A (`1 w))
           with eq_refl => eq_refl end). }
  intros x y p q; destruct p; symmetry; apply loops.
Qed.

(** ** A skeletal category is its own skeleton *)

Program Definition Wide_Sub (C : Category) : Subcategory C := {|
  sobj := fun _ => poly_unit;
  shom := fun x y ox oy f => True
|}.

Section SkeletalOwnSkeleton.
#[local] Obligation Tactic := idtac.

Program Definition Skeleton_of_Skeletal {C : Category} (H : Skeletal C) :
  Skeleton C := {|
  skel_sub  := Wide_Sub C;
  skel_full := fun x y ox oy f => I;
  skel_rep  := fun x => (x; ttt);
  skel_iso  := fun x => iso_id;
  skel_uniq := _
|}.
Next Obligation.
  intros C H x a i.
  destruct a as [y oy]; simpl in *.
  destruct (H x y i).
  now destruct oy.
Qed.

End SkeletalOwnSkeleton.

Lemma DiscreteCat_Skeletal (A : Type) : Skeletal (DiscreteCat A).
Proof. intros x y f; exact (to f). Qed.

(** ** Awodey §7.10 Exercise 11, positive half *)

(* Skeletality IS invariant under isomorphism of categories.  The other
   half — that it is not invariant under equivalence — is
   [skeletality_is_not_equivalence_invariant] in
   Theory/Skeleton/Separation.v. *)

Theorem Skeletal_StrictCat_invariant {C D : Category}
        (i : C ≅[StrictCat] D) : Skeletal C → Skeletal D.
Proof.
  intro SC.
  destruct (iso_to_from i) as [eq_ob _].
  assert (E : ∀ d : D, fobj[to i] (fobj[from i] d) = d)
    by (intro d; exact (eq_ob d)).
  intros x y f.
  exact (eq_trans (eq_sym (E x))
           (eq_trans (f_equal (fobj[to i])
                        (SC (from i x) (from i y) (fobj_iso (from i) x y f)))
              (E y))).
Qed.

(* The posetal REFLECTION — that every preorder HAS a skeleton — is a
   different statement and is not made: it needs an object-level quotient, and
   Construction/Quotient.v quotients homs only.  The catalog assigns that
   clause to #372.  What is proved is the given-skeleton form,
   [skeleton_of_proset_antisymmetric] (Instance/Proset/Skeletal.v): the
   carrier of a skeleton of a preorder is antisymmetric, that is, a poset. *)
