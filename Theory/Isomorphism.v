Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Morphisms.

Generalizable All Variables.

Section Isomorphism.

Universes o h p.
Context {C : Category@{o h p}}.

(* nLab: https://ncatlab.org/nlab/show/isomorphism
   Wikipedia: https://en.wikipedia.org/wiki/Isomorphism

   An isomorphism `x ≅ y` is a morphism `to : x ~> y` equipped with a
   two-sided inverse `from : y ~> x`, witnessed by `to ∘ from ≈ id`
   (iso_to_from) and `from ∘ to ≈ id` (iso_from_to). Because identities are
   isomorphisms (iso_id), the inverse of an isomorphism is an isomorphism
   (iso_sym), and a composite of isomorphisms is an isomorphism (iso_compose),
   the relation `≅` is an equivalence relation on objects (iso_equivalence).
   As elsewhere in the library the inverse laws use the hom-setoid equivalence
   `≈` rather than Coq's `=`. *)

(* This defines what it means for two objects in a category to be
   "isomorphic". This requires both witnesses to the isomoprhism, and proof
   their compositions are equivalent to identity in both directions. Since
   this is a computationally relevant definition, having an isomorphism allows
   for conversion of objects within definitions.

   An isomorphism in Cat is the same as an equivalence of categories. In order
   to get actual isomorphism between categories, the compositions F ○ G and G
   ○ F need to be equal, rather than equivalent, to identity. Since this is
   usually too strong a notion, it does not have its own abstraction here. *)

(* Sameness up to isomorphism: history, principle, and reach

   nLab:  https://ncatlab.org/nlab/show/principle+of+equivalence
   nLab:  https://ncatlab.org/nlab/show/core
   Words: https://mathshistory.st-andrews.ac.uk/Miller/mathword/i/
   Paper: Eilenberg, Mac Lane, "General Theory of Natural Equivalences",
          Trans. Amer. Math. Soc. 58, 1945
   Essay: Mazur, "When is one thing equal to some other thing?", 2007

   The word predates the theory.  Built from the Greek isos (equal) and
   morphe (form), it reached mathematics from crystallography: per Jeff
   Miller's Earliest Known Uses survey, geology texts before 1864 already
   spoke of the geometrical isomorphism of crystals, Camille Jordan's
   Traité des substitutions (1870) called one group "isomorphe" to
   another, and Walther von Dyck used it in his Gruppentheoretische
   Studien (1882).  The founding paper of category theory then renamed the
   concept: Eilenberg and Mac Lane (1945) say "equivalence" for an
   invertible morphism, prove as their Lemma 1.4 that its left and right
   inverses coincide and are unique, and remark that the resulting
   relation between objects is reflexive, symmetric and transitive.  This
   file restates those opening lemmas in setoid form:
   [comp_inverse_unique] is Lemma 1.4, and [iso_equivalence] is the
   equivalence-relation remark, recorded on objects as [ob_setoid].

   The concept decides when two objects are the same for categorical
   purposes.  "The major concept that replaces equality in the context of
   categories is isomorphism", and it is "usually either quixotic, or
   irrelevant" to ask whether two objects are equal; the pertinent request
   is "a specific isomorphism from X to Y" (Mazur, "When is one thing equal
   to some other thing?", 2007).  Makkai's Principle of Isomorphism asks
   that every grammatically correct property of objects be invariant under
   isomorphism, Aczel's Structure Identity Principle states the same for
   structures, and Voevodsky's univalence axiom makes the invariance
   automatic by identifying equivalences with inhabitants of the identity
   type (nLab, principle of equivalence).  Mazur's insistence on a
   specific isomorphism is the stance [Isomorphism] takes: a Class landing
   in Type — the data [to] and [from] with the two inverse laws — rather
   than a bare existence statement; his example is the two constructions
   of the algebraic closure of F₂, abstractly isomorphic yet with no way
   of pinpointing a specific isomorphism.  [IsIsomorphism] keeps the
   predicate reading available when only invertibility of a given morphism
   is at issue.

   The payoff theorem is uniqueness of universal objects: "representing
   objects qua representations are unique up to unique isomorphism.
   Hence, limits qua limits are unique up to unique isomorphism" (Riehl,
   "A survey of categorical concepts").  In this library the statement is
   [univ_property_unique_up_to_unique_iso] in Structure/UniversalProperty.v,
   with Structure/Terminal.v the simplest instance.  Isomorphisms also
   occur as structure rather than property: the coherence cells
   [unit_left], [unit_right] and [tensor_assoc] of Structure/Monoidal.v are
   fields of type ≅, chosen data that a monoidal category carries.

   Discarding the non-invertible morphisms of a category leaves its core,
   the maximal subgroupoid; the core construction is right adjoint to the
   inclusion of groupoids into categories (nLab, core).
   Construction/Groupoid.v builds it from this file directly, taking
   [iso_setoid] for its hom-setoids and [iso_id] and [iso_compose] for
   identity and composition.  Groupoids themselves predate category theory:
   Brandt introduced and named them in a 1926/27 paper on the composition
   of quadratic forms in four variables, and they have since unified
   internal and external symmetry, from group actions to Grothendieck's
   moduli problems (Weinstein, "Groupoids: unifying internal and external
   symmetry", Notices Amer. Math. Soc. 1996).

   The computational reading extends the remark in the header above.  A
   term of type x ≅ y is a transport device, the same data as the Iso
   optic of Haskell's lens library, built "from a pair of inverse
   functions" (Kmett, Control.Lens.Iso); type isomorphisms — those holding
   in every cartesian closed category — likewise let function libraries be
   searched by type modulo isomorphism (Rittri, "Using types as search
   keys in function libraries", JFP 1991; Di Cosmo, "Isomorphisms of
   Types", Birkhäuser 1995).  Transport along an isomorphism is well
   defined because inverses are unique: [to_equiv_implies_iso_equiv] shows
   an isomorphism is determined up to [iso_equiv] by its [to] component
   alone, the setoid-local shadow of the homotopy-type-theoretic fact that
   being an isomorphism is a proposition (nLab, isomorphism). *)

Class Isomorphism (x y : C) : Type := {
  to   : x ~> y;            (* the forward morphism x ~> y *)
  from : y ~> x;            (* its two-sided inverse y ~> x *)

  iso_to_from : to ∘ from ≈ id;   (* right inverse law: to ∘ from ≈ id *)
  iso_from_to : from ∘ to ≈ id    (* left  inverse law: from ∘ to ≈ id *)
}.

Arguments to {x y} _.
Arguments from {x y} _.
Arguments iso_to_from {x y} _.
Arguments iso_from_to {x y} _.

Infix "≅" := Isomorphism (at level 91) : category_scope.

(* The predicate form: `f` is an isomorphism iff it has a two-sided inverse.
   This is the nLab definition "an invertible morphism", phrased about a
   single morphism `f` rather than about a pair of objects; [IsIsoToIso]
   below recovers the object-level [Isomorphism] from it. *)

Class IsIsomorphism {x y : C} (f : x ~> y) := {
    two_sided_inverse : y ~> x;                  (* the inverse g : y ~> x *)
    is_right_inverse : f ∘ two_sided_inverse ≈ id;  (* right inverse: f ∘ g ≈ id *)
    is_left_inverse : two_sided_inverse ∘ f ≈ id    (* left  inverse: g ∘ f ≈ id *)
  }.

#[export]
Instance IsIsoToIso {x y : C} (f : x ~> y) ( _ : IsIsomorphism f) : Isomorphism x y :=
  {|
    to := f;
    from := two_sided_inverse;
    iso_to_from := is_right_inverse;
    iso_from_to := is_left_inverse
  |}.

(* Reflexivity of ≅: the identity is an isomorphism. *)
#[export] Program Instance iso_id {x : C} : x ≅ x := {
  to   := id;
  from := id
}.

(* Symmetry of ≅: the inverse of an isomorphism is an isomorphism,
   obtained by swapping `to` and `from` and the two inverse laws. *)
Program Definition iso_sym {x y : C} `(f : x ≅ y) : y ≅ x := {|
  to   := from f;
  from := to f;

  iso_to_from := iso_from_to f;
  iso_from_to := iso_to_from f
|}.

(* Transitivity of ≅: a composite of isomorphisms is an isomorphism, with
   inverse `from g ∘ from f` (the inverses compose in the opposite order). *)
Program Definition iso_compose {x y z : C} `(f : y ≅ z) `(g : x ≅ y) :
  x ≅ z := {|
  to   := to f ∘ to g;
  from := from g ∘ from f
|}.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (to g)).
  rewrite iso_to_from; cat.
  apply iso_to_from.
Defined.
Next Obligation.
  rewrite <- comp_assoc.
  rewrite (comp_assoc (from f)).
  rewrite iso_from_to; cat.
  apply iso_from_to.
Defined.

(* Bundling the three constructions above: `≅` is an equivalence relation on
   the objects of C. (Per nLab, the isomorphisms of C are the morphisms of its
   core groupoid; this instance records the relation they induce on objects.) *)
#[export] Program Instance iso_equivalence : Equivalence Isomorphism := {
  Equivalence_Reflexive  := @iso_id;
  Equivalence_Symmetric  := @iso_sym;
  Equivalence_Transitive := fun _ _ _ g f => iso_compose f g
}.

Definition ob_equiv : crelation C := Isomorphism.

#[export] Instance ob_setoid : Setoid C :=
  {| equiv := Isomorphism
   ; setoid_equiv := iso_equivalence |}.

(* Equivalence of two isomorphisms between the *same* pair of objects (as
   opposed to `≅`, which relates objects): two isos are equal when their `to`
   and `from` components are equal as morphisms under `≈`. This makes each
   hom `x ≅ y` of isomorphisms into a setoid ([iso_setoid] below). *)
Definition iso_equiv {x y : C} : crelation (x ≅ y) :=
  fun f g => (to f ≈ to g) * (from f ≈ from g).

#[export] Program Instance iso_equiv_equivalence {x y : C} :
  Equivalence (@iso_equiv x y).
Next Obligation. now firstorder. Qed.
Next Obligation. now firstorder. Qed.
Next Obligation.
  firstorder;
  try solve [ now transitivity (to y0)
            | now transitivity (from y0) ].
Qed.

#[export] Instance iso_setoid {x y : C} : Setoid (x ≅ y) := {
  equiv := iso_equiv;
  setoid_equiv := iso_equiv_equivalence
  }.

#[local] Obligation Tactic := program_simpl.

#[export] Program Instance Iso_Proper :
  Proper (Isomorphism ==> Isomorphism ==> iffT) Isomorphism.
Next Obligation.
  proper.
  - refine (iso_compose _ (iso_sym X)).
    exact (iso_compose _ X1).
  - refine (iso_compose _ X).
    refine (iso_compose _ X1).
    exact (iso_sym X0).
Defined.

End Isomorphism.

Declare Scope isomorphism_scope.
Delimit Scope isomorphism_scope with isomorphism.
Open Scope isomorphism_scope.

Notation "x ≅ y" := (@Isomorphism _%category x%object y%object)
  (at level 91) : isomorphism_scope.
Notation "x ≅[ C ] y" := (@Isomorphism C%category x%object y%object)
  (at level 91, only parsing) : isomorphism_scope.

Arguments to {_%_category x%_object y%_object} _%_morphism.
Arguments from {_%_category x%_object y%_object} _%_morphism.
Arguments iso_to_from {_ _ _} _.
Arguments iso_from_to {_ _ _} _.

Coercion to : Isomorphism >-> hom.

Notation "f '⁻¹'" := (from f) (at level 9, format "f '⁻¹'") : morphism_scope.

#[export] Hint Unfold iso_equiv : core.

Ltac isomorphism :=
  unshelve (refine {| to := _; from := _ |}; simpl; intros).

(* Every isomorphism is both monic and epic, in each direction: `to` and
   `from` are cancellable on both sides because each has a two-sided inverse.
   (The converse fails in general; see [Monic_Retraction_Iso] below for the
   extra hypothesis that recovers an isomorphism.) *)
#[export]
Program Instance iso_to_monic {C : Category} {x y} (iso : @Isomorphism C x y) :
  Monic iso.
Next Obligation.
  rewrite <- (id_left g1).
  rewrite <- (id_left g2).
  rewrite <- !(iso_from_to iso).
  rewrite <- !comp_assoc.
  rewrites; reflexivity.
Qed.

#[export]
Program Instance iso_from_monic {C : Category} {x y} (iso : @Isomorphism C x y) :
  Monic (iso⁻¹).
Next Obligation.
  rewrite <- (id_left g1).
  rewrite <- (id_left g2).
  rewrite <- !(iso_to_from iso).
  rewrite <- !comp_assoc.
  rewrites; reflexivity.
Qed.

#[export]
Program Instance iso_to_epic {C : Category} {x y} (iso : @Isomorphism C x y) :
  Epic iso.
Next Obligation.
  rewrite <- (id_right g1).
  rewrite <- (id_right g2).
  rewrite <- !(iso_to_from iso).
  rewrite !comp_assoc.
  rewrites; reflexivity.
Qed.

(* Two-sided inverses are unique up to ≈: if `g` is a right inverse and `g'`
   a left inverse of the same `f`, they agree. Stated for plain morphisms (no
   isomorphism packaging), which is the form inverted coherence laws
   downstream consume (e.g. the interchange toolkit of
   Structure/Monoidal/Braided/Proofs.v). *)
Lemma comp_inverse_unique
      {C : Category} {x y : C} (f : x ~> y) (g g' : y ~> x) :
  f ∘ g ≈ id[y] -> g' ∘ f ≈ id[x] -> g ≈ g'.
Proof.
  intros H1 H2.
  rewrite <- (id_left g).
  rewrite <- H2.
  rewrite <- comp_assoc.
  rewrite H1.
  apply id_right.
Qed.

(* Two-sided inverses are unique, so an isomorphism is determined by its `to`
   component: if `to f ≈ to g` then the `from` components agree as well, hence
   `f ≈ g`. The proof uses that `to f` is epic (a standard inverse-uniqueness
   argument). *)
Proposition to_equiv_implies_iso_equiv {C : Category} {x y} (f g : x ≅ y) :
  to f ≈ to g -> f ≈ g.
Proof.
  intro eq. split; [ assumption | ].
  assert (m := iso_to_epic f).
  destruct f as [tof fromf tofrom_eqf fromto_eqf],
      g as [tog fromg tofrom_eqg fromto_eqg].
  simpl in *.
  destruct m as [epic]. apply epic.
  rewrite fromto_eqf, eq, fromto_eqg; reflexivity.
Qed.

#[export]
Instance iso_sym_proper {C: Category} {x y : C} : Proper (equiv ==> equiv) (@iso_sym C x y).
Proof.
  intros f g [fg_toeq fg_fromeq]; destruct f as [ffrom fto ? ?], g as [gfrom gto ? ?];
    simpl in *.
  unfold iso_equiv; split; assumption.
Qed.

#[export]
Instance iso_compose_proper {C : Category} {x y z : C} :
  Proper ((@iso_equiv C y z) ==> @iso_equiv C x y ==> (@iso_equiv C x z)) iso_compose.
Proof.
  intros f1 f2 eqf g1 g2 eqg.
  apply to_equiv_implies_iso_equiv.
  destruct f1 as [f1to ? ? ?], f2 as [f2to ? ? ?], eqf as [eqfto _], eqg as [eqgto _].
  simpl in *.
  rewrite eqfto, eqgto.
  reflexivity.
Qed.

Proposition iso_sym_left_inverse {C : Category} {x y : C} (f : x ≅ y) :
  iso_compose (iso_sym f) f ≈ iso_id.
Proof.
  apply to_equiv_implies_iso_equiv, iso_from_to.
Qed.

Proposition iso_sym_right_inverse {C : Category} {x y : C} (f : x ≅ y) :
  iso_compose f (iso_sym f) ≈ iso_id.
Proof.
  apply to_equiv_implies_iso_equiv, iso_to_from.
Qed.

Proposition from_equiv_implies_iso_equiv {C : Category} {x y} (f g : x ≅ y) :
  from f ≈ from g -> f ≈ g.
Proof.
  set (f1 := iso_sym f).
  set (g1 := iso_sym g).
  change f with (iso_sym (iso_sym f)).
  change g with (iso_sym (iso_sym g)).
  change (iso_sym f) with f1.
  change (iso_sym g) with g1.
  clearbody f1 g1. clear f g.
  simpl. intro eq; apply to_equiv_implies_iso_equiv in eq.
  now apply iso_sym_proper.
Qed.

#[export]
Program Instance iso_from_epic {C : Category} {x y} (iso : @Isomorphism C x y) :
  Epic (iso⁻¹).
Next Obligation.
  rewrite <- (id_right g1).
  rewrite <- (id_right g2).
  rewrite <- !(iso_from_to iso).
  rewrite !comp_assoc.
  rewrites; reflexivity.
Qed.

(* Partial converses to "isos are monic and epic": a morphism that is both
   monic and a retraction (split epi) is an isomorphism, and dually a morphism
   that is both epic and a section (split mono) is an isomorphism. In each case
   the one-sided inverse supplied by the split, together with cancellability,
   upgrades to a two-sided inverse. *)
#[export]
Program Instance Monic_Retraction_Iso
        {C : Category} {x y : C} `(r : @Retraction _ _ _ f) `(m : @Monic _ _ _ f) :
  x ≅ y := {
  to := f;
  from := retract
}.
Next Obligation.
  destruct r; simpl.
  apply monic.
  rewrite comp_assoc.
  rewrite <- retract_comp; cat.
Qed.
Next Obligation.
  destruct r; simpl.
  apply monic.
  rewrite comp_assoc.
  rewrite retract_comp; cat.
Qed.

#[export]
Program Instance Epic_Section_Iso
        {C : Category} {x y : C} `(s : @Section _ _ _ f) `(e : @Epic _ _ _ f) :
  x ≅ y := {
  to := f;
  from := section
}.
Next Obligation.
  destruct s; simpl.
  specialize (epic y (f ∘ section) id).
  intros.
  apply epic.
  rewrite <- comp_assoc.
  rewrite section_comp; cat.
Qed.
Next Obligation.
  destruct s; simpl.
  specialize (epic y (f ∘ section) id).
  intros.
  apply epic.
  rewrite <- comp_assoc.
  rewrite <- section_comp; cat.
Qed.

Notation "f ⊙ g" := (@iso_compose _ _ _ _ f g) (at level 40, left associativity).
