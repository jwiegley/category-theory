(** * Ab, the category of abelian groups

    Mac Lane treats [Ab] as the running example of a category that is
    "concrete" in the same way [Set] is but carries strictly more algebraic
    structure (Categories for the Working Mathematician, 2nd ed., §I.7,
    printed pp. 24-25 (PDF pp. 34-35), following issue #256's locations).  It
    is the base of homological algebra.  Be careful about the relationship to
    Structure/Abelian.v, in two steps that are easy to run together.  Hom-sets
    carrying abelian-group structure is [Additive] (Structure/Additive.v:38-40,
    "each hom-setoid UPGRADES from a commutative monoid to an abelian group"),
    NOT [Preadditive] -- Structure/Preadditive.v:20-21 is explicit that
    "additive inverses are deliberately not demanded, so the class is precisely
    enrichment in commutative monoids".  And [Class Abelian]
    (Structure/Abelian.v:137-152) is not that either: hom-group structure is
    one of its five fields, reached transitively through [abelian_additive],
    alongside kernels, cokernels and normality of monos and epis.  This file
    instantiates NONE of [Preadditive], [Additive] or [Abelian] (see SCOPE),
    so it claims to witness none of them.

    Cited by location only: the printed text was not consulted while writing
    this file.  The locations follow issue jwiegley/category-theory#256.

    WHAT IS BUILT ON.  An abelian group is a commutative monoid with additive
    inverses, so the objects EXTEND Instance/CMon.v's [CMonObject] by a
    negation rather than restating the carrier and the four monoid laws.  The
    coercion [ab_cmon :> CMonObject] makes [carrier], [cmon_zero],
    [cmon_plus], associativity, commutativity and the unit laws available
    unchanged.  The homomorphisms are literally [CMonHom]s: preservation of
    negation is a THEOREM ([ab_map_neg] below), not a field, which is the
    standard fact that a monoid map between groups is automatically a group
    map.

    WHY NOT [Instance/Comp.v].  That file does have group inverses concretely
    -- [inv] at :288, [inv_left]/[inv_right] at :322-323, the variety [Group]
    at :382, a [Bool] witness at :405 -- so it is NOT true that additive
    inverses are absent from the concrete layer, and this file does not claim
    that.  What is true, and what matters here, is narrower: [Instance/Comp.v]
    is a LEIBNIZ-EQUALITY development.  Its [AlgHom]'s [op_commute] uses [=]
    (:67-68), its hom-setoid is [∀ x, f x = g x] (:76), and it invokes
    [functional_extensionality] (:370, :375) and
    [functional_extensionality_dep] (:440).  [Ab] lives in the
    setoid-carrier layer with [≈] throughout and no axioms, so [CMon] is the
    donor and [Comp] cannot be.

    THE PROPOSITION.  Mac Lane's §I.7 proposition is that a homomorphism of
    abelian groups is monic exactly when it is injective and epic exactly when
    it is surjective.  Both halves are proved below, constructively.

    WHAT MAKES THE EPIC HALF GO THROUGH: COMMUTATIVITY, and nothing else.  For
    [ab_coset_eq] to be a CONGRUENCE -- for [B/fA] to be an [AbObject] rather
    than a bare setoid, and so usable as a probe object at all -- one must
    commute [f a] past another element.  That is the [cmon_plus_comm] step in
    [AbQuotient]'s [cmon_plus_respects] obligation below.  Where the image need
    not be normal, the corresponding quotient is not an object of the category
    and this probe is simply unavailable.  No constructivity consideration is
    involved.

    A NOTE ON THE COMPARISON WITH [Sets], and on how it changed.  When this
    file was first written, Instance/Sets.v's [surjectivity_is_epic] did not
    enter the environment: its proof was abandoned, because the argument then
    used needed a truth-value object whose carrier is [Type], which does not
    fit as an [obj[Sets]] at the same universe.  That is no longer so.
    Instance/Sets.v:509 now proves it outright, via a cokernel-pair setoid
    ([CKSetoid], [ck_left], [ck_right], [ck_agree]) -- which is to say, by
    exactly the kind of quotient probe used here.

    So there is NO contrast to draw, and none is claimed: [Sets] and [Ab] both
    have "epi iff surjective", and both get it by probing with a quotient.  The
    interest of the construction below is the one thing stated above -- that
    commutativity is what makes [B/fA] an object of the category at all -- not
    any comparative strength.

    WHERE THE NEGATION IS SPENT, stated precisely.  Among the three EQUIVALENCE
    laws of the coset relation, symmetry is the only one that consumes
    inverses: reflexivity needs just [g 0 = 0] and transitivity just
    [g (a + a')], while symmetry turns [x ≈ y + g a] into [y ≈ x + g (-a)]
    using that [g (-a)] inverts [g a].  Inverses are ALSO spent elsewhere in
    the construction -- [AbQuotient]'s [ab_neg_respects] and [ab_neg_left]
    obligations both need them -- so the claim is about the equivalence laws,
    not about the development as a whole. *)

(*  SCOPE.  Issue #256 also asks for [Ab] as a [Preadditive] instance and for a
    forgetful [Ab ⟶ Grp] alongside [Ab ⟶ Sets].  NEITHER is delivered here.
    [Structure/Preadditive.v] is available and the instance was not attempted;
    [Ab ⟶ Grp] has no target, since no category of groups exists in this tree
    (it is proposed by a separate, unmerged change).  Only [Ab_Forget : Ab ⟶
    Sets] is provided.  *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.

Generalizable All Variables.

(** ** Objects *)

(** An abelian group: a commutative monoid with a negation that is a
    left inverse.  The right inverse law follows by commutativity
    ([ab_neg_right] below), so it is not a field. *)
Record AbObject := {
  ab_cmon :> CMonObject;

  ab_neg : carrier (cmon_setoid ab_cmon) → carrier (cmon_setoid ab_cmon);
  ab_neg_respects : Proper (equiv ==> equiv) ab_neg;

  ab_neg_left : ∀ a, cmon_plus ab_cmon (ab_neg a) a ≈ cmon_zero ab_cmon
}.

#[export] Existing Instance ab_neg_respects.

Corollary ab_neg_right (A : AbObject) (a : carrier (cmon_setoid A)) :
  cmon_plus A a (ab_neg A a) ≈ cmon_zero A.
Proof.
  rewrite cmon_plus_comm.
  apply ab_neg_left.
Qed.

(** Cancellation, used repeatedly below.  This is the one property that
    genuinely separates a group from a monoid. *)
Lemma ab_cancel_l (A : AbObject) (a b c : carrier (cmon_setoid A)) :
  cmon_plus A a b ≈ cmon_plus A a c → b ≈ c.
Proof.
  intro H.
  rewrite <- (cmon_plus_zero_l A b), <- (cmon_plus_zero_l A c).
  rewrite <- (ab_neg_left A a).
  rewrite !cmon_plus_assoc.
  now rewrite H.
Qed.

(** Negation is determined: anything acting as a left inverse IS the
    negation.  Needed to show homomorphisms preserve it. *)
Lemma ab_neg_unique (A : AbObject) (a b : carrier (cmon_setoid A)) :
  cmon_plus A b a ≈ cmon_zero A → b ≈ ab_neg A a.
Proof.
  intro H.
  apply (ab_cancel_l A a).
  rewrite (cmon_plus_comm A a b), H.
  now symmetry; apply ab_neg_right.
Qed.

Lemma ab_neg_zero (A : AbObject) : ab_neg A (cmon_zero A) ≈ cmon_zero A.
Proof.
  symmetry; apply ab_neg_unique.
  apply cmon_plus_zero_l.
Qed.

(** Negation distributes over addition.  This needs commutativity, so it is an
    abelian-group fact rather than a group fact, and it is what makes the
    quotient below respect negation. *)
Lemma ab_neg_plus (A : AbObject) (a b : carrier (cmon_setoid A)) :
  ab_neg A (cmon_plus A a b)
    ≈ cmon_plus A (ab_neg A a) (ab_neg A b).
Proof.
  symmetry; apply ab_neg_unique.
  rewrite cmon_plus_assoc.
  rewrite <- (cmon_plus_assoc A (ab_neg A b) a b).
  rewrite (cmon_plus_comm A (ab_neg A b) a).
  rewrite (cmon_plus_assoc A a (ab_neg A b) b).
  rewrite ab_neg_left, cmon_plus_zero_r.
  apply ab_neg_left.
Qed.

(** ** Morphisms *)

(** A homomorphism of abelian groups is exactly a homomorphism of the
    underlying commutative monoids.  Preservation of negation is derived, not
    demanded -- the standard fact that a monoid map between groups is a group
    map. *)
Definition AbHom (A B : AbObject) := CMonHom A B.

Lemma ab_map_neg {A B : AbObject} (f : AbHom A B) (a : carrier (cmon_setoid A)) :
  cmon_map f (ab_neg A a) ≈ ab_neg B (cmon_map f a).
Proof.
  apply ab_neg_unique.
  rewrite <- cmon_map_plus.
  rewrite ab_neg_left.
  apply cmon_map_zero.
Qed.

(** ** The category *)

(** [Ab] is the full subcategory of [CMon] on the objects carrying a negation:
    same homs, same identities, same composition, same hom-setoid.  Stating it
    this way is what makes [ab_map_neg] a theorem rather than a coherence
    obligation. *)
Program Definition Ab : Category := {|
  obj     := AbObject;
  hom     := AbHom;
  homset  := fun A B => @CMonHom_Setoid A B;
  id      := fun A => @cmon_hom_id A;
  compose := fun A B C f g => @cmon_hom_compose A B C f g;

  (* [compose_respects] is inherited from [CMon] literally.  The remaining four
     laws are NOT: they are [Program] obligations, discharged afresh by the
     file-global [Obligation Tactic] (Lib/Tactics.v:225's [cat_simpl]).  What is
     true is that no new mathematical content is needed -- [Ab]'s homs,
     identities and composition ARE [CMon]'s -- not that nothing is reproved. *)
  compose_respects := fun A B C => @cmon_hom_compose_respects A B C
|}.

(** The forgetful functor to [Sets], through the underlying setoid. *)
Program Definition Ab_Forget : Ab ⟶ Sets := {|
  fobj := fun A => cmon_setoid (ab_cmon A);
  fmap := fun _ _ f => cmon_map f
|}.

(** ** The zero group as a zero object *)

(** The one-element abelian group.  Its negation is forced: there is only one
    element, so [ab_neg] is the constant map and the inverse law is
    [reflexivity]. *)
Definition Ab_trivial : AbObject.
Proof.
  unshelve notypeclasses refine {|
    ab_cmon := CMon_trivial;
    ab_neg  := fun _ => ttt
  |}.
  - intros x y Hxy; reflexivity.
  - intros a; reflexivity.
Defined.

(** Everything maps to the point, and only one map does. *)
Definition Ab_one (A : AbObject) : A ~{Ab}~> Ab_trivial := CMon_one A.

Lemma Ab_one_unique (A : AbObject) (f : A ~{Ab}~> Ab_trivial) :
  f ≈ Ab_one A.
Proof. intro a; destruct (cmon_map f a); reflexivity. Qed.

Program Definition Ab_Terminal : @Terminal Ab := {|
  terminal_obj := Ab_trivial;
  one          := Ab_one
|}.
Next Obligation. now rewrite (Ab_one_unique _ f), (Ab_one_unique _ g). Qed.

(** Dually: the unique map OUT of the point sends the point to zero.  This is
    where the group being trivial does the work -- there is nothing to choose. *)
Definition Ab_zero_hom (A : AbObject) : Ab_trivial ~{Ab}~> A :=
  CMon_zero_hom A.

Lemma Ab_zero_hom_unique (A : AbObject) (f : Ab_trivial ~{Ab}~> A) :
  f ≈ Ab_zero_hom A.
Proof.
  intro a; destruct a; simpl.
  now rewrite (cmon_map_zero f).
Qed.

Program Definition Ab_Initial : @Initial Ab := {|
  terminal_obj := Ab_trivial : obj[Ab^op];
  one          := Ab_zero_hom
|}.
Next Obligation.
  (* Routed through transitivity at the hom-setoid level rather than by
     [rewrite]: rewriting puts both sides under [cmon_map], where it leaves
     undetermined evars. *)
  etransitivity;
    [ apply Ab_zero_hom_unique | symmetry; apply Ab_zero_hom_unique ].
Qed.

(** The same object is both, so the coincidence iso is the identity -- exactly
    as at Instance/CMon/Biproduct.v:160. *)
#[export] Instance Ab_Zero : ZeroObject Ab :=
  @Build_ZeroObject Ab Ab_Terminal Ab_Initial iso_id.

(** ** Mac Lane's §I.7 proposition: monic = injective, epic = surjective *)

Definition AbInjective {A B : AbObject} (f : A ~{Ab}~> B) : Type :=
  ∀ x y : carrier (cmon_setoid A), cmon_map f x ≈ cmon_map f y → x ≈ y.

Definition AbSurjective {A B : AbObject} (f : A ~{Ab}~> B) : Type :=
  ∀ b : carrier (cmon_setoid B), { a & cmon_map f a ≈ b }.

(** *** The kernel, used as the probe object for the monic half *)

(** A probe object is genuinely needed: monic does not imply injective in an
    arbitrary category.  The kernel is the cheapest one available here --
    unlike the usual textbook probe it needs neither the free abelian group on
    one generator nor any scalar action, only a sub-setoid. *)

Section Kernel.

Context {A B : AbObject}.
Context (f : A ~{Ab}~> B).

Definition ab_ker_carrier : Type :=
  { a : carrier (cmon_setoid A) & cmon_map f a ≈ cmon_zero B }.

Program Definition ab_ker_setoid : Setoid ab_ker_carrier := {|
  equiv := fun p q => projT1 p ≈ projT1 q
|}.

Lemma ab_ker_zero_pf : cmon_map f (cmon_zero A) ≈ cmon_zero B.
Proof. apply cmon_map_zero. Qed.

Lemma ab_ker_plus_pf (p q : ab_ker_carrier) :
  cmon_map f (cmon_plus A (projT1 p) (projT1 q)) ≈ cmon_zero B.
Proof.
  rewrite cmon_map_plus, (projT2 p), (projT2 q).
  apply cmon_plus_zero_l.
Qed.

Lemma ab_ker_neg_pf (p : ab_ker_carrier) :
  cmon_map f (ab_neg A (projT1 p)) ≈ cmon_zero B.
Proof.
  rewrite ab_map_neg, (projT2 p).
  apply ab_neg_zero.
Qed.

Definition AbKernel : AbObject.
Proof using A B f.
  unshelve notypeclasses refine {|
    ab_cmon :=
      {| cmon_setoid := {| carrier := ab_ker_carrier ; is_setoid := ab_ker_setoid |}
       ; cmon_zero := existT _ (cmon_zero A) ab_ker_zero_pf
       ; cmon_plus := fun p q =>
           existT _ (cmon_plus A (projT1 p) (projT1 q)) (ab_ker_plus_pf p q) |};
    ab_neg := fun p => existT _ (ab_neg A (projT1 p)) (ab_ker_neg_pf p)
  |}.
  - (* cmon_plus_respects *)
    intros p p' Hp q q' Hq; simpl in *.
    now rewrite Hp, Hq.
  - (* cmon_plus_assoc *)
    intros a b c; simpl; apply cmon_plus_assoc.
  - (* cmon_plus_comm *)
    intros a b; simpl; apply cmon_plus_comm.
  - (* cmon_plus_zero_l *)
    intros a; simpl; apply cmon_plus_zero_l.
  - (* ab_neg_respects *)
    intros p q Hpq; simpl in *; now rewrite Hpq.
  - (* ab_neg_left *)
    intros a; simpl; apply ab_neg_left.
Defined.

(** The inclusion of the kernel, and the zero map alongside it.  [f] equalizes
    them, which is the whole point. *)
Program Definition ab_kernel_incl : AbKernel ~{Ab}~> A :=
  {| cmon_map := {| morphism := fun p : ab_ker_carrier => projT1 p |} |}.

Program Definition ab_kernel_zero : AbKernel ~{Ab}~> A :=
  {| cmon_map := {| morphism := fun _ : ab_ker_carrier => cmon_zero A |} |}.
Next Obligation. symmetry; apply cmon_plus_zero_l. Qed.

End Kernel.

Arguments AbKernel {A B} f.
Arguments ab_kernel_incl {A B} f.
Arguments ab_kernel_zero {A B} f.

(** *** Monic *)

(** Monic implies injective, by probing with the kernel: [f] equalizes the
    inclusion and the zero map, so monic collapses them, so every kernel
    element is zero -- and then [f x ≈ f y] puts [x - y] in the kernel.

    NOTE what this does and does not show.  [x - y] is where THIS proof spends
    the group structure, but the THEOREM does not need it: monic implies
    injective already in [CMon], probing with the free commutative monoid on
    one generator ([nat]) instead of a kernel.  So the kernel is a convenient
    probe here, not a necessary one, and the monic half is NOT a place where
    [Ab] does something [CMon] cannot. *)
Lemma ab_monic_injective {A B : AbObject} (f : A ~{Ab}~> B) :
  Monic f → AbInjective f.
Proof.
  intros Hm x y Hxy.
  (* Step 1: monic collapses the two maps out of the kernel. *)
  assert (Hk : ∀ p : carrier (cmon_setoid (AbKernel f)),
                 projT1 p ≈ cmon_zero A).
  { apply (@monic _ _ _ f Hm (AbKernel f)
             (ab_kernel_incl f) (ab_kernel_zero f)).
    intro p; simpl.
    rewrite (projT2 p).
    symmetry; apply cmon_map_zero. }
  (* Step 2: x - y lies in the kernel. *)
  assert (Hd : cmon_map f (cmon_plus A x (ab_neg A y)) ≈ cmon_zero B).
  { rewrite cmon_map_plus, ab_map_neg, Hxy.
    apply ab_neg_right. }
  (* Step 3: so x - y is zero, hence x ≈ y. *)
  pose proof (Hk (existT _ (cmon_plus A x (ab_neg A y)) Hd)) as Hz.
  simpl in Hz.
  apply (ab_cancel_l A (ab_neg A y)).
  rewrite (cmon_plus_comm A (ab_neg A y) x) in *.
  rewrite Hz.
  now rewrite (cmon_plus_comm A (ab_neg A y) y), ab_neg_right.
Qed.

Lemma ab_injective_monic {A B : AbObject} (f : A ~{Ab}~> B) :
  AbInjective f → Monic f.
Proof.
  intros Hi.
  constructor; intros Z g h Hgh z.
  apply Hi.
  exact (Hgh z).
Qed.

Theorem ab_monic_iff_injective {A B : AbObject} (f : A ~{Ab}~> B) :
  Monic f ↔ AbInjective f.
Proof.
  split; [ apply ab_monic_injective | apply ab_injective_monic ].
Qed.

(** *** The quotient B/fA, used as the probe object for the epic half *)

(** Mac Lane's construction.  The carrier is [B] itself; only the equality
    coarsens, to "differ by something in the image of [f]".  Note the relation
    is TYPE-valued -- [{ a & ... }], not [∃] -- which is what lets the witness
    be read back out at the end without any choice principle. *)

Section Quotient.

Context {A B : AbObject}.
Context (f : A ~{Ab}~> B).

Definition ab_coset_eq (x y : carrier (cmon_setoid B)) : Type :=
  { a : carrier (cmon_setoid A) & x ≈ cmon_plus B y (cmon_map f a) }.

Lemma ab_coset_refl (x : carrier (cmon_setoid B)) : ab_coset_eq x x.
Proof.
  exists (cmon_zero A).
  rewrite cmon_map_zero.
  symmetry; apply cmon_plus_zero_r.
Qed.

(** SYMMETRY IS WHERE THE INVERSES ARE SPENT.  From [x ≈ y + f a] one recovers
    [y ≈ x + f (-a)] only because [f (-a)] inverts [f a].  This single step is
    the formal reason the construction works in [Ab] and has no analogue one
    level down in [CMon]. *)
Lemma ab_coset_sym (x y : carrier (cmon_setoid B)) :
  ab_coset_eq x y → ab_coset_eq y x.
Proof.
  intros [a Ha].
  exists (ab_neg A a).
  rewrite ab_map_neg, Ha.
  rewrite cmon_plus_assoc.
  rewrite ab_neg_right.
  symmetry; apply cmon_plus_zero_r.
Qed.

Lemma ab_coset_trans (x y z : carrier (cmon_setoid B)) :
  ab_coset_eq x y → ab_coset_eq y z → ab_coset_eq x z.
Proof.
  intros [a Ha] [b Hb].
  exists (cmon_plus A b a).
  rewrite cmon_map_plus.
  rewrite Ha, Hb.
  now rewrite cmon_plus_assoc.
Qed.

Program Definition ab_coset_setoid : Setoid (carrier (cmon_setoid B)) := {|
  equiv := ab_coset_eq
|}.
Next Obligation.
  constructor.
  - exact ab_coset_refl.
  - exact ab_coset_sym.
  - exact ab_coset_trans.
Qed.

Definition AbQuotient : AbObject.
Proof using A B f.
  unshelve notypeclasses refine {|
    ab_cmon :=
      {| cmon_setoid := {| carrier := carrier (cmon_setoid B)
                         ; is_setoid := ab_coset_setoid |}
       ; cmon_zero := cmon_zero B
       ; cmon_plus := cmon_plus B |};
    ab_neg := ab_neg B
  |}.
  - (* cmon_plus_respects *)
    intros x x' [a Ha] y y' [b Hb].
    exists (cmon_plus A a b).
    rewrite cmon_map_plus, Ha, Hb.
    (* (x' + f a) + (y' + f b) ≈ (x' + y') + (f a + f b) *)
    rewrite !cmon_plus_assoc.
    apply cmon_plus_respects; [ reflexivity | ].
    rewrite <- !cmon_plus_assoc.
    apply cmon_plus_respects; [ | reflexivity ].
    apply cmon_plus_comm.
  - (* cmon_plus_assoc *)
    intros x y z; exists (cmon_zero A).
    rewrite cmon_map_zero, cmon_plus_zero_r.
    apply cmon_plus_assoc.
  - (* cmon_plus_comm *)
    intros x y; exists (cmon_zero A).
    rewrite cmon_map_zero, cmon_plus_zero_r.
    apply cmon_plus_comm.
  - (* cmon_plus_zero_l *)
    intros x; exists (cmon_zero A).
    rewrite cmon_map_zero, cmon_plus_zero_r.
    apply cmon_plus_zero_l.
  - (* ab_neg_respects *)
    intros x y [a Ha].
    exists (ab_neg A a).
    rewrite ab_map_neg.
    change (ab_neg B x ≈ cmon_plus B (ab_neg B y) (ab_neg B (cmon_map f a))).
    rewrite <- ab_neg_plus.
    now rewrite Ha.
  - (* ab_neg_left *)
    intros x; exists (cmon_zero A).
    rewrite cmon_map_zero, cmon_plus_zero_r.
    apply ab_neg_left.
Defined.

(** The projection (identity on carriers, coarser equality) and the zero map.
    [f] equalizes them -- which is exactly the statement that [f a] is
    congruent to zero modulo the image. *)
Program Definition ab_quot_proj : B ~{Ab}~> AbQuotient :=
  {| cmon_map := {| morphism := fun b : carrier (cmon_setoid B) => b |} |}.
Next Obligation. intros x y Hxy; exists (cmon_zero A);
  rewrite cmon_map_zero, cmon_plus_zero_r; exact Hxy. Qed.
Next Obligation. apply ab_coset_refl. Qed.
Next Obligation. apply ab_coset_refl. Qed.

Program Definition ab_quot_zero : B ~{Ab}~> AbQuotient :=
  {| cmon_map :=
       {| morphism := fun _ : carrier (cmon_setoid B) => cmon_zero B |} |}.
Next Obligation. intros x y Hxy; apply ab_coset_refl. Qed.
Next Obligation. apply ab_coset_refl. Qed.
Next Obligation.
  exists (cmon_zero A).
  rewrite cmon_map_zero, cmon_plus_zero_r.
  symmetry; apply cmon_plus_zero_l.
Qed.

End Quotient.

Arguments AbQuotient {A B} f.
Arguments ab_quot_proj {A B} f.
Arguments ab_quot_zero {A B} f.

(** *** Epic *)

(** Epic implies surjective, CONSTRUCTIVELY and with no double-negation.

    [f] equalizes the projection and the zero map into [B/fA], so an epi
    collapses them -- and [ab_quot_proj ≈ ab_quot_zero] says precisely that
    every [b] is congruent to zero modulo the image, whose witness IS the
    preimage -- read straight back out, with nothing chosen and nothing doubly
    negated. *)
Lemma ab_epic_surjective {A B : AbObject} (f : A ~{Ab}~> B) :
  Epic f → AbSurjective f.
Proof.
  intros He b.
  assert (Hpq : ab_quot_proj f ≈ ab_quot_zero f).
  { apply (@epic _ _ _ f He (AbQuotient f)
             (ab_quot_proj f) (ab_quot_zero f)).
    intro a; simpl.
    exists a.
    rewrite cmon_plus_zero_l.
    reflexivity. }
  specialize (Hpq b); simpl in Hpq.
  destruct Hpq as [a Ha].
  exists a.
  rewrite cmon_plus_zero_l in Ha.
  now symmetry.
Qed.

Lemma ab_surjective_epic {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSurjective f → Epic f.
Proof.
  intros Hs.
  constructor; intros Z g h Hgh b.
  destruct (Hs b) as [a Ha].
  rewrite <- Ha.
  exact (Hgh a).
Qed.

(** Mac Lane §I.7's proposition, second half. *)
Theorem ab_epic_iff_surjective {A B : AbObject} (f : A ~{Ab}~> B) :
  Epic f ↔ AbSurjective f.
Proof.
  split; [ apply ab_epic_surjective | apply ab_surjective_epic ].
Qed.
