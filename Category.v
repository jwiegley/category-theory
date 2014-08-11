(* Copyright (c) 2014, John Wiegley
 *
 * This work is licensed under a
 * Creative Commons Attribution-Noncommercial-No Derivative Works 3.0
 * Unported License.
 * The license text is available at:
 *   http://creativecommons.org/licenses/by-nc-nd/3.0/
 *)

(** %\chapter{Hask.Category}% *)

Require Export Hask.Utils.

Set Universe Polymorphism.
Generalizable All Variables.

(** * Category *)

(** Category theory is a language for reasoning about abstractions.
Awodey%\cite{Awodey}% calls it, "the algebra of abstract functions."  Its
power lies in relating ideas from differing disciplines, and unifying them
under a common framework.

At its heart we have the [Category].  Every category is characterized by
its objects, and the morphisms (also called arrows) between those
objects. *)

(* begin hide *)
Reserved Notation "a ~> b" (at level 90, right associativity).
Reserved Notation "f ∘ g" (at level 45).
Reserved Notation "C ^op" (at level 90).
(* end hide *)

Class Category := {
    ob   : Type;
    uhom := Type : Type;
    hom  : ob → ob → uhom where "a ~> b" := (hom a b);
(**

It is important to note that objects and arrows have no inherent meaning: The
notion of a category requires only that they exist, and that they be
well-behaved.  Since all we can know about objects is that they exist, they
serve only to differentiate morphisms.  Conversely, morphisms are how we
characterize objects. *)

(** * Morphisms

In this formalization, as in many textbooks, morphisms are called [hom], for
"homomorphism" (algebraic structure-preserving maps).  Each morphism
represents the set of all morphism having that type, so they are also called
"hom-sets".

Since categories may have other categories as objects, we require that the
type of [hom] be larger than the type of its arguments.  This is the purpose
of the [uhom] type, allowing us to make use of Coq's support for universe
polymorphism.

*)

    id : ∀ {A}, A ~> A;
    compose : ∀ {A B C}, (B ~> C) → (A ~> B) → (A ~> C) where "f ∘ g" := (compose f g);
(**

If [ob] and [hom] are the nouns of category theory, [id] and [compose] are its
fundamental verbs.  Using only these notions we can reason about concepts such
as _idempotency_, _involution_, _section_ and _retraction_, _equalizers_ and
_co-equalizers_, and more.  Before we may do so, however, we must constrain
identity and composition under three laws:

*)

    right_identity : ∀ A B (f : A ~> B), f ∘ id = f;
    left_identity : ∀ A B (f : A ~> B), id ∘ f = f;
    comp_assoc : ∀ A B C D (f : C ~> D) (g : B ~> C) (h : A ~> B),
        f ∘ (g ∘ h) = (f ∘ g) ∘ h
}.

(**

Note the difference between the arrow used for function types in Coq, such as
[A → B], and for morphisms in a category [A ~> B].  If the category must be
indicated, it is stated in the arrow: [A ~{C}~> B]. *)

(* begin hide *)
(* Using a [Category] in a context requiring a [Type] will do what is expected
   using this coercion. *)
Coercion ob : Category >-> Sortclass.
(* Coercion hom : Category >-> Funclass. *)

Infix "~>" := hom : category_scope.
Infix "~{ C }~>" := (@hom C) (at level 100) : category_scope.
Infix "∘" := compose : category_scope.

Notation "ob/ C" := (@ob C) (at level 44) : category_scope.
Notation "id/ X" := (@id _ X) (at level 44) : category_scope.

Open Scope category_scope.

Hint Resolve left_identity.
Hint Resolve right_identity.
Hint Resolve comp_assoc.

Lemma cat_irrelevance `(C : Category) `(D : Category)
  : ∀ (m n : ∀ {A}, A ~> A)
      (p q : ∀ {A B C}, (B ~> C) → (A ~> B) → (A ~> C))
      l l' r r' c c',
  @m = @n →
  @p = @q →
  {| ob             := C
   ; hom            := @hom C
   ; id             := @m
   ; compose        := @p
   ; left_identity  := l
   ; right_identity := r
   ; comp_assoc     := c
 |} =
  {| ob             := C
   ; hom            := @hom C
   ; id             := @n
   ; compose        := @q
   ; left_identity  := l'
   ; right_identity := r'
   ; comp_assoc     := c'
 |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.

(* end hide *)

(**

We may now extend our discourse about functions, using only the few terms
we've defined so far:

*)

(* begin hide *)
Section Morphisms.
Context `{C : Category}.
(* end hide *)

Definition Idempotent `(f : X ~> X) := f ∘ f = f.
Definition Involutive `(f : X ~> X) := f ∘ f = id.

(**

We can also define relationships between two functions:

*)

Definition Section' `(f : X ~> Y) := { g : Y ~> X & g ∘ f = id }.
Definition Retraction `(f : X ~> Y) := { g : Y ~> X & f ∘ g = id }.

Class SplitIdempotent {X Y : C} := {
    split_idem_retract := Y;
    split_idem         : X ~> X;
    split_idem_r       : X ~> split_idem_retract;
    split_idem_s       : split_idem_retract ~> X;
    split_idem_law_1   : split_idem_s ∘ split_idem_r = split_idem;
    split_idem_law_2   : split_idem_r ∘ split_idem_s = id/Y
}.

(**

A Σ-type (sigma type) is used to convey [Section'] and [Retraction] to make
the witness available to proofs.  The definition could be expressed with an
existential quantifier (∃), but it would not convey which [g] was chosen.

*)

Definition Epic `(f : X ~> Y)  := ∀ {Z} (g1 g2 : Y ~> Z), g1 ∘ f = g2 ∘ f → g1 = g2.
Definition Monic `(f : X ~> Y) := ∀ {Z} (g1 g2 : Z ~> X), f ∘ g1 = f ∘ g2 → g1 = g2.

Definition Bimorphic `(f : X ~> Y) := Epic f ∧ Monic f.
Definition SplitEpi `(f : X ~> Y)  := Retraction f.
Definition SplitMono `(f : X ~> Y) := Section' f.

(**

The only morphism we've seen so far is [id], but we can trivially prove it is
both _idempotent_ and _involutive_. *)

(* begin hide *)
Hint Unfold Idempotent.
Hint Unfold Involutive.
Hint Unfold Section'.
Hint Unfold Retraction.
Hint Unfold Epic.
Hint Unfold Monic.
Hint Unfold Bimorphic.
Hint Unfold SplitEpi.
Hint Unfold SplitMono.
(* end hide *)

Lemma id_idempotent : ∀ X, Idempotent (id (A := X)).
Proof. auto. Qed.

Lemma id_involutive : ∀ X, Involutive (id (A := X)).
Proof. auto. Qed.

(**

We can also prove some relationships among these definitions. *)

(* begin hide *)
Section Lemmas.
Variables X Y : C.
Variable f : X ~> Y.
(* end hide *)

Lemma retractions_are_epic : Retraction f → Epic f.
Proof.
  autounfold.
  intros.
  destruct X0.
  rewrite <- right_identity.
  symmetry.
  rewrite <- right_identity.
  rewrite <- e.
  rewrite comp_assoc.
  rewrite comp_assoc.
  f_equal. auto.
Qed.

Lemma sections_are_monic : Section' f → Monic f.
Proof.
  autounfold.
  intros.
  destruct X0.
  rewrite <- left_identity.
  symmetry.
  rewrite <- left_identity.
  rewrite <- e.
  rewrite <- comp_assoc.
  rewrite <- comp_assoc.
  f_equal. auto.
Qed.

(* begin hide *)
End Lemmas.
End Morphisms.
(* end hide *)

(** * Isomorphism

An isomorphism is a pair of mappings that establish an equivalence between
objects.  Using the language above, it is a pair of functions which are both
sections and retractions of one another.  That is, they compose to identity in
both directions:

*)

Class Isomorphism `{C : Category} (X Y : C) := {
  to : X ~> Y;
  from : Y ~> X;
  iso_to : to ∘ from = id/Y;
  iso_from : from ∘ to = id/X
}.

(* begin hide *)
Lemma iso_irrelevance `(C : Category) {X Y : C}
  : ∀ (f g : X ~> Y) (k h : Y ~> X) tl tl' fl fl',
  @f = @g →
  @k = @h →
  {| to       := f
   ; from     := k
   ; iso_to   := tl
   ; iso_from := fl
  |} =
  {| to       := g
   ; from     := h
   ; iso_to   := tl'
   ; iso_from := fl'
  |}.
Proof.
  intros. subst. f_equal.
  apply proof_irrelevance.
  apply proof_irrelevance.
Qed.
(* end hide *)

(**

Typically isomorphisms are characterized by this pair of functions, but they
can also be expressed as an equivalence between objects using the notation [A
≅ B].  A double-tilde is used to express the same notion of equivalence
between value terms [a ≈ b].

*)

Notation "X ≅ Y" := (Isomorphism X Y) (at level 50) : category_scope.
Notation "x ≈ y" := (to x = y ∧ from y = x) (at level 50).

Definition eq_iso (C : Category) (X Y : C) : Prop := X ≅ Y.

(**

[id] witnesses the isomorphism between any object and itself.  Isomorphisms
are likewise symmetric and transitivity, making them parametric relations.
This will allows us to use them in proof rewriting as though they were
equalities.

*)

Program Instance iso_identity `{Category} : X ≅ X := {
    to := id; from := id
}.

Program Instance iso_symmetry `{C : Category} `(iso : X ≅ Y) : Y ≅ X := {
    from := @to C X Y iso;
    to := @from C X Y iso
}.
(* begin hide *)
Obligation 1. apply iso_from. Qed.
Obligation 2. apply iso_to. Qed.
(* end hide *)

Program Instance iso_compose `{C : Category} {X Y Z : C}
    (iso_a : Y ≅ Z) (iso_b : X ≅ Y) : X ≅ Z := {
    from := (@from C X Y iso_b) ∘ (@from C Y Z iso_a);
    to := (@to C Y Z iso_a) ∘ (@to C X Y iso_b)
}.
(* begin hide *)
Obligation 1.
  destruct iso_a.
  destruct iso_b.
  simpl.
  rewrite <- comp_assoc.
  rewrite (comp_assoc _ _ _ _ to1).
  rewrite iso_to1.
  rewrite left_identity.
  assumption.
Qed.
Obligation 2.
  destruct iso_a.
  destruct iso_b.
  simpl.
  rewrite <- comp_assoc.
  rewrite (comp_assoc _ _ _ _ from0).
  rewrite iso_from0.
  rewrite left_identity.
  assumption.
Qed.
(* end hide *)

Program Instance Iso_Proper `{C : Category} {X Y Z : C}
  : Proper (@eq_iso C ==> @eq_iso C ==> Basics.impl) Isomorphism.
Obligation 1.
  unfold eq_iso, respectful.
  intros.
  unfold Basics.impl.
  intros.
  destruct H.
  destruct H0.
  destruct H1.
  apply Build_Isomorphism
    with (to := to1 ∘ to2 ∘ from0)
         (from := to0 ∘ from2 ∘ from1).
    repeat (rewrite <- comp_assoc).
    rewrite (comp_assoc _ _ _ _ from0).
    rewrite iso_from0.
    rewrite left_identity.
    rewrite (comp_assoc _ _ _ _ to2).
    rewrite iso_to2.
    rewrite left_identity.
    auto.
  repeat (rewrite <- comp_assoc).
  rewrite (comp_assoc _ _ _ _ from1).
  rewrite iso_from1.
  rewrite left_identity.
  rewrite (comp_assoc _ _ _ _ from2).
  rewrite iso_from2.
  rewrite left_identity.
  auto.
Qed.

Add Parametric Relation `{C : Category} {A B : C} : (@ob C) (@eq_iso C)
  reflexivity proved by (@iso_identity C)
  symmetry proved by (@iso_symmetry C)
  transitivity proved by (fun X Y Z => Basics.flip (@iso_compose C X Y Z))
  as Isomorphic_relation.

(**

A [Groupoid] is a [Category] where every morphism has an inverse, and is
therefore an isomorphism.

*)

Program Instance Groupoid `(C : Category) : Category := {
    ob      := @ob C;
    hom     := @Isomorphism C;
    id      := @iso_identity C;
    compose := @iso_compose C
}.
(* begin hide *)
Obligation 1.
  unfold iso_compose, iso_identity.
  destruct f.
  apply iso_irrelevance; crush.
Qed.
Obligation 2.
  unfold iso_compose, iso_identity.
  destruct f.
  apply iso_irrelevance; crush.
Qed.
Obligation 3.
  unfold iso_compose.
  destruct f.
  destruct g.
  destruct h. simpl.
  apply iso_irrelevance; crush.
Qed.
(* end hide *)

(**

A function which is both a retraction and monic, or a section and epic,
expresses an isomorphism with its respective witness.

*)

Program Instance Monic_Retraction_Iso
    `{C : Category} {X Y : C} `(r : Retraction f) `(m : Monic f) : X ≅ Y := {
    to := f;
    from := projT1 r
}.
(* begin hide *)
Obligation 1.
  autounfold in *.
  destruct r.
  auto.
Qed.
Obligation 2.
  autounfold in *.
  destruct r.
  simpl.
  specialize (m X (x ∘ f) id).
  apply m.
  rewrite comp_assoc.
  rewrite e.
  auto.
  rewrite left_identity.
  rewrite right_identity.
  reflexivity.
Qed.
(* end hide *)

Program Instance Epic_Section_Iso
    `{C : Category} {X Y} `(s : Section' f) `(e : Epic f) : X ≅ Y := {
    to := f;
    from := projT1 s
}.
(* begin hide *)
Obligation 1.
  autounfold in *.
  destruct s.
  simpl.
  specialize (e Y (f ∘ x) id).
  apply e.
  rewrite <- comp_assoc.
  rewrite e0.
  rewrite left_identity.
  rewrite right_identity.
  reflexivity.
Qed.
Obligation 2.
  autounfold in *.
  destruct s.
  specialize (e Y (f ∘ x) id).
  auto.
Qed.

Hint Unfold Idempotent.
Hint Unfold Involutive.
Hint Unfold Section'.
Hint Unfold Retraction.
Hint Unfold Epic.
Hint Unfold Monic.
Hint Unfold Bimorphic.
Hint Unfold SplitEpi.
Hint Unfold SplitMono.
(* end hide *)

(**

A section may be flipped using its witness to provide a retraction, and
vice-versa.

*)

Definition flip_section `{Category} `(f : X ~> Y)
  (s : @Section' _ X Y f) : @Retraction _ Y X (projT1 s).
Proof.
  autounfold.
  destruct s.
  exists f.
  crush.
Qed.

Definition flip_retraction `{Category} `(f : X ~> Y)
  (s : @Retraction _ X Y f) : @Section' _ Y X (projT1 s).
Proof.
  autounfold.
  destruct s.
  exists f.
  crush.
Qed.

(** * Sets

[Sets] is our first real category: the category of Coq types and functions.
The objects of this category are all the Coq types (including [Set], [Prop]
and [Type]), and its morphisms are functions from [Type] to [Type].  [id]
simply returns whatever object is passed, and [compose] is regular composition
between functions.  Proving it is a category in Coq is automatic.

Note that in many textbooks this category (or one similar to it) is called
just [Set], but since that name conflicts with types of the same name in Coq,
the plural is used instead.

*)

Program Instance Sets : Category := {
    ob      := Type;
    hom     := fun X Y => X → Y;
    id      := fun _ x => x;
    compose := fun _ _ _ f g x => f (g x)
}.

(**

Within the category of [Sets] we can prove that monic functions are injective,
and epic functions are surjective.  This is not necessarily true in other
categories.

*)

Lemma injectivity_is_monic `(f : X ~> Y) : (∀ x y, f x = f y → x = y) ↔ Monic f.
Proof. split.
- intros.
  unfold Monic.
  intros.
  extensionality e.
  apply H.
  simpl in H0.
  apply (equal_f H0).
- intros.
  unfold Monic in H.
  pose (fun (_ : unit) => x) as const_x.
  pose (fun (_ : unit) => y) as const_y.
  specialize (H unit const_x const_y).
  unfold const_x in H.
  unfold const_y in H.
  simpl in H.
  apply equal_f in H.
  + assumption.
  + extensionality e. assumption.
  + constructor.
Qed.

Lemma surjectivity_is_epic `(f : X ~> Y) : (∀ y, ∃ x, f x = y) ↔ Epic f.
Proof. split.
- intros.
  unfold Epic.
  intros.
  simpl in H0.
  extensionality e.
  specialize (H e).
  destruct H.
  rewrite <- H.
  apply (equal_f H0).
- intros.
  unfold Epic in H.
  specialize H with (Z := Prop).
  specialize H with (g1 := fun y0 => ∃ x0, f x0 = y0).
  simpl in *.
  specialize H with (g2 := fun y  => True).
  eapply equal_f in H.
  erewrite H. constructor.
  extensionality e.
  apply propositional_extensionality.
  exists e.
  reflexivity.
Qed.

(** ** Graphs

Another trivial category is that of a simple graph, whose objects are elements
of some [Set] [S], and where edges exist whenever a symmetric, reflexive
relation holds between elements.

*)

Program Instance A_Graph (S : Set) : Category := {
    ob      := S;
    hom     := fun _ _   => bool;
    id      := fun _     => true;
    compose := fun x y z => andb
}.
(* begin hide *)
Obligation 1. destruct f; auto. Qed.
Obligation 3. destruct f; auto. Qed.
(* end hide *)

(** * Dual Category

The opposite, or categorical dual, of a category is expressed [C^op].  It has
the same objects as its parent, but the direction of all morphisms is flipped.
Further, doing this twice should result in the same category, making it an
involutive operation.

*)

Program Instance Opposite `(C : Category) : Category := {
    ob      := @ob C;
    hom     := fun x y => @hom C y x;
    id      := @id C;
    compose := fun _ _ _ f g => g ∘ f
}.

(* begin hide *)
Notation "C ^op" := (Opposite C) (at level 90) : category_scope.
(* end hide *)

Lemma op_involutive (C : Category) : (C^op)^op = C.
Proof.
  unfold Opposite.
  induction C.
  apply f_equal3.
  unfold Opposite_obligation_1.
  repeat (extensionality e; simpl; crush).
  unfold Opposite_obligation_2.
  repeat (extensionality e; simpl; crush).
  unfold Opposite_obligation_3.
  repeat (extensionality e; simpl; crush).
  extensionality f.
  extensionality g.
  extensionality h.
  extensionality i.
  extensionality j.
  extensionality k. crush.
Qed.

(**

Using the functions [op] and [unop], we can "flip" a particular morphism by
mapping to its corresponding morphism in the dual category.

*)

Definition op `{C : Category} : ∀ {X Y}, (X ~{C^op}~> Y) → (Y ~{C}~> X).
Proof. auto. Defined.

Definition unop `{C : Category} : ∀ {X Y}, (Y ~{C}~> X) → (X ~{C^op}~> Y).
Proof. auto. Defined.
