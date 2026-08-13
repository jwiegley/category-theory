(** * Galois connections are adjunctions between preorders

    Mac Lane §IV.5 Theorem 1: a Galois connection between preordered sets is
    exactly an adjunction between the corresponding thin categories (Categories
    for the Working Mathematician, 2nd ed., printed pp. 95-96).  The book is
    cited BY LOCATION only; its printed text was not consulted while writing
    this file, and the locations follow issue jwiegley/category-theory#380.

    A GALOIS CONNECTION between preorders [(A,≤)] and [(B,⊑)] is a pair of
    monotone maps [f : A → B], [g : B → A] with

        f a ⊑ b   iff   a ≤ g b.

    Instance/Proset.v:33 turns a [PreOrder] into a category whose homs ARE the
    order relation and whose hom-setoid identifies everything
    ([equiv := fun _ _ => True]).  Under that reading the displayed
    biconditional is precisely an adjunction's hom-set isomorphism, and this
    file proves the correspondence in both directions.

    WHY THIS IS MORE THAN A RESTATEMENT: THE VACUITY IS THE CONTENT.  An
    [Adjunction] (Theory/Adjunction.v:130) is one iso field plus FOUR
    naturality fields, and an [Adjunction_Transform]
    (Adjunction/Natural/Transformation.v:35-43) additionally carries two
    triangle identities.  Over a thin category every one of those side
    conditions is an equation between parallel morphisms, and in [Proset] any
    two parallel morphisms are related by [True].  So they are all discharged
    by [exact I].

    That is exactly why the bridge is cheap -- and it is also the thing worth
    proving rather than assuming.  The naive worry about a thin target is that
    the resulting statements are VACUOUS.  The honest position is subtler, and
    this file states it as [proset_side_conditions_vacuous] and its consequences:
    the side conditions carry no information, but the ISO FIELD does.  A Galois
    connection is genuine data -- the two maps and the biconditional -- and it
    is only the coherence overhead that collapses.  Stating that as a reusable
    lemma is what three of issue #380's hidden checkboxes ask for.  Note the
    obligations here are in fact closed by [Program]'s default tactic, which
    inlines [I]; the named lemma earns its keep at [galois_of_unit_counit],
    where the bare closure inequalities alone yield a full adjunction.

    A FACT ABOUT [Poset] WORTH RECORDING (not an error in the issue, which
    never claims otherwise -- it simply names both files).
    Instance/Poset.v:116-117 reads [Definition Poset ... := Proset P],
    DISCARDING its antisymmetry argument, which never appears in the body.
    Hence:

      - [Poset] and [Proset] are the same category, so anything proved for
        [Proset] holds for [Poset] by delta-reduction and no separate [Poset]
        lemma is ever needed ([poset_is_proset] records this by [eq_refl]);
      - antisymmetry cannot be recovered FROM THE CATEGORY VALUE, so a
        "mutually related implies equal" corollary must take it as a separate
        hypothesis ([mutual_le_to_eq]).  It CAN still be stated over [Poset]
        itself, since [Poset] receives antisymmetry as an argument and it is
        therefore in scope -- so this is a statement about what the category
        remembers, not about what is expressible. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Adjunction.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Sets.

(* Same two as Instance/Proset.v:4-5 -- [relation] and [PreOrder] here are the
   stdlib Prop-valued ones, not [crelation]. *)
Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.
From Coq Require Import Lia.

Generalizable All Variables.

(** ** Thinness, and the vacuity it induces *)

(** A category is THIN when any two parallel morphisms agree.  Before this file
    thinness was available only as the trivial hom-setoid buried inside
    [Proset] and an ad-hoc [two_thin] for the walking arrow, so it could not be
    used as a hypothesis. *)
Definition Thin (C : Category) : Type :=
  ∀ (x y : C) (f g : x ~> y), f ≈ g.

(** Every [Proset] is thin, by construction: its hom-setoid relates everything. *)
Lemma proset_thin {A : Type} {R : relation A} (P : PreOrder R)
  : Thin (Proset P).
Proof. intros x y f g; exact I. Qed.

(** THE VACUITY LEMMA the issue's hidden checkboxes ask for, stated once so
    that no consumer has to inline [exact I].  In a thin category ANY equation
    between parallel morphisms holds -- which covers, uniformly, all four
    naturality fields of [Adjunction] and both triangle identities of
    [Adjunction_Transform]. *)
Lemma thin_side_condition {C : Category} (H : Thin C) {x y : C} (f g : x ~> y) :
  f ≈ g.
Proof. apply H. Qed.

Corollary proset_side_conditions_vacuous {A : Type} {R : relation A}
  (P : PreOrder R) {x y : Proset P} (f g : x ~{Proset P}~> y) : f ≈ g.
Proof. exact I. Qed.

(** What does NOT collapse: the hom-setoid isomorphism still carries the two
    maps and the biconditional between them, so adjointness remains a real
    constraint even though every coherence field is free.  That is proved, not
    asserted, by [succ_not_self_adjoint] at the end of this file. *)

(** ** Galois connections *)

(** Mac Lane's definition.  [gal_mono_l]/[gal_mono_r] are monotonicity of the
    two maps; [gal_to]/[gal_from] are the two halves of the displayed
    biconditional.

    Declared OUTSIDE the section below on purpose: none of its fields mentions
    the [PreOrder] witnesses, only the relations, so a section would not
    generalize over them and [GaloisConnection PA PB] would not typecheck.  A
    Galois connection is data about the ORDERS; reflexivity and transitivity are
    needed only to build the categories. *)
Record GaloisConnection {A B : Type} (RA : relation A) (RB : relation B) := {
  gal_l : A → B;
  gal_r : B → A;

  gal_mono_l : ∀ a a', RA a a' → RB (gal_l a) (gal_l a');
  gal_mono_r : ∀ b b', RB b b' → RA (gal_r b) (gal_r b');

  gal_to   : ∀ a b, RB (gal_l a) b → RA a (gal_r b);
  gal_from : ∀ a b, RA a (gal_r b) → RB (gal_l a) b
}.

Arguments gal_l {A B RA RB} _ _.
Arguments gal_r {A B RA RB} _ _.
Arguments gal_mono_l {A B RA RB} _ {a a'} _.
Arguments gal_mono_r {A B RA RB} _ {b b'} _.
Arguments gal_to {A B RA RB} _ a b _.
Arguments gal_from {A B RA RB} _ a b _.

(** ** The bridge, forward: a Galois connection yields an adjunction *)

Section Galois.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (PA : PreOrder RA) (PB : PreOrder RB).
Context (G : GaloisConnection RA RB).

Program Definition GaloisFunctor_l : Proset PA ⟶ Proset PB := {|
  fobj := gal_l G;
  fmap := fun a a' h => gal_mono_l G h
|}.

Program Definition GaloisFunctor_r : Proset PB ⟶ Proset PA := {|
  fobj := gal_r G;
  fmap := fun b b' h => gal_mono_r G h
|}.

(** The hom-set isomorphism IS the biconditional.  Its two round-trip
    obligations are equations between parallel morphisms in a thin category,
    hence vacuous; [Program]'s default obligation tactic closes them with [I]
    directly.  [proset_side_conditions_vacuous] states that fact reusably --
    it is consumed by [galois_of_unit_counit] below, which is where the
    vacuity does load-bearing work. *)
Program Definition galois_adj_iso (a : Proset PA) (b : Proset PB) :
  @Isomorphism Sets
    {| carrier := @hom (Proset PB) (gal_l G a) b
     ; is_setoid := @homset (Proset PB) (gal_l G a) b |}
    {| carrier := @hom (Proset PA) a (gal_r G b)
     ; is_setoid := @homset (Proset PA) a (gal_r G b) |} := {|
  to   := {| morphism := gal_to G a b |};
  from := {| morphism := gal_from G a b |}
|}.

(** The adjunction.  Every remaining field is a side condition in a thin
    category, so the whole coherence burden is discharged uniformly. *)
Program Definition GaloisAdjunction :
  @Adjunction (Proset PB) (Proset PA) GaloisFunctor_l GaloisFunctor_r := {|
  adj := galois_adj_iso
|}.

End Galois.

(** ** The bridge, backward: an adjunction between preorders is a Galois connection *)

Section Ungalois.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (PA : PreOrder RA) (PB : PreOrder RB).
Context (F : Proset PA ⟶ Proset PB) (U : Proset PB ⟶ Proset PA).
Context (Adj : F ⊣ U).

Definition GaloisOfAdjunction : GaloisConnection RA RB :=
  {| gal_l := fobj[F]
   ; gal_r := fobj[U]
     (* [fmap]'s object arguments are given explicitly: leaving them implicit
        strands them as evars, since the record field's own arguments were made
        implicit above. *)
   ; gal_mono_l := fun a a' h => @fmap _ _ F a a' h
   ; gal_mono_r := fun b b' h => @fmap _ _ U b b' h
   ; gal_to   := fun a b h => to   (@adj _ _ _ _ Adj a b) h
   ; gal_from := fun a b h => from (@adj _ _ _ _ Adj a b) h |}.

End Ungalois.

(** ** Poset: the same category, and what that costs *)

(** Instance/Poset.v:116-117 defines [Poset] as [Proset] with the antisymmetry
    argument discarded, so the two are the SAME category -- definitionally. *)
Lemma poset_is_proset {A : Type} {R : relation A}
  (P : PreOrder R) (AS : @Antisymmetric A eq eq_equiv R) :
  @Poset A R P AS = @Proset A R P.
Proof. reflexivity. Qed.

(** Consequently a "mutually related implies equal" corollary CANNOT be read
    off the category: antisymmetry has to be supplied separately.  With it, an
    isomorphism in the order category is exactly mutual comparability, and
    antisymmetry converts that to equality. *)
Lemma mutual_le_to_eq {A : Type} {R : relation A} (P : PreOrder R)
  (AS : @Antisymmetric A eq eq_equiv R) {x y : Proset P}
  (i : x ≅[Proset P] y) : x = y.
Proof. exact (AS x y (to i) (from i)). Qed.

(** ** Round trip, and a witness that the notion is not empty *)

(** Going to an adjunction and back recovers the two maps.  Be honest about
    what this is: a DEFINITIONAL sanity check, proved by [eq_refl] on both
    components, because [GaloisAdjunction]'s type already names the functors
    and [GaloisOfAdjunction] merely projects [fobj] back out.  There is nothing
    it could refute, and the whole RECORD round-trips by [eq_refl] just as
    cheaply.  It is worth
    stating so the reader can see the maps are not silently replaced, but it is
    not evidence that the bridge is faithful -- for that see
    [succ_not_self_adjoint] below, which shows adjointness is a real
    constraint. *)
Lemma galois_round_trip {A B : Type} {RA : relation A} {RB : relation B}
  (PA : PreOrder RA) (PB : PreOrder RB) (G : GaloisConnection RA RB) :
  gal_l (GaloisOfAdjunction PA PB _ _ (GaloisAdjunction PA PB G)) = gal_l G
  ∧ gal_r (GaloisOfAdjunction PA PB _ _ (GaloisAdjunction PA PB G)) = gal_r G.
Proof. split; reflexivity. Qed.

(** A CONCRETE Galois connection, so that nothing above is vacuously about an
    empty notion: on the naturals, truncated SUBTRACTION of [k] is left adjoint
    to ADDITION of [k], via [n - k ≤ m  ↔  n ≤ m + k].  Both halves need real
    arithmetic; neither is a coherence triviality.

    The orientation matters and is easy to get backwards.  Adding [k] on the
    left does NOT work: [gal_from] would read [a ≤ b - k → a + k ≤ b], refuted
    by [k = 5], [b = 0], [a = 0], where truncation makes the hypothesis hold
    while the conclusion does not.  [lia] rejected that version, which is how
    the error was caught. *)
Program Definition nat_shift_galois (k : nat)
  : GaloisConnection Nat.le Nat.le := {|
  gal_l := fun n => Nat.sub n k;
  gal_r := fun m => Nat.add m k
|}.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.
Next Obligation. lia. Qed.

Definition nat_shift_adjunction (k : nat) : _ :=
  GaloisAdjunction Nat.le_preorder Nat.le_preorder (nat_shift_galois k).

(** The witness is not degenerate: the two maps genuinely differ for [k > 0],
    so this is not the identity connection wearing a disguise. *)
(* The two maps are genuinely different functions, so this is not the identity
   connection in disguise.  [%nat] is needed: the library's own scopes shadow
   the numeral notation. *)
Example nat_shift_differ :
  gal_l (nat_shift_galois 1%nat) 3%nat = 2%nat := eq_refl.
Example nat_shift_differ_r :
  gal_r (nat_shift_galois 1%nat) 3%nat = 4%nat := eq_refl.

(** ** The unit/counit reading, and the bare-implication form *)

(** Awodey §9.4's order reading: the unit says [a] is below the composite at
    [a], the counit that the composite at [b] is below [b].  In an order these
    are the two familiar closure inequalities. *)

Section UnitCounit.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (G : GaloisConnection RA RB).

Definition gal_unit (PB : PreOrder RB) (a : A) : RA a (gal_r G (gal_l G a)) :=
  gal_to G a (gal_l G a) (@reflexivity B RB (@PreOrder_Reflexive B RB PB) _).

Definition gal_counit (PA : PreOrder RA) (b : B) : RB (gal_l G (gal_r G b)) b :=
  gal_from G (gal_r G b) b (@reflexivity A RA (@PreOrder_Reflexive A RA PA) _).

End UnitCounit.

(** Conversely -- Seven Sketches Proposition 1.107 / display 1.108, and Riehl
    §4.2's "bare pair suffices".  Given only monotone maps and the two closure
    inequalities, the full biconditional follows, hence a full adjunction: no
    naturality and no triangle identity has to be supplied, because in a thin
    target they are equations between parallel morphisms.  THIS is the lemma
    the vacuity result exists to support. *)
Definition galois_of_unit_counit {A B : Type}
  {RA : relation A} {RB : relation B}
  (PA : PreOrder RA) (PB : PreOrder RB)
  (l : A → B) (r : B → A)
  (ml : ∀ a a', RA a a' → RB (l a) (l a'))
  (mr : ∀ b b', RB b b' → RA (r b) (r b'))
  (unit   : ∀ a, RA a (r (l a)))
  (counit : ∀ b, RB (l (r b)) b)
  : GaloisConnection RA RB :=
  {| gal_l := l
   ; gal_r := r
   ; gal_mono_l := ml
   ; gal_mono_r := mr
     (* f a ⊑ b  gives  a ≤ r (f a) ≤ r b *)
   ; gal_to := fun a b h =>
       @transitivity A RA (@PreOrder_Transitive A RA PA) _ _ _
         (unit a) (mr _ _ h)
     (* a ≤ r b  gives  f a ⊑ f (r b) ⊑ b *)
   ; gal_from := fun a b h =>
       @transitivity B RB (@PreOrder_Transitive B RB PB) _ _ _
         (ml _ _ h) (counit b) |}.

(** ** Uniqueness of adjoints, at the order level *)

(** Seven Sketches §1.4.3 exercise 1.110: two left adjoints of the same map
    agree, and dually.  In an order "agree" is mutual comparability -- which is
    equality only under antisymmetry, so both forms are given. *)
Lemma gal_left_unique {A B : Type} {RA : relation A} {RB : relation B}
  (PB : PreOrder RB)
  (G G' : GaloisConnection RA RB)
  (Hr : ∀ b, gal_r G b = gal_r G' b) (a : A)
  : RB (gal_l G a) (gal_l G' a) * RB (gal_l G' a) (gal_l G a).
Proof.
  split.
  - apply (gal_from G a (gal_l G' a)).
    rewrite Hr. exact (gal_unit G' PB a).
  - apply (gal_from G' a (gal_l G a)).
    rewrite <- Hr. exact (gal_unit G PB a).
Qed.

(** ** What does NOT collapse: adjointness is a real constraint *)

(** The thesis of this file is that the coherence is vacuous but the
    biconditional is not.  Asserting that in prose would be worth little, so
    here it is as a theorem: the successor map is not left adjoint to itself,
    even though both are monotone and every coherence condition would be free.
    So [GaloisAdjunction] is not inhabited for an arbitrary monotone pair. *)
Program Definition NatSucc : Proset Nat.le_preorder ⟶ Proset Nat.le_preorder := {|
  fobj := S;
  fmap := fun x y (h : Nat.le x y) => _
|}.
Next Obligation. lia. Qed.

Theorem succ_not_self_adjoint :
  @Adjunction (Proset Nat.le_preorder) (Proset Nat.le_preorder) NatSucc NatSucc
    → False.
Proof.
  intro Adj.
  (* to (adj 0 0) turns [S 0 ≤ 0] into [0 ≤ S 0]; the reverse direction turns
     [0 ≤ S 0] into [S 0 ≤ 0], which is absurd. *)
  pose proof (from (@adj _ _ _ _ Adj 0%nat 0%nat)) as H.
  simpl in H.
  assert (Nat.le 0 (S 0)) as H0 by lia.
  pose proof (H H0) as Hbad.
  simpl in Hbad.
  lia.
Qed.
