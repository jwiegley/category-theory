Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Construction.Opposite.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Structure.Dagger.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Rel.
Require Import Category.Instance.Cat.
Require Import Category.Instance.StrictCat.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Proset.
Require Import Coq.Sets.Ensembles.

Generalizable All Variables.

#[local] Obligation Tactic := idtac.

(** * Rel: converse, self-duality, and the graph embedding's faithfulness

    Mac Lane, "Categories for the Working Mathematician", 2nd ed., §I.7
    (printed p. 26) [maclane:I.7:construction8]: Rel carries the
    CONVERSE relation R† = { (b, a) | (a, b) ∈ R }, an involution that
    is an anti-homomorphism for the relative product; and Set sits
    inside Rel by taking graphs of functions.
    Awodey, "Category Theory", 2nd ed., §1.9 Exercise 2 (printed
    p. 29) [awodey:1:ex2]: which of these hold?  (a) Rel ≅ Rel^op;
    (b) Sets ≅ Sets^op; (c) P(X) ≅ P(X)^op for a fixed set X.
    nLab: https://ncatlab.org/nlab/show/Rel

    This file completes Instance/Rel.v's disclosed gaps:

    - [Rel_Dagger]: the converse as the first instance of
      Structure/Dagger.v's [DaggerCategory] — the design choice the
      issue left open is resolved toward the general class, since the
      ZX and compact-closed prose already speak of daggers.
    - [Rel_Converse] / [Rel_self_dual_strict] / [Rel_self_dual]: the
      dagger packaged as an identity-on-objects functor Rel ⟶ Rel^op
      and the self-duality at BOTH strengths — strict functor equality
      in StrictCat, the genuine isomorphism of categories Awodey asks
      for, and the ≅[Cat] equivalence reading — Awodey's (a),
      affirmative.
    - [Relation_Functor_Faithful]: functions with pointwise-equal
      graphs are pointwise equal, so Coq really is a WIDE SUBCATEGORY
      of Rel, not merely mapped into it.
    - [Rel_Terminal] / [Rel_Zero]: the empty set is terminal as well
      as initial — the zero-object half Instance/Rel.v recorded as
      missing.
    - [Powerset] / [Powerset_self_dual]: Awodey's (c), affirmative,
      via complementation — over DECIDABLE (bool-valued) subsets, the
      constructive transposition of the classical statement: the
      Prop-valued complement is an involution only up to double
      negation, and a predicate-comparing setoid is equivalent to
      double-negation elimination (the disclosure pattern of
      Instance/Top/Closed.v's [pred_comparison_forces_DNE]).  On
      bool-valued subsets the round trips close by case analysis on
      the membership bit, with no axiom.
    - [Sets_not_self_dual]: Awodey's (b), NEGATIVE, proved: any
      isomorphism Sets ≅ Sets^op in Cat repackages as an equivalence
      ([Cat_Iso_to_Equivalence]), hence a full and faithful functor F;
      fullness reads a would-be element of Sets(F ∅, F 1) back through
      the EMPTY hom-setoid Sets(1, ∅), so carrier (F 1) is empty; and
      then the two points of Sets(1, 2) have vacuously equivalent
      images — every parallel pair into an empty-carrier setoid agrees
      — so faithfulness forces true = false.  All three parts of
      Awodey's exercise are thereby answered: (a) yes, (b) no,
      (c) yes. *)

(** ** The converse is a dagger *)

#[export] Program Instance Rel_Dagger : DaggerCategory Rel := {
  dagger := fun x y (R : x ~{Rel}~> y) (b : y) (a : x) => R a b
}.
Next Obligation.
  intros x y R S H b a; exact (H a b).
Qed.
Next Obligation.
  intros x y R b a; split; intro H; exact H.
Qed.
Next Obligation.
  intros x b a; split; intro H; destruct H; constructor.
Qed.
Next Obligation.
  intros x y z f g c a; split; intro H;
    destruct H as [e [H1 H2]]; exists e; split; assumption.
Qed.

(** ** Self-duality: Rel ≅ Rel^op in Cat (Awodey 1.9.2(a)) *)

(* The dagger, as an identity-on-objects functor.  [fmap] must be
   [Proper] and functorial with the OPPOSITE composition order — which
   is exactly [dagger_compose].

   HOW STRONG THE SELF-DUALITY IS.  [Cat]'s hom-setoid makes ≅[Cat]
   an EQUIVALENCE of categories (Instance/Cat.v's header); Awodey's
   exercise asks about an isomorphism of categories.  Both are
   delivered below, the two-tier presentation of
   Structure/Groupoid/Inversion.v: [Rel_self_dual_strict] in
   StrictCat — free, both composites being identity-on-objects and
   the round trips holding by strict functor equality — and the
   ≅[Cat] reading [Rel_self_dual]. *)
Program Definition Rel_Converse : Rel ⟶ Rel^op := {|
  fobj := fun x => x;
  fmap := fun x y (R : x ~{Rel}~> y) => @dagger Rel Rel_Dagger x y R
|}.
Next Obligation.
  intros x y R S H b a; exact (H a b).
Qed.
Next Obligation.
  intros x b a; split; intro H; destruct H; constructor.
Qed.
Next Obligation.
  intros x y z f g c a; split; intro H;
    destruct H as [e [H1 H2]]; exists e; split; assumption.
Qed.

Program Definition Rel_Converse_op : Rel^op ⟶ Rel := {|
  fobj := fun x => x;
  fmap := fun x y (R : x ~{Rel^op}~> y) => @dagger Rel Rel_Dagger y x R
|}.
Next Obligation.
  intros x y R S H b a; exact (H a b).
Qed.
Next Obligation.
  intros x b a; split; intro H; destruct H; constructor.
Qed.
Next Obligation.
  intros x y z f g c a; split; intro H;
    destruct H as [e [H1 H2]]; exists e; split; assumption.
Qed.

#[local] Obligation Tactic := cat_simpl.

Program Definition Rel_self_dual_strict : Rel ≅[StrictCat] Rel^op := {|
  to   := Rel_Converse;
  from := Rel_Converse_op
|}.

#[local] Obligation Tactic := idtac.

Program Definition Rel_self_dual : Rel ≅[Cat] Rel^op := {|
  to   := Rel_Converse;
  from := Rel_Converse_op
|}.
Next Obligation.
  exists (fun x => iso_id).
  intros x y R a b; simpl.
  split; intro H.
  - exists b; split; [| constructor ].
    exists a; split; [ constructor | exact H ].
  - destruct H as [e [[e0 [He0 HR]] Hb]].
    destruct He0.
    destruct Hb.
    exact HR.
Qed.
Next Obligation.
  exists (fun x => iso_id).
  intros x y R a b; simpl.
  split; intro H.
  - exists a; split; [ constructor |].
    exists b; split; [ exact H | constructor ].
  - destruct H as [e [He [e0 [HR Hb]]]].
    destruct He.
    destruct Hb.
    exact HR.
Qed.

(** ** The graph embedding is faithful: Coq is a wide subcategory *)

#[export] Instance Relation_Functor_Faithful : Faithful Relation_Functor.
Proof.
  constructor; intros x y f g H a.
  destruct (H a (f a)) as [Hfg _].
  destruct (Hfg (In_singleton _ _)).
  reflexivity.
Qed.

(** ** The empty set is terminal too, hence a zero object *)

#[export] Program Instance Rel_Terminal : @Terminal Rel := {
  terminal_obj := False;
  one := fun _ _ (f : False) => False_rect _ f
}.
Next Obligation. intros x f g a b; contradiction. Qed.

#[export] Program Instance Rel_Zero : ZeroObject Rel := {
  zero_terminal := Rel_Terminal;
  zero_initial  := Rel_Initial;
  zero_coincide := iso_id
}.

(** ** The powerset order is self-dual (Awodey 1.9.2(c)) *)

Section Powerset.

Context (X : Type).

(* Decidable subsets of X, ordered by pointwise containment.  The
   bool-valued reading is the constructive transposition of Awodey's
   P(X) (see the header): complementation is then a genuine involution,
   the round trips closing by case analysis on the membership bit. *)
Definition psub (A B : X → bool) : Prop :=
  ∀ x : X, A x = true → B x = true.

#[export] Instance psub_preorder : RelationClasses.PreOrder psub.
Proof.
  constructor.
  - intros A x H; exact H.
  - intros A B C H1 H2 x H; exact (H2 x (H1 x H)).
Qed.

Definition Powerset : Category := Proset psub_preorder.

(* Complementation is antitone, hence a functor into the opposite
   order; the thin target makes every functor law free. *)
Program Definition Powerset_Compl : Powerset ⟶ Powerset^op := {|
  fobj := fun A x => negb (A x);
  fmap := fun A B (H : psub A B) x HB => _
|}.
Next Obligation.
  intros A B H x HB; simpl in HB |- *.
  destruct (A x) eqn:HA.
  - rewrite (H x HA) in HB; discriminate HB.
  - reflexivity.
Qed.
Next Obligation. intros A B f g H; exact I. Qed.
Next Obligation. intros A; exact I. Qed.
Next Obligation. intros A B C f g; exact I. Qed.

Program Definition Powerset_Compl_op : Powerset^op ⟶ Powerset := {|
  fobj := fun A x => negb (A x);
  fmap := fun A B (H : psub B A) x HB => _
|}.
Next Obligation.
  intros A B H x HB; simpl in HB |- *.
  destruct (B x) eqn:HB'.
  - rewrite (H x HB') in HB; discriminate HB.
  - reflexivity.
Qed.
Next Obligation. intros A B f g H; exact I. Qed.
Next Obligation. intros A; exact I. Qed.
Next Obligation. intros A B C f g; exact I. Qed.

Program Definition Powerset_self_dual : Powerset ≅[Cat] Powerset^op := {|
  to   := Powerset_Compl;
  from := Powerset_Compl_op
|}.
Next Obligation.
  unshelve eexists.
  - intro A; unshelve econstructor.
    + intros x H; vm_compute in H |- *; rewrite H; reflexivity.
    + intros x H; vm_compute in H |- *; destruct (A x) eqn:HA;
        [ reflexivity | discriminate H ].
    + exact I.
    + exact I.
  - intros A B H; exact I.
Qed.
Next Obligation.
  unshelve eexists.
  - intro A; unshelve econstructor.
    + intros x H; vm_compute in H |- *; destruct (A x) eqn:HA;
        [ reflexivity | discriminate H ].
    + intros x H; vm_compute in H |- *; rewrite H; reflexivity.
    + exact I.
    + exact I.
  - intros A B H; exact I.
Qed.

End Powerset.

(** ** Sets is NOT self-dual (Awodey 1.9.2(b)) *)

Definition SEmpty : Sets := {| carrier := False; is_setoid := eq_Setoid False |}.
Definition SUnit  : Sets := {| carrier := unit;  is_setoid := eq_Setoid unit  |}.
Definition SBool  : Sets := {| carrier := bool;  is_setoid := eq_Setoid bool  |}.

#[local] Obligation Tactic := cat_simpl.

Program Definition kbool (b : bool) : SUnit ~{Sets}~> SBool :=
  {| morphism := fun _ => b |}.

(* Any Cat-isomorphism repackages as an equivalence, hence a full and
   faithful F : Sets ⟶ Sets^op.  Fullness reads a would-be element of
   Sets(F ∅, F 1) back through the EMPTY hom-setoid Sets(1, ∅), so
   carrier (F 1) is empty; then the two constant maps 1 ⇉ 2 have
   vacuously equivalent images — every parallel pair into an
   empty-carrier setoid agrees — and faithfulness forces true = false. *)
Theorem Sets_not_self_dual : Sets ≅[Cat] Sets^op → False.
Proof.
  intro iso.
  pose (E := Cat_Iso_to_Equivalence iso).
  pose (F := to iso).
  pose proof (Equivalence_Full E)     as HFull.
  pose proof (Equivalence_Faithful E) as HFaith.
  assert (Hno : (F SEmpty ~{Sets}~> F SUnit) → False).
  { intro g. exact (@prefmap _ _ F HFull SUnit SEmpty g tt). }
  assert (He : carrier (F SUnit) → False).
  { intro e. unshelve refine (Hno {| morphism := fun _ => e |}).
    abstract (proper). }
  assert (Hfe : fmap[F] (kbool true) ≈ fmap[F] (kbool false)).
  { intro a. elim (He (fmap[F] (kbool true) a)). }
  pose proof (@fmap_inj _ _ F HFaith SUnit SBool _ _ Hfe tt) as Hc.
  discriminate Hc.
Qed.
