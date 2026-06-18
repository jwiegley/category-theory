Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Initial.
Require Import Category.Instance.Coq.
Require Import Coq.Sets.Ensembles.

Generalizable All Variables.

Local Set Warnings "-intuition-auto-with-star".

(** The category REL of sets and binary relations. *)

(* nLab: https://ncatlab.org/nlab/show/Rel
   Wikipedia: https://en.wikipedia.org/wiki/Category_of_relations

   REL has sets (here Coq types, via [obj Coq]) as objects, and a morphism
   `A ~> B` is a heterogeneous binary relation `R ⊆ A × B`. We curry this as
   `A → Ensemble B` (equivalently `A → B → Prop`), so `R a b` means
   `(a, b) ∈ R`. Two relations are equivalent when they are pointwise
   logically equivalent, `f ≈ g := ∀ x y, f x y ↔ g x y` (Prop-valued, so `↔`
   is the right notion of equality on homs).

    objects               Coq types (sets)
    arrows                relations `R ⊆ A × B`, as `A → Ensemble B`
    arrow equivalence     pointwise `↔`
    identity              the diagonal/equality relation `Δ = { (a, a) }`
    composition           relational composition via an existential witness

   Identity is [Singleton]: `id A a = Singleton a`, so `In (id A a) b` holds
   iff `b = a` — the diagonal Δ_A. Composition of `R : A ~> B` then `S : B ~> C`
   is `(S ∘ R) a c = ∃ b, R a b ∧ S b c`, the standard existential-witness
   relational composite (note the diagrammatic order: [compose f g] applies
   `g` first, then `f`).

   REL is a dagger category: the converse `R† = { (b, a) | (a, b) ∈ R }` is an
   involution with `(S ∘ R)† = R† ∘ S†`, and the dagger witnesses the
   self-duality `Rel ≅ Rel^op`. It is moreover locally posetal (relations
   ordered by inclusion) and dagger-compact closed. None of that extra
   structure is built here; this file constructs the bare category, its initial
   object (the empty set, which is in fact a zero object — see [Rel_Initial]),
   and the wide embedding `Coq ⟶ Rel` of functions as relations. The category
   laws hold with no axioms. *)

Program Definition Rel : Category := {|
  obj     := @obj Coq;                  (* objects are Coq types (sets)        *)
  hom     := fun A B => A ~> Ensemble B; (* a relation `R ⊆ A × B`, curried    *)
  homset  := fun P Q =>                 (* hom-equivalence: pointwise `↔`      *)
               {| equiv := fun f g => ∀ x y, f x y ↔ g x y |};
  id      := Singleton;                 (* diagonal: `id a = { b | b = a }`    *)
  compose := fun x y z f g a b =>       (* `(f ∘ g) a b = ∃ e, g a e ∧ f e b`  *)
               (exists e : y, In y (g a) e ∧ In z (f e) b)%type
|}.
Next Obligation.
  equivalence.
  - apply X; assumption.
  - apply X; assumption.
  - apply X0, X; assumption.
  - apply X, X0; assumption.
Qed.
Next Obligation.
  proper;
  destruct H as [w [H1 H2]];
  exists w; firstorder.
Qed.
Next Obligation.
  split; intros.
  - destruct H as [? [? H2]].
    destruct H2; assumption.
  - exists y0.
    intuition; auto with *.
Qed.
Next Obligation.
  split; intros.
  - destruct H as [? [H1 ?]].
    destruct H1; assumption.
  - exists x0.
    intuition; auto with *.
Qed.
Next Obligation. firstorder. Qed.
Next Obligation. firstorder. Qed.

(* The initial object of REL is the empty set [False]: the only relation
   `∅ ~> A` is the empty relation, and it is forced. (Dually the empty set is
   also terminal, so it is in fact a zero object; only the initial half is
   recorded here.) Since [Initial Rel] unfolds to [Terminal (Rel^op)], the
   primitive field names below are the C^op-side [terminal_obj]/[one]; the
   C-side names [initial_obj]/[zero] are recovered by Structure/Initial.v. *)
#[export]
Program Instance Rel_Initial : @Initial Rel := {
  terminal_obj := False;
  one := fun _ _ => False_rect _ _
}.
Next Obligation. contradiction. Qed.

(*
Program Instance Rel_Cartesian : @Cartesian Rel := {
  product_obj := @Prod Coq _;
  fork := fun _ _ _ f g x y => f x (fst y) ∧ g x (snd y);
  exl  := fun _ _ p x => In _ (Singleton _ (fst p)) x;
  exr  := fun _ _ p x => In _ (Singleton _ (snd p)) x
}.
Next Obligation.
  proper.
  split; intros.
    destruct H.
    split; intros.
      apply X0; assumption.
    apply X1; assumption.
  destruct H.
  split; intros.
    apply X0; assumption.
  apply X1; assumption.
Qed.
Next Obligation.
  firstorder.
  - destruct H1.
    apply H, H0.
  - eexists (y, _).
    split.
      apply H; simpl.
      split.
        assumption.
      apply H.
Qed.

Program Instance Rel_Cocartesian : @Cocartesian Rel := {
  product_obj := or;
  fork := fun _ _ _ f g x =>
            match x with
            | or_introl v => f v
            | or_intror v => g v
            end;
  exl  := fun _ _ p => or_introl p;
  exr  := fun _ _ p => or_intror p
}.
Obligation 1. proper; autounfold in *; apply proof_irrelevance. Qed.
Obligation 2.
  autounfold in *.
  split; intros.
    split; intros;
    apply proof_irrelevance.
  apply proof_irrelevance.
Qed.

Program Instance Rel_Closed : @Closed Rel _ := {
  exponent_obj := Basics.impl;
  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f a b => f (conj a b) |}
     ; from := {| morphism := fun f p => f (proj1 p) (proj2 p) |} |}
}.
Next Obligation. proper; autounfold in *; apply proof_irrelevance. Qed.
Next Obligation. proper; autounfold in *; apply proof_irrelevance. Qed.
Next Obligation. autounfold in *; apply proof_irrelevance. Qed.
Next Obligation. autounfold in *; apply proof_irrelevance. Qed.
Next Obligation. autounfold in *; apply proof_irrelevance. Qed.
*)

(* A sample non-functional morphism: the strict-order relation `<` on nat,
   a genuine relation of REL that is not the graph of any function. *)
Definition some_number : nat ~{Rel}~> nat := fun x y => (x < y)%nat.

(* The wide embedding of functions as relations, `Coq ⟶ Rel`: a function `f`
   is sent to its graph `{ (x, y) | f x = y }`. It is the identity on objects
   and faithful, exhibiting Coq (Set) as a wide subcategory of REL. *)
#[export]
Program Instance Relation_Functor : Coq ⟶ Rel := {
  fobj := fun x => x;
  fmap := fun x y (f : x ~{Coq}~> y) x y => In _ (Singleton _ (f x)) y
}.
Next Obligation. proper; congruence. Qed.
Next Obligation.
  simplify; firstorder.
  destruct a, b; constructor.
Qed.
