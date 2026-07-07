Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.PROP.
Require Import Category.Construction.PROP.Signature.
Require Import Category.Construction.PROP.Term.
Require Import Category.Construction.PROP.Free.
Require Import Category.Construction.PROP.Instance.
Require Import Category.Construction.PROP.Interp.
Require Import Category.Construction.PROP.Universal.

Generalizable All Variables.

(** * Algebras (models) of a signature in a PROP *)

(* nLab: https://ncatlab.org/nlab/show/PROP (see the section on algebras)
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   Fixing a signature [S] and a PROP [P], a MODEL (or algebra) of [S]
   in [P] is a valuation [v : Valuation P S] — an assignment of a
   [P]-morphism [⟦m⟧ ~{P}~> ⟦n⟧] to every generator [g : S m n]
   (see [Construction/PROP/Interp.v]).  This file builds the category
   of such models:

     - [ModelHom v w] — a morphism of models: a family of
       endomorphisms [mh_component n : ⟦n⟧ ~{P}~> ⟦n⟧] that is
       monoidal (the identity at arity [0], sending sums of arities to
       [⊞]-tensors of components) and compatible with the two
       valuations at every generator.  (The name avoids the [AlgHom]
       of [Instance/Comp.v], which is the single-sorted operadic
       cousin of this notion.)

     - [model_hom_natural] — the fundamental theorem: the components
       of a model morphism are automatically natural against the
       interpretation of EVERY term, not just the generators.  The
       generator squares extend along [interp] by structural
       induction, using the K-kit of [Interp.v] (K2/K3 for the
       tensor case and K5 for the braid case; K1 enters later, in
       the monoidality of the identity model morphism).

     - [Alg] — the category of models: objects are valuations,
       morphisms are [ModelHom]s, with componentwise identity,
       composition, and hom-equivalence.

     - [ModelHom_Transform] — the packaging of [model_hom_natural]: a
       model morphism induces a natural transformation
       [InterpF S P v ⟹ InterpF S P w] between the interpretation
       functors of [Construction/PROP/Universal.v].

   In PROP-theoretic terms a [ModelHom] is a monoidal natural
   transformation between the strict symmetric monoidal functors
   corresponding to [v] and [w], re-indexed along the Leibniz
   strictness equalities [prop_unit_zero] / [prop_tensor_plus]; the
   full functor-category packaging (a functor from [Alg] into the
   functor category [[FreeCat S, P]]) is deferred to a successor
   file, as no current consumer needs it. *)

Section Algebra.

Context (S : Signature).
Context (P : PROP).
Context {HP : HomEqProp P}.
Context {OD : @ObjDecEq P}.

Open Scope nat_scope.

(** The PROP-object [⟦n⟧], as in [Construction/PROP.v] (whose notation
    is section-local there and must be re-declared per file). *)
Notation "⟦ n ⟧" := (@prop_of_nat P n) (at level 0, format "⟦ n ⟧").

(** Parallel composition at [⟦·⟧]-indexed objects, from [Interp.v]. *)
Infix "⊞" := (prop_tensor_hom P) (at level 30, right associativity).

(** ** Model morphisms

    A model morphism [v ⇒ w] is a monoidal family of endomorphisms of
    the canonical objects, intertwining the two valuations.  The
    monoidality field [mh_tensor] is stated in [⊞] form — terser than
    an explicit [id_cast] conjugation, and exactly the shape the K-kit
    of [Interp.v] consumes. *)

Record ModelHom (v w : Valuation P S) : Type := {
  mh_component : ∀ n : nat, ⟦n⟧ ~{P}~> ⟦n⟧;

  (* the component at the monoidal unit is the identity *)
  mh_unit : mh_component 0 ≈ id;

  (* components at a sum of arities are the tensor of components *)
  mh_tensor : ∀ m n : nat,
    mh_component (m + n) ≈ mh_component m ⊞ mh_component n;

  (* the intertwining square at every generator *)
  mh_gen : ∀ m n (g : S m n),
    mh_component n ∘ v m n g ≈ w m n g ∘ mh_component m
}.

Arguments mh_component {v w} _ _.
Arguments mh_unit {v w} _.
Arguments mh_tensor {v w} _ _ _.
Arguments mh_gen {v w} _ _ _ _.

(** ** Naturality against every interpreted term

    The generator squares of a [ModelHom] extend to naturality squares
    at ALL terms: identities by the unit laws, sequential composition
    by pasting, parallel composition by [mh_tensor] on both flanks and
    the interchange law K2 (rewriting under [⊞] via K3), and the block
    braid by [mh_tensor] and the braid naturality K5. *)

Theorem model_hom_natural {v w : Valuation P S} (α : ModelHom v w)
  {m n : nat} (t : Term S m n) :
  mh_component α n ∘ interp P S v t ≈ interp P S w t ∘ mh_component α m.
Proof.
  induction t as [k | bm bn | cm cn cp tg IHg tf IHf
                  | m1 n1 m2 n2 tf IHf tg IHg | gm gn gg].
  - (* T_id *)
    cbn [interp].
    now rewrite id_left, id_right.
  - (* T_braid *)
    cbn [interp].
    rewrite (mh_tensor α bn bm), (mh_tensor α bm bn).
    apply prop_braid_swap.
  - (* T_comp *)
    cbn [interp].
    rewrite comp_assoc.
    rewrite IHg.
    rewrite <- comp_assoc.
    rewrite IHf.
    apply comp_assoc.
  - (* T_tens *)
    cbn [interp].
    rewrite (mh_tensor α n1 n2), (mh_tensor α m1 m2).
    rewrite <- !tensor_hom_comp.
    now rewrite IHf, IHg.
  - (* T_gen *)
    cbn [interp].
    apply (mh_gen α).
Qed.

(** ** The identity model morphism

    Componentwise the identity; monoidality is K1 ([tensor_hom_id])
    read right-to-left. *)

Lemma mh_id_unit : id[⟦0⟧] ≈ id[⟦0⟧].
Proof. reflexivity. Qed.

Lemma mh_id_tensor (m n : nat) :
  id[⟦m + n⟧] ≈ id[⟦m⟧] ⊞ id[⟦n⟧].
Proof. symmetry; apply tensor_hom_id. Qed.

Lemma mh_id_gen (v : Valuation P S) (m n : nat) (g : S m n) :
  id[⟦n⟧] ∘ v m n g ≈ v m n g ∘ id[⟦m⟧].
Proof. now rewrite id_left, id_right. Qed.

Definition ModelHom_id (v : Valuation P S) : ModelHom v v := {|
  mh_component := fun n : nat => id[⟦n⟧];
  mh_unit := mh_id_unit;
  mh_tensor := mh_id_tensor;
  mh_gen := mh_id_gen v
|}.

(** ** Composition of model morphisms

    Componentwise composition; monoidality is the interchange law K2
    ([tensor_hom_comp]) read right-to-left, and the generator squares
    paste. *)

Lemma mh_compose_unit {u v w : Valuation P S}
  (α : ModelHom v w) (β : ModelHom u v) :
  mh_component α 0 ∘ mh_component β 0 ≈ id[⟦0⟧].
Proof.
  rewrite (mh_unit α), (mh_unit β).
  apply id_left.
Qed.

Lemma mh_compose_tensor {u v w : Valuation P S}
  (α : ModelHom v w) (β : ModelHom u v) (m n : nat) :
  mh_component α (m + n) ∘ mh_component β (m + n)
    ≈ (mh_component α m ∘ mh_component β m)
        ⊞ (mh_component α n ∘ mh_component β n).
Proof.
  rewrite (mh_tensor α m n), (mh_tensor β m n).
  symmetry; apply tensor_hom_comp.
Qed.

Lemma mh_compose_gen {u v w : Valuation P S}
  (α : ModelHom v w) (β : ModelHom u v) (m n : nat) (g : S m n) :
  (mh_component α n ∘ mh_component β n) ∘ u m n g
    ≈ w m n g ∘ (mh_component α m ∘ mh_component β m).
Proof.
  rewrite <- comp_assoc.
  rewrite (mh_gen β m n g).
  rewrite (comp_assoc (mh_component α n) (v m n g) (mh_component β m)).
  rewrite (mh_gen α m n g).
  apply comp_assoc_sym.
Qed.

Definition ModelHom_compose {u v w : Valuation P S}
  (α : ModelHom v w) (β : ModelHom u v) : ModelHom u w := {|
  mh_component := fun n : nat => mh_component α n ∘ mh_component β n;
  mh_unit := mh_compose_unit α β;
  mh_tensor := mh_compose_tensor α β;
  mh_gen := mh_compose_gen α β
|}.

(** ** The category of models

    Hom-equivalence is componentwise; identity, composition and the
    category laws are inherited pointwise from [P]. *)

#[export] Program Instance ModelHom_Setoid {v w : Valuation P S} :
  Setoid (ModelHom v w) := {|
  equiv := fun α β => ∀ n : nat, mh_component α n ≈ mh_component β n
|}.
Next Obligation.
  split.
  - intros α n.
    reflexivity.
  - intros α β Hαβ n.
    symmetry; apply Hαβ.
  - intros α β γ Hαβ Hβγ n.
    rewrite (Hαβ n); apply Hβγ.
Qed.

(** Componentwise congruence of composition.  The [Proper] obligation
    is discharged by the global obligation tactic ([cat_simpl]). *)
#[export] Program Instance ModelHom_compose_respects
  {u v w : Valuation P S} :
  Proper (equiv ==> equiv ==> equiv) (@ModelHom_compose u v w).

Program Definition Alg : Category := {|
  obj := Valuation P S;
  hom := ModelHom;
  homset := @ModelHom_Setoid;
  id := ModelHom_id;
  compose := @ModelHom_compose;
  compose_respects := @ModelHom_compose_respects;
  id_left := fun v w α n => id_left (mh_component α n);
  id_right := fun v w α n => id_right (mh_component α n);
  comp_assoc := fun t u v w α β γ n =>
    comp_assoc (mh_component α n) (mh_component β n) (mh_component γ n);
  comp_assoc_sym := fun t u v w α β γ n =>
    comp_assoc_sym (mh_component α n) (mh_component β n) (mh_component γ n)
|}.

(** ** Model morphisms as natural transformations

    [model_hom_natural] is exactly the naturality square of a
    transformation between the interpretation functors of
    [Universal.v] — components in the orientation [Transform]
    expects. *)

Lemma ModelHom_Transform_natural {v w : Valuation P S} (α : ModelHom v w)
  (m n : nat) (t : Term S m n) :
  interp P S w t ∘ mh_component α m ≈ mh_component α n ∘ interp P S v t.
Proof. symmetry; apply model_hom_natural. Qed.

(* Built with the explicit [Build_Transform'] so that the source and
   target functors are pinned, as for [InterpF] itself in
   [Universal.v].  A [ModelHom] is a monoidal natural transformation
   re-indexed along the Leibniz strictness equalities; only the bare
   [Transform] packaging is provided here (see the header). *)
Definition ModelHom_Transform {v w : Valuation P S} (α : ModelHom v w) :
  InterpF S P v ⟹ InterpF S P w :=
  @Build_Transform' (FreeCat S) P (InterpF S P v) (InterpF S P w)
    (fun n : nat => mh_component α n)
    (fun m n t => ModelHom_Transform_natural α m n t).

End Algebra.

Arguments ModelHom S P v w : assert.
Arguments mh_component {S P v w} _ _.
Arguments mh_unit {S P v w} _.
Arguments mh_tensor {S P v w} _ _ _.
Arguments mh_gen {S P v w} _ _ _ _.
Arguments model_hom_natural S P {v w} α {m n} t : assert.
Arguments ModelHom_id S P v : assert.
Arguments ModelHom_compose S P {u v w} α β : assert.
Arguments Alg S P : assert.
Arguments ModelHom_Transform S P {HP OD v w} α : assert.
