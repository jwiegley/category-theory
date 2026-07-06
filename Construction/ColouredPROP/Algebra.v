Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.ColouredPROP.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.
Require Import Category.Construction.ColouredPROP.Cast.
Require Import Category.Construction.ColouredPROP.Monoidal.
Require Import Category.Construction.ColouredPROP.Braided.
Require Import Category.Construction.ColouredPROP.Instance.
Require Import Category.Construction.ColouredPROP.Interp.
Require Import Category.Construction.ColouredPROP.Universal.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * Algebras (models) of a coloured signature in a coloured PROP *)

(* nLab: https://ncatlab.org/nlab/show/PROP
   nLab: https://ncatlab.org/nlab/show/algebra+over+a+PROP
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   Fixing a coloured signature [S] and a coloured PROP [P], a MODEL
   (or algebra) of [S] in [P] is a valuation [v : CValuation P S] — an
   assignment of a [P]-morphism [⟦cs⟧ ~{P}~> ⟦ds⟧] to every generator
   [g : S cs ds] (see [Construction/ColouredPROP/Interp.v]).  This
   file builds the category of such models, as the many-sorted mirror
   of [Construction/PROP/Algebra.v] (the one-sorted donor), with
   [list Colour] replacing [nat], [++] replacing [+], and [[]]
   replacing [0]:

     - [CModelHom v w] — a morphism of models: a family of
       endomorphisms [cmh_component cs : ⟦cs⟧ ~{P}~> ⟦cs⟧] that is
       monoidal (the identity at the empty boundary, sending
       concatenations of boundaries to [⊞c]-tensors of components)
       and compatible with the two valuations at every generator.
       (The [c]-prefixed name keeps clear of the one-sorted
       [ModelHom], and — as there — of the [AlgHom] of
       [Instance/Comp.v], the single-sorted operadic cousin of this
       notion.)

     - [cmodel_hom_natural] — the fundamental theorem: the components
       of a model morphism are automatically natural against the
       interpretation of EVERY term, not just the generators.  The
       generator squares extend along [cinterp] by structural
       induction, using the K-kit of [Interp.v] (K2/K3 for the
       tensor case and K5 for the braid case; K1 enters later, in
       the monoidality of the identity model morphism).  Only the
       coherence-free part of the kit (K1–K5) is consumed: no
       [ObjDecEq]-flavoured cast juggling appears in any proof of
       this file — [HomEqProp] / [ObjDecEq] enter only to TYPE the
       interpretation functor [CInterpF] in the [Transform]
       packaging below.

     - [CAlg] — the category of models: objects are valuations,
       morphisms are [CModelHom]s, with componentwise identity,
       composition, and hom-equivalence.

     - [CModelHom_Transform_natural] — the naturality square of
       [cmodel_hom_natural], restated in the orientation a
       [Transform] between the interpretation functors expects.

     - [CModelHom_Transform] — the packaging of [cmodel_hom_natural]:
       a model morphism induces a natural transformation
       [CInterpF S P v ⟹ CInterpF S P w] between the interpretation
       functors of [Construction/ColouredPROP/Universal.v].

   In PROP-theoretic terms a [CModelHom] is a monoidal natural
   transformation between the strict symmetric monoidal functors
   corresponding to [v] and [w], re-indexed along the Leibniz
   strictness equalities [cprop_unit_nil] / [cprop_tensor_app]; as
   in the one-sorted donor, the full functor-category packaging (a
   functor from [CAlg] into the functor category [[CFreeCat S, P]])
   is deferred to a successor file, as no current consumer needs
   it. *)

Section CAlgebra.

Context {Colour : Type}.
Context (S : CSignature Colour).
Context (P : ColouredPROP Colour).
Context {HP : @HomEqProp P}.
Context {OD : @ObjDecEq P}.

(** The coloured-PROP-object [⟦cs⟧], as in
    [Construction/ColouredPROP.v] (whose notation is section-local
    there and must be re-declared per file). *)
Notation "⟦ cs ⟧" := (@cprop_of_list Colour P cs)
  (at level 0, format "⟦ cs ⟧").

(** Parallel composition at [⟦·⟧]-indexed objects, from [Interp.v]. *)
Infix "⊞c" := (ctensor_hom P) (at level 30, right associativity).

(** ** Model morphisms

    A model morphism [v ⇒ w] is a monoidal family of endomorphisms of
    the canonical objects, intertwining the two valuations.  The
    monoidality field [cmh_tensor] is stated in [⊞c] form — terser
    than an explicit [chcast] conjugation, and exactly the shape the
    K-kit of [Interp.v] consumes. *)

Record CModelHom (v w : CValuation P S) : Type := {
  cmh_component : ∀ cs : list Colour, ⟦cs⟧ ~{P}~> ⟦cs⟧;

  (* the component at the monoidal unit is the identity *)
  cmh_unit : cmh_component [] ≈ id;

  (* components at a concatenation of boundaries are the tensor of
     components *)
  cmh_tensor : ∀ cs ds : list Colour,
    cmh_component (cs ++ ds) ≈ cmh_component cs ⊞c cmh_component ds;

  (* the intertwining square at every generator *)
  cmh_gen : ∀ cs ds (g : S cs ds),
    cmh_component ds ∘ v cs ds g ≈ w cs ds g ∘ cmh_component cs
}.

Arguments cmh_component {v w} _ _.
Arguments cmh_unit {v w} _.
Arguments cmh_tensor {v w} _ _ _.
Arguments cmh_gen {v w} _ _ _ _.

(** ** Naturality against every interpreted term

    The generator squares of a [CModelHom] extend to naturality
    squares at ALL terms: identities by the unit laws, sequential
    composition by pasting, parallel composition by [cmh_tensor] on
    both flanks and the interchange law K2 (rewriting under [⊞c] via
    K3), and the block braid by [cmh_tensor] and the braid naturality
    K5. *)

Theorem cmodel_hom_natural {v w : CValuation P S} (α : CModelHom v w)
  {cs ds : list Colour} (t : CTerm S cs ds) :
  cmh_component α ds ∘ cinterp P S v t ≈ cinterp P S w t ∘ cmh_component α cs.
Proof.
  induction t as [ks | bcs bds | ccs cds ces tg IHg tf IHf
                  | cs1 ds1 cs2 ds2 tf IHf tg IHg | gcs gds gg].
  - (* CT_id *)
    cbn [cinterp].
    now rewrite id_left, id_right.
  - (* CT_braid *)
    cbn [cinterp].
    rewrite (cmh_tensor α bds bcs), (cmh_tensor α bcs bds).
    apply cbraid_hom_swap.
  - (* CT_comp *)
    cbn [cinterp].
    rewrite comp_assoc.
    rewrite IHg.
    rewrite <- comp_assoc.
    rewrite IHf.
    apply comp_assoc.
  - (* CT_tens *)
    cbn [cinterp].
    rewrite (cmh_tensor α ds1 ds2), (cmh_tensor α cs1 cs2).
    rewrite <- !ctensor_hom_comp.
    now rewrite IHf, IHg.
  - (* CT_gen *)
    cbn [cinterp].
    apply (cmh_gen α).
Qed.

(** ** The identity model morphism

    Componentwise the identity; monoidality is K1 ([ctensor_hom_id])
    read right-to-left. *)

Lemma cmh_id_unit : id[⟦[]⟧] ≈ id[⟦[]⟧].
Proof. reflexivity. Qed.

Lemma cmh_id_tensor (cs ds : list Colour) :
  id[⟦cs ++ ds⟧] ≈ id[⟦cs⟧] ⊞c id[⟦ds⟧].
Proof. symmetry; apply ctensor_hom_id. Qed.

Lemma cmh_id_gen (v : CValuation P S) (cs ds : list Colour) (g : S cs ds) :
  id[⟦ds⟧] ∘ v cs ds g ≈ v cs ds g ∘ id[⟦cs⟧].
Proof. now rewrite id_left, id_right. Qed.

Definition CModelHom_id (v : CValuation P S) : CModelHom v v := {|
  cmh_component := fun cs : list Colour => id[⟦cs⟧];
  cmh_unit := cmh_id_unit;
  cmh_tensor := cmh_id_tensor;
  cmh_gen := cmh_id_gen v
|}.

(** ** Composition of model morphisms

    Componentwise composition; monoidality is the interchange law K2
    ([ctensor_hom_comp]) read right-to-left, and the generator squares
    paste. *)

Lemma cmh_compose_unit {u v w : CValuation P S}
  (α : CModelHom v w) (β : CModelHom u v) :
  cmh_component α [] ∘ cmh_component β [] ≈ id[⟦[]⟧].
Proof.
  rewrite (cmh_unit α), (cmh_unit β).
  apply id_left.
Qed.

Lemma cmh_compose_tensor {u v w : CValuation P S}
  (α : CModelHom v w) (β : CModelHom u v) (cs ds : list Colour) :
  cmh_component α (cs ++ ds) ∘ cmh_component β (cs ++ ds)
    ≈ (cmh_component α cs ∘ cmh_component β cs)
        ⊞c (cmh_component α ds ∘ cmh_component β ds).
Proof.
  rewrite (cmh_tensor α cs ds), (cmh_tensor β cs ds).
  symmetry; apply ctensor_hom_comp.
Qed.

Lemma cmh_compose_gen {u v w : CValuation P S}
  (α : CModelHom v w) (β : CModelHom u v)
  (cs ds : list Colour) (g : S cs ds) :
  (cmh_component α ds ∘ cmh_component β ds) ∘ u cs ds g
    ≈ w cs ds g ∘ (cmh_component α cs ∘ cmh_component β cs).
Proof.
  rewrite <- comp_assoc.
  rewrite (cmh_gen β cs ds g).
  rewrite (comp_assoc (cmh_component α ds) (v cs ds g) (cmh_component β cs)).
  rewrite (cmh_gen α cs ds g).
  apply comp_assoc_sym.
Qed.

Definition CModelHom_compose {u v w : CValuation P S}
  (α : CModelHom v w) (β : CModelHom u v) : CModelHom u w := {|
  cmh_component := fun cs : list Colour =>
    cmh_component α cs ∘ cmh_component β cs;
  cmh_unit := cmh_compose_unit α β;
  cmh_tensor := cmh_compose_tensor α β;
  cmh_gen := cmh_compose_gen α β
|}.

(** ** The category of models

    Hom-equivalence is componentwise; identity, composition and the
    category laws are inherited pointwise from [P]. *)

#[export] Program Instance CModelHom_Setoid {v w : CValuation P S} :
  Setoid (CModelHom v w) := {|
  equiv := fun α β => ∀ cs : list Colour,
    cmh_component α cs ≈ cmh_component β cs
|}.
Next Obligation.
  split.
  - intros α cs.
    reflexivity.
  - intros α β Hαβ cs.
    symmetry; apply Hαβ.
  - intros α β γ Hαβ Hβγ cs.
    rewrite (Hαβ cs); apply Hβγ.
Qed.

(** Componentwise congruence of composition.  The [Proper] obligation
    is discharged by the global obligation tactic ([cat_simpl]). *)
#[export] Program Instance CModelHom_compose_respects
  {u v w : CValuation P S} :
  Proper (equiv ==> equiv ==> equiv) (@CModelHom_compose u v w).

Program Definition CAlg : Category := {|
  obj := CValuation P S;
  hom := CModelHom;
  homset := @CModelHom_Setoid;
  id := CModelHom_id;
  compose := @CModelHom_compose;
  compose_respects := @CModelHom_compose_respects;
  id_left := fun v w α cs => id_left (cmh_component α cs);
  id_right := fun v w α cs => id_right (cmh_component α cs);
  comp_assoc := fun t u v w α β γ cs =>
    comp_assoc (cmh_component α cs) (cmh_component β cs)
               (cmh_component γ cs);
  comp_assoc_sym := fun t u v w α β γ cs =>
    comp_assoc_sym (cmh_component α cs) (cmh_component β cs)
                   (cmh_component γ cs)
|}.

(** ** Model morphisms as natural transformations

    [cmodel_hom_natural] is exactly the naturality square of a
    transformation between the interpretation functors of
    [Construction/ColouredPROP/Universal.v] — components in the
    orientation [Transform] expects. *)

Lemma CModelHom_Transform_natural {v w : CValuation P S}
  (α : CModelHom v w) (cs ds : list Colour) (t : CTerm S cs ds) :
  cinterp P S w t ∘ cmh_component α cs ≈ cmh_component α ds ∘ cinterp P S v t.
Proof. symmetry; apply cmodel_hom_natural. Qed.

(* Built with the explicit [Build_Transform'] so that the source and
   target functors are pinned, as for [CInterpF] itself in
   [Universal.v].  A [CModelHom] is a monoidal natural transformation
   re-indexed along the Leibniz strictness equalities; only the bare
   [Transform] packaging is provided here (see the header). *)
Definition CModelHom_Transform {v w : CValuation P S}
  (α : CModelHom v w) : CInterpF S P v ⟹ CInterpF S P w :=
  @Build_Transform' (CFreeCat S) P (CInterpF S P v) (CInterpF S P w)
    (fun cs : list Colour => cmh_component α cs)
    (fun cs ds t => CModelHom_Transform_natural α cs ds t).

End CAlgebra.

Arguments CModelHom {Colour} S P v w : assert.
Arguments cmh_component {Colour S P v w} _ _.
Arguments cmh_unit {Colour S P v w} _.
Arguments cmh_tensor {Colour S P v w} _ _ _.
Arguments cmh_gen {Colour S P v w} _ _ _ _.
Arguments cmodel_hom_natural {Colour} S P {v w} α {cs ds} t : assert.
Arguments CModelHom_id {Colour} S P v : assert.
Arguments CModelHom_compose {Colour} S P {u v w} α β : assert.
Arguments CAlg {Colour} S P : assert.
Arguments CModelHom_Transform_natural {Colour} S P {v w} α cs ds t : assert.
Arguments CModelHom_Transform {Colour} S P {HP OD v w} α : assert.
