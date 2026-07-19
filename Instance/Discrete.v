Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Discrete.

Generalizable All Variables.

Import EqNotations.

(** * The discrete category on a Type *)

(* nLab: https://ncatlab.org/nlab/show/discrete+category

   Given any [Type] [A], the discrete category [DiscreteCat A] has the elements
   of [A] as objects and *propositional equality* [x = y] as the hom from [x] to
   [y]. Identity is [eq_refl] and composition is [eq_trans] (in the categorical
   orientation: [compose (g : y = z) (f : x = y) : x = z]). The hom-setoid is the
   strict-equality setoid [Morphism_equality], so every [≈]-goal here reduces to
   an [eq]-goal between equality proofs and is discharged by destructing the
   proofs — no UIP, function extensionality, or other axiom is needed, because
   the equivalence is [eq] itself rather than a quotient.

   This is the object-level construction: [DiscreteCat] *builds* a category out
   of a type. It is a genuinely different notion from the [Discrete] predicate of
   Structure/Discrete.v, which *asserts* that a given category has only identity
   morphisms. The sanity lemma [DiscreteCat_Discrete] at the end connects the two
   by showing that every [DiscreteCat A] does satisfy that predicate.

   Functors out of [DiscreteCat A] are exactly functions [A → C]: any [f : A → C]
   extends to [DiscreteCat_Functor f], transporting [id] along the equality
   witness. This is the left adjoint `Set ⟶ Cat` at the level of a single
   functor. *)

(* The discrete category on [A]: objects are elements of [A], morphisms are
   proofs of equality, composition is transitivity of equality. The explicit
   [@{o h p}] binders follow convention 2.4.11 (cf. Instance/One.v). *)
Program Definition DiscreteCat@{o h p} (A : Type@{o}) : Category@{o h p} := {|
  obj     := A;                       (* objects are elements of A *)
  hom     := fun x y => x = y;        (* morphisms are equality proofs *)
  homset  := fun x y => Morphism_equality@{o h p} x y;  (* strict-eq setoid *)
  id      := fun _ => eq_refl;        (* identity is reflexivity *)
  compose := fun _ _ _ g f => eq_trans f g  (* composition is transitivity *)
|}.
(* The category laws (id_left, id_right, comp_assoc, comp_assoc_sym) and the
   [compose_respects] Proper are all discharged by the default obligation
   tactic: every goal is an [eq] between equality proofs, closed by reduction
   and reflexivity. *)

(* Every function [f : A → C] induces a functor out of the discrete category:
   an object [x] maps to [f x], and the unique morphism [e : x = y] maps to [id]
   transported along [e] (which is [id] whenever [e] is [eq_refl]). *)
Program Definition DiscreteCat_Functor
  {A : Type} {C : Category} (f : A → C) :
  DiscreteCat A ⟶ C := {|
  fobj := f;
  fmap := fun x y (e : x = y) => match e with eq_refl => id end
|}.
(* The functor laws ([fmap_respects], [fmap_id], [fmap_comp]) are all discharged
   by the default obligation tactic: on the discrete source every morphism is an
   equality proof, so each goal reduces to a trivial identity in [C]. *)

(* Sanity lemma bridging the two notions: the constructed category
   [DiscreteCat A] satisfies the [Discrete] predicate of Structure/Discrete.v —
   every morphism forces its endpoints equal and is the transported identity. *)
Lemma DiscreteCat_Discrete@{o h p} (A : Type@{o}) :
  Discrete (DiscreteCat@{o h p} A).
Proof.
  intros x y e.
  exists e.                     (* the equality witness is the morphism itself *)
  now destruct e.               (* [e ≈ rew e in eq_refl] by destructing [e] *)
Qed.
