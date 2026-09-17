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
   witness. This is the left adjoint at the level of a single functor; the
   adjunction itself is [Disc_Objects_Adjunction] in Instance/Cat/Objects.v.
   NOTE THE AMBIENT: it is [Coq ⟶ StrictCat], not `Set ⟶ Cat`. That
   file proves [objects_not_functorial_over_Cat]: over [Cat] the swap
   endofunctor of [Indiscrete bool] is naturally isomorphic to the
   identity while moving every object, so no objects functor into a
   target comparing object maps by LEIBNIZ equality exists there. An
   isomorphism-setoid one does; the strict reading is the exercise's
   choice. *)

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
   transported along [e] (which is [id] whenever [e] is [eq_refl]).

   THE BINDERS ARE LOAD-BEARING.  An earlier revision declared this with bare
   [{A : Type} {C : Category}]; universe minimization then instantiated the
   shape's hom and proof levels at [Set], so the printed type carried
   [DiscreteCat@{u Set Set} A ⟶ C].  Because [Limit] and [IsLimitCone]
   identify the shape's hom-and-proof universe with the AMBIENT's (unlike
   [Cone], which keeps them apart), that [Set] propagated into the statement
   of every limit over a discrete diagram — [iprod], [Complete] applied to a
   discrete shape, and thence [GAFT] and [representability_theorem], which
   printed [Category@{u1 Set Set}] and refused instantiation at any category
   whose homs live above [Set].  Annotating here, on the model of
   [DiscreteCat_Functor'] (Structure/Limit/Comparison.v:535), leaves the
   shape's levels free; the trailing [+] allows the auxiliary universes that
   [Program]'s obligations introduce.  The measured signature is

     DiscreteCat_Functor@{o h p uo uh up u} :
     ∀ {A : Type@{o}} {C : Category@{uo uh up}},
     (A → obj) → Functor@{o h p uo uh up}
     (* o h p uo uh up u |= up < u / h <= p / h <= uh / h <= up
                            / p <= up / uh <= up / … *)

   — no literal [Set] anywhere. *)
Program Definition DiscreteCat_Functor@{o h p uo uh up +}
  {A : Type@{o}} {C : Category@{uo uh up}} (f : A → C) :
  DiscreteCat@{o h p} A ⟶ C := {|
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
