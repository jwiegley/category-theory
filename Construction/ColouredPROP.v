Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Structure.Monoidal.Hypergraph.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * Coloured PROPs

    Reference: nLab "coloured PROP" (also known as "many-sorted PROP" or
    "typed PROP"); Lack–Sobocinski "Adhesive and quasiadhesive
    categories" §7; Bonchi–Sobocinski–Zanasi "A categorical semantics
    of signal flow graphs" §4.

    A coloured PROP is the natural many-sorted generalisation of a
    PROP.  Fix a set [Colour : Type] of "wire types".  Objects of the
    PROP are LISTS of colours rather than natural numbers; tensor is
    list concatenation rather than addition; the monoidal unit is the
    empty list.  In a PROP all wires are interchangeable; in a coloured
    PROP they carry a type so that morphisms have shape-typed
    signatures.

    Coloured PROPs are the natural setting for tensor-shape-aware
    rewriting: a "transpose" generator on rank-3 inputs is a different
    morphism from the rank-4 version, where the dimensions appear in
    the colour-list signature.

    The class structure mirrors [PROP] (`Construction/PROP.v`) with
    [nat] replaced by [list Colour] and [+] replaced by [++]. *)

Section ColouredPROP.

Context (Colour : Type).

Class ColouredPROP : Type := {
  cprop_cat : Category;

  cprop_strict : @StrictMonoidal cprop_cat;
  cprop_symmetric : @SymmetricMonoidal cprop_cat;

  (** Coherence between the two [Monoidal] paths — see the analogous
      [prop_monoidal_coherence] in [Construction/PROP.v] for
      motivation. *)
  cprop_monoidal_coherence :
    (@strict_is_monoidal cprop_cat cprop_strict)
    = (@braided_is_monoidal cprop_cat
         (@symmetric_is_braided cprop_cat cprop_symmetric));

  (** The canonical object correspondence: every list of colours names
      an object of [cprop_cat], with the empty list the monoidal unit
      and concatenation reflecting tensor. *)
  cprop_of_list : list Colour -> @obj cprop_cat;

  cprop_unit_nil :
    @I cprop_cat (@strict_is_monoidal cprop_cat cprop_strict)
    = cprop_of_list nil;

  cprop_tensor_app : forall (cs ds : list Colour),
    ((cprop_of_list cs) ⨂[@strict_is_monoidal cprop_cat cprop_strict]
     (cprop_of_list ds))%object
    = cprop_of_list (cs ++ ds)
}.

#[export] Existing Instance cprop_strict.
#[export] Existing Instance cprop_symmetric.

Coercion cprop_cat : ColouredPROP >-> Category.

End ColouredPROP.

Arguments ColouredPROP Colour : assert.
Arguments cprop_cat {Colour} _.
Arguments cprop_strict {Colour} _.
Arguments cprop_symmetric {Colour} _.
Arguments cprop_monoidal_coherence {Colour} _.
Arguments cprop_of_list {Colour _} _.
Arguments cprop_unit_nil {Colour _}.
Arguments cprop_tensor_app {Colour _} _ _.

(** ** Smart accessors *)

Section ColouredPROPLemmas.

Context {Colour : Type}.
Context (P : ColouredPROP Colour).

(** The Coloured-PROP-object indexed by colour list [cs]. *)
Notation "'⟦' cs '⟧c'" := (cprop_of_list (ColouredPROP := P) cs)
  (at level 0, format "⟦ cs ⟧c").

(** Sanity: the unit object of [P] is [⟦[]⟧c]. *)
Lemma cprop_I_eq_nil : @I P _ = ⟦nil⟧c.
Proof. exact (@cprop_unit_nil Colour P). Qed.

(** Sanity: tensor on objects is list concatenation. *)
Lemma cprop_tensor_eq_app (cs ds : list Colour) :
  (⟦cs⟧c ⨂ ⟦ds⟧c)%object = ⟦cs ++ ds⟧c.
Proof. exact (cprop_tensor_app cs ds). Qed.

(** Singleton-colour wire: [⟦[c]⟧c] is the canonical 1-colour object. *)
Definition wire (c : Colour) : @obj P := ⟦[c]⟧c.

End ColouredPROPLemmas.

Arguments wire {Colour P} c.

(** ** Hypergraph Coloured PROPs

    Analogous to [HypergraphPROP]: a [ColouredPROP] whose underlying
    symmetric monoidal category carries a [Hypergraph] instance.
    Every wire-list carries a special commutative Frobenius algebra
    coherent under concatenation. *)

Class HypergraphColouredPROP {Colour : Type} : Type := {
  hcprop : ColouredPROP Colour;

  hcprop_hyper : @Hypergraph
                   (@cprop_cat Colour hcprop)
                   (@cprop_symmetric Colour hcprop)
}.

Arguments HypergraphColouredPROP Colour : assert.

#[export] Existing Instance hcprop_hyper.

Coercion hcprop : HypergraphColouredPROP >-> ColouredPROP.

(** ** Discussion: relationship to plain PROPs

    A [PROP] is the special case of [ColouredPROP unit] (one colour).
    The wire-list [list unit] is in bijection with [nat] via length,
    so [cprop_of_list (repeat tt n)] corresponds to [prop_of_nat n]
    and concatenation corresponds to addition.

    Formalising that correspondence as a functor / equivalence would
    show that coloured PROPs are a strict generalisation, but we
    leave the formal bridge as a downstream construction since the
    two presentations are typically used in different application
    domains. *)
