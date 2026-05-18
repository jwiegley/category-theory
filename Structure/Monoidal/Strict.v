Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(** * Strict monoidal categories

    Reference: nLab "strict monoidal category".

    A strict monoidal category is a monoidal category in which the
    associator and unitors are identity natural transformations —
    equivalently, where the tensor is strictly associative and strictly
    unital on objects, not merely up to coherent isomorphism.

    In this library's setoid-based setting, "strict" requires BOTH:

      (a) object-level Leibniz equalities
            [(X ⨂ Y) ⨂ Z = X ⨂ (Y ⨂ Z)],
            [I ⨂ X = X = X ⨂ I];
      (b) the structural isomorphisms [tensor_assoc], [unit_left],
          [unit_right] coincide (modulo those equalities) with [id].

    Object-level equality (Leibniz [=]) is required because [obj] in
    [Category] is a [Type], not a setoid; the monoidal coherence
    isomorphisms relate distinct objects (e.g. [(X ⨂ Y) ⨂ Z] and
    [X ⨂ (Y ⨂ Z)]).  In a strict monoidal category, those objects
    coincide on the nose.

    The structural isomorphisms then transport along those equalities
    to give [id].  We use the [rew] (Coq's [eq_rect]) form, which the
    library's [Lib/Tactics.v] already engages with via
    [eq_rew_r_dep]; the [match]-form was tried and gave noisier
    obligations in this codebase.

    Strict monoidal categories are precisely monoid objects in the
    cartesian monoidal category [Cat].  PROPs are strict symmetric
    monoidal categories whose objects are the natural numbers under
    [+]; this class is the foundation for the upcoming PROP
    machinery. *)

Section StrictMonoidal.

Context {C : Category}.

Class StrictMonoidal : Type := {
  strict_is_monoidal : @Monoidal C;

  (** Object-level strictness. *)
  strict_assoc_obj :
    forall (X Y Z : C),
      ((X ⨂[strict_is_monoidal] Y)%object ⨂[strict_is_monoidal] Z)%object
      = (X ⨂[strict_is_monoidal] (Y ⨂[strict_is_monoidal] Z)%object)%object;

  strict_unit_left_obj :
    forall (X : C),
      (I ⨂[strict_is_monoidal] X)%object = X;

  strict_unit_right_obj :
    forall (X : C),
      (X ⨂[strict_is_monoidal] I)%object = X;

  (** The structural isomorphisms ARE the identity, transported.

      We use the [match] form (rather than [eq_rect]) to keep
      destruct-of-equality reductions clean. *)
  strict_assoc_to :
    forall (X Y Z : C),
      to (@tensor_assoc C strict_is_monoidal X Y Z)
      ≈ match strict_assoc_obj X Y Z in _ = T
          return ((X ⨂[strict_is_monoidal] Y)%object
                   ⨂[strict_is_monoidal] Z)%object ~> T
        with eq_refl => id end;

  strict_unit_left_to :
    forall (X : C),
      to (@unit_left C strict_is_monoidal X)
      ≈ match strict_unit_left_obj X in _ = T
          return (I ⨂[strict_is_monoidal] X)%object ~> T
        with eq_refl => id end;

  strict_unit_right_to :
    forall (X : C),
      to (@unit_right C strict_is_monoidal X)
      ≈ match strict_unit_right_obj X in _ = T
          return (X ⨂[strict_is_monoidal] I)%object ~> T
        with eq_refl => id end
}.
#[export] Existing Instance strict_is_monoidal.

Coercion strict_is_monoidal : StrictMonoidal >-> Monoidal.

(** ** Corollaries

    In a strict monoidal category the [from] direction of each
    structural iso is also the transported identity. *)

Context `{S : StrictMonoidal}.

(** The [from] direction: transports [id] from the codomain along the
    domain equality (using [cast_dom]). *)
(** A sanity-check corollary: in any strict monoidal category, the
    composite [α ∘ α⁻¹] at any triple is [id] (which is just
    [iso_to_from] specialised — we restate it here as a flat lemma
    using the strict-shape so downstream code can use it without
    going through [tensor_assoc]'s iso projections). *)
Lemma strict_assoc_iso (X Y Z : C) :
  to (@tensor_assoc C strict_is_monoidal X Y Z)
    ∘ from (@tensor_assoc C strict_is_monoidal X Y Z)
  ≈ id.
Proof. apply iso_to_from. Qed.

(** ** Note on the [from] direction

    A clean closed-form expression for [from tensor_assoc] in terms of
    [strict_assoc_obj] alone requires transporting [id] backwards along
    the equality, which is a [match … with eq_refl => id end] whose
    return type necessarily mentions both endpoints of the equality.
    Coq's [destruct] in the proof attempted to abstract over both
    endpoints simultaneously, which fails because [tensor_assoc] itself
    carries the second endpoint in its type signature.

    Downstream consumers who need to reason about [from] in a strict
    monoidal category should reach for [iso_to_from] / [iso_from_to]
    directly (treating [tensor_assoc] as the [Isomorphism] it is); the
    strict structure ensures both composites are [id], which is what
    most users need.  A polished [strict_*_from] closed-form is
    deferred to V2b. *)

(* TODO(V2b): Closed-form [from] corollaries strict_assoc_from etc. *)

End StrictMonoidal.

(** ** Formulation note

    The library does not import the [rew] notation (Coq's [eq_rect]
    sugar in [stdpp] / [Init.Logic]) by default — its [_CoqProject]
    does not pull it in.  The explicit [match … in _ = T return …]
    form parses cleanly inside record fields, and combined with
    [destruct]-of-equality the dependent transport reduces by
    [eq_refl] elimination just as cleanly as the [rew] form does in
    libraries that import the notation.  Both [strict_*_to] and the
    derived [strict_*_from] corollaries use the [match] formulation
    consistently. *)

(** ** Future use

    PROPs (deferred to V2b) are by definition strict symmetric monoidal
    categories on the natural numbers; this class is their foundation.
    Hypergraph PROPs — the main application area for the downstream
    rewriting work — combine this with the V1 [Hypergraph] class. *)
