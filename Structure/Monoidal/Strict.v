Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.

Generalizable All Variables.

(** * Strict monoidal categories

    nLab: https://ncatlab.org/nlab/show/strict+monoidal+category
    Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category#Strict_monoidal_category

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
    to give [id].  We use the explicit [match … in _ = T return …]
    form (Coq's primitive dependent elimination on equality), rather
    than the [rew]/[eq_rect] notation, which the library's [_CoqProject]
    does not pull in.  See the "Formulation note" at the end of the file
    for the rationale; both the [strict_*_to] fields and the derived
    [strict_*_from] corollaries use the [match] form consistently.

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

(* A sanity-check corollary: in any strict monoidal category, the
   composite [α ∘ α⁻¹] at any triple is [id] (which is just
   [iso_to_from] specialised — we restate it here as a flat lemma
   using the strict-shape so downstream code can use it without
   going through [tensor_assoc]'s iso projections).  The closed-form
   [from] direction of each structural iso (the transported identity
   along the symmetric equality) is given by the [strict_*_from]
   corollaries below. *)
Lemma strict_assoc_iso (X Y Z : C) :
  to (@tensor_assoc C strict_is_monoidal X Y Z)
    ∘ from (@tensor_assoc C strict_is_monoidal X Y Z)
  ≈ id.
Proof. apply iso_to_from. Qed.

(** ** Closed-form [from] corollaries

    The [from] direction of each structural isomorphism is, like its
    [to] direction, the transported identity — but transported along the
    SYMMETRIC equality (so that the domain and codomain of the resulting
    morphism are swapped).

    The phrasing uses a single match-and-return-on-the-domain (rather
    than a doubly-dependent [a ~> b]).  Concretely, given
    [e : a = b], the morphism [b ~> a] is given by
    [match e in _ = T return T ~> a with eq_refl => id end]:
    at [eq_refl], [T = b] reduces to [a] by elimination, and the branch
    [id : a ~> a] inhabits the resulting type. *)

(** A general lemma: given an iso [phi : a ≅ b] and an equality [e : a = b]
    such that [to phi] equals the transported identity along [e], the
    [from phi] equals the transported identity along [e] in the other
    direction.

    This is purely group-theoretic — once you know [to phi] is "id along
    e", uniqueness of inverses in [Isomorphism] forces [from phi] to be
    "id along the symmetric e". *)
Lemma transported_iso_from
  {C' : Category} {a b : C'} (e : a = b) (phi : a ≅[C'] b)
  (Hto : to phi ≈ match e in _ = T return a ~> T with eq_refl => id end) :
  from phi ≈ match e in _ = T return T ~> a with eq_refl => id end.
Proof.
  pose proof (iso_to_from phi) as Htf.
  rewrite Hto in Htf.
  destruct e.
  simpl in Htf |- *.
  rewrite id_left in Htf.
  exact Htf.
Qed.

Lemma strict_assoc_from (X Y Z : C) :
  from (@tensor_assoc C strict_is_monoidal X Y Z)
  ≈ match strict_assoc_obj X Y Z in _ = T
      return T ~> ((X ⨂[strict_is_monoidal] Y)%object
                    ⨂[strict_is_monoidal] Z)%object
    with eq_refl => id end.
Proof.
  apply (transported_iso_from
           (strict_assoc_obj X Y Z)
           (@tensor_assoc C _ X Y Z)).
  apply strict_assoc_to.
Qed.

Lemma strict_unit_left_from (X : C) :
  from (@unit_left C strict_is_monoidal X)
  ≈ match strict_unit_left_obj X in _ = T
      return T ~> (I ⨂[strict_is_monoidal] X)%object
    with eq_refl => id end.
Proof.
  apply (transported_iso_from
           (strict_unit_left_obj X)
           (@unit_left C _ X)).
  apply strict_unit_left_to.
Qed.

Lemma strict_unit_right_from (X : C) :
  from (@unit_right C strict_is_monoidal X)
  ≈ match strict_unit_right_obj X in _ = T
      return T ~> (X ⨂[strict_is_monoidal] I)%object
    with eq_refl => id end.
Proof.
  apply (transported_iso_from
           (strict_unit_right_obj X)
           (@unit_right C _ X)).
  apply strict_unit_right_to.
Qed.

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
