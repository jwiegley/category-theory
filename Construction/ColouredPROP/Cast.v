Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.ColouredPROP.Signature.
Require Import Category.Construction.ColouredPROP.TermEq.
Require Import Category.Construction.ColouredPROP.Free.

From Coq Require Import Lists.List.
Import ListNotations.
From Coq Require Import Eqdep_dec.

Generalizable All Variables.

(** * Transport infrastructure for the free coloured PROP

    The free coloured PROP needs to talk about morphisms between
    objects whose colour words are PROPOSITIONALLY but not
    DEFINITIONALLY equal — e.g. [cs ++ []] and [cs], or
    [(x ++ y) ++ z] and [x ++ (y ++ z)].  List concatenation [app] is
    left-strict but not right-strict in Coq (exactly the asymmetry of
    [Nat.add] in the one-sorted donor [Construction/PROP/Cast.v]), so
    these boundary equations do not reduce definitionally and must be
    transported across.

    [CT_cast e] is the identity term, transported across an equality
    [e] of colour words.  Together with the associated rewrite lemmas
    it lets the Monoidal instance on [CFreeCat S] package up the
    structural isomorphisms (unitors, associator) for the cases where
    the boundary equality is not [eq_refl].

    This file merges the three cast-layer donors of the one-sorted
    spine into one:

      - the [T_cast] kit of [Construction/PROP/Cast.v] (UIP-free core
        plus the decidability-conditional UIP layer);
      - the tensor-cast fusion lemmas of
        [Construction/PROP/CastTensor.v];
      - the structural isomorphisms of
        [Construction/PROP/Structural.v].

    Deviation from the donor, by design: [nat] has the canonical
    decider [Nat.eq_dec], so the donor's UIP layer was unconditional.
    An arbitrary [Colour : Type] carries no such decider, so here
    every UIP-dependent lemma threads a colour-equality decider
    [Cdec] as an EXPLICIT argument, and uses
    [UIP_dec (list_eq_dec Cdec)] on colour words.  The UIP-free core
    (inverse laws, composition, naturality, tensor fusion) needs no
    decidability at all. *)

(** ** The cast term

    Identity, transported across [e : cs = ds].  Kept transparent (a
    plain [Definition] in [match] form): downstream files compute
    with it, and the structural isomorphisms below are built from it
    definitionally. *)
Definition CT_cast {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (e : cs = ds) : CTerm S cs ds :=
  match e in _ = k return CTerm S cs k with
  | eq_refl => CT_id cs
  end.

(** Cast at [eq_refl] is the literal identity. *)
Lemma CT_cast_refl {Colour : Type} {S : CSignature Colour}
  (cs : list Colour) :
  @CT_cast Colour S cs cs eq_refl = CT_id cs.
Proof. reflexivity. Qed.

(** Composing two casts gives a cast along the transitive equation. *)
Lemma CT_cast_compose {Colour : Type} {S : CSignature Colour}
  {cs ds es : list Colour} (e1 : cs = ds) (e2 : ds = es) :
  CTermEq S (CT_comp (CT_cast e2) (CT_cast e1)) (CT_cast (eq_trans e1 e2)).
Proof.
  destruct e1, e2.
  cbn.
  apply CTE_id_left.
Qed.

(** Casting along [e] after casting along [eq_sym e] is the identity
    on the TARGET word [ds]. *)
Lemma CT_cast_inv {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (e : cs = ds) :
  CTermEq S (CT_comp (CT_cast e) (CT_cast (eq_sym e))) (CT_id ds).
Proof.
  destruct e.
  cbn.
  apply CTE_id_left.
Qed.

(** Casting along [eq_sym e] after casting along [e] is the identity
    on the SOURCE word [cs]. *)
Lemma CT_cast_inv_sym {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (e : cs = ds) :
  CTermEq S (CT_comp (CT_cast (eq_sym e)) (CT_cast e)) (CT_id cs).
Proof.
  destruct e.
  cbn.
  apply CTE_id_left.
Qed.

(** Instantiation helper mirrored from the one-sorted donor
    (Construction/PROP/Cast.v): the hypothesis [Hfg] is the conclusion
    universally quantified over the boundary equation, so this lemma
    is a bare instantiation at [e] with no proof content of its own,
    and it is stated for endo-boundaries only.  It is NOT what
    discharges the Monoidal coherence obligations: the naturality
    squares of the unitors and the associator are proved in Monoidal.v
    via [CT_cast_id] / [CT_cast_irrelevant] (UIP on colour words,
    hence [Cdec]-conditional) together with Monoidal.v's [ceq_rect_*]
    transport bridges.  Kept for donor parity. *)
Lemma CT_cast_natural {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (e : cs = ds)
  (f : CTerm S cs cs) (g : CTerm S ds ds)
  (Hfg : forall (q : cs = ds),
           CTermEq S (CT_comp (CT_cast q) f)
                     (CT_comp g (CT_cast q))) :
  CTermEq S (CT_comp (CT_cast e) f) (CT_comp g (CT_cast e)).
Proof. apply Hfg. Qed.

(** Degenerate naturality at [eq_refl]: a [CT_cast eq_refl] is
    [CT_id], so it commutes with any morphism trivially. *)
Lemma CT_cast_natural_refl {Colour : Type} {S : CSignature Colour}
  {cs : list Colour} (f : CTerm S cs cs) :
  CTermEq S (CT_comp (CT_cast eq_refl) f) (CT_comp f (CT_cast eq_refl)).
Proof.
  cbn.
  apply CTE_trans with f.
  - apply CTE_id_left.
  - apply CTE_sym, CTE_id_right.
Qed.

(** ** Transport bridges for strict-PROP equations

    The strict right-unit, associativity, hexagon, and unit-braid
    axioms in [CTermEq] are stated in [eq_rect] transport form (over
    [app_nil_r] and [app_assoc]).  Below we expose small helpers for
    use when downstream proofs need to work with both ends of the
    transport. *)

(** Transport-spelling bridge: the [eq_rect] transport of a term
    along [e : cs = ds] over the codomain index equals the [match]
    (dependent pattern-match) spelling of the same transport.  Both
    sides are [CT_cast e] applied to [t]; this lemma just lets a
    proof switch between the [eq_rect] form used in [CTermEq]'s
    strict-PROP axioms and the [match] form used by [CT_cast].

    This is the standard "destruct the eq_rect" pattern.  This lemma
    and [CT_term_eq_rect_r_refl] below are exported kit with no
    in-tree consumer yet: the naturality proofs in Monoidal.v
    destruct their quantified boundary equations via the
    [ceq_rect_*] transport bridges instead. *)
Lemma CT_term_eq_rect_destruct {Colour : Type} {S : CSignature Colour}
  {cs ds : list Colour} (e : cs = ds) (t : CTerm S cs cs) :
  eq_rect cs (fun k => CTerm S cs k) t ds e
  = match e in _ = k return CTerm S cs k with
    | eq_refl => t
    end.
Proof. destruct e; reflexivity. Qed.

(** Dual: an [eq_rect_r] transport on the domain index reduces at
    [eq_refl] to the term itself.  More general transport shapes
    require a [destruct e] in context. *)
Lemma CT_term_eq_rect_r_refl {Colour : Type} {S : CSignature Colour}
  {cs : list Colour} (t : CTerm S cs cs) :
  eq_rect_r (fun k => CTerm S k cs) t (@eq_refl _ cs) = t.
Proof. reflexivity. Qed.

(** ** [CT_cast] interaction with [CT_tens]

    Bridge lemmas that the Monoidal instance on [CFreeCat S] will
    need to discharge naturality of the structural isomorphisms.
    [CT_tens] concatenates two boundary words; [CT_cast] rewrites a
    single boundary along a propositional equation.  The lemmas below
    all reduce the cast away by [destruct]-ing the boundary equation,
    after which the goal is closed by a primitive tensor/identity
    constructor of [CTermEq] ([CTE_tens_id], [CTE_id_left], or
    [CTE_id_right]).  None of them needs colour decidability. *)

(** Tensoring an identity with a cast on the right factor equals a
    single cast along the [++]-congruenced boundary equation.

    [(id_cs ⊕c CT_cast e) ≈ CT_cast (f_equal (cs ++ _) e)]

    The right-hand boundary equation [cs ++ a = cs ++ b] is [e]
    congruenced by left-concatenation of [cs]; at [eq_refl] it
    reduces to [eq_refl] and the goal becomes [CTE_tens_id]. *)
Lemma CT_tens_id_cast_left {Colour : Type} {S : CSignature Colour}
  {cs a b : list Colour} (e : a = b) :
  CTermEq S (CT_tens (CT_id cs) (CT_cast e))
            (CT_cast (f_equal (fun ks => cs ++ ks) e)).
Proof.
  destruct e.
  cbn.
  apply CTE_tens_id.
Qed.

(** Symmetric variant: cast on the LEFT, identity on the RIGHT. *)
Lemma CT_tens_cast_id_right {Colour : Type} {S : CSignature Colour}
  {a b ns : list Colour} (e : a = b) :
  CTermEq S (CT_tens (CT_cast e) (CT_id ns))
            (CT_cast (f_equal (fun ks => ks ++ ns) e)).
Proof.
  destruct e.
  cbn.
  apply CTE_tens_id.
Qed.

(** Tensor preserves identities: [id_cs ⊕c id_ds ≈ id_(cs ++ ds)].
    This is just the primitive [CTE_tens_id] constructor restated as
    a named lemma (no cast involved).  Together with the two
    [eq_refl]-collapse lemmas below ([CT_comp_cast_tens_left] and
    [CT_comp_tens_cast_right]) it is exported kit with no in-tree
    consumer yet. *)
Lemma CT_tens_id_id {Colour : Type} {S : CSignature Colour}
  (cs ds : list Colour) :
  CTermEq S (CT_tens (CT_id cs) (CT_id ds)) (CT_id (cs ++ ds)).
Proof. apply CTE_tens_id. Qed.

(** Composing a trivial [CT_cast eq_refl] (which is [CT_id]) onto a
    tensor is the identity operation.  [CT_cast eq_refl] reduces to
    [CT_id (ds1 ++ ds2)], so the composite collapses by left
    identity. *)
Lemma CT_comp_cast_tens_left {Colour : Type} {S : CSignature Colour}
  {cs1 ds1 cs2 ds2 : list Colour}
  (f : CTerm S cs1 ds1) (g : CTerm S cs2 ds2) :
  CTermEq S (CT_comp (CT_cast eq_refl) (CT_tens f g))
            (CT_tens f g).
Proof. cbn. apply CTE_id_left. Qed.

(** Dual: post-composing a trivial [CT_cast eq_refl] on the input
    side of a tensor collapses by right identity. *)
Lemma CT_comp_tens_cast_right {Colour : Type} {S : CSignature Colour}
  {cs1 ds1 cs2 ds2 : list Colour}
  (f : CTerm S cs1 ds1) (g : CTerm S cs2 ds2) :
  CTermEq S (CT_comp (CT_tens f g) (CT_cast eq_refl))
            (CT_tens f g).
Proof. cbn. apply CTE_id_right. Qed.

(** ** The UIP layer: proof irrelevance of boundary casts

    Proof-irrelevance for colour-word casts: any two proofs [e1 e2]
    of [cs = ds] give equal cast terms.

    A colour type with decidable equality gives decidable equality on
    colour words by [list_eq_dec], hence Uniqueness of Identity
    Proofs (UIP) on [list Colour] without any axioms — proved by
    [Eqdep_dec.UIP_dec (list_eq_dec Cdec)].  This lets us replace one
    proof of a boundary equation by another inside [CT_cast].

    The decider [Cdec] is threaded as an EXPLICIT argument rather
    than assumed globally: the UIP-free core
    above stays available for arbitrary colour types, and every
    downstream file states exactly which of its results are
    decidability-conditional.  Downstream instance sites must fix ONE
    canonical [Cdec] per colour type, since different deciders give
    different (albeit provably equal) cast-irrelevance proofs. *)
Lemma CT_cast_irrelevant {Colour : Type} {S : CSignature Colour}
  (Cdec : forall c d : Colour, {c = d} + {c <> d})
  {cs ds : list Colour} (e1 e2 : cs = ds) :
  CT_cast (S := S) e1 = CT_cast (S := S) e2.
Proof.
  rewrite (UIP_dec (list_eq_dec Cdec) e1 e2).
  reflexivity.
Qed.

(** Special case: any cast along an equation of [cs = cs] is the
    identity, because [eq_refl cs] is the canonical proof of
    [cs = cs] and [CT_cast eq_refl = CT_id cs] reduces
    definitionally. *)
Lemma CT_cast_id {Colour : Type} {S : CSignature Colour}
  (Cdec : forall c d : Colour, {c = d} + {c <> d})
  {cs : list Colour} (e : cs = cs) :
  CT_cast (S := S) e = CT_id cs.
Proof.
  rewrite (CT_cast_irrelevant Cdec e eq_refl).
  reflexivity.
Qed.

(** * Structural isomorphisms for the free coloured PROP *)

(* nLab: https://ncatlab.org/nlab/show/monoidal+category
   nLab: https://ncatlab.org/nlab/show/associator
   Wikipedia: https://en.wikipedia.org/wiki/Monoidal_category
   Wikipedia: https://en.wikipedia.org/wiki/Coherence_condition

   Package the three structural maps of a monoidal category — left
   unitor, right unitor, associator — as isomorphisms in [CFreeCat S]
   using [CT_cast].

   "Structural" here is the monoidal-coherence sense (the unitors and
   associator of nLab/Mac Lane), not the permutation sense: a
   coloured PROP also has the symmetric structural maps built from
   braids and identities (see [CT_braid] in Signature.v), which are a
   separate family.

   The boundary equations are pure [list] facts:

     [app_nil_l cs]    : [] ++ cs = cs                  (left unit)
     [app_nil_r cs]    : cs ++ [] = cs                  (right unit)
     [app_assoc x y z] : x ++ (y ++ z) = (x ++ y) ++ z  (associator)

   Because [app] is left-strict in Coq, the left-unit boundary
   EQUATION [[] ++ cs = cs] holds definitionally; but [app_nil_l] is
   a Qed-opaque stdlib proof, so the left unitor's cast is a stuck
   [match] that does NOT reduce to [CT_id] by computation (it is
   eliminated via [CT_cast_id] under [Cdec] in Monoidal.v, exactly
   like the right unitor's and associator's genuinely propositional
   casts).  Note the stdlib orientation of [app_assoc] (right-to-left
   reassociation, same as [Nat.add_assoc]), so the associator's [to]
   is the [eq_sym] cast.

   The isomorphisms are built with explicit [Build_Isomorphism]
   applications: the two inverse-law fields are exactly
   [CT_cast_inv] / [CT_cast_inv_sym] instances, since composition in
   [CFreeCat S] is [CT_comp], identity is [CT_id], and the
   hom-equivalence is [CTermEq S], all definitionally. *)

(** Left unitor [[] ++ cs ≅ cs] in [CFreeCat S].  The boundary
    equation [[] ++ cs = cs] is definitional, but [app_nil_l] is a
    Qed-opaque stdlib proof, so [CT_cast (app_nil_l cs)] is a stuck
    [match], not [CT_id cs]; Monoidal.v eliminates it with
    [CT_cast_id] under [Cdec].  (The proof term is deliberately kept
    as [app_nil_l]: Instance.v compares these structural maps by the
    same proof term.) *)
Definition CFreeCat_unit_left {Colour : Type} (S : CSignature Colour)
  (cs : list Colour) :
  @Isomorphism (CFreeCat S) ([] ++ cs) cs :=
  @Build_Isomorphism (CFreeCat S) ([] ++ cs) cs
    (CT_cast (app_nil_l cs))
    (CT_cast (eq_sym (app_nil_l cs)))
    (CT_cast_inv (app_nil_l cs))
    (CT_cast_inv_sym (app_nil_l cs)).

(** Right unitor [cs ++ [] ≅ cs] in [CFreeCat S].  [app_nil_r] is
    propositional, not definitional, so the cast is along a
    non-trivial equation. *)
Definition CFreeCat_unit_right {Colour : Type} (S : CSignature Colour)
  (cs : list Colour) :
  @Isomorphism (CFreeCat S) (cs ++ []) cs :=
  @Build_Isomorphism (CFreeCat S) (cs ++ []) cs
    (CT_cast (app_nil_r cs))
    (CT_cast (eq_sym (app_nil_r cs)))
    (CT_cast_inv (app_nil_r cs))
    (CT_cast_inv_sym (app_nil_r cs)).

(** Associator [(x ++ y) ++ z ≅ x ++ (y ++ z)] in [CFreeCat S].
    Likewise propositional via [app_assoc].  Oriented
    [to : (x ++ y) ++ z ~> x ++ (y ++ z)], matching the nLab
    associator α : (A⊗B)⊗C → A⊗(B⊗C); with the stdlib orientation of
    [app_assoc] this makes [to] the [eq_sym] cast. *)
Definition CFreeCat_tensor_assoc {Colour : Type} (S : CSignature Colour)
  (x y z : list Colour) :
  @Isomorphism (CFreeCat S) ((x ++ y) ++ z) (x ++ (y ++ z)) :=
  @Build_Isomorphism (CFreeCat S) ((x ++ y) ++ z) (x ++ (y ++ z))
    (CT_cast (eq_sym (app_assoc x y z)))
    (CT_cast (app_assoc x y z))
    (CT_cast_inv_sym (app_assoc x y z))
    (CT_cast_inv (app_assoc x y z)).

Arguments CFreeCat_unit_left {Colour} S cs : assert.
Arguments CFreeCat_unit_right {Colour} S cs : assert.
Arguments CFreeCat_tensor_assoc {Colour} S x y z : assert.
