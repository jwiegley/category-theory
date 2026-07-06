Require Import Category.Lib.

From Coq Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** * Signatures over coloured PROPs *)

(* nLab:      https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   A COLOURED SIGNATURE is the data of a many-sorted symmetric monoidal
   theory: a family of typed generators indexed by their input/output
   boundary.  Where a one-sorted PROP signature ([Construction/PROP/
   Signature.v]) indexes generators by a pair of natural numbers — how
   MANY wires enter and leave — a coloured signature over a set
   [Colour] of wire types indexes them by pairs of LISTS of colours:
   which wire types enter, in which order, and which leave.  It is a
   family of types indexed by pairs of colour words — an object of
   [Set^(W x W)] (here in [Type]) where [W := list Colour] is the free
   monoid of finite words over [Colour] — the underlying object of the
   free-coloured-PROP adjunction.

   Concretely [Sig cs ds] is the [Type] of generator names whose input
   boundary is the colour list [cs] and whose output boundary is [ds].
   In examples:

     - The empty signature [Empty_CSig] presents a coloured PROP with
       NO non-structural generators: its free coloured PROP has as
       morphisms exactly the structural rearrangements (identities,
       composites, tensors, braids), i.e. colour-preserving
       permutations of wires.
     - A typed circuit signature over [Colour := {wire; clk}] might
       have a generator in [Sig [wire; wire] [wire]] (a join that
       needs two data wires), one in [Sig [clk; wire] [wire]] (a
       latch), one in [Sig [] [clk]] (a clock source), etc.  The
       colour discipline makes ill-typed pluggings unrepresentable.

   The signature is the INPUT to the free construction: given [S],
   the free coloured PROP on [S] is the strict symmetric monoidal
   category whose morphisms are [S]-labelled typed string diagrams
   modulo the strict-SMC axioms.  This file defines the signatures,
   the raw [CTerm] syntax, and smart constructors; the equational
   theory lives in [Construction/ColouredPROP/TermEq.v] and the free
   category in [Construction/ColouredPROP/Free.v]. *)

Section CSignature.

Context (Colour : Type).

Definition CSignature : Type := list Colour -> list Colour -> Type.

(** ** Examples *)

(** The empty signature.  Useful as a base case: the free coloured
    PROP on [Empty_CSig] is the coloured permutation category. *)
Definition Empty_CSig : CSignature :=
  fun _ _ => Empty_set.

(** The signature of a single generator [g : ms -> ns] (with input
    boundary [ms] and output boundary [ns]), and no other generators.

    Deviation from the one-sorted donor: [Single_Sig] tested arities
    with [Nat.eqb], which presumes decidable equality.  Colour lists
    over an arbitrary [Colour : Type] have no such test, so the
    coloured form is PROOF-CARRYING instead: an inhabitant of
    [Single_CSig ms ns xs ys] is a pair of equality proofs, with
    canonical inhabitant [(eq_refl, eq_refl)] at boundary [(ms, ns)].
    This is decidability-free and definitionally empty nowhere — it
    is provably empty exactly off the diagonal. *)
Definition Single_CSig (ms ns : list Colour) : CSignature :=
  fun xs ys => ((xs = ms) * (ys = ns))%type.

(** ** Operations on signatures

    Sum (disjoint union) of two signatures: a generator is a generator
    of one or the other.  This builds complex signatures from smaller
    ones — e.g. a typed monoid-and-comonoid signature is the sum of
    the two single-generator families. *)
Definition Sum_CSig (S T : CSignature) : CSignature :=
  fun cs ds => (S cs ds + T cs ds)%type.

(** Sub-signature: an embedding into a larger signature, preserving
    boundaries on the nose.  Inhabited by [inl] / [inr] / nested
    projection chains. *)
Definition CSubSig (Sub Sup : CSignature) : Type :=
  forall cs ds, Sub cs ds -> Sup cs ds.

(** The identity sub-signature. *)
Definition CSubSig_id (S : CSignature) : CSubSig S S :=
  fun _ _ g => g.

(** Sub-signature composition. *)
Definition CSubSig_compose {S T U : CSignature}
  (h2 : CSubSig T U) (h1 : CSubSig S T) : CSubSig S U :=
  fun cs ds g => h2 cs ds (h1 cs ds g).

End CSignature.

Arguments CSignature Colour : assert.
Arguments Empty_CSig {Colour} _ _.
Arguments Single_CSig {Colour} ms ns _ _.
Arguments Sum_CSig {Colour} S T _ _.
Arguments CSubSig {Colour} Sub Sup.
Arguments CSubSig_id {Colour} S.
Arguments CSubSig_compose {Colour S T U} h2 h1.

(** * Raw terms over a coloured signature

    The syntactic representation of morphisms in the free coloured
    PROP on a signature [S].  A term of type [CTerm S cs ds] is a
    typed string-diagram expression whose input wires carry the
    colours [cs] (in order) and whose output wires carry [ds], built
    up from:

      - identity wires [CT_id cs]
      - braids [CT_braid cs ds] (the canonical "block braiding" that
        crosses a [cs]-typed bundle past a [ds]-typed bundle)
      - sequential composition [CT_comp]
      - parallel composition (tensor) [CT_tens]
      - signature-supplied generators [CT_gen]

    This defines just the SYNTAX — no equational theory.  Boundaries
    propagate through the constructors by list operations: tensor
    concatenates ([++] replacing the donor's [+] on [nat]), and the
    braid has boundary [(cs ++ ds, ds ++ cs)].

    The inductive lives in its own section, which closes here before
    any lemma about it; downstream files always state results as
    [CTerm S cs ds] with the signature [S] explicit. *)

Section CTerm.

Context {Colour : Type}.
Context (S : CSignature Colour).

Inductive CTerm : list Colour -> list Colour -> Type :=
  | CT_id (cs : list Colour) : CTerm cs cs
  | CT_braid (cs ds : list Colour) : CTerm (cs ++ ds) (ds ++ cs)
  | CT_comp {cs ds es} : CTerm ds es -> CTerm cs ds -> CTerm cs es
  | CT_tens {cs1 ds1 cs2 ds2} :
      CTerm cs1 ds1 -> CTerm cs2 ds2 -> CTerm (cs1 ++ cs2) (ds1 ++ ds2)
  | CT_gen {cs ds} : S cs ds -> CTerm cs ds.

End CTerm.

Arguments CT_id    {Colour S} cs.
Arguments CT_braid {Colour S} cs ds.
Arguments CT_comp  {Colour S cs ds es} _ _.
Arguments CT_tens  {Colour S cs1 ds1 cs2 ds2} _ _.
Arguments CT_gen   {Colour S cs ds} _.

Declare Scope cterm_scope.
Delimit Scope cterm_scope with cterm.

Notation "g ⊙c f" := (CT_comp g f)
  (at level 40, left associativity) : cterm_scope.
Notation "f ⊕c g" := (CT_tens f g)
  (at level 30, right associativity) : cterm_scope.

(** ** Smart constructors *)

(** The "swap" braid on two single typed wires.  Note that
    [[c] ++ [d]] is definitionally [[c; d]], so this term also
    inhabits [CTerm S [c; d] [d; c]] on the nose. *)
Definition CT_swap {Colour} {S : CSignature Colour} (c d : Colour) :
  CTerm S ([c] ++ [d]) ([d] ++ [c]) :=
  CT_braid [c] [d].

(** Identity on a single typed wire.  Named [cwire] to steer clear of
    the [wire] projection of [Construction/ColouredPROP.v]'s supply
    vocabulary. *)
Definition cwire {Colour} {S : CSignature Colour} (c : Colour) :
  CTerm S [c] [c] :=
  CT_id [c].

(** The empty term: no input wires, no output wires — the monoidal
    unit's identity. *)
Definition CT_nothing {Colour} {S : CSignature Colour} : CTerm S [] [] :=
  CT_id [].

(* NOTE: there is deliberately no analogue of the donor's [T_inj]
   here.  Relabelling a term along a sub-signature embedding is the
   computing fixpoint [CT_map] of [Construction/ColouredPROP/
   Relabel.v] from day one — in the one-sorted development [T_inj]
   was superseded by [T_map], and the coloured spine skips the
   intermediate step. *)
