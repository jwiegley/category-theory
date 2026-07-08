Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Braided.
Require Import Category.Structure.Monoidal.Symmetric.
Require Import Category.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.
Require Import Category.Functor.Structure.Monoidal.Strict.
Require Import Category.Functor.Structure.Monoidal.Braided.
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

(** * Base change: reindexing coloured PROPs along a colour function *)

(* nLab: https://ncatlab.org/nlab/show/base+change
   nLab: https://ncatlab.org/nlab/show/restriction+of+scalars
   nLab: https://ncatlab.org/nlab/show/PROP
   Wikipedia: https://en.wikipedia.org/wiki/PROP_(category_theory)

   A function [f : Colour → Colour'] between colour sets induces a
   monoid homomorphism [map f : list Colour → list Colour'] between the
   free monoids of colour words, and along it two constructions:

   1.  RESTRICTION OF SCALARS ([ColouredPROP_restrict]): every coloured
       PROP [P] over [Colour'] becomes a coloured PROP over [Colour] on
       the SAME underlying category, by reading the object
       correspondence through [map f]:

         cprop_of_list cs := cprop_of_list (map f cs).

       Only the object-naming data changes; the category, its strict
       and symmetric monoidal structures, and their coherence are
       carried over verbatim, so the [cprop_monoidal_coherence] field
       — the fragile one, per the discussion in [Construction/PROP.v]
       — is P's own proof, untouched.  The unit condition holds
       because [map f [] ≡ []] is definitional, and the tensor
       condition is P's own [cprop_tensor_app] composed with the image
       of [map_app f cs ds : map f (cs ++ ds) = map f cs ++ map f ds]
       — the one genuinely propositional seam in the whole
       construction (stdlib's [map_app] is opaque).

   2.  THE BASE-CHANGE FUNCTOR ([BaseChangeF]): a signature morphism
       OVER [f] — a boundary-reindexing generator map

         h : ∀ cs ds, S cs ds → S' (map f cs) (map f ds)

       ([CSigMap]) — induces a strict symmetric monoidal functor
       [CFreeCat S ⟶ CFreeCat S'] between the free coloured PROPs,
       acting on objects by [map f] and sending each generator [g] to
       [CT_gen (h _ _ g)].

   ** Design: the functor is built THROUGH the universal property

   Rather than writing a fresh term-recursion and re-proving the
   19-case [CTermEq] soundness induction, [BaseChangeF] is one
   instantiation of the free coloured PROP's universal property
   ([Construction/ColouredPROP/Universal.v]): the target of the
   interpretation is the RESTRICTION of [FreeColouredPROP S' C'dec]
   along [f].  In that restriction the hom-set
   [⟦cs⟧ ~> ⟦ds⟧] IS [CTerm S' (map f cs) (map f ds)] on the nose, so
   the valuation [basechange_val := fun _ _ g => CT_gen (h _ _ g)]
   typechecks with no casts, and [CInterpF] delivers the functor
   together with its entire monoidal tower — [CInterpF_Monoidal] /
   [CInterpF_Strict] / [CInterpF_Braided] / [CInterpF_Symmetric] /
   [CInterpF_SymmetricStrict] instantiate to the [BaseChangeF_*]
   records below — and, downstream, its functoriality laws come from
   the uniqueness theorem [cinterp_unique] (see
   [Construction/ColouredPROP/BaseChange/Laws.v]) rather than from
   fresh inductions.

   Because [cinterp] COMPUTES on constructors, the functor's action is
   definitional where it matters: objects go to [map f cs], generators
   to [CT_gen (h _ _ g)], identities to identities and composites to
   composites, each machine-checked by an [eq_refl] [Example] below.

   ** The strictness comparisons are NOT all reflexivity

   [strict_pure_obj] of [BaseChangeF_Strict] is [eq_refl] (the unit
   colour word is fixed by [map f] definitionally), but
   [strict_ap_obj cs ds] is the [map_app]-shaped composite

     eq_trans eq_refl (f_equal (fun ks => ks) (eq_sym (map_app f cs ds)))

   and CANNOT be [eq_refl]: for variable [cs], the colour words
   [map f cs ++ map f ds] and [map f (cs ++ ds)] are propositionally
   but not definitionally equal.  This is exactly the seam that the
   [hom_cast]-conjugated functoriality statements of
   [BaseChange/Laws.v] have to thread, so it is pinned here by
   [Example]s at its source.

   ** Deciders (D2 discipline)

   Two colour deciders circulate, one per colour type: [Cdec] for
   [Colour] (naming the source's shared [Monoidal] record
   [CFreeCat_Monoidal S Cdec]) and [C'dec] for [Colour'] (naming the
   target's, and supplying the [ObjDecEq] side condition of the
   universal property).  Per the D2 discipline of
   [Construction/ColouredPROP/Instance.v], both are explicit
   arguments, and each instance site should pass the ONE canonical
   decider of its colour type.

   Design alternative (not developed): a computing [C_base_map]
   Fixpoint on [CTerm] with cast-conjugated braid and tensor clauses
   would also yield the functor, at the cost of a fresh 19-case
   transport soundness induction mirroring [CT_map_CTermEq] of
   [Construction/ColouredPROP/Relabel.v].  The via-universal-property
   route delivers everything below without it, so the fixpoint form
   is left undeveloped. *)

(** ** The free coloured PROP's braiding, on the strict path

    For the free coloured PROP the coherence between the strict and
    symmetric [Monoidal] paths is [eq_refl]
    ([FreeColouredPROP_coherence_is_refl]), so the [transport_braid]
    re-indexing inside [cstrict_braid] is the identity and the
    strict-path braiding is the [CT_braid] constructor ON THE NOSE.
    This is the fact that makes braid-square hypotheses against free
    targets ([CSymmetricStrict] competitors in [BaseChange/Laws.v])
    definitionally transparent.  Machine-checked here, over an
    arbitrary signature and decider. *)

Example free_cstrict_braid {Colour : Type} (S : CSignature Colour)
  (Cdec : forall c d : Colour, {c = d} + {c <> d})
  (cs ds : list Colour) :
  cstrict_braid (FreeColouredPROP S Cdec) cs ds = CT_braid cs ds := eq_refl.

Section BaseChange.

Context {Colour Colour' : Type}.
Context (f : Colour -> Colour').
Context (Cdec : forall c d : Colour, {c = d} + {c <> d}).
Context (C'dec : forall c d : Colour', {c = d} + {c <> d}).

(** ** 1. Restriction of scalars

    The [ColouredPROP Colour] induced on a [ColouredPROP Colour'] by
    reading colour words through [map f].  The underlying category and
    all monoidal structure are [P]'s own — only [cprop_of_list] and
    the two object-equality fields change.  An explicit
    [Build_ColouredPROP] application: [Colour] occurs in no field
    type, so a record literal could not infer it.

    Since the underlying category is untouched, the side-condition
    instances of [Construction/Quotient.v] carry over on the nose: any
    [HomEqProp P] IS a [HomEqProp (ColouredPROP_restrict P)], and any
    [ObjDecEq P] an [ObjDecEq (ColouredPROP_restrict P)] — the classes
    mention only the category, which is judgmentally the same — so no
    new instances are declared here. *)

Definition ColouredPROP_restrict (P : ColouredPROP Colour') :
  ColouredPROP Colour :=
  Build_ColouredPROP Colour
    (cprop_cat P)
    (cprop_strict P)
    (cprop_symmetric P)

    (* The coherence between the two [Monoidal] paths is [P]'s own
       proof: both paths project through the untouched structures. *)
    (@cprop_monoidal_coherence Colour' P)

    (* Objects: colour words over [Colour], read through [map f]. *)
    (fun cs : list Colour => @cprop_of_list Colour' P (map f cs))

    (* [map f [] ≡ []] is definitional, so the unit condition is [P]'s
       own field at the empty word. *)
    (@cprop_unit_nil Colour' P)

    (* The tensor condition: [P]'s own strictness at the image words,
       composed with the [cprop_of_list]-image of the (propositional)
       monoid-homomorphism law of [map f]. *)
    (fun cs ds : list Colour =>
       eq_trans (@cprop_tensor_app Colour' P (map f cs) (map f ds))
                (f_equal (@cprop_of_list Colour' P)
                         (eq_sym (map_app f cs ds)))).

(** Machine-checked: the restriction changes only the object naming. *)

Example ColouredPROP_restrict_cat (P : ColouredPROP Colour') :
  cprop_cat (ColouredPROP_restrict P) = cprop_cat P := eq_refl.

Example ColouredPROP_restrict_of_list (P : ColouredPROP Colour')
  (cs : list Colour) :
  cprop_of_list (ColouredPROP := ColouredPROP_restrict P) cs
  = cprop_of_list (ColouredPROP := P) (map f cs) := eq_refl.

Example ColouredPROP_restrict_unit (P : ColouredPROP Colour') :
  @cprop_unit_nil Colour (ColouredPROP_restrict P)
  = @cprop_unit_nil Colour' P := eq_refl.

(** A restricted wire is the wire of the image colour ([map f [c]]
    computes to [[f c]]). *)
Example ColouredPROP_restrict_wire (P : ColouredPROP Colour') (c : Colour) :
  wire (P := ColouredPROP_restrict P) c = wire (P := P) (f c) := eq_refl.

(** ** 2. Signature morphisms over a colour function

    The base-change analogue of [CSubSig] ([Construction/ColouredPROP/
    Signature.v]): where a signature relabelling ([CSubSig]) preserves
    boundaries on the nose, a [CSigMap] REINDEXES them through
    [map f].  The identity and composition of such maps involve
    transports along [map_id] / [map_map] and live with the
    functoriality laws in [BaseChange/Laws.v]. *)

Definition CSigMap (S : CSignature Colour) (S' : CSignature Colour') : Type :=
  forall cs ds : list Colour, S cs ds -> S' (map f cs) (map f ds).

Context (S : CSignature Colour).
Context (S' : CSignature Colour').
Context (h : CSigMap S S').

(** ** 3. The base-change functor, through the universal property

    The interpretation target: the free coloured PROP on [S'],
    restricted along [f].  Its hom-sets at restricted objects are
    [CTerm S' (map f cs) (map f ds)] ON THE NOSE, so the generator
    valuation needs no casts. *)

Definition basechange_target : ColouredPROP Colour :=
  ColouredPROP_restrict (FreeColouredPROP S' C'dec).

Definition basechange_val : CValuation basechange_target S :=
  fun (cs ds : list Colour) (g : S cs ds) => CT_gen (h cs ds g).

(** The functor: [CInterpF] at the restricted target.  The
    side-condition instances are the free category's own
    ([CFreeCat_HomEqProp] / [CFreeCat_ObjDecEq], carried over across
    the restriction per the note above); [ObjDecEq] is
    [C'dec]-conditional and therefore passed explicitly (D2).  The
    stated target category [CFreeCat S'] is judgmentally
    [cprop_cat basechange_target], so the ascription pins the functor
    at the type its consumers want. *)

Definition BaseChangeF : CFreeCat S ⟶ CFreeCat S' :=
  @CInterpF Colour S basechange_target
    (CFreeCat_HomEqProp S') (CFreeCat_ObjDecEq S' C'dec)
    basechange_val.

(** Machine-checked: the action of [BaseChangeF] is definitional on
    objects, generators, identities, and composites ([cinterp]
    computes; [id] and [compose] of [CFreeCat S'] are [CT_id] and
    [CT_comp]).  Braids and tensors map to their cast-conjugated
    images — the [cbraid_hom] / [ctensor_hom] combinators of
    [Construction/ColouredPROP/Interp.v] at [basechange_target] — and
    are handled by the cast algebra of [BaseChange/Laws.v]. *)

Example BaseChangeF_fobj (cs : list Colour) :
  fobj[BaseChangeF] cs = map f cs := eq_refl.

Example BaseChangeF_gen {cs ds : list Colour} (g : S cs ds) :
  fmap[BaseChangeF] (CT_gen g) = CT_gen (h cs ds g) := eq_refl.

(* Named after [CInterpF_fmap_id] / [CInterpF_fmap_comp] of
   [Universal.v] (these are their instances at [basechange_target]);
   the short names [BaseChangeF_id] / [BaseChangeF_comp] are reserved
   for the pseudofunctoriality theorems of [BaseChange/Laws.v]. *)
Example BaseChangeF_fmap_id (cs : list Colour) :
  fmap[BaseChangeF] (CT_id cs) = CT_id (map f cs) := eq_refl.

Example BaseChangeF_fmap_comp {cs ds es : list Colour}
  (u : CTerm S ds es) (t : CTerm S cs ds) :
  fmap[BaseChangeF] (CT_comp u t)
  = CT_comp (fmap[BaseChangeF] u) (fmap[BaseChangeF] t) := eq_refl.

(** ** 4. The strict symmetric monoidal packaging, for free

    Each record below is the corresponding [CInterpF_*] packaging of
    [Construction/ColouredPROP/Universal.v] at [basechange_target],
    re-typed at the target's own monoidal tower — legitimate because
    the restriction leaves the structures untouched, so
    [MPc basechange_target] is judgmentally [CFreeCat_Monoidal S'
    C'dec], and likewise for the braided and symmetric records.  Both
    [Monoidal] instances in each type are THE shared records of their
    respective colour types (see the D2 WARNING in
    [Construction/ColouredPROP/Instance.v]). *)

Definition BaseChangeF_Monoidal :
  @MonoidalFunctor (CFreeCat S) (CFreeCat S')
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal S' C'dec) BaseChangeF :=
  @CInterpF_Monoidal Colour S Cdec basechange_target
    (CFreeCat_HomEqProp S') (CFreeCat_ObjDecEq S' C'dec)
    basechange_val.

Definition BaseChangeF_Strict :
  @StrictMonoidalFunctor (CFreeCat S) (CFreeCat S')
    (CFreeCat_Monoidal S Cdec) (CFreeCat_Monoidal S' C'dec) BaseChangeF :=
  @CInterpF_Strict Colour S Cdec basechange_target
    (CFreeCat_HomEqProp S') (CFreeCat_ObjDecEq S' C'dec)
    basechange_val.

(** Machine-checked: the unit comparison is reflexivity... *)
Example BaseChangeF_strict_pure_obj_is_refl :
  @strict_pure_obj _ _ _ _ BaseChangeF BaseChangeF_Strict = eq_refl
  := eq_refl.

(** ...but the tensor comparison is the restriction's
    [cprop_tensor_app] — the [map_app]-shaped composite, NOT [eq_refl]
    (which would be ill-typed here: [map f cs ++ map f ds] and
    [map f (cs ++ ds)] differ definitionally for variable [cs]).
    First the comparison is pinned to the class field verbatim
    (mirroring [CInterpF_strict_ap_obj_is_cprop_tensor_app]), then the
    field's shape is exposed: through the free instance the
    [eq_trans]'s first leg collapses to [eq_refl] and [cprop_of_list]
    to the identity function, leaving [map_app] as the sole residue. *)

Example BaseChangeF_strict_ap_obj_is_tensor_app (cs ds : list Colour) :
  @strict_ap_obj _ _ _ _ BaseChangeF BaseChangeF_Strict cs ds
  = @cprop_tensor_app Colour basechange_target cs ds := eq_refl.

Example basechange_tensor_app_shape (cs ds : list Colour) :
  @cprop_tensor_app Colour basechange_target cs ds
  = eq_trans eq_refl
      (f_equal (fun ks : list Colour' => ks) (eq_sym (map_app f cs ds)))
  := eq_refl.

Definition BaseChangeF_Braided :
  @BraidedMonoidalFunctor (CFreeCat S) (CFreeCat S')
    (CFreeCat_Braided S Cdec) (CFreeCat_Braided S' C'dec) BaseChangeF :=
  @CInterpF_Braided Colour S Cdec basechange_target
    (CFreeCat_HomEqProp S') (CFreeCat_ObjDecEq S' C'dec)
    basechange_val.

(** Machine-checked: because the free target's monoidal coherence is
    [eq_refl], the [MonoidalFunctor_transport] inside
    [CInterpF_Braided] is the identity, so the braided record's
    underlying strong structure IS [BaseChangeF_Monoidal] — one shared
    tensor comparison across the whole tower, on the nose. *)
Example BaseChangeF_Braided_is_strong :
  @braided_is_strong _ _ _ _ BaseChangeF BaseChangeF_Braided
  = BaseChangeF_Monoidal := eq_refl.

(** A braided monoidal functor between symmetric monoidal categories
    IS a symmetric monoidal functor ([SymmetricMonoidalFunctor] is a
    definition, not a class); supplied explicitly, as the alias does
    not participate in instance resolution. *)
Definition BaseChangeF_Symmetric :
  @SymmetricMonoidalFunctor (CFreeCat S) (CFreeCat S')
    (CFreeCat_Symmetric S Cdec) (CFreeCat_Symmetric S' C'dec) BaseChangeF :=
  BaseChangeF_Braided.

(** The braid-compatibility square over the strict-path braiding — the
    hypothesis-pack form that the uniqueness theorem
    ([cinterp_unique]) consumes.  [BaseChange/Laws.v] instantiates the
    functoriality arguments with exactly this witness. *)
Definition BaseChangeF_SymmetricStrict :
  CSymmetricStrict S Cdec basechange_target BaseChangeF BaseChangeF_Monoidal :=
  @CInterpF_SymmetricStrict Colour S Cdec basechange_target
    (CFreeCat_HomEqProp S') (CFreeCat_ObjDecEq S' C'dec)
    basechange_val.

(** The target-side instance of [free_cstrict_braid], through the
    restriction: the strict-path braiding of [basechange_target] is
    the [CT_braid] constructor of [CTerm S'] on the nose (the
    restriction carries [P]'s coherence verbatim, and the free
    coherence is [eq_refl]). *)
Example basechange_cstrict_braid (xs ys : list Colour') :
  cstrict_braid basechange_target xs ys = CT_braid xs ys := eq_refl.

End BaseChange.

Arguments ColouredPROP_restrict {Colour Colour'} f P : assert.
Arguments CSigMap {Colour Colour'} f S S' : assert.
Arguments basechange_target {Colour Colour'} f C'dec S' : assert.
(* [basechange_val] keeps its auto-generated argument status
   ({Colour Colour'} f C'dec S S' h, then the [CValuation] binders):
   its type unfolds to a ∀, so the boundary words and the generator
   ride along as trailing arguments. *)
Arguments BaseChangeF {Colour Colour'} f C'dec S S' h : assert.
Arguments BaseChangeF_Monoidal {Colour Colour'} f Cdec C'dec S S' h : assert.
Arguments BaseChangeF_Strict {Colour Colour'} f Cdec C'dec S S' h : assert.
Arguments BaseChangeF_Braided {Colour Colour'} f Cdec C'dec S S' h : assert.
Arguments BaseChangeF_Symmetric {Colour Colour'} f Cdec C'dec S S' h : assert.
(* [BaseChangeF_SymmetricStrict] keeps its auto-generated argument
   status: its type [CSymmetricStrict ...] is a definitionally
   unfolding ∀, so the constant carries the boundary binders [cs ds]
   as trailing arguments (compare [CInterpF_SymmetricStrict] in
   [Construction/ColouredPROP/Universal.v]). *)

(** ** Discussion: functoriality and further structure

    Base change is (pseudo)functorial in [f]: along the identity
    colour function it is the identity up to the [map_id] transports,
    and along a composite [g ∘ f] it agrees with the composite of the
    base changes up to the [map_map] transports.  Both statements are
    necessarily [hom_cast]-conjugated — [map_id] and [map_map] are
    propositional, not definitional — and both are consequences of the
    uniqueness half of the universal property rather than fresh
    inductions; they live in [Construction/ColouredPROP/BaseChange/
    Laws.v], together with the subset-restriction specialisation
    (base change along [proj1_sig]) and the descent of base change to
    presented coloured PROPs. *)
