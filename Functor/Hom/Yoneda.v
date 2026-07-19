Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Sheaf.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * The Yoneda lemma and the Yoneda embedding. *)

(* nLab: https://ncatlab.org/nlab/show/Yoneda+lemma
   Wikipedia: https://en.wikipedia.org/wiki/Yoneda_lemma

   For a presheaf F : C^op ⟶ Sets and an object A, the Yoneda lemma is the
   natural bijection between natural transformations out of the representable
   [Hom ─,A] and elements of F A:

       Nat([Hom ─,A], F) ≅ F A,      natural in both A and F.

   Here the left-hand side is written [Presheaves [Hom ─,A] F]: the Category
   [Presheaves] = [C^op, Sets] coerces (via [Curried_Hom]) to a functor whose
   value on the pair ([Hom ─,A], F) is the hom-setoid of natural transformations
   [Hom ─,A] ⟹ F, so [≅] is an isomorphism in Sets. The forward map [to] is
   evaluation at the identity, η ↦ η_A id_A; its inverse [from] sends y ∈ F A to
   the transformation whose component at x carries φ : x ~> A to fmap[F] φ y.
   [Covariant_Yoneda_Lemma] is the dual for a copresheaf F : C ⟶ Sets and the
   covariant representable [Hom A,─].

   Specialising F to a representable recovers the Yoneda embedding as a fully
   faithful functor (see [Yoneda_Full] and [Yoneda_Faithful] in Functor/Hom.v):
   on hom-setoids it gives Nat([Hom ─,A], [Hom ─,B]) ≅ (A ~> B), realised below
   as [Yoneda_Embedding] and its covariant counterpart.

   The intuition: since the only thing knowable about a functor is its ability
   to map objects and morphisms, any object `F x` through which we map a
   morphism `x ~> A` to obtain an element of `F A` *must* be determined by `F A`
   obtained directly, since the functor has no way of introducing additional
   meaning.

   A benefit of the lemma is that we can displace any source object `a` (from
   an arbitrary category `C`) into an object in the category of Sets -- i.e.,
   the hom-set whose domain or codomain is `a` -- allowing us to handle it
   using the structure of sets. This has the benefit of making many proofs
   easier, which become more difficult when restricted to the fully abstract
   nature of `C`. *)

(* Where the lemma comes from, and what follows from it

   Memoir: Yoshiki Kinoshita, categories mailing list, 23 April 1996,
           https://mta.ca/~cat-dist/catlist/1999/yoneda
   Text:   Emily Riehl, "Category Theory in Context", Dover 2016, §2.2

   The lemma entered mathematics by conversation rather than by
   publication.  Kinoshita's memorial post records the circumstances:
   Saunders Mac Lane, anxious to learn from Nobuo Yoneda during a visit to
   Paris — dated to 1954 by Mac Lane's later account — interviewed him in
   a café at the Gare du Nord, and the interview continued on Yoneda's
   train until its departure.  Mac Lane learned the result there and later
   baptized it, publishing his own brief telling (Mac Lane, "The Yoneda
   lemma", Mathematica Japonica 47, 1998) beside Kinoshita's obituary; the
   French nickname "le lemme de la Gare du Nord" survives (Wikipedia).
   Its first appearance in print is in Grothendieck's descent seminar
   (Grothendieck, "Technique de descente et théorèmes d'existence en
   géométrie algébriques", Séminaire Bourbaki 1960; Riehl, §2.2, footnote
   9) — the same functor-of-points program that studies a scheme through
   the presheaf it represents, and that rests on this lemma for its
   faithfulness.

   Riehl calls the result "arguably the most important result in category
   theory", and its weight is carried by a chain of corollaries.  Full
   faithfulness of the embedding ([Yoneda_Full] and [Yoneda_Faithful] in
   Functor/Hom.v) yields that [Hom ─,A] ≅ [Hom ─,B] exactly when A ≅ B:
   an object is determined, up to isomorphism, by the totality of maps
   into it — probes by the other objects of the category suffice to
   distinguish it (nLab, Corollary II).  Tai-Danae Bradley states the
   perspective as slogans: mathematical objects are completely determined
   by their relationships to other objects, so the properties of an
   object matter more than any particular presentation of it (Bradley,
   "The Yoneda Perspective", 2017).  Two classical specializations.  At a
   one-object category, full faithfulness of the covariant embedding is
   Cayley's theorem — every group embeds into a permutation group (Riehl,
   Corollary 2.2.11) — and Construction/Cayley.v builds the Cayley
   representation of an arbitrary category on
   [Covariant_Yoneda_Embedding] below.  And every row operation defined
   uniformly on matrices with n rows is left multiplication by a fixed
   matrix, found by applying the operation to the identity matrix —
   evaluation at the identity being precisely the forward map of the
   lemma (Riehl, Corollary 2.2.10).

   Within the library the lemma is the engine of representability.
   Structure/UniversalProperty.v consumes [Yoneda_Lemma] and
   Functor/Hom.v's [Yoneda_Embedding'] to identify universal properties
   with representations and to conclude that universal objects are unique
   up to unique isomorphism, a program continued for limits and universal
   arrows in Structure/UniversalProperty/Limit.v and
   Structure/UniversalProperty/Universal/Arrow.v.  The end/coend form of
   the lemma — the ninja Yoneda reductions of Theory/Coend/Yoneda.v —
   drives the Day convolution unitors of Construction/Day.v, and the
   profunctor unit laws of Construction/Profunctor/Laws.v perform the
   same co-Yoneda collapse inline.

   The computational reading is genuine, and this library carries it out.
   In programming terms the lemma says that f a ≅ ∀ r, (a → r) → f r for
   any functor f: a machine that accepts a handler a → r and uniformly
   produces an f r can only operate by holding an f a and mapping the
   handler over it, since it has no other means of manufacturing results
   (Piponi, "Reverse Engineering Machines with the Yoneda Lemma", 2006,
   which calls the lemma "the hardest trivial thing in mathematics").  At
   the identity functor this reads ∀ r, (a → r) → r ≅ a: a value is
   interchangeable with its continuation-passing form (Milewski, "The
   Yoneda Lemma", 2015).  Because the handler is an accumulating
   parameter, the encoding fuses successive uses of fmap into one — the
   optimization shipped as Data.Functor.Yoneda in the kan-extensions
   package (Kmett, "Free Monads for Less, Part 2: Yoneda", 2011) — and
   difference lists are the same idea one categorical level down, the
   Cayley representation of the list monoid (Rivas and Jaskelioff,
   "Notions of Computation as Monoids", 2014).  Theory/Coq/Functor.v
   realizes the encoding as [Yoneda] with [Yoneda_Functor], a functor in
   its argument whether or not F is one, and Theory/Coq/Applicative.v and
   Theory/Coq/Monad.v transport the Applicative and Monad structures
   across the isomorphism Yoneda F ≅ F.  There is a coda: on the advice
   of his thesis advisor Shokiti Iyanaga, Yoneda spent much of his career
   in computing, serving on the ALGOL 68 committee and teaching
   information science at the University of Tokyo (Kinoshita, 1996) — the
   man behind the lemma worked in the field where its
   continuation-passing reading now lives. *)

#[export]
Program Instance Yoneda_Lemma `(C : Category) `(F : C^op ⟶ Sets) :
  ∀ A : C, Presheaves [Hom ─,A] F ≅ F A := {
  to   := {| morphism := fun x => transform[x] A id |};
  from := {| morphism := fun y : F A =>
             {| transform := fun x : C =>
                {| morphism := fun phi : A ~{ C^op }~> x =>
                     @fmap (C^op) Sets F A x phi y |} |} |}
}.
Next Obligation.
  (* [transform] preserves morphism equivalences. *)
  proper.
  destruct F; simpl in *.
  apply fmap_respects, X.
Qed.
Next Obligation.
  (* The action of [transform] is natural. *)
  autounfold.
  destruct F; simpl in *.
  symmetry.
  apply fmap_comp.
Qed.
Next Obligation.
  (* The action of [transform] is natural (symmetric). *)
  autounfold.
  destruct F; simpl in *.
  apply fmap_comp.
Qed.
Next Obligation.
  (* [from] preserves morphism equivalences. *)
  proper.
  destruct F; simpl in *.
  apply proper_morphism; assumption.
Qed.
Next Obligation.
  (* The result of [from] respects the laws of the functor category. *)
  autounfold; simpl.
  destruct F; simpl in *.
  apply fmap_id.
Qed.
Next Obligation.
  (* The result of [from] preserves morphism equivalences. *)
  autounfold.
  destruct F, x; simpl in *; intros.
  autounfold in *.
  rewrite naturality.
  apply transform; cat.
Qed.

#[export]
Program Instance Covariant_Yoneda_Lemma `(C : Category) `(F : C ⟶ Sets) :
  ∀ A : C, Copresheaves [Hom A,─] F ≅ F A := {
  to   := {| morphism := fun x => transform[x] A id |};
  from := {| morphism := fun y : F A =>
             {| transform := fun x : C =>
                {| morphism := fun phi : A ~{ C }~> x =>
                     @fmap C Sets F A x phi y |} |} |}
}.
Next Obligation.
  (* [transform] preserves morphism equivalences. *)
  proper.
  destruct F; simpl in *.
  apply fmap_respects, X.
Qed.
Next Obligation.
  (* The action of [transform] is natural. *)
  autounfold.
  destruct F; simpl in *.
  symmetry.
  apply fmap_comp.
Qed.
Next Obligation.
  (* The action of [transform] is natural (symmetric). *)
  autounfold.
  destruct F; simpl in *.
  apply fmap_comp.
Qed.
Next Obligation.
  (* [from] preserves morphism equivalences. *)
  proper.
  destruct F; simpl in *.
  apply proper_morphism; assumption.
Qed.
Next Obligation.
  (* The result of [from] respects the laws of the functor category. *)
  autounfold; simpl.
  destruct F; simpl in *.
  apply fmap_id.
Qed.
Next Obligation.
  (* The result of [from] preserves morphism equivalences. *)
  autounfold.
  destruct F, x; simpl in *; intros.
  autounfold in *.
  rewrite naturality.
  apply transform; cat.
Qed.

#[export]
Program Instance Yoneda_Embedding `(C : Category) :
  ∀ A B : C, Presheaves [Hom ─,A] [Hom ─,B] ≊ A ~> B.
Next Obligation. morphism. Defined.
Next Obligation.
  morphism.
  - intros.
    transform; simpl.
    + intros.
      construct.
      * exact (X ∘ X0).
      * proper.
    + simpl; cat.
    + simpl; cat.
  - proper.
Defined.
Next Obligation.
  destruct x; simpl in *.
  rewrite naturality.
  apply proper_morphism; cat.
Qed.

#[export]
Program Instance Covariant_Yoneda_Embedding `(C : Category) :
  ∀ A B : C, Copresheaves [Hom B,─] [Hom A,─] ≊ A ~> B.
Next Obligation. morphism. Defined.
Next Obligation.
  morphism.
  - intros.
    transform; simpl.
    + intros.
      construct.
      * exact (X0 ∘ X).
      * proper.
    + simpl; cat.
    + simpl; cat.
  - proper.
Defined.
Next Obligation.
  destruct x; simpl in *.
  rewrite naturality.
  apply proper_morphism; cat.
Qed.
