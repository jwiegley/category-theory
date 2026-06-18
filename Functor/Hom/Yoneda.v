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
