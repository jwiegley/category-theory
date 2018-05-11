Set Warnings "-notation-overridden".

Require Import Category.Lib.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Theory.Sheaf.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Hom.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.

Generalizable All Variables.
Set Primitive Projections.
Set Universe Polymorphism.
Unset Transparent Obligations.

(* The Yoneda lemma tells us that a natural transformation, from the covariant
   or contravariant hom-functor on some object in C, to some other functor
   from C to Sets, is isomorphic to mapping the object by that functor
   directly from C to Sets.

   Writing this statement in code, it becomes a bit clearer what it's telling
   us: If the contravariant functor on `A` turns any `X` into the arrow `A ~>
   X`, and if natural transformation is given by `∀ x, f x ~> g x` (assuming
   naturality), the statement of the Yoneda lemma is:

       ∀ f x a, Functor f => (x ~{Sets}~> a) ~{Sets}~> f x ≅ f a

   The Lemma states: Since the only thing knowable about a functor is its
   ability to map objects and morphisms, any object `f x` through which we map
   a morphism `x ~> a` to obtain an object `f a`, *must* be identical to `f a`
   obtained directly, since the functor has no way of introducing additional
   meaning.

   A benefit of the lemma is that we can displace any source object `a` (from
   an arbitrary category `C`) into an object in the category of Sets -- i.e.,
   the hom-set whose domain or codomain is `a` -- allowing us to handle it
   using the structure of sets. This has the benefit of making many proofs
   easier, which become more difficult when restricted to the fully abstract
   nature of `C`. *)

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
