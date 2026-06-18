Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.

Generalizable All Variables.

(* nLab: https://ncatlab.org/nlab/show/closed+category
   nLab: https://ncatlab.org/nlab/show/closed+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Closed_monoidal_category

   This file is an in-progress stub for a "closed category" in the sense of
   Eilenberg and Kelly: a category C equipped with an internal hom bifunctor

       [-, -] : C^op ∏ C ⟶ C,

   a unit object I, a natural isomorphism x ≅ [I, x], an identity element
   I ~> [x, x], and a composition morphism [y, z] ~> [[x, y], [x, z]],
   subject to coherence axioms. Unlike a closed *monoidal* category, a closed
   category need not carry a tensor product; the internal hom is primitive and
   the tensor-hom adjunction Hom(x ⊗ y, z) ≅ Hom(x, [y, z]) is not assumed.

   The [Closed] class capturing this structure is sketched but commented out
   below (see the jww TODO); only the two helper functors [Curry] and [Flip]
   are live. The fully worked closed *monoidal* category, with tensor, an
   evaluation morphism eval[a, b] : (a ⇒ b) ⊗ a ~> b, and the currying
   universal property, lives instead in [Structure.Monoidal.Closed]. *)

Section Closed.

Context {C : Category}.
Context {D : Category}.
Context {E : Category}.

#[local] Set Transparent Obligations.

(* [Curry] partially applies a bifunctor in its first argument: it sends a
   functor of two variables F : C^op ∏ D ⟶ E to the functor-valued functor
   x ↦ (y ↦ F (x, y)), of type C^op ⟶ [D, E]. On objects the inner functor
   acts by F (x, -); the outer fmap of f : x ~> y yields the natural
   transformation z ↦ fmap[F] (f, id[z]). This is the section [F x, ─] of a
   bifunctor, and is what makes the [ X , ─ ] / [ ─ , X ] notations below
   denote genuine functors. *)
Program Definition Curry (F : C^op ∏ D ⟶ E) : C^op ⟶ [D, E] := {|
  fobj := fun x => {|
    fobj := fun y => F (x, y);
    fmap := fun y z (f : y ~{D}~> z) => fmap[F] (id[x], f)
  |};
  fmap := fun x y (f : x ~{C^op}~> y) => {|
    transform := fun z => fmap[F] (f, id[z])
  |}
|}.
Next Obligation. now proper; simpl_eq; rewrite X. Qed.
Next Obligation. now rewrite <- fmap_comp; simpl; cat. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.
Next Obligation. now proper; rewrite X. Qed.
Next Obligation. now rewrite <- !fmap_comp; simpl; cat. Qed.

(* [Flip] swaps the two arguments of a bifunctor, sending
   F : C^op ∏ D ⟶ E to (x, y) ↦ F (y, x) of type D ∏ C^op ⟶ E. Composing
   [Curry] with [Flip] partially applies the *second* argument, giving the
   contravariant section [ ─ , X ]. *)
Program Definition Flip (F : C^op ∏ D ⟶ E) : D ∏ C^op ⟶ E := {|
  fobj := fun x => F (snd x, fst x);
  fmap := fun _ _ f => fmap[F] (snd f, fst f)
|}.
Next Obligation. now proper; simpl_eq; simpl in *; rewrite X, H. Qed.
Next Obligation. now rewrite <- fmap_comp. Qed.

Reserved Notation "[ X , Y ]"
  (at level 90, right associativity, format "[ X ,  Y ]").

(* jww (2018-10-05): TODO

   The class below sketches the Eilenberg-Kelly data: the internal hom
   bifunctor, the unit object I (= unit_object), the unit isomorphism
   i : x ≅ [I, x] (hom_id_iso), the identity element j : I ~> [x, x]
   (hom_id), and the composition morphism L : [y, z] ~> [[x, y], [x, z]]
   (hom_compose). The two coherence fields are still incomplete: hom_id_right
   and the unnamed hom_ field both contain underscores standing for morphisms
   that have not yet been pinned down, so the class does not yet typecheck.
   Completing it means stating the five Eilenberg-Kelly axioms relating i, j
   and L; until then the whole block is left commented out.

Class Closed := {
  internal_hom_functor : C^op ∏ C ⟶ C       (* [-, -] internal hom *)
    where "[ X , Y ]" := (@internal_hom_functor (X, Y));
  unit_object : C;                          (* the unit object I *)

  (* hom_id_iso  : Id[C] ≅[Fun] Curry internal_hom_functor unit_object; *)
  hom_id_iso {x} : x ≅ [unit_object, x];    (* unit iso i : x ≅ [I, x] *)

  hom_id {x} : unit_object ~> [x, x];                 (* identity j : I ~> [x, x] *)
  hom_compose {x y z} : [y, z] ~> [[x, y], [x, z]];   (* composition L *)

  hom_id_right {x y} :
    @hom_compose x y y ∘ hom_id << unit_object ~~> [[x, y], [x, y]] >> hom_id;

  hom_ {x y} :
    _ ∘ @hom_compose x x y
      << [x, y] ~~> [unit_object, [x, y]] >>
    to (hom_id_iso ([x, y]))
}.

Notation "[ X , Y ]" := (internal_hom_functor (X, Y))
  (at level 90, right associativity, format "[ X ,  Y ]") : object_scope.

Notation "[ X , ─ ]" := (Curry internal_hom_functor X)
  (at level 90, right associativity, format "[ X ,  ─ ]") : object_scope.

Notation "[ ─ , X ]" := (Curry (Flip internal_hom_functor) X)
  (at level 90, right associativity, format "[ ─ ,  X ]") : object_scope.

*)

End Closed.
