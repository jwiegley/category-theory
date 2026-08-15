(** * Exercise II.4.8: the cylinder and arrow-category encodings agree *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Construction.Product.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Arrow.Functor.
Require Import Category.Construction.Cylinder.
Require Import Category.Instance.Two.
Require Import Category.Instance.Cat.
Require Import Category.Instance.Cat.Cartesian.
Require Import Category.Instance.Cat.Cartesian.Closed.
Require Import Category.Instance.Fun.
Require Import Category.Theory.Shapes.

Generalizable All Variables.

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              §II.4 Exercise 8, printed p. 42 (PDF 52) — maclane:II.4:ex8
   Book:      Awodey, "Category Theory" (1st ed., 2005 pre-print), §7.7,
              Example 7.16, printed p. 171 (PDF pp. 180–181) —
              awodey:7.7:example16

   Exercise II.4.8, and Awodey's "transcendental deduction": under the
   exponential transpose of Cat, the cylinder encoding of a natural
   transformation — a functor C ∏ 2 ⟶ B restricting to its boundary
   functors — corresponds to the arrow-category encoding — a functor
   C ⟶ B⃗ — of the SAME transformation.  The chain is: [Cat_Closed]'s
   [exp_iso] transposes F : C ∏ 2 ⟶ B to C ⟶ [_2, B]; Theory/Shapes.v's
   [Arrow_of_Fun] (the [to] leg of [Two_Fun_Arrow]) turns functors out
   of the walking arrow into arrow objects; and
   Construction/Arrow/Functor.v's [Arrow_extract] reads the classified
   triple back off.  [cylinder_arrow_agree] states that this composite
   carries [Cyl_functor τ] to a triple equivalent to (S, T, τ) in the
   triple setoid — the two encodings classify the same transformation.

     - [Cyl_transpose]: the exponential transpose of a cylinder
       functor, C ⟶ [_2, B]
     - [Cyl_to_arrow]: the transpose pushed into the arrow category,
       C ⟶ B⃗
     - [cylinder_arrow_agree]: extracting the triple recovers
       (S, T, τ) up to [ArrowTriple_Setoid]

   Design:

   1. UNIVERSE SCOPE, MEASURED.  The composite here elaborates at
      [Category@{Set Set Set}] — object universe INCLUDED — so it
      cannot be applied to categories whose objects live above [Set]
      ([cylinder_arrow_agree_at_two] below witnesses that it has
      content at small categories).  This is a stronger pin than the
      donor's: Theory/Shapes.v's [Arrow_of_Fun] keeps its object
      universe free, and whether the object pin introduced by this
      composite is forced by the [Cat]/[Fun] plumbing or avoidable
      has not been settled here.  It is why this file is separate
      from Construction/Cylinder.v, whose universal property carries
      no Set-level pin at all (verified by instantiation strictly
      above [Set]).

   2. NATURALITY IN THE TRIPLE, IN THE SETOID SENSE.
      [cylinder_arrow_natural] below states it: triples equivalent
      in [ArrowTriple_Setoid] are carried to equivalent extracted
      triples — a corollary of the pointwise agreement and the
      triple setoid's own equivalence.  The stronger packaging of
      the correspondence as an isomorphism in Sets (the shape
      [Arrow_classification] uses) is not delivered here: the
      object-level bijection of the two encodings is already the
      composite of [Arrow_classification] with the exponential
      transpose, and is not restated. *)

(** ** The transpose and its arrow-category form *)

Definition Cyl_transpose {C B : Category} (F : C ∏ _2 ⟶ B) :
  C ⟶ [_2, B] :=
  @curry' Cat Cat_Cartesian Cat_Closed C _2 B F.

Definition Cyl_to_arrow {C B : Category} (F : C ∏ _2 ⟶ B) :
  C ⟶ @Arrow B :=
  Arrow_of_Fun ◯ Cyl_transpose F.

(** ** The two encodings classify the same transformation *)

Lemma cylinder_arrow_dom_nat {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T) :
  ∀ x y (f : x ~{C}~> y),
    fmap[Arrow_dom (Cyl_to_arrow (Cyl_functor τ))] f
      ≈ from (@iso_id B (S y)) ∘ fmap[S] f ∘ to (@iso_id B (S x)).
Proof.
  intros x y f; simpl; cat.
Qed.

Lemma cylinder_arrow_cod_nat {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T) :
  ∀ x y (f : x ~{C}~> y),
    fmap[Arrow_cod (Cyl_to_arrow (Cyl_functor τ))] f
      ≈ from (@iso_id B (T y)) ∘ fmap[T] f ∘ to (@iso_id B (T x)).
Proof.
  intros x y f; simpl; cat.
Qed.

Theorem cylinder_arrow_agree {C B : Category} {S T : C ⟶ B} (τ : S ⟹ T) :
  @equiv _ (@ArrowTriple_Setoid C B)
    (Arrow_extract (Cyl_to_arrow (Cyl_functor τ)))
    (S; (T; τ)).
Proof.
  exists (existT _ (fun c => iso_id) (cylinder_arrow_dom_nat τ)).
  exists (existT _ (fun c => iso_id) (cylinder_arrow_cod_nat τ)).
  intro c; simpl; cat.
Qed.

#[local] Existing Instance ArrowTriple_Setoid.

(* Naturality in the triple, in the setoid sense: equivalent triples
   are carried to equivalent extracted triples. *)
Corollary cylinder_arrow_natural {C B : Category}
          {S T S' T' : C ⟶ B} (τ : S ⟹ T) (τ' : S' ⟹ T')
          (E : ((S; (T; τ)) : ArrowTriple C B) ≈ (S'; (T'; τ'))) :
  (Arrow_extract (Cyl_to_arrow (Cyl_functor τ)) : ArrowTriple C B)
    ≈ Arrow_extract (Cyl_to_arrow (Cyl_functor τ')).
Proof.
  transitivity ((S; (T; τ)) : ArrowTriple C B).
  - apply cylinder_arrow_agree.
  - transitivity ((S'; (T'; τ')) : ArrowTriple C B).
    + exact E.
    + symmetry; apply cylinder_arrow_agree.
Qed.

(* The theorem has content at small categories; the walking arrow
   itself is the donor's own precedent ([Two_Fun_Arrow_at_three]). *)
Example cylinder_arrow_agree_at_two {S T : _2 ⟶ _2} (τ : S ⟹ T) :
  @equiv _ (@ArrowTriple_Setoid _2 _2)
    (Arrow_extract (Cyl_to_arrow (Cyl_functor τ)))
    (S; (T; τ)) :=
  cylinder_arrow_agree τ.
