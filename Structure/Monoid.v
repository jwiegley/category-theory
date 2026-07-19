Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Functor.Bifunctor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Instance.Sets.

Generalizable All Variables.

(** * Monoid objects in a monoidal category *)

(* nLab:      https://ncatlab.org/nlab/show/monoid+in+a+monoidal+category
   Wikipedia: https://en.wikipedia.org/wiki/Monoid_(category_theory)

   Given a monoidal category (C, ⨂, I), a monoid object on an object [mon : C]
   is a triple (mon, mappend, mempty) consisting of a multiplication
   [mappend : mon ⨂ mon ~> mon] and a unit [mempty : I ~> mon] subject to the
   associativity and left/right unit laws, with the associator and unitors
   inserted so the maps compose:

     associativity  mappend ∘ (mappend ⨂ id) ≈ mappend ∘ (id ⨂ mappend) ∘ α
     left unit      mappend ∘ (mempty ⨂ id)  ≈ λ
     right unit     mappend ∘ (id ⨂ mempty)  ≈ ρ

   Here ⨂ on morphisms is [bimap], α = [to tensor_assoc] is the associator
   (mon ⨂ mon) ⨂ mon ≅ mon ⨂ (mon ⨂ mon), and λ = [to unit_left],
   ρ = [to unit_right] are the left/right unitors I ⨂ mon ≅ mon and
   mon ⨂ I ≅ mon. This is exactly the nLab/Wikipedia definition (the names
   [mempty]/[mappend] echo Haskell's [Monoid] type class).

   Relationship to [Theory.Algebra.Monoid]: that file defines the very same
   structure under the name [Monoid] with fields [mu]/[eta], as a standalone
   abstract building block (used for Frobenius algebras and dualised to give
   comonoids). This file is the older, richer development: it specialises the
   monoid object to a cartesian monoidal category (giving an ordinary monoid)
   and proves closure under products ([Product_Monoid]) and exponentials
   ([Hom_Monoid]). The two definitions are equivalent up to field renaming. *)

(* One definition, many algebras: what internalization is for

   nLab:  https://ncatlab.org/nlab/show/microcosm+principle
   nLab:  https://ncatlab.org/nlab/show/Eckmann-Hilton+argument
   nLab:  https://ncatlab.org/nlab/show/Day+convolution
   Paper: Eckmann, Hilton, "Group-like structures in general categories
          I. Multiplications and comultiplications", Mathematische
          Annalen 145, 1962
   Paper: Bénabou, "Algèbre élémentaire dans les catégories", C. R.
          Acad. Sci. Paris 258, 1964
   Paper: Rivas, Jaskelioff, "Notions of Computation as Monoids", 2014

   The systematic study of algebraic structure carried by an OBJECT of
   a category, rather than by a set, begins with Eckmann and Hilton
   (Math. Ann. 145, 1962), whose motivation was homotopy theory: to
   explain why group structures arise on homotopy classes and why they
   are natural.  nLab cites Bénabou (1964) for the definition of a
   monoid in a monoidal category itself; the textbook treatment is
   Mac Lane, Categories for the Working Mathematician, Sections III.6
   and VII.3.

   A monoidal category is exactly enough structure to state the monoid
   axioms, and each choice of ambient category then instantiates a
   different classical theory.  In Set with the cartesian product,
   [MonoidObject] yields ordinary monoids; in abelian groups under the
   tensor product, rings; in R-modules, associative unital R-algebras;
   in endofunctors under composition, monads; and in C^op, comonoids in
   C (nLab, "monoid in a monoidal category").  It follows that a
   theorem proved once at this generality — closure under products,
   transport along lax monoidal functors, free monoids — specializes
   everywhere at once.  The library proves the canonical instance one
   directory away: Mac Lane's dictum that a monad "is just a monoid in
   the category of endofunctors" (op. cit., 2nd ed., p. 138) is
   [Monoid_Monad] in Monad/Monoid.v, a logical equivalence between
   [MonoidObject] at the composition tensor and a [Monad].  Yet the
   tensor is genuinely a parameter: a monoid object in StrictCat under
   the funny tensor is a strict premonoidal category
   (Instance/StrictCat/Premonoid.v), so changing the tensor changes
   what a monoid is.

   Two structural principles govern the tower.  Downward, the fact that
   a monoid object can only be stated inside a categorified monoid — a
   monoidal category — is the prototype of the microcosm principle of
   Baez and Dolan ("Higher-Dimensional Algebra III", 1997): certain
   algebraic structures can be defined in any category equipped with a
   categorified version of the same structure.  Upward, the
   Eckmann–Hilton argument shows that iterating the definition adds no
   generality: a monoid object in the category of monoids is already a
   commutative monoid, so the next rung is braided or symmetric
   structure rather than a second multiplication.  The same argument
   appears in this library at Structure/Semiadditive.v, where the two
   convolutions on hom-sets satisfy interchange and therefore coincide,
   commute, and associate.

   The computational reading is direct: the header already notes that
   [mempty] and [mappend] are borrowed from Haskell's Monoid class, and
   the cartesian section below supplies the categorical semantics of
   two standard library instances — [Product_Monoid] is the
   componentwise monoid on pairs, and [Hom_Monoid] is the pointwise
   monoid on functions into a monoid, with [doppel] distributing the
   shared argument to both evaluations, obtained internally via
   currying.  Rivas and Jaskelioff ("Notions of Computation as
   Monoids", 2014) carry the pattern further: monads, applicative
   functors, and arrows are all monoids in suitable monoidal
   categories, so free constructions and Cayley representations
   transfer uniformly.  On nLab's account of Day convolution, monoids
   for the Day tensor are the lax monoidal functors underlying
   Applicative; Construction/Day.v builds that tensor in-tree, though
   this correspondence is not yet proved here.  Within the library,
   [MonoidObject] is also the base of a tower of one-object structures:
   [GroupObject] in Structure/Group.v extends it with an inverse, and
   Theory/Algebra/Frobenius.v pairs the sibling definition of
   Theory/Algebra/Monoid.v with a comonoid on the same carrier to form
   Frobenius algebras. *)

Section MonoidObject.

Context {C : Category}.
Context `{M : @Monoidal C}.

Class MonoidObject (mon : C) := {
  mempty  : I ~> mon;             (* unit           η : I       ~> mon *)
  mappend : mon ⨂ mon ~> mon;     (* multiplication μ : mon ⨂ mon ~> mon *)

  (* left unit law: mappend ∘ (mempty ⨂ id) ≈ λ (left unitor I ⨂ mon ≅ mon) *)
  mempty_left : mappend ∘ bimap mempty id ≈ to (@unit_left C _ mon);
  (* right unit law: mappend ∘ (id ⨂ mempty) ≈ ρ (right unitor mon ⨂ I ≅ mon) *)
  mempty_right : mappend ∘ bimap id mempty ≈ to (@unit_right C _ mon);

  (* associativity, with the associator α reassociating the triple tensor:
     (mon ⨂ mon) ⨂ mon ≅ mon ⨂ (mon ⨂ mon) *)
  mappend_assoc :
    mappend ∘ bimap mappend id ≈ mappend ∘ bimap id mappend ∘ to tensor_assoc
}.

Context (mon : C).
Context `{@MonoidObject mon}.

(* Symmetric form of [mappend_assoc], reassociating in the opposite direction
   by composing with the inverse associator [tensor_assoc ⁻¹]. *)
Lemma mappend_assoc_sym :
  mappend ∘ bimap id mappend ≈ mappend ∘ bimap mappend id ∘ (tensor_assoc ⁻¹).
Proof.
  rewrite mappend_assoc.
  rewrite <- comp_assoc.
  rewrite iso_to_from.
  cat.
Qed.

End MonoidObject.

(* Projections to the unit and multiplication of a given monoid object [M]. *)
Notation "mempty[ M ]" := (@mempty _ _ _ M)
  (at level 9, format "mempty[ M ]") : category_scope.
Notation "mappend[ M ]" := (@mappend _ _ _ M)
  (at level 9, format "mappend[ M ]") : category_scope.

Section Monoid.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Terminal C}.

(* A monoid object for the cartesian monoidal structure [CC_Monoidal] (tensor
   = categorical product ×, unit = terminal object 1) is a monoid in the usual
   sense, with [mappend] reducing a product of two objects to one.

   nLab: "Classical monoids are of course just monoids in Set with the
   cartesian product." *)
Definition Monoid := @MonoidObject C CC_Monoidal.

(* The categorical product of two monoids is again a monoid, multiplying and
   uniting componentwise; [toggle] rearranges (x × y) × (x × y) into the
   (x × x) × (y × y) form expected by the componentwise [split] of the
   two multiplications. *)
#[export] Program Instance Product_Monoid `(X : Monoid x) `(Y : Monoid y) :
  @MonoidObject C CC_Monoidal (x × y) := {|
  mempty  := @mempty _ _ _ X △ @mempty _ _ _ Y;
  mappend := split (@mappend _ _ _ X) (@mappend _ _ _ Y) ∘ toggle
|}.
Next Obligation.
  spose (@mempty_left _ _ _ X) as HX.
  spose (@mempty_left _ _ _ Y) as HY.
  assert ((mempty[X] △ mempty[Y] ∘ exl) △ (id[x × y] ∘ exr)
            ≈ split (mempty[X] △ mempty[Y]) id[x × y])
    by (unfork; cat).
  rewrite X0; clear X0.
  unfold toggle.
  rewrite <- !comp_assoc.
  rewrite <- fork_comp.
  rewrite !split_comp.
  rewrite exl_fork, exr_fork.
  rewrite !id_right.
  rewrite <- (id_right mempty[X]).
  rewrite <- (id_left exl).
  rewrite <- (id_right mempty[Y]).
  rewrite <- (id_left exr).
  rewrite <- !split_comp.
  rewrite split_fork.
  rewrite !comp_assoc.
  rewrite HX, HY.
  unfold split; cat.
  now rewrite fork_comp; cat.
Qed.
Next Obligation.
  spose (@mempty_right _ _ _ X) as HX.
  spose (@mempty_right _ _ _ Y) as HY.
  assert ((id[x × y] ∘ exl) △ (mempty[X] △ mempty[Y] ∘ exr)
            ≈ split id[x × y] (mempty[X] △ mempty[Y]))
    by (unfork; cat).
  rewrite X0; clear X0.
  unfold toggle.
  rewrite <- !comp_assoc.
  rewrite <- fork_comp.
  rewrite !split_comp.
  rewrite exl_fork, exr_fork.
  rewrite !id_right.
  rewrite <- (id_right mempty[X]).
  rewrite <- (id_left exl).
  rewrite <- (id_right mempty[Y]).
  rewrite <- (id_left exr).
  rewrite <- !split_comp.
  rewrite split_fork.
  rewrite !comp_assoc.
  rewrite HX, HY.
  unfold split; cat.
  now rewrite fork_comp; cat.
Qed.
Next Obligation.
  spose (@mappend_assoc _ _ _ X) as HX.
  spose (@mappend_assoc _ _ _ Y) as HY.
  assert ((split mappend[X] mappend[Y] ∘ toggle ∘ exl) △ (id[x × y] ∘ exr)
            ≈ split (split mappend[X] mappend[Y] ∘ toggle) id[x × y])
    by (unfork; cat).
  rewrite X0; clear X0.
  assert ((id[x × y] ∘ exl) △ (split mappend[X] mappend[Y] ∘ toggle ∘ exr)
            ≈ split id[x × y] (split mappend[X] mappend[Y] ∘ toggle))
    by (unfork; cat).
  rewrite X0; clear X0.
  unfold toggle.
  rewrite !split_fork.
  rewrite <- !fork_comp.
  rewrite <- !comp_assoc.
  rewrite !split_fork.
  rewrite !id_left.
  rewrite !comp_assoc.
  rewrite !exl_fork.
  rewrite !exr_fork.
  rewrite <- !comp_assoc.
  rewrite !split_comp.
  rewrite !exl_fork.
  rewrite !exr_fork.
  rewrite !id_right.
  rewrite <- (id_left (exl (x:=x) (y:=y))) at 1.
  rewrite <- (id_left (exr (x:=x) (y:=y))) at 1.
  rewrite <- !split_comp.
  rewrite !comp_assoc.
  rewrite HX, HY.
  rewrite !id_left.
  apply fork_respects; clear;
  now unfold split; unfork; cat.
Qed.

Context `{@Closed C _}.

(* Duplicate the [z] component across both halves of a product:
   (x × y) × z ~> (x × z) × (y × z). Used to feed the shared argument to both
   pointwise multiplications in [Hom_Monoid]. *)
Definition doppel {x y z : C} : (x × y) × z ~> (x × z) × (y × z) :=
  first exl △ first exr.

(* The pair of uncurried projections equals evaluating both function arguments
   at the shared point, after distributing that point via [doppel]. *)
Lemma uncurry_exl_fork_exr {x y : C} :
  uncurry exl △ uncurry exr ≈ split eval eval ∘ @doppel (y ^ x) (y ^ x) x.
Proof.
  unfold doppel.
  rewrite split_fork.
  now rewrite !eval_first.
Qed.

(* The exponential [y ^ x] inherits a monoid structure pointwise from a monoid
   [Y] on [y]: the unit is the constant function at [mempty[Y]], and two
   functions are combined by evaluating each at the same point and multiplying
   the results with [mappend[Y]]. This is the "monoid of functions into a
   monoid", obtained here internally via currying. *)
#[export] Program Instance Hom_Monoid {x} `(Y : Monoid y) :
  @MonoidObject C CC_Monoidal (y ^ x) := {
  mempty  := curry (@mempty _ _ _ Y ∘ exl);
  mappend := curry (@mappend _ _ _ Y ∘ uncurry exl △ uncurry exr)
}.
Next Obligation.
  spose (@mempty_left _ _ _ Y) as HY.
  remember ((curry _ ∘ exl) △ (id[y ^ x] ∘ exr)) as h.
  assert (h ≈ split (curry (mempty[Y] ∘ exl)) id[y ^ x])
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  rewrite uncurry_exl_fork_exr.
  unfold doppel.
  rewrite split_fork.
  rewrite curry_comp_l.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc.
  rewrite <- !first_comp.
  rewrite exl_split.
  rewrite exr_split.
  rewrite !eval_first.
  rewrite !uncurry_comp.
  rewrite !uncurry_curry.
  rewrite <- !comp_assoc.
  rewrite !exl_first.
  rewrite <- split_fork.
  rewrite <- (id_right mempty[Y]) at 1.
  rewrite <- (id_left (uncurry id[y ^ x])).
  rewrite <- split_comp.
  rewrite !comp_assoc.
  rewrite HY; clear HY.
  rewrite <- comp_assoc.
  rewrite split_fork.
  rewrite exr_fork.
  rewrite eval_first.
  now rewrite curry_uncurry.
Qed.
Next Obligation.
  spose (@mempty_right _ _ _ Y) as HY.
  remember ((id[y ^ x] ∘ exl) △ (curry _ ∘ exr)) as h.
  assert (h ≈ split id[y ^ x] (curry (mempty[Y] ∘ exl)))
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  rewrite uncurry_exl_fork_exr.
  unfold doppel.
  rewrite split_fork.
  rewrite curry_comp_l.
  rewrite <- comp_assoc.
  rewrite <- fork_comp.
  rewrite <- !comp_assoc.
  rewrite <- !first_comp.
  rewrite exl_split.
  rewrite exr_split.
  rewrite !eval_first.
  rewrite !uncurry_comp.
  rewrite !uncurry_curry.
  rewrite <- !comp_assoc.
  rewrite !exl_first.
  rewrite <- split_fork.
  rewrite <- (id_right mempty[Y]) at 1.
  rewrite <- (id_left (uncurry id[y ^ x])).
  rewrite <- split_comp.
  rewrite !comp_assoc.
  rewrite HY; clear HY.
  rewrite <- comp_assoc.
  rewrite split_fork.
  rewrite exl_fork.
  rewrite eval_first.
  now rewrite curry_uncurry.
Qed.
Next Obligation.
  spose (@mappend_assoc _ _ _ Y) as HY.
  rewrite uncurry_exl_fork_exr.
  remember ((curry _ ∘ exl) △ (id[y ^ x] ∘ exr)) as h.
  assert (h ≈ split (curry (mappend[Y] ∘ split eval eval ∘ doppel)) id[y ^ x])
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  remember ((id[y ^ x] ∘ exl) △ (curry _ ∘ exr)) as h.
  assert (h ≈ split id[y ^ x] (curry (mappend[Y] ∘ split eval eval ∘ doppel)))
    by (rewrite Heqh; unfork; cat).
  rewrite X; clear X Heqh h.
  unfold doppel.
  rewrite <- !comp_assoc.
  rewrite !split_fork.
  rewrite !eval_first.
  simpl.
  rewrite split_fork.
  rewrite !eval_first.
  unfold split.
  rewrite !id_left.
  rewrite !curry_comp_l.
  rewrite <- !comp_assoc.
  rewrite <- !fork_comp.
  rewrite <- !uncurry_comp.
  rewrite exl_fork.
  rewrite exr_fork.
  rewrite !uncurry_curry.
  rewrite <- (id_left (uncurry exr)).
  rewrite <- split_fork.
  rewrite comp_assoc.
  rewrite HY; clear HY.
  rewrite id_left.
  rewrite <- !comp_assoc.
  rewrite <- !fork_comp.
  rewrite <- !comp_assoc.
  rewrite !exl_fork.
  rewrite !exr_fork.
  now rewrite uncurry_curry.
Qed.

End Monoid.
