Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.

Generalizable All Variables.

(** The internal-hom functor [-,-] : C^op ∏ C ⟶ C. *)

(* nLab: https://ncatlab.org/nlab/show/internal+hom
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category
   Wikipedia: https://en.wikipedia.org/wiki/Exponential_object

   In a closed (here cartesian-closed) category C the hom is internalized:
   instead of the Set-valued external hom Hom(-,-) : C^op ∏ C ⟶ Sets, the
   exponential object provides an object [a, b] = b ^ a of C itself, so the
   internal hom is a bifunctor

       [-,-] : C^op ∏ C ⟶ C,   [a, b] := exponent_obj a b = b ^ a.

   It is contravariant in its first argument and covariant in its second:
   given (f, g) : (a, b) ~> (a', b') in C^op ∏ C — that is, f : a' ~{C}~> a
   (an arrow a ~{C^op}~> a') and g : b ~{C}~> b' — the action is

       [f, g] := curry (g ∘ eval ∘ second f) : b ^ a ~> b' ^ a',

   which pre-composes by f in the exponent and post-composes by g in the base.
   (Here [op f] only re-reads the C^op arrow f as the underlying C-morphism
   a' ~{C}~> a; the hom-sets are definitionally equal.)

   The exponential b ^ a is right adjoint to (- × a) — the tensor-hom (here
   product-hom) adjunction Hom(x × a, b) ≅ Hom(x, b ^ a) of [Closed] — and
   [eval : b ^ a × a ~> b] is its counit. So this functor is the internal
   counterpart of Functor/Hom.v, with the cartesian product playing the role
   of the monoidal tensor. *)

Program Definition InternalHomFunctor `(C : Category)
        {E : @Cartesian C} {O : @Closed C _} : C^op ∏ C ⟶ C := {|
  fobj := fun p => @exponent_obj C E O (fst p) (snd p);   (* (a, b) ↦ b ^ a *)
  (* (f, g) ↦ curry (g ∘ eval ∘ second f): pre-compose f, post-compose g *)
  fmap := fun x y '(f, g) => curry (g ∘ eval ∘ second (op f))
|}.
Next Obligation.
  proper; simpl.
  now rewrites.
Qed.
Next Obligation. unfork; cat. Qed.
Next Obligation.
  rewrite <- !comp_assoc.
  rewrite curry_comp.
  symmetry.
  rewrite curry_comp.
  rewrite <- comp_assoc.
  apply compose_respects.
  - reflexivity.
  - symmetry.
    rewrite curry_comp_l.
    rewrite <- !comp_assoc.
    rewrite <- first_second.
    rewrite !comp_assoc.
    rewrite ump_exponents.
    rewrite <- !comp_assoc.
    rewrite <- second_comp.
    reflexivity.
Qed.

(* Shorthand for the internal hom [a, b] = b ^ a as an object of C, with the
   ambient category inferred; this is the internal counterpart of the external
   hom-set Hom(a, b). *)
Notation "a ≈> b":= (InternalHomFunctor _ (a, b))
  (at level 89) : category_scope.
(* As above, but naming the category C explicitly when it cannot be inferred. *)
Notation "a ≈{ C }≈> b":= (InternalHomFunctor C (a, b))
  (at level 89) : category_scope.
