Require Import Category.Lib.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.

Generalizable All Variables.

Local Set Warnings "-intuition-auto-with-star".

(** * Cartesian closure of [Sets] *)

(* nLab: https://ncatlab.org/nlab/show/cartesian+closed+category
   nLab: https://ncatlab.org/nlab/show/exponential+object
   Wikipedia: https://en.wikipedia.org/wiki/Cartesian_closed_category
   Wikipedia: https://en.wikipedia.org/wiki/Exponential_object

   [Sets] is the category of setoids (Bishop sets: a carrier type with an
   equivalence relation ≈), and it is cartesian closed.  The exponential
   z^y = [exponent_obj y z] is the setoid SetoidMorphism y z of ≈-respecting
   maps y → z, equipped with the pointwise equivalence f ≈ g ⟺ ∀x, f x ≈ g x
   (the function setoid, via [SetoidMorphism_Setoid]).

   The CCC adjunction (- × y) ⊣ (- ^ y) is witnessed by [exp_iso], the
   bijection Hom(x × y, z) ≅ Hom(x, z^y): the forward (curry) direction sends
   f : x × y → z to λx.λy. f (x, y), and the inverse (uncurry) direction sends
   g : x → z^y to λp. g (fst p) (snd p).  Evaluation z^y × y → z is the image
   of the identity under uncurry, namely λp. (fst p) (snd p).

   This construction is fully constructive: the function setoid and currying
   require no choice, so [Sets] is cartesian closed in plain intuitionistic
   logic.

   This instance must appear in a separate file, because the Closed structure
   makes use of isomorphisms in [Sets]. *)

#[export]
Program Instance Sets_Closed : @Closed Sets _ := {
  exponent_obj := fun x y =>
    {| carrier := SetoidMorphism x y
     ; is_setoid := @SetoidMorphism_Setoid x y |};

  exp_iso := fun _ _ _ =>
    {| to   := {| morphism := fun f =>
                    {| morphism := fun x =>
                         {| morphism := fun y => f (x, y) |} |} |}
     ; from := {| morphism := fun f =>
                    {| morphism := fun p => f (fst p) (snd p) |} |} |}
}.
Next Obligation.
  proper; destruct f; simpl.
  apply proper_morphism.
  split; simpl; intuition; auto with *.
Qed.
Next Obligation.
  proper; destruct f; simpl.
  apply proper_morphism.
  split; simpl; intuition; auto with *.
Qed.
Next Obligation.
  proper; simpl in *.
  destruct f; simpl in *.
  unfold Proper, respectful, SetoidMorphism_equiv in proper_morphism.
  rewrite (proper_morphism _ _ X).
  destruct (morphism y).
  apply proper_morphism0; assumption.
Qed.
