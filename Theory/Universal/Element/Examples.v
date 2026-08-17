Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Representable.
Require Import Category.Instance.Sets.
Require Import Category.Structure.Terminal.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Initial.
Require Import Category.Construction.Elements.
Require Import Category.Instance.Coq.
Require Import Category.Instance.Coq.Nat.
Require Import Category.Theory.Universal.Element.
Require Import Category.Theory.Universal.Element.Elements.

Generalizable All Variables.

(** * Non-vacuity: the natural numbers as a universal element *)

(* The class of Theory/Universal/Element.v is inhabited, and by the object
   the tree already computes with.  Instance/Coq/Nat.v exhibits
   [nat_succ_Representable : Representable Endos_Forget] -- the pair
   ⟨(nat, S), 0⟩ representing the forgetful functor from sets-with-an-endomap
   -- and separately checks by [reflexivity] that the image of the identity
   under its representing isomorphism is [O] ([nat_universal_element], :415).
   That check is the SPECIAL CASE, for one functor, of the general equation
   [ue_of_repr_elem]; here the general class is run at that representation and
   the same [O] comes back out, by [eq_refl].

   This is what makes the file's central claim non-vacuous in the strong
   sense the brief asks for: the general definition is not merely inhabited,
   it RECOVERS the concrete criterion the tree had computed by hand.

   WHAT IS AND IS NOT RECOVERED.  What is: the universal element itself, on
   the nose, and -- through Theory/Universal/Element/Elements.v -- the
   initial object of the category of elements that Riehl's Proposition 2.4.8
   produces from it.  What is NOT: Instance/Coq/Nat.v's [repr_initial]
   proper.  That lands in [FAlg NatF], and the passage from
   [Elements Endos_Forget] to [FAlg NatF] is a comparison of categories the
   tree does not carry (Nat.v builds the object-level dictionary
   [alg_of_triple] / [alg_hom_clauses] but no functor).  So [repr_initial] is
   NOT re-derived, NOT made redundant, and NOT claimed to follow; what is
   shown is that the general machine produces the same universal element and
   an initial object of the general elements category. *)

(* The universal element of [Endos_Forget], produced by the general class
   from the representation Instance/Coq/Nat.v builds. *)
Definition nat_UniversalElement : UniversalElement Endos_Forget :=
  UniversalElement_of_Representable nat_succ_Representable.

(* Its object is the representing object, by conversion. *)
Example nat_ue_obj : @ue_obj Endos Endos_Forget nat_UniversalElement = NatSucc.
Proof. reflexivity. Qed.

(* ... and its element is [O] -- Instance/Coq/Nat.v:415's
   [nat_universal_element], obtained here through the general definition
   rather than checked for this one functor.  Note the type: an element of
   [Endos_Forget NatSucc] IS a [nat]. *)
Example nat_ue_elem : @ue_elem Endos Endos_Forget nat_UniversalElement = O.
Proof. reflexivity. Qed.

(* The general equation of which Nat.v's check is the instance, at this
   representation: the universal element is the image of the identity. *)
Example nat_ue_is_image_of_id :
  @ue_elem Endos Endos_Forget nat_UniversalElement
    = transform (to nat_succ_represents) NatSucc (id{Endos}).
Proof. reflexivity. Qed.

(* Mac Lane's unique-factorization clause, at this instance: every element n
   of every [Endos]-object is reached from [O] by a unique endomorphism-
   preserving map out of (nat, S) -- which is iteration.  The general class
   supplies it; nothing here is proved. *)
Definition nat_ue_factor (y : Endos) (n : Endos_Forget y)
  : NatSucc ~{Endos}~> y :=
  unique_obj (@ue_universal Endos Endos_Forget nat_UniversalElement y n).

Example nat_ue_factor_at_zero (y : Endos) (n : Endos_Forget y) :
  fmap[Endos_Forget] (nat_ue_factor y n) O ≈ n.
Proof. exact (unique_property (@ue_universal _ _ nat_UniversalElement y n)). Qed.

(* And Riehl's Proposition 2.4.8 at this instance: the pair ⟨(nat, S), 0⟩ is
   an initial object of the category of elements of [Endos_Forget].  This is
   the general form of Instance/Coq/Nat.v's [repr_initial]; see the header on
   what is and is not claimed about the relation between the two. *)
Definition nat_Elements_Initial : @Initial (Elements Endos_Forget) :=
  Elements_Initial Endos_Forget
    (AUniversalElement_of_UniversalElement nat_UniversalElement).

Example nat_Elements_Initial_obj :
  `1 (@initial_obj (Elements Endos_Forget) nat_Elements_Initial) = NatSucc.
Proof. reflexivity. Qed.

Example nat_Elements_Initial_elem :
  `2 (@initial_obj (Elements Endos_Forget) nat_Elements_Initial) = O.
Proof. reflexivity. Qed.
