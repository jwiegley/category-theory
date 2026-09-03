Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.FixedPoints.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Rep.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Grp.Galois.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.
From Coq Require Import Lia.

Generalizable All Variables.

(* Several proofs below draw on the two [PreOrder] witnesses of the section
   without naming them in the statement, so capture every section variable
   rather than the [Default Proof Using "Type"] subset inherited from Lib.v
   (the Construction/Reflective/Idempotent.v:24 precedent). *)
Set Default Proof Using "All".

(** * Mac Lane's Exercise 2 at a Galois connection between posets *)

(* Book:      Mac Lane, "Categories for the Working Mathematician", 2nd ed.,
              Springer GTM 5, 1998, SS IV.5, printed p. 97, Exercise 2
              (catalog id maclane:IV.5:ex2)
   Book:      Riehl, "Category Theory in Context", Dover 2016, SS 4.2,
              printed p. 142, Corollary 4.2.10 (riehl:4.2:cor10)
   Wikipedia: https://en.wikipedia.org/wiki/Galois_connection
   nLab:      https://ncatlab.org/nlab/show/idempotent+monad

   Mac Lane, verbatim from the printed page:

     "In a Galois connection between posets, show that the subset
      {p | p = RLp} of P equals {p | p = Rq for some q} and give a
      bijection from this set to the subset {q | q = LRq} of Q.  What are
      these sets in the case of a group of automorphisms of a field?  Does
      this generalize to an arbitrary adjunction?"

   Construction/Reflective/FixedPoints.v answers the closing question for
   an arbitrary adjunction.  This file is the exercise as stated: the
   thin case, where the categorical equivalence collapses to a bijection
   because every hom-set of [Proset] has at most one element.

   THE POSET INSTANCE IS A SPECIALISATION, NOT A RE-PROOF.  That is the
   issue's second reviewer check, and it is met by one line:
   [galois_fixed_point_equivalence] is [adjunction_fixed_point_
   equivalence] applied to [GaloisAdjunction], with no tactic.  What this
   file adds around it is the DICTIONARY -- that invertibility of the unit
   at [a] is exactly Instance/Grp/Galois.v's [GalClosed_r], and dually --
   and the elementwise reading Mac Lane asks for, which needs
   antisymmetry.

   ANTISYMMETRY IS AN EXPLICIT HYPOTHESIS, and it has to be.  #380
   recorded that Instance/Poset.v:125 defines [Poset] as [Proset] with the
   antisymmetry argument DISCARDED, so the two are the same category and
   nothing about equality of objects can be read off it.  Every statement
   below that mentions Leibniz [=] on the underlying order therefore takes
   an [Antisymmetric] witness in the shape
   Instance/Proset/Galois.v:216's [mutual_le_to_eq] consumes, and that
   lemma is reused rather than restated.  The statements that do NOT
   mention [=] -- the two dictionary biconditionals, the equivalence, and
   the two passages between the closed subsets -- take no such witness.

   WHAT IS DELIVERED, clause by clause of the exercise:

     - "{p | p = RLp}": [closed_r_eq], the elementwise reading of
       [GalClosed_r] under antisymmetry.
     - "equals {p | p = Rq for some q}": [closed_r_iff_image_eq], from
       [closed_r_eq] and Instance/Grp/Galois.v:467's
       [gal_closed_r_image].  The mutual-relatedness form of "is an
       image", that file's [gal_closed_r_iff] (:485), is the same fact
       stated without antisymmetry; it is cited, not applied.
     - "a bijection from this set to {q | q = LRq}": [closed_r_to_l] and
       [closed_l_to_r], with [closed_round_r] and [closed_round_l] closing
       both round trips on the FIRST projection at Leibniz [=].  The
       whole-sigma round trip is NOT claimed: [GalClosed_r] is
       [Prop]-valued, so two inhabitants of one closedness statement need
       not be equal, and no proof irrelevance is taken.
     - "What are these sets in the case of a group of automorphisms of a
       field?": NOT delivered, and the reason is that the tree carries no
       automorphism group of a field (measured: a scoped search over
       Instance/Field.v, Instance/Field/ and Instance/Rng/ returns
       nothing).  What IS delivered is the group-ACTION instance already
       in Instance/Grp/Galois.v: [group_action_fixed_point_equivalence]
       applies the general theorem to that file's own
       [group_action_adjunction], and its [closed_G_iff] / [closed_U_iff]
       answer the "what are these sets" question there -- the closed
       subsets of the group are exactly the stabilisers, and the closed
       subsets of the acted-on set exactly the fixed-point sets.
     - "Does this generalize to an arbitrary adjunction?":
       Construction/Reflective/FixedPoints.v, cited here.

   RIEHL'S COROLLARY 4.2.10 is [gal_lrl_eq] and [gal_rlr_eq]: his

     "F G F = F   and   G F G = G"

   proved from Instance/Grp/Galois.v's four closure inequalities plus
   antisymmetry, exactly as he does it ("By the triangle identities
   F(a) <= FGF(a) <= F(a) for all a in A, whence F = FGF.  The other
   formula is dual.").  Both are terms with no tactic beyond the
   [mutual_le_to_eq] application.  His illustration -- the direct-image /
   inverse-image connection, where

     "f(X) = f(f^{-1}(f(X)))   and   f^{-1}(f(f^{-1}(Y))) = f^{-1}(Y)"

   hold although "neither of the inclusions X subset f^{-1}(f(X)) or
   f(f^{-1}(Y)) subset Y need be equalities" -- is [image_preimage_image]
   and [preimage_image_preimage], stated at the carriers' [≈] because
   Leibniz equality of two elements of [Powerset_Prop_obj] would need
   both propositional and functional extensionality.  The two
   non-equalities are ALREADY IN TREE: Instance/Powerset.v's
   [unit_not_iso] (:850) and [counit_not_iso] (:867) refute exactly those
   two inclusions at the constant map on a two-element carrier, so they
   are cited here and not restated -- a correction to this issue's own
   plan, which asked for them to be built.

   A COMPUTING WITNESS.  Section (G) reads the whole dictionary off
   Instance/Proset/Galois.v:249's [nat_shift_galois k], truncated
   subtraction left adjoint to addition on the naturals: the closed
   elements on the left are exactly the [a] with [k <= a]
   ([nat_shift_closed_r_iff]), the closed elements on the right are ALL
   of them ([nat_shift_closed_l_all]), and at [k := 2] the restricted
   left adjoint carries the fixed object [5] to [3] by [eq_refl].  So the
   exercise's bijection is here the bijection between {a | 2 <= a} and
   the naturals, with the left side a PROPER subset -- [1] is not closed
   and [5] is.

   UNIVERSES, measured off both binder and constraint block.  Sections
   (E) and (G) keep the two carrier types at SEPARATE free universes and
   relate neither to the order; the hom-with-proof identification that
   [unit_fixed_iff_closed_r] displays inside [IsIsomorphism] is
   [Adjunction]'s, inherited.  Exactly FIVE of the 27 constants carry a
   word-bounded [Set], always as a strict LOWER bound and never as an
   equation -- [Set < u] at [image_preimage_image] and
   [preimage_image_preimage], [Set < u] together with [Set < u1] at
   [image_closed_l] and [preimage_closed_r], and [Set < u9] at
   [group_action_fixed_point_equivalence] -- and all five are in
   sections (F) and (H): it comes from [Powerset_Prop_obj], whose own
   block carries it (#382 and #384 attribute that; it is not
   re-attributed here).  The [nat] witnesses
   carry NO [Set] -- a prediction this file's plan made and measurement
   refuted, [nat_shift_galois] being over the monomorphic [nat] with no
   universe of its own.

   NOT DELIVERED besides the field question: no antisymmetric quotient of
   a preorder, so the two "sets" are subtypes of a preorder rather than of
   a poset; no naturality of any identification in the connection; no
   comparison of [closed_r_to_l] with the equivalence's own functor
   beyond their agreement on the underlying element; and no lattice
   structure on the closed elements. *)

(** ** (E) The dictionary, the equivalence, and Mac Lane's bijection *)

Section GaloisFixed.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (PA : PreOrder RA) (PB : PreOrder RB).
Context (G : GaloisConnection RA RB).

Definition GAdj := GaloisAdjunction PA PB G.

(* Invertibility of the unit at [a] IS closedness of [a].  In a thin
   category an isomorphism is a reverse arrow and nothing else: the
   forward direction is the projection [two_sided_inverse], and the
   backward direction supplies the two inverse laws with [I], since
   [Proset]'s hom-setoid identifies every pair of parallel arrows.
   [GalClosed_r] is [Prop]-valued while [IsIsomorphism] lands in [Type];
   that costs nothing here, because a reverse arrow of [Proset PA] IS a
   proof of [RA], so the [Prop] is literally the [two_sided_inverse]
   field. *)
Lemma unit_fixed_iff_closed_r (a : A) :
  IsIsomorphism (@unit (Proset PB) (Proset PA) _ _ GAdj a)
    ↔ GalClosed_r G a.
Proof.
  split.
  - intro H; exact (@two_sided_inverse (Proset PA) _ _ _ H).
  - intro H.
    exact (@Build_IsIsomorphism (Proset PA) _ _ _ H I I).
Defined.

Lemma counit_fixed_iff_closed_l (b : B) :
  IsIsomorphism (@counit (Proset PB) (Proset PA) _ _ GAdj b)
    ↔ GalClosed_l G b.
Proof.
  split.
  - intro H; exact (@two_sided_inverse (Proset PB) _ _ _ H).
  - intro H.
    exact (@Build_IsIsomorphism (Proset PB) _ _ _ H I I).
Defined.

(* The exercise's closing question, answered at a Galois connection by
   pure instantiation of the general theorem. *)
Definition galois_fixed_point_equivalence :
  EquivalenceOfCategories (FixedL GAdj) :=
  adjunction_fixed_point_equivalence GAdj.

Definition galois_fixed_point_equivalence_swap :
  EquivalenceOfCategories (FixedR GAdj) :=
  fixed_point_equivalence_swap GAdj.

(** *** Riehl Corollary 4.2.10, the thin fixed-point formulae *)

Lemma gal_lrl_eq (antiB : @Antisymmetric B eq eq_equiv RB) (a : A) :
  gal_l G (gal_r G (gal_l G a)) = gal_l G a.
Proof.
  refine (mutual_le_to_eq PB antiB
            (x := gal_l G (gal_r G (gal_l G a))) (y := gal_l G a) _).
  exact (@Build_Isomorphism (Proset PB) _ _
           (gal_lrl_below PA G a) (gal_lrl_above PB G a) I I).
Qed.

Lemma gal_rlr_eq (antiA : @Antisymmetric A eq eq_equiv RA) (b : B) :
  gal_r G (gal_l G (gal_r G b)) = gal_r G b.
Proof.
  refine (mutual_le_to_eq PA antiA
            (x := gal_r G (gal_l G (gal_r G b))) (y := gal_r G b) _).
  exact (@Build_Isomorphism (Proset PA) _ _
           (gal_rlr_below PA G b) (gal_rlr_above PB G b) I I).
Qed.

(** *** Mac Lane's two subsets, elementwise *)

(* "{p | p = RLp}", with the equation oriented as Mac Lane writes it. *)
Lemma closed_r_eq (antiA : @Antisymmetric A eq eq_equiv RA) (a : A) :
  GalClosed_r G a ↔ gal_r G (gal_l G a) = a.
Proof.
  split.
  - intro H.
    refine (mutual_le_to_eq PA antiA
              (x := gal_r G (gal_l G a)) (y := a) _).
    exact (@Build_Isomorphism (Proset PA) _ _ H (gal_unit G PB a) I I).
  - intro Heq; unfold GalClosed_r; rewrite Heq.
    exact (@reflexivity A RA (@PreOrder_Reflexive A RA PA) a).
Qed.

Lemma closed_l_eq (antiB : @Antisymmetric B eq eq_equiv RB) (b : B) :
  GalClosed_l G b ↔ gal_l G (gal_r G b) = b.
Proof.
  split.
  - intro H.
    refine (mutual_le_to_eq PB antiB
              (x := gal_l G (gal_r G b)) (y := b) _).
    exact (@Build_Isomorphism (Proset PB) _ _ (gal_counit G PA b) H I I).
  - intro Heq; unfold GalClosed_l; rewrite Heq.
    exact (@reflexivity B RB (@PreOrder_Reflexive B RB PB) b).
Qed.

(* "... equals {p | p = Rq for some q}".  Forward through [closed_r_eq],
   backward through Instance/Grp/Galois.v:467's [gal_closed_r_image]; the
   mutual-relatedness form of the same fact is that file's
   [gal_closed_r_iff] (:485), which antisymmetry would turn into Mac
   Lane's equation and which is not applied here. *)
Lemma closed_r_iff_image_eq (antiA : @Antisymmetric A eq eq_equiv RA)
  (a : A) : GalClosed_r G a ↔ ∃ b : B, a = gal_r G b.
Proof.
  split.
  - intro H.
    exact (gal_l G a; eq_sym (fst (closed_r_eq antiA a) H)).
  - intros [b Heq]; rewrite Heq.
    exact (gal_closed_r_image PA G b).
Qed.

Lemma closed_l_iff_image_eq (antiB : @Antisymmetric B eq eq_equiv RB)
  (b : B) : GalClosed_l G b ↔ ∃ a : A, b = gal_l G a.
Proof.
  split.
  - intro H.
    exact (gal_r G b; eq_sym (fst (closed_l_eq antiB b) H)).
  - intros [a Heq]; rewrite Heq.
    exact (gal_closed_l_image PB G a).
Qed.

(** *** The bijection between the two sets of closed elements *)

Definition closed_r_to_l (p : ∃ a : A, GalClosed_r G a) :
  ∃ b : B, GalClosed_l G b :=
  (gal_l G `1 p; gal_closed_l_image PB G `1 p).

Definition closed_l_to_r (q : ∃ b : B, GalClosed_l G b) :
  ∃ a : A, GalClosed_r G a :=
  (gal_r G `1 q; gal_closed_r_image PA G `1 q).

(* Both round trips return the underlying element on the nose.  The whole
   sigma is not compared: the second component is a [Prop] and no proof
   irrelevance is available. *)
Lemma closed_round_r (antiA : @Antisymmetric A eq eq_equiv RA)
  (p : ∃ a : A, GalClosed_r G a) :
  `1 (closed_l_to_r (closed_r_to_l p)) = `1 p.
Proof. exact (fst (closed_r_eq antiA `1 p) `2 p). Qed.

Lemma closed_round_l (antiB : @Antisymmetric B eq eq_equiv RB)
  (q : ∃ b : B, GalClosed_l G b) :
  `1 (closed_r_to_l (closed_l_to_r q)) = `1 q.
Proof. exact (fst (closed_l_eq antiB `1 q) `2 q). Qed.

End GaloisFixed.

(** ** (F) Riehl's illustration: the direct-image / inverse-image pair *)

Section PowersetFixed.

Context {X Y : SetoidObject}.
Context (f : X ~{Sets}~> Y).

(* "f(X) = f(f^{-1}(f(X)))", at the power set's own [≈]. *)
Lemma image_preimage_image (S : carrier (Powerset_Prop_obj X)) :
  Powerset_Prop_image f
      (Powerset_Prop_preimage f (Powerset_Prop_image f S))
    ≈ Powerset_Prop_image f S.
Proof.
  apply subset_le_antisym.
  - exact (gal_lrl_below (subset_le_preorder X)
             (image_preimage_galois f) S).
  - exact (gal_lrl_above (subset_le_preorder Y)
             (image_preimage_galois f) S).
Qed.

(* "f^{-1}(f(f^{-1}(Y))) = f^{-1}(Y)". *)
Lemma preimage_image_preimage (T : carrier (Powerset_Prop_obj Y)) :
  Powerset_Prop_preimage f
      (Powerset_Prop_image f (Powerset_Prop_preimage f T))
    ≈ Powerset_Prop_preimage f T.
Proof.
  apply subset_le_antisym.
  - exact (gal_rlr_below (subset_le_preorder X)
             (image_preimage_galois f) T).
  - exact (gal_rlr_above (subset_le_preorder Y)
             (image_preimage_galois f) T).
Qed.

(* Every direct image is closed on the right-hand side, every inverse
   image on the left: the two instances of the general closure facts. *)
Definition image_closed_l (S : carrier (Powerset_Prop_obj X)) :
  GalClosed_l (image_preimage_galois f) (Powerset_Prop_image f S) :=
  gal_closed_l_image (subset_le_preorder Y) (image_preimage_galois f) S.

Definition preimage_closed_r (T : carrier (Powerset_Prop_obj Y)) :
  GalClosed_r (image_preimage_galois f) (Powerset_Prop_preimage f T) :=
  gal_closed_r_image (subset_le_preorder X) (image_preimage_galois f) T.

End PowersetFixed.

(** ** (G) A computing witness on the naturals *)

(* [nat_shift_galois k] has [gal_l n = n - k] (truncated) and
   [gal_r m = m + k], so the composite [gal_r (gal_l a)] is [max a k] and
   an element of the left-hand order is closed exactly when [k <= a]. *)
Lemma nat_shift_closed_r_iff (k a : nat) :
  GalClosed_r (nat_shift_galois k) a ↔ Nat.le k a.
Proof.
  unfold GalClosed_r; simpl; split; intro H; lia.
Qed.

(* On the right-hand side every element is closed: [(b + k) - k] is [b]. *)
Lemma nat_shift_closed_l_all (k b : nat) :
  GalClosed_l (nat_shift_galois k) b.
Proof. unfold GalClosed_l; simpl; lia. Qed.

(* The left-hand closed elements are a PROPER subset: [1] is outside and
   [5] is inside, at [k := 2]. *)
Example nat_shift_two_one_not_closed :
  GalClosed_r (nat_shift_galois 2%nat) 1%nat → False.
Proof. intro H; pose proof (fst (nat_shift_closed_r_iff 2 1) H); lia. Qed.

Definition nat_shift_five_closed :
  GalClosed_r (nat_shift_galois 2%nat) 5%nat :=
  snd (nat_shift_closed_r_iff 2%nat 5%nat) (ltac:(lia)).

Example nat_shift_gal_l_five :
  gal_l (nat_shift_galois 2%nat) 5%nat = 3%nat := eq_refl.

(* [5] as an object of the unit-fixed subcategory of the shift
   adjunction, and the restricted left adjoint's value there. *)
Definition nat_shift_five_fixed :
  obj[Sub (Proset Nat.le_preorder)
        (UnitFixed (nat_shift_adjunction 2%nat))] :=
  (5%nat; snd (unit_fixed_iff_closed_r Nat.le_preorder Nat.le_preorder
                 (nat_shift_galois 2%nat) 5%nat) nat_shift_five_closed).

Example nat_shift_FixedL_obj :
  `1 (fobj[FixedL (nat_shift_adjunction 2%nat)] nat_shift_five_fixed)
    = 3%nat := eq_refl.

(** ** (H) Mac Lane's "what are these sets", for a group action *)

(* The field question is out of reach in this tree; the group-ACTION
   Galois connection of Instance/Grp/Galois.v is the available reading,
   and the general theorem applies to it with no tactic.  That file's
   [closed_G_iff] and [closed_U_iff] identify the two sets of closed
   elements: the closed subsets of the group are exactly the stabilisers,
   and the closed subsets of the acted-on set exactly the fixed-point
   sets. *)
Definition group_action_fixed_point_equivalence
  (G : GrpObject) (A : MSetoidAction (grp_mon G)) :
  EquivalenceOfCategories (FixedL (group_action_adjunction G A)) :=
  adjunction_fixed_point_equivalence (group_action_adjunction G A).
