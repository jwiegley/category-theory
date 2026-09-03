Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Monad.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Instance.Sets.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Construction.Reflective.Idempotent.
Require Import Category.Construction.Reflective.FixedPoints.
Require Import Category.Monad.Comparison.
Require Import Category.Comonad.Core.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Instance.Proset.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Instance.Sets.Powerset.Universal.
Require Import Category.Instance.Poset.
Require Import Category.Instance.Proset.Galois.
Require Import Category.Instance.Powerset.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Rep.
Require Import Category.Construction.Deloop.Functors.
Require Import Category.Instance.Grp.Galois.
Require Import Category.Instance.Proset.Galois.FixedPoints.
Require Import Category.Instance.Coq.
Require Import Category.Theory.Algebra.Monoid.Hom.
Require Import Category.Structure.Monoidal.
Require Import Category.Instance.Coq.Monoid.Free.
Require Import Category.Instance.Adjoints.
Require Import Category.Adjunction.Compose.

Require Import Coq.Classes.Equivalence.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Arith.PeanoNat.

Generalizable All Variables.

(** * Probe for Construction/Reflective/FixedPoints.v and its poset instance *)

(* This file states, from OUTSIDE both targets, every boundary those two
   files measure, so that a rename or a change of definition breaks a
   build rather than turning a guard silently green.  It mirrors the
   UNION of the two targets' [Require] lists (plus what the witnesses
   need); a short prefix would let a guard pass for the wrong reason.

   Contents: one scope-free instrument check, then negatives of THREE
   kinds kept lexically apart -- TYPING, CONVERSION and FORMABILITY --
   each with a control naming the same constants outside any guard, and
   finally the two concrete witnesses.

   The two witnesses are here rather than in the library files because
   Instance/Coq/Monoid/Free.v has a transitive closure of 67 modules
   (excluding itself), 44 of them outside the general file's 37, and the
   general theory needs none of it. *)

(** ** Instrument check *)

(* A guard that must trigger for a trivial reason: the mechanism itself
   is working, and no [Require] above is needed for it. *)
Fail Check probe386_instrument_no_such_constant.

(** ** Negatives of kind TYPING *)

Section ProbeTyping.

Context {C D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(* NEGATIVE 1 (TYPING).  The equivalence is between the two FIXED
   subcategories; it is not an equivalence carried by the original left
   adjoint.  The error is a plain "has type ... while it is expected to
   have type ...", with no unification clause. *)
Fail Check (adjunction_fixed_point_equivalence A : EquivalenceOfCategories F).

(* Controls: the term does elaborate at its own type, and [F] is a
   functor that [EquivalenceOfCategories] accepts as an argument. *)
Check (adjunction_fixed_point_equivalence A).
Check (fun (E : EquivalenceOfCategories F) => quasi_inverse).
Check (FixedL A).
Check (FixedR A).
Check (fixed_point_equivalence_swap A).
Check (fixed_AdjointEquivalence A).
Check (fixed_adjunction A).
Check (UnitFixed A).
Check (CounitFixed A).
Check (UnitFixed_Full A).
Check (CounitFixed_Full A).
Check (counit_iso_of_unit_iso A).
Check (unit_iso_of_counit_iso A).
Check (unit_fixed_iff_image A).
Check (counit_fixed_iff_image A).
Check (unit_iso_of_image A).
Check (counit_iso_of_image A).
Check (fixed_unit_inverse A).
Check (fixed_counit_inverse A).
Check (unit_fixed_reflective_of_idempotent A).
Check (counit_fixed_op_reflective_of_idempotent A).

End ProbeTyping.

Section ProbeTypingComonad.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Coreflective S).

(* NEGATIVE 2 (TYPING).  The converse of [Idempotent_Coreflective] is NOT
   available as an [IdempotentComonad]: that class asks for an
   endofunctor presented as [W^op] for some [W : C ⟶ C], and the
   endofunctor a coreflection induces on C^op is [Incl ◯ reflector],
   which has no such presentation.  The error names the two classes
   directly. *)
Fail Check (Reflective_IdempotentMonad R
              : IdempotentComonad
                  (Incl (C^op) (op_subcategory S) ◯ reflector R)
                  (Reflective_Monad R)).

(* Control: in the op form the very same term typechecks, which is what
   [Coreflective_IdempotentMonad_op] delivers. *)
Check (Coreflective_IdempotentMonad_op R).
Check (Reflective_IdempotentMonad R).
Check (Reflective_Monad R).
Check @Incl.
Check @op_subcategory.
Check @reflector.
Check @sobj.
Check @IsIsomorphism.
Check @IdempotentComonad.
Check @Idempotent_Coreflective.
Check @WLocal_Subcategory.
Check @wlocal_obj_iff.
Check @wlocal_to_extract.
Check @extract_to_wlocal.

End ProbeTypingComonad.

(** ** Negatives of kind CONVERSION *)

Section ProbeConversion.

Context {C D : Category}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).

(* NEGATIVE 3 (CONVERSION).  The counit-fixed subcategory is not the
   opposite reading of the opposite adjunction's unit-fixed one: the two
   [sobj] fields carry [IsIsomorphism] in C and in C^op respectively, and
   those are different applications of the same class.  Only the
   underlying morphism agrees, which is [counit_fixed_op_strict]. *)
Fail Example probe_counit_fixed_not_op :
  CounitFixed A = op_subcategory (UnitFixed (Opposite_Adjunction F U A))
  := eq_refl.

(* Controls: the morphism identification that DOES hold, and the
   monad-side bridge, which holds on the whole record. *)
Check (fun c : C =>
  eq_refl : @unit (D^op) (C^op) (U^op) (F^op) (Opposite_Adjunction F U A) c
              = @counit C D F U A c).
Check (eq_refl : UnitFixed A
                   = @MLocal_Subcategory D (U ◯ F)
                       (Adjunction_Induced_Monad A)).
Check (fun x : Sub D (UnitFixed A) =>
  eq_refl : `1 (@unit _ _ (FixedL A) (FixedR A) (fixed_adjunction A) x)
              = @unit C D F U A `1 x).
Check (fun y : Sub C (CounitFixed A) =>
  eq_refl : `1 (@counit _ _ (FixedL A) (FixedR A) (fixed_adjunction A) y)
              = @counit C D F U A `1 y).
Check (Opposite_Adjunction F U A).

End ProbeConversion.

Section ProbeConversionComonad.

Context {C : Category}.
Context {W : C ⟶ C}.
Context (H : @Comonad C W).

(* NEGATIVE 4 (CONVERSION).  Membership in the colocal subcategory is
   invertibility read in C^op, and the covariant reading in C is a
   DIFFERENT type: the two inverse laws are exchanged.  That is why
   [wlocal_obj_iff] is a biconditional rather than an equation. *)
Fail Example probe_wlocal_not_covariant (x : C) :
  sobj C (WLocal_Subcategory H) x = IsIsomorphism (@extract C W H x)
  := eq_refl.

(* Controls: the op-side reading, which does hold on the nose, and the
   two passages. *)
Check (fun x : C =>
  eq_refl : sobj C (WLocal_Subcategory H) x
              = @IsIsomorphism (C^op) x (W x) (@extract C W H x)).
Check (wlocal_to_extract H).
Check (extract_to_wlocal H).
Check (fun x : C => @extract C W H x).

End ProbeConversionComonad.

Section ProbeConversionGalois.

Context {A B : Type}.
Context {RA : relation A} {RB : relation B}.
Context (PA : PreOrder RA) (PB : PreOrder RB).
Context (G : GaloisConnection RA RB).

(* NEGATIVE 5 (CONVERSION).  The bijection between the two sets of closed
   elements returns the underlying element on the nose only AFTER
   antisymmetry; the whole-sigma round trip is not even a conversion,
   the second component being a [Prop] with no proof irrelevance
   available.  This is what [closed_round_r] states instead. *)
Fail Example probe_closed_sigma_round
  (p : ∃ a : A, GalClosed_r G a) :
  closed_l_to_r PA G (closed_r_to_l PB G p) = p := eq_refl.

(* NEGATIVE 6 (CONVERSION).  Mac Lane's equation [p = RLp] is NOT a
   conversion: at a variable closed element the two sides are unrelated
   terms, and antisymmetry is what relates them.  This is the whole
   reason [closed_r_eq] carries an [Antisymmetric] hypothesis. *)
Fail Example probe_closed_not_definitional
  (a : A) (Hc : GalClosed_r G a) : gal_r G (gal_l G a) = a := eq_refl.

(* Controls: the relatedness that DOES hold with no hypothesis, and the
   antisymmetric statement that supplies the equation. *)
Check (fun (a : A) (Hc : GalClosed_r G a) =>
  Hc : RA (gal_r G (gal_l G a)) a).
Check (gal_unit G PB).
Check (closed_r_eq PA PB G).
Check (closed_l_eq PA PB G).
Check (closed_r_iff_image_eq PA PB G).
Check (closed_l_iff_image_eq PA PB G).
Check (gal_lrl_eq PA PB G).
Check (gal_rlr_eq PA PB G).
Check (closed_r_to_l PB G).
Check (closed_l_to_r PA G).
Check (closed_round_r PA PB G).
Check (closed_round_l PA PB G).
Check (unit_fixed_iff_closed_r PA PB G).
Check (counit_fixed_iff_closed_l PA PB G).
Check (galois_fixed_point_equivalence PA PB G).
Check (galois_fixed_point_equivalence_swap PA PB G).
Check (GAdj PA PB G).

End ProbeConversionGalois.

(** ** Negatives of kind FORMABILITY *)

Section ProbeUniverses.

Universes uo uh up.
Constraint uh < up.

Context (Cu Du : Category@{uo uh up}).
Context (Fu : Du ⟶ Cu) (Uu : Cu ⟶ Du).

(* Controls at the very same declared levels: the category's homs and its
   identities are formable, and so are functors in both directions. *)
Check (fun x y : Cu => x ~{Cu}~> y).
Check (fun x : Cu => id[x]).
Check Fu.
Check Uu.

(* NEGATIVE 7 (FORMABILITY).  [Adjunction] identifies the hom universe
   with the proof universe.  This is inherited, not introduced by the
   targets (#367, #368 and #379 measure the same donor). *)
Fail Check (Fu ⊣ Uu).

(* NEGATIVE 8 (FORMABILITY).  [Subcategory] does so independently, with
   no adjunction anywhere in the command. *)
Fail Check (Subcategory Cu).

End ProbeUniverses.

(* Controls for the two donors, at levels where they ARE formable. *)
Section ProbeUniversesControl.

Universes vo vh.

Context (Cv Dv : Category@{vo vh vh}).
Context (Fv : Dv ⟶ Cv) (Uv : Cv ⟶ Dv).

Check (Fv ⊣ Uv).
Check (Subcategory Cv).
Check (fun (Av : Fv ⊣ Uv) => UnitFixed Av).
Check (fun (Av : Fv ⊣ Uv) => adjunction_fixed_point_equivalence Av).

End ProbeUniversesControl.

(** ** Witness: the free-monoid adjunction *)

(* Instance/Coq/Monoid/Free.v declares [MonCoq] and [UMon] as [#[local]]
   notations, which do not export; hence these two. *)
Notation MonC := (@Mon Coq Coq_Monoidal).
Notation UMonC := (@Mon_Forget Coq Coq_Monoidal).

(* The unit at X carries [a] to the one-letter word [a :: nil]. *)
Example probe_free_unit_is_insert (X : Coq) (a : X) :
  @unit MonC Coq FreeMonoid UMonC free_monoid_adjunction X a
    = (a :: nil)%list := eq_refl.

(* NO object of [Coq] is unit-fixed for this adjunction: a two-sided
   inverse [k] would give [k nil :: nil = nil].  So the unit-fixed
   subcategory of the free-monoid adjunction is EMPTY -- that is exactly
   what this states, and nothing is claimed about the counit-fixed one
   beyond the single object below. *)
Theorem free_monoid_unit_never_iso (X : Coq) :
  IsIsomorphism (@unit MonC Coq FreeMonoid UMonC free_monoid_adjunction X)
    → False.
Proof.
  intros [k Hr Hl].
  pose proof (Hr nil) as Hn.
  simpl in Hn.
  discriminate Hn.
Qed.

(* The one-sided reading of "the fixed objects are the image of U" is
   therefore refuted: [list bool] IS [U (F bool)], so it lies in the
   image of the right adjoint, and yet the unit is not invertible there.
   The biconditional [unit_fixed_iff_image] escapes this because its
   right-hand side quantifies over COUNIT-FIXED objects. *)
Example probe_list_is_U_of_F (X : Coq) :
  fobj[UMonC] (fobj[FreeMonoid] X) = list X := eq_refl.

Theorem probe_image_of_U_not_unit_fixed :
  IsIsomorphism
    (@unit MonC Coq FreeMonoid UMonC free_monoid_adjunction
       (fobj[UMonC] (fobj[FreeMonoid] bool)))
    → False.
Proof. exact (free_monoid_unit_never_iso (list bool)). Qed.

(* The canonical comparison [eps (F x)] is not invertible here either, so
   [F eta] is not its inverse: Riehl's "F G F = F" reading is a
   statement about a Galois connection between POSETS and does not carry
   over to an arbitrary adjunction.  Whether some OTHER natural
   isomorphism [F ◯ U ◯ F ≈ F] exists at this adjunction is neither
   proved nor refuted here. *)
(* The object in question IS an [F]-image, which is what makes the next
   two computations a statement about the CANONICAL comparison. *)
Example probe_FreeMon_is_F_bool :
  FreeMon bool = fobj[FreeMonoid] bool := eq_refl.

Example probe_counit_of_two_words :
  `1 (@counit MonC Coq FreeMonoid UMonC free_monoid_adjunction
        (FreeMon bool)) (cons (@nil bool) nil)
    = @nil bool.
Proof.
  exact (free_monoid_counit_is_free_ext (FreeMon bool)
           (cons (@nil bool) nil)).
Qed.

Example probe_counit_of_empty_word :
  `1 (@counit MonC Coq FreeMonoid UMonC free_monoid_adjunction
        (FreeMon bool)) (@nil (list bool))
    = @nil bool.
Proof.
  exact (free_monoid_counit_is_free_ext (FreeMon bool)
           (@nil (list bool))).
Qed.

Theorem free_monoid_counit_not_iso :
  IsIsomorphism
    (@counit MonC Coq FreeMonoid UMonC free_monoid_adjunction
       (FreeMon bool))
    → False.
Proof.
  intros [k Hr Hl].
  assert (Hinj : ∀ u v : list (list bool),
            `1 (@counit MonC Coq FreeMonoid UMonC free_monoid_adjunction
                  (FreeMon bool)) u
              = `1 (@counit MonC Coq FreeMonoid UMonC
                      free_monoid_adjunction (FreeMon bool)) v → u = v).
  { intros u v Huv.
    transitivity (`1 k
      (`1 (@counit MonC Coq FreeMonoid UMonC free_monoid_adjunction
             (FreeMon bool)) u)).
    - symmetry; exact (Hl u).
    - rewrite Huv; exact (Hl v). }
  pose proof (Hinj (cons (@nil bool) nil) (@nil (list bool))) as Hc.
  rewrite probe_counit_of_two_words, probe_counit_of_empty_word in Hc.
  discriminate (Hc eq_refl).
Qed.

(* The general theorem still applies there, with both fixed
   subcategories as they are: this is the control that the equivalence
   asks nothing of the adjunction. *)
Check (adjunction_fixed_point_equivalence free_monoid_adjunction).

(** ** Witness: the identity adjunction, where every object is fixed *)

(* The other extreme.  [adj_id]'s unit is [≈ id], so transporting
   invertibility of the identity along that equation makes every object
   of C unit-fixed, and dually. *)
Definition probe_id_unit_fixed {C : Category} (x : C) :
  sobj C (UnitFixed (@adj_id C)) x.
Proof.
  refine (fixed_IsIso_along (fixed_IsIso_of_iso (@iso_id C x)) _).
  symmetry; exact (@adj_id_unit C x).
Defined.

Definition probe_id_counit_fixed {C : Category} (x : C) :
  sobj C (CounitFixed (@adj_id C)) x.
Proof.
  refine (fixed_IsIso_along (fixed_IsIso_of_iso (@iso_id C x)) _).
  symmetry; exact (@adj_id_counit C x).
Defined.

Check (fun C : Category => adjunction_fixed_point_equivalence (@adj_id C)).

(** ** Witness: the shift connection on the naturals *)

(* The restricted left adjoint carries the fixed object 5 to 3, by
   computation, and 1 is not fixed. *)
Check nat_shift_five_closed.
Check nat_shift_five_fixed.
Check nat_shift_closed_r_iff.
Check nat_shift_closed_l_all.
Check nat_shift_two_one_not_closed.
Check nat_shift_gal_l_five.
Check nat_shift_FixedL_obj.
Check @image_preimage_image.
Check @preimage_image_preimage.
Check @image_closed_l.
Check @preimage_closed_r.
Check @group_action_fixed_point_equivalence.
