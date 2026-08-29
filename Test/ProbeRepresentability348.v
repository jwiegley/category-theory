(** * Probe: boundaries of the pointwise-representability criterion

    Guards the strength claims of Adjunction/Representability.v and of
    the packaging equivalence added to Theory/Universal/Arrow.v, from
    OUTSIDE both files -- an in-file [Fail] renames in lockstep with the
    constant it guards and so cannot detect a rename.

    Two negatives, both CONVERSION, each with its cause exhibited by an
    adjacent control rather than described:

      1. [neg_ua_round] -- the packaging round trip does not return the
         [UniversalArrow] record.  Controls [ctl_obj]/[ctl_arrow] show
         BOTH derived projections do return on the nose, so what fails
         is exactly the rebuilt [arrow_initial] field.

      2. [neg_roundtrip_arrow] -- recovering the unit from a family of
         representations does not return it on the nose.  Control
         [ctl_residue] exhibits the offending term literally: the value
         is [fmap[G] id ∘ unit], so the obstruction is that residue and
         nothing else.

    The import list mirrors Adjunction/Representability.v's in full; a
    short prefix is what makes a probe pass vacuously, and a vacuity
    check cannot detect it. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Instance.Sets.
Require Import Category.Theory.Adjunction.
Require Import Category.Adjunction.Opposite.
Require Import Category.Functor.Representable.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Arrow.Dual.
Require Import Category.Theory.Universal.Element.
Require Import Category.Adjunction.Representability.

Generalizable All Variables.

Section ProbePackaging.

Context {C : Category}.
Context {D : Category}.
Context {c : C}.
Context {F : D ⟶ C}.

(* INSTRUMENT CHECK: scope-free, and it must fail. *)
Fail Definition instrument_check : True = False := eq_refl.

(* CONTROL: both derived projections DO return on the nose. *)
Example ctl_obj (W : UniversalArrow c F) :
  @arrow_obj C D c F (ua_of_aua (aua_of_ua W)) = @arrow_obj C D c F W
  := eq_refl.

Example ctl_arrow (W : UniversalArrow c F) :
  @arrow C D c F (ua_of_aua (aua_of_ua W)) = @arrow C D c F W := eq_refl.

(* CONTROL: the other round trip returns the arrow on the nose. *)
Example ctl_aua_arrow {a : D} (W : AUniversalArrow c F a) :
  @universal_arrow C D c F a (aua_of_ua (ua_of_aua W))
    = @universal_arrow C D c F a W := eq_refl.

(* NEGATIVE 1 (CONVERSION).  [ua_of_aua] rebuilds the comma category's
   [Initial] record from the UMP, so [arrow_initial] is a different term
   even though both projections above reduce. *)
Fail Definition neg_ua_round (W : UniversalArrow c F) :
  ua_of_aua (aua_of_ua W) = W := eq_refl.

End ProbePackaging.

Section ProbeResidue.

Context {C : Category}.
Context {D : Category}.
Context {F : C ⟶ D}.
Context {G : D ⟶ C}.
Context (A : F ⊣ G).

(* CONTROL: the residue is EXACTLY [fmap[G] id ∘ unit] -- exhibited, so
   the negative below is attributable to that term and to nothing else. *)
Example ctl_residue (c : C) :
  @arrow C D c G (universal_of_representable G (adj_representable A) c)
    = fmap[G] (id{D}) ∘ @unit D C F G A c := eq_refl.

(* CONTROL: and it IS the unit up to [≈], so the negative is about
   conversion and not about the mathematics. *)
Example ctl_residue_equiv (c : C) :
  @arrow C D c G (universal_of_representable G (adj_representable A) c)
    ≈ @unit D C F G A c := representable_roundtrip_arrow A c.

(* CONTROL: the object half of the same round trip DOES return. *)
Example ctl_roundtrip_obj (c : C) :
  fobj[left_adjoint_of_representable G (adj_representable A)] c = F c
  := eq_refl.

(* NEGATIVE 2 (CONVERSION): the arrow half does not. *)
Fail Definition neg_roundtrip_arrow (c : C) :
  @arrow C D c G (universal_of_representable G (adj_representable A) c)
    = @unit D C F G A c := eq_refl.

End ProbeResidue.

(* Names the negatives depend on must also appear OUTSIDE a [Fail], or a
   rename would leave this file compiling and the guard vacuously green. *)
Check @ua_of_aua.
Check @aua_of_ua.
Check @universal_of_representable.
Check @adj_representable.
Check @left_adjoint_of_representable.
Check @adjunction_iff_pointwise_representable.
Check @coadjunction_iff_pointwise_representable.
