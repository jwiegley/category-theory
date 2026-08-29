(** * Probe: boundaries of the additive-adjunction results

    Guards the strength claims of Adjunction/Additive.v from OUTSIDE
    that file — an in-file [Fail] renames in lockstep with the constant
    it guards and so cannot detect a rename.

    That file's header MEASURES three equations as rejected at
    [eq_refl] and says plainly that nothing there would notice if a
    later change made one of them definitional.  This file closes that
    gap: each of the three is pinned as a CONVERSION negative, beside a
    control establishing the same equation holds at [≈], so the
    negatives are about conversion and not about the mathematics.

    The import list mirrors the target's in full; a short prefix is what
    makes a probe pass vacuously, and a vacuity check cannot detect it. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Adjunction.Opposite.
Require Import Category.Structure.Preadditive.
Require Import Category.Structure.AbCategory.
Require Import Category.Instance.Sets.
Require Import Category.Instance.CMon.
Require Import Category.Instance.Ab.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Biproduct.
Require Import Category.Structure.Semiadditive.
Require Import Category.Adjunction.Additive.

Generalizable All Variables.

Section ProbeTranspose.

Context {C D : Category}.
Context {AC : AbEnriched C}.
Context {AD : AbEnriched D}.
Context {F : D ⟶ C}.
Context {U : C ⟶ D}.
Context (A : F ⊣ U).
Context (AU : @AdditiveFunctor C D AC AD U).

(* INSTRUMENT CHECK: scope-free, and it must fail. *)
Fail Definition instrument_check : True = False := eq_refl.

(* CONTROL: transpose additivity DOES hold at [≈]. *)
Example ctl_to_adj_padd {x : D} {y : C} (f g : F x ~{C}~> y) :
  to adj (padd f g) ≈ padd (to adj f) (to adj g)
  := @to_adj_padd C D AC AD F U A AU x y f g.

(* NEGATIVE 1 (CONVERSION): and not on the nose.  [padd] is an abstract
   field of a class, so neither side reduces. *)
Fail Definition neg_to_adj_padd {x : D} {y : C} (f g : F x ~{C}~> y) :
  to adj (padd f g) = padd (to adj f) (to adj g) := eq_refl.

(* CONTROL: Theorem 3's own field holds at [≈]. *)
Example ctl_left_adjoint_fmap_padd {x y : D} (f g : x ~{D}~> y) :
  fmap[F] (padd f g) ≈ padd (fmap[F] f) (fmap[F] g)
  := @left_adjoint_fmap_padd C D AC AD F U A AU x y f g.

(* NEGATIVE 2 (CONVERSION): and not on the nose. *)
Fail Definition neg_left_adjoint_fmap_padd {x y : D} (f g : x ~{D}~> y) :
  fmap[F] (padd f g) = padd (fmap[F] f) (fmap[F] g) := eq_refl.

End ProbeTranspose.

Section ProbeBiproduct.

Context {C : Category}.
Context `{ZC : @ZeroObject C}.
Context {P : @Preadditive C}.

(* CONTROL: the coproduct-diagonal factorization holds at [≈].  Note it
   needs only [Preadditive], not the full [AbEnriched] — the negation
   plays no part. *)
Example ctl_padd_copair_diag {a c : C} (B : Biproduct a a) (f g : a ~> c) :
  bi_copair B f g ∘ bi_diag B ≈ padd f g
  := @padd_copair_diag C ZC P a c B f g.

(* NEGATIVE 3 (CONVERSION): and not on the nose. *)
Fail Definition neg_padd_copair_diag {a c : C}
  (B : Biproduct a a) (f g : a ~> c) :
  bi_copair B f g ∘ bi_diag B = padd f g := eq_refl.

End ProbeBiproduct.

(** ** The universe donors, pinned

    Adjunction/Additive.v measures that [u0 = u2] — the identification
    of the two categories' hom-and-proof universes — has AT LEAST THREE
    INDEPENDENT donors.  An earlier revision of that file attributed it
    to the [Adjunction] class alone and called the attribution
    DISCRIMINATING; it is not, because the control it cited removes all
    three donors at once.  These negatives guard the corrected reading:
    the levels are declared so that D's hom sits STRICTLY BELOW C's,
    which satisfies the bound [bh <= ah] while violating the equation,
    and then each donor is rejected ON ITS OWN while the cited control
    is accepted at those very levels. *)

Section ProbeUniverseDonors.

Universes ao ah bo bh.
Constraint bh < ah.

Context (Cu : Category@{ao ah ah}).
Context (Du : Category@{bo bh bh}).
Context (ZCu : @ZeroObject Cu) (ZDu : @ZeroObject Du).
Context (PCu : @Preadditive Cu) (PDu : @Preadditive Du).
Context (ACu : AbEnriched Cu) (ADu : AbEnriched Du).
Context (Gu : Du ⟶ Cu).

(* CONTROL: the statement the withdrawn attribution cited IS formable
   at these levels — so the negatives below fire on the donors and not
   on the level declaration itself. *)
Check (@fmap_padd_of_preserved_coproduct Cu Du ZCu ZDu PCu PDu Gu).

(* CONTROL: naming a hom of each category at these levels is fine. *)
Check (fun (x y : Cu) => x ~{Cu}~> y).
Check (fun (x y : Du) => x ~{Du}~> y).

(* NEGATIVE 4 (FORMABILITY) — donor (i).  [AdditiveFunctor] alone, with
   ONE functor in the command and no adjunction anywhere: its binder
   reuses a single level for both categories while its own constraint
   block is empty. *)
Fail Check (@AdditiveFunctor Du Cu ADu ACu Gu).

(* CONTROL: the functor we HAVE, D ⟶ C, is formable at these levels. *)
Check (Du ⟶ Cu).

(* NEGATIVE 5 (FORMABILITY) — donor (ii).  Merely wanting a functor in
   the OTHER direction, with no adjunction anywhere: [Functor] forces
   source-hom below target-hom, so having both directions forces
   equality.  Written WITHOUT an explicit universe instance on purpose:
   [Functor]'s instance arity differs between Rocq 9.1 and the 8.x
   line, so a [Functor@{...}] spelling could make this [Fail] succeed
   on an ARITY error rather than the universe inconsistency — passing
   vacuously on two of the three supported toolchains, which no vacuity
   check would detect. *)
Fail Check (Cu ⟶ Du).

(* NEGATIVE 6 (FORMABILITY) — donor (iii).  [Adjunction] itself. *)
Fail Check (@Adjunction Cu Du).

End ProbeUniverseDonors.

(* Names the negatives depend on must also be named OUTSIDE a [Fail],
   or a rename would leave this file compiling and the guard green. *)
Check @to_adj_padd.
Check @left_adjoint_fmap_padd.
Check @padd_copair_diag.
Check @left_adjoint_additive.
Check @right_adjoint_additive.
Check @adj_hom_ab_iso.
Check @left_adjoint_additive_of_biproducts.
Check @hom_ab.
Check @fmap_padd_of_preserved_coproduct.
Check @AdditiveFunctor.
Check @AbEnriched_op.
Check @Preadditive_op.
