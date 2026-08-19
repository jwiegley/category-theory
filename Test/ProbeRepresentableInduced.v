(** * Boundary probes for the induced-arrow theorem

    Companion to Functor/Representable.v and Functor/Representable/Functorial.v
    (issue #317; Mac Lane §III.2 Exercise 1, printed p. 62).  Those files make
    strength claims of two DIFFERENT kinds, and this file pins both.  **If the
    [Fail] commands below stop failing, this file breaks the build.**

    THE TWO KINDS ARE NOT THE SAME AND ARE NOT DESCRIBED WITH ONE WORD.

    (1) FORMABILITY.  [Yoneda_Full], [Yoneda_Faithful] and the [Yoneda_Embedding']
    assembled from them (Functor/Hom.v:85, :96, :109) are stated over
    [C : Category@{u u u}] — object, hom and proof universes IDENTIFIED — so
    nothing built over them applies to a category whose objects live strictly
    below its homs.  [repr_pair_iso] (Functor/Hom/Yoneda/Iso.v:162) consumes
    [Yoneda_Embedding'] and inherits the pin, and so does
    Functor/Representable/Functorial.v's [repr_pair_iso_from_is_induced] —
    whose printed BINDER shows [Category@{u u0 u0}] and whose CONSTRAINT BLOCK
    carries [u = u0].  The rejections in group (1) are UNIVERSE
    INCONSISTENCIES: the term is not formable at all, not merely
    non-convertible.

    The point of the group is that Functor/Representable.v does NOT inherit
    that pin, so the controls are as load-bearing as the negatives: the
    [Representable] class, [repr_induced], its uniqueness packaging, the
    tautological representation and the representing-object FUNCTOR are all
    formable at exactly the category the donors are rejected at.  That is the
    file's claim that the development escaped the donors' restriction, and
    that claim is what would break here if someone re-routed
    Functor/Representable.v through [Yoneda_Embedding'].

    The pin on the donors is an artifact of top-level minimization on an
    unannotated [(C : Category)] binder, not something inherent to Yoneda
    fullness or faithfulness: re-running those two proof scripts verbatim
    inside a section whose category is annotated [Category@{uo uh uh}]
    succeeds, and controls 7 and 8 are those two re-derivations performed
    here, so that negatives 1-3 are pinned as facts about the CONSTANTS.
    Nothing in this development repairs the donors.

    (2) CONVERSION.  Two claims of Leibniz equality are rejected because the
    two sides carry a different number of [fmap] applications, while the
    corresponding claims elsewhere DO hold on the nose.  These are
    [Fail Definition ... := eq_refl] and not [Fail Example ... : T.]: a failing
    type ascription would guard only the statement, whereas what is claimed is
    convertibility of the two terms.

    COUNTS.  Eight negatives — six in group (1) and two in group (2) — and
    twelve positive controls, which is not a one-to-one pairing: group (1)'s
    nine controls serve its six negatives jointly, and group (2)'s three
    controls are successes of exactly the [Fail Definition ... := eq_refl]
    shape its two negatives are rejections of.  Every negative is accompanied
    by at least one control that must SUCCEED.  The instrument itself was
    checked twice, once on a [Check] control and once on a
    [Definition ... := eq_refl] control — wrapping [Fail] around a succeeding
    command reports "The command has not failed!" and aborts compilation — and
    every negative was compiled once with the [Fail] stripped, to confirm the
    error is the intended one: six universe inconsistencies for group (1), of
    which five report "Cannot enforce uh = uo because uo < uh" naming the
    declared universes and the sixth (negative 4) reports "Cannot enforce
    uo = ..." while unifying the [Copresheaves] and [Fun] spellings of the
    functor category, and two "cannot unify" conversion errors for group (2).
    The import list is Functor/Representable/Functorial.v's own, in that
    file's order, plus both target files. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Deloop.
Require Import Category.Functor.Hom.
Require Import Category.Functor.Hom.Yoneda.
Require Import Category.Functor.Hom.Yoneda.Iso.
Require Import Category.Functor.Hom.Yoneda.Natural.
Require Import Category.Functor.Representable.
Require Import Category.Functor.Representable.Functorial.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Structure.UniversalProperty.

Generalizable All Variables.

(** ** (1) The donors' universe restriction, and the escape from it

    A category whose object universe is declared STRICTLY BELOW its hom
    universe.  The Yoneda donors do not reach it; the induced-arrow
    development does. *)

Section ObjectsBelowHoms.

Universes uo uh.
Constraint uo < uh.

Context (C : Category@{uo uh uh}).

(* Control 1: the curried hom-functor itself is formable here — so what the
   negatives reject is the fullness/faithfulness packaging, not [Curried_Hom]
   and not the [[C, Sets]] target. *)
Check (Curried_Hom C).

(* Control 2: so is the [Representable] class, which is what makes the
   restriction worth escaping — the class is more general than its donors. *)
Check (fun F : C ⟶ Sets => Representable F).

(* Controls 3-6: and so is the whole of Functor/Representable.v's
   development — the induced arrow, its uniqueness packaging, the
   isomorphism upgrade, and the tautological representation. *)
Check (fun (K K' : C ⟶ Sets) (R : Representable K) (R' : Representable K')
           (tau : K ⟹ K') => repr_induced R R' tau).
Check (fun (K K' : C ⟶ Sets) (R : Representable K) (R' : Representable K')
           (tau : K ⟹ K') => repr_induced_universal R R' tau).
Check (fun (K K' : C ⟶ Sets) (R : Representable K) (R' : Representable K')
           (i : K ≅[Fun] K') => repr_induced_iso R R' i).
Check (fun c : C => Hom_Representable c).

(* Negative 1: faithfulness of the Yoneda embedding is not formable here. *)
Fail Check (Yoneda_Faithful C).

(* Negative 2: neither is fullness... *)
Fail Check (Yoneda_Full C).

(* ...and negative 3, therefore neither is the packaged hom-bijection the
   issue suggested routing through. *)
Fail Check (fun c d : C => Yoneda_Embedding' C c d).

(* Negative 4: the pin propagates to [repr_pair_iso], which consumes
   [Yoneda_Embedding'] — so it is the DONORS' restriction and not something
   Functor/Hom/Yoneda/Iso.v introduces. *)
Fail Check (fun (F : C ⟶ Sets) (c v : C)
                (b1 : [Hom c,─] ≅[Fun] F) (b2 : [Hom v,─] ≅[Fun] F) =>
              repr_pair_iso b1 b2).

(* Negative 5: ...and thence to Functor/Representable/Functorial.v's
   cross-link, whose printed binder does NOT show the identification. *)
Fail Check (repr_pair_iso_from_is_induced C).

(* Negative 6 is negative 1 one application further in: the projection out of
   the instance is rejected too, for the same reason.  It earns its place by
   pairing with control 7, which inhabits the very same class at this very
   category — so what is rejected is the CONSTANT [Yoneda_Faithful], not the
   claim that [Curried_Hom C] is faithful here. *)
Fail Check (@fmap_inj _ _ (Curried_Hom C) (Yoneda_Faithful C)).

(* Controls 7 and 8: the same two proof scripts, copied verbatim from
   Functor/Hom.v:85-103 and run here, succeed.  This is what makes negatives
   1-3 a statement about minimization rather than about mathematics. *)
Definition probe_faithful_rederived : Functor.Faithful (Curried_Hom C).
Proof.
  constructor.
  intros c c' f g same.
  simpl in same.
  specialize same with c id. now rewrite 2 id_left in same.
Qed.

Definition probe_full_rederived : Functor.Full (Curried_Hom C).
Proof.
  unshelve econstructor; simpl in *.
  - exact (fun c d f => f c id).
  - abstract(intros x y [Ftrans Fnat ?] c f; simpl in *;
    unfold op;
    now rewrite Fnat, id_right).
Defined.

End ObjectsBelowHoms.

(* Control 9, outside the section: the representing-object functor is formable
   over a category with the same strict separation.  It is stated separately
   because it needs the section's constraint discharged into its own binder. *)
Section FunctorBelowHoms.

Universes uo uh.
Constraint uo < uh.

Context (C : Category@{uo uh uh}).

Check (ReprObjFunctor C).

End FunctorBelowHoms.

(** ** (2) The conversion boundaries *)

Section Conversion.

Context (C : Category).
Context {F : C ⟶ Sets}.
Context {c v : C}.
Context (b1 : [Hom c,─] ≅[Fun] F) (b2 : [Hom v,─] ≅[Fun] F).

(* Control 10: the issue's suggested route and the route taken produce the SAME
   TERM — [repr_induced] IS the Yoneda transpose, by [eq_refl]. *)
Definition probe_yoneda_transpose (K K' : C ⟶ Sets)
  (R : Representable K) (R' : Representable K') (tau : K ⟹ K') :
  @two_sided_inverse _ _ _ _
    (Yoneda_Embedding' C (@repr_obj _ _ R) (@repr_obj _ _ R'))
    (repr_transport R R' tau)
  = repr_induced R R' tau := eq_refl.

(* Control 11: the isomorphism [univ_property_unique_up_to_unique_iso]
   produces IS [repr_pair_iso], on the nose. *)
Definition probe_up_unique_obj (P : C → Type) (eqP : ∀ x, Setoid (P x))
  (H : IsUniversalProperty C P eqP) (x y : C) (t : P x) (s : P y) :
  unique_obj (univ_property_unique_up_to_unique_iso C P eqP H x y t s)
  = repr_pair_iso (to (repr_equivalence x) t) (to (repr_equivalence y) s)
  := eq_refl.

(* Negative 7: but [repr_pair_iso]'s leg is NOT the induced arrow on the nose.
   [nat_id]'s component is [fmap[F] id] rather than [id]
   (Theory/Natural/Transformation.v:220), so the induced arrow carries one
   [fmap] application the leg does not, and the agreement is only [≈]
   ([repr_pair_iso_from_is_induced]). *)
Fail Definition probe_pair_iso_strict :
  from (repr_pair_iso b1 b2)
  = repr_induced (repr_of_representation c b1)
                 (repr_of_representation v b2) nat_id := eq_refl.

End Conversion.

Section ConversionWitness.

Notation BNat := (Deloop Nat_Plus).

(* Control 12: against the tautological representations the induced arrow
   computes on the nose. *)
Definition probe_wit_computes (n : nat) :
  repr_induced (Hom_Representable (C:=BNat) ttt)
               (Hom_Representable (C:=BNat) ttt) (wit_tau n) = n := eq_refl.

(* Negative 8: against [YoEvalAt_Representable] it does not, even
   componentwise — the Yoneda isomorphism's backward leg leaves an [∘ id],
   which over (ℕ, +) is an [n + 0].  The agreement is [≈]
   ([wit_ev_induced]). *)
Fail Definition probe_wit_ev_strict (n : nat) (d : BNat) (g : ttt ~{BNat}~> d) :
  transform[repr_induced (YoEvalAt_Representable BNat ttt)
                         (YoEvalAt_Representable BNat ttt) (wit_ev_tau n)] d g
  = transform[wit_tau n] d g := eq_refl.

End ConversionWitness.
