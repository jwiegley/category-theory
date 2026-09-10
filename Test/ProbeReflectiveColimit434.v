(** * Probe for Construction/Reflective/Colimit.v (issue #434)

    Pins the measured boundaries of the reflected colimit with negatives
    of two kinds, kept lexically apart: TYPING (N1: the reflected colimit's
    apex is an object of the SUBCATEGORY, not the ambient apex — the
    inclusion does not create the colimit, the reflector computes a new
    one; N3: the cocone-level result is not an instance of
    [PreservesColimitCocone K (Incl C S)] — the transfer is by reflection,
    and the inclusion is not shown to preserve colimits; N4: nor is the
    reflected colimit a [CreatesColimit K (Incl C S)] — Riehl §4.6 ex xi's
    counterexample is scoped out, not contradicted) and CONVERSION (N2:
    [Cocomplete (Sub C S)] and [Cocomplete C] are different types; the
    theorem is a function between them, not a coercion).  The [eq_refl]
    readbacks are positive controls: the transparent counit isomorphism
    reduces to the counit (Construction/Reflective.v's own is [Qed], which
    Test/ProbeReflectiveLimit373.v already pins), the reflected apex and
    injections compute to the formula the issue asks for, and the
    hypothesis-free witness, instantiated here at the torsion-free
    reflection of abelian groups over the shape [Ordinal 2] (two objects
    and a non-identity arrow, so the leg condition is exercised), computes
    its apex — the instantiation lives in this probe rather than in the
    target so that Construction/ does not import Instance/Ab.  Each
    refutation was stripped one at a time in a copy of the whole file; the
    import list mirrors the target's, plus Structure/Limit/Creation.v for
    N4 and the three modules of the torsion-free witness. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Structure.Complete.
Require Import Category.Adjunction.Continuity.
Require Import Category.Theory.Equivalence.Limit.
Require Import Category.Theory.Equivalence.Colimit.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Instance.Ordinal.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Ab.TorsionFree.
Require Import Category.Construction.Reflective.Colimit.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe434_absent_name.

Section Probe.

Context {C : Category}.
Context {S : Subcategory C}.
Context (R : Reflective S).
Context {J : Category}.
Context (K : J ⟶ Sub C S).
Context (L : Colimit (Incl C S ◯ K)).

(** ** A: TYPING — the reflected colimit lives in the subcategory *)

(* control: the reflected apex is the reflector at the ambient apex *)
Example p434_apex (HL : Colimit (Incl C S ◯ K)) :
  colimit_apex (reflective_colimit R K HL) = reflector R (colimit_apex HL)
  := eq_refl.

(* N1 TYPING: it is not the ambient apex — the two live in different
   categories *)
Fail Example p434_apex_is_ambient :
  colimit_apex (reflective_colimit R K L) = colimit_apex L := eq_refl.

(** ** B: CONVERSION — cocompleteness of the two categories *)

(* control: the theorem is a function between the two *)
Check (reflective_Cocomplete R : @Cocomplete C → @Cocomplete (Sub C S)).

(* N2 CONVERSION: the two types are not the same type *)
Fail Example p434_cocomplete_same : @Cocomplete (Sub C S) = @Cocomplete C
  := eq_refl.

(** ** C: TYPING — reflection is neither preservation nor creation by the
       inclusion *)

(* control: the cocone-level statement *)
Check (reflective_colimit_cocone R K
         : ∀ N : Cocone (Incl C S ◯ K),
             IsColimitCocone N
             → IsColimitCocone (reflective_lift_cocone R K N)).

(* N3 TYPING: it does not ascribe to preservation by the inclusion *)
Fail Check (reflective_colimit_cocone R K
              : PreservesColimitCocone K (Incl C S)).

(* N4 TYPING: nor does the reflected colimit ascribe to creation *)
Fail Check (reflective_colimit R K : CreatesColimit K (Incl C S)).

(** ** D: readbacks *)

(* the transparent counit isomorphism reduces to the counit *)
Example p434_rc_to (x : Sub C S) :
  to (rc_counit_iso R x)
    = @counit (Sub C S) C (reflector R) (Incl C S) (reflective_adj R) x
  := eq_refl.

(* the injections are the issue's formula, on the nose *)
Example p434_inj (x : J) :
  colimit_inj (colimit_is_acolimit (reflective_colimit R K L)) x
    = fmap[reflector R] (colimit_inj (colimit_is_acolimit L) x)
        ∘ rc_unit_hom R (K x) := eq_refl.

Example p434_lift_apex (N : Cocone (Incl C S ◯ K)) :
  vertex_obj[reflective_lift_cocone R K N] = reflector R vertex_obj[N]
  := eq_refl.

Example p434_lift_inj (N : Cocone (Incl C S ◯ K)) (x : J) :
  cocone_inj (reflective_lift_cocone R K N) x
    = fmap[reflector R] (cocone_inj N x) ∘ rc_unit_hom R (K x) := eq_refl.

Check (reflective_reflector_Cocontinuous R : CocontinuousFunctor (reflector R)).
Check (reflective_subcategory_cocomplete R).

End Probe.

(** ** The witness at a concrete reflection: torsion-free abelian groups *)

Definition p434_torsionfree_colimit
  (K : Ordinal 2 ⟶ Sub Ab TorsionFree_Sub) : Colimit K :=
  reflective_terminal_shape_colimit TorsionFree_Reflective
    (Ordinal_Succ_Terminal 1) K.

(* its apex is the reflector at the terminal index, on the nose *)
Example p434_torsionfree_apex (K : Ordinal 2 ⟶ Sub Ab TorsionFree_Sub) :
  colimit_apex (p434_torsionfree_colimit K)
    = TorsionFree_reflector (Incl Ab TorsionFree_Sub (K (ord_top 1)))
  := eq_refl.

(** ** Guard block *)

Check @reflective_colimit.
Check @reflective_colimit_cocone.
Check @reflective_lift_cocone.
Check @reflective_Cocomplete.
Check @reflective_subcategory_cocomplete.
Check @reflective_reflector_Cocontinuous.
Check @reflective_terminal_shape_colimit.
Check @terminal_Colimit.
Check @Ordinal_Succ_Terminal.
Check @rc_counit_iso.
Check @rc_unit_hom.
Check @reflective_diagram_iso.
Check @colimit_apex.
Check @colimit_inj.
Check @colimit_is_acolimit.
Check @cocone_inj.
Check @Cocomplete.
Check @Colimit.
Check @Cocone.
Check @IsColimitCocone.
Check @PreservesColimitCocone.
Check @CreatesColimit.
Check @CocontinuousFunctor.
Check @Incl.
Check @Sub.
Check @reflector.
Check @reflective_adj.
Check @counit.
Check @Reflective.
Check @Subcategory.
Check @TorsionFree_Sub.
Check @TorsionFree_Reflective.
Check @TorsionFree_reflector.
Check @Ordinal.
Check @ord_top.
