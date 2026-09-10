(** * Probe for Instance/Top/CompHaus.v and Construction/Subcategory/Creation.v
    (issue #413)

    Pins the measured boundaries of the compact-Hausdorff development: what
    is formable, what converts, and exactly where the classical arguments
    stop constructively.  Every refutation command below was stripped ONE
    AT A TIME in a copy of the whole file and compiled alone with its error
    read, so each refusal is of the kind its label says.

    Numbering:
     instrument      an absent name, refused — the refutation keyword is
                     live in this file.
     N1 SORT/TYPING  the pairing into the truncated product is NOT shown
                     continuous by eliminating the squashed box datum into
                     the [Type]-valued [IsOpen Z]: the eliminator's motive
                     must be a [Prop] ("has type Type while it is expected
                     to have type Prop"); eliminating into [True] is
                     accepted (control).  N1 and N2 both say "universe
                     inconsistency"; they are told apart by "expected to
                     have type Prop" against "because o < …".
     N2 UNIVERSE     the other route to that continuity, a union indexed by
                     ALL boxes inside [W], is refused because the box datum
                     lives one universe above the space's points and
                     [open_union] indexes at the points' level; a union
                     indexed by the points themselves is accepted (control).
     N3 TYPING       [CompHaus_Forget] lands in [Sets], not in [Top] — a
                     plain has-type mismatch.
     N4 TYPING       [compact_hausdorff_bijection_iso] is NOT an isomorphism
                     without its decidability hypothesis: applied to the six
                     other arguments it still has a function type, refused
                     at [X ≅[Top] Y] ("has type … → X ≅ Y").

    POSITIVE, recorded because a survey predicted the opposite: the issue's
    pinned statement [CreatesLimit K CompHaus_Forget] IS formable, for a
    diagram out of any shape [J] — the forgetful functor lands in the [Sets]
    whose hom level is [Top]'s, so the limit-cone predicates apply on both
    sides.  What is not delivered is a PROOF of it (see the target's header).

    Readbacks at [eq_refl]: [CompHaus] IS [CompactHausdorffSpaces]; the
    inclusion's object map is the first projection; the truncated product's
    projections are [fst] and [snd] on points; the bijection isomorphism's
    forward map is [f] itself; the generic creation lemma's lift keeps the
    apex and the legs.  Non-vacuity: the per-open inverse lemma is applied
    at the one-point space with the identity bijection and the whole space
    as the decidable open.

    Guard coverage: every constant a negative names is also named outside a
    refutation command (the guard block at the end) — under the plain
    tokenization 31 identifiers inside, 29 also outside, the two exceptions
    exhaustively the instrument's absent name and the bound variable [z] of
    N1's lambda — so a renamed or removed constant breaks the build on a
    positive line rather than letting a refutation pass for the wrong
    reason. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Subcategory.Creation.
Require Import Category.Instance.Top.
Require Import Category.Instance.Top.Forgetful.
Require Import Category.Instance.Top.CompHaus.
Require Import Coq.Lists.List.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe413_absent_name.

(** ** A: the two walls in front of the product's universal property *)

Section Fork.
Universe o o1.
Constraint o < o1.
Context (X Y Z : TopSpace@{o}) (f : Z ~{Top}~> X) (g : Z ~{Top}~> Y) (z0 : Z).

(* control: eliminating the squashed box datum into a Prop is accepted *)
Check (fun (W : sq_carrier X Y → Type@{o}) (HW : sq_open X Y W)
           (p : sq_carrier X Y) (w : W p) => (snd HW p w) True).

(* N1 TYPING *)
Fail Check (fun (W : sq_carrier X Y → Type@{o}) (HW : sq_open X Y W)
                (p : sq_carrier X Y) (w : W p) =>
              (snd HW p w) (IsOpen Z (fun z => W (sq_fork_map X Y f g z)))).

(* control: a union indexed by the points of Z is accepted *)
Check (@open_union Z (carrier (top_carrier Z))).

(* N2 UNIVERSE *)
Fail Check (@open_union Z (sq_boxdata X Y (fun _ => poly_unit)
                              (sq_fork_map X Y f g z0))).
End Fork.

(** ** B: the forgetful functor and the pinned creation statement *)

(* POSITIVE: the issue's statement is formable *)
Check (fun (J : Category) (K : J ⟶ CompHaus) =>
         @CreatesLimit J CompHaus _ K CompHaus_Forget).

(* control: creation by the inclusion, the delivered conditional *)
Check (fun (closed : ClosedUnderLimits CompactHausdorff_Subcategory)
           (J : Category) (K : J ⟶ CompHaus) =>
         CompHaus_Incl_CreatesLimit closed K : CreatesLimit K CompHaus_Incl).

(* N3 TYPING *)
Fail Check (CompHaus_Forget : CompHaus ⟶ Top).

(** ** C: the bijection theorem needs its hypothesis *)

Section Bij.
Context {X Y : TopSpace} (f : X ~{Top}~> Y)
        (g : SetoidMorphism (top_carrier Y) (top_carrier X))
        (Hfg : ∀ y : Y, continuous_map f (g y) ≈ y)
        (Hgf : ∀ x : X, g (continuous_map f x) ≈ x)
        (HX : IsCompact X) (HY : IsHausdorff Y)
        (dec : ∀ U : X → Type, IsOpen X U → ∀ x : X, U x + (U x → False)).

(* control *)
Check (compact_hausdorff_bijection_iso f g Hfg Hgf HX HY dec : X ≅[Top] Y).

(* N4 TYPING *)
Fail Check (compact_hausdorff_bijection_iso f g Hfg Hgf HX HY : X ≅[Top] Y).

(* readback: the forward map is f itself *)
Example p413_iso_to :
  to (compact_hausdorff_bijection_iso f g Hfg Hgf HX HY dec) = f := eq_refl.
End Bij.

(* non-vacuity: the one-point space, the identity, the whole open *)
Definition p413_point_inverse_open :
  IsOpen Point_Top
    (fun y => (fun _ : Point_Top => poly_unit)
                (continuous_map (@id Top Point_Top) y)) :=
  inverse_open_of_decidable (X := Point_Top) (Y := Point_Top)
    (@id Top Point_Top) (continuous_map (@id Top Point_Top))
    (fun _ => reflexivity _) (fun _ => reflexivity _)
    Point_Compact Point_Hausdorff (fun _ => poly_unit) (open_whole _)
    (fun _ => inl ttt).

(** ** D: readbacks *)

Example p413_comphaus : CompHaus = CompactHausdorffSpaces := eq_refl.

Example p413_incl_obj (x : CompHaus) : fobj[CompHaus_Incl] x = `1 x := eq_refl.

Example p413_sq_fst (X Y : TopSpace) (p : sq_carrier X Y) :
  continuous_map (Top_sq_fst X Y) p = fst p := eq_refl.

Example p413_sq_snd (X Y : TopSpace) (p : sq_carrier X Y) :
  continuous_map (Top_sq_snd X Y) p = snd p := eq_refl.

Section LiftReadback.
Context {C : Category} (S : Subcategory C) (full : Full C S)
        (closed : ClosedUnderLimits S) {J : Category} (K : J ⟶ Sub C S)
        (N : Cone (Incl C S ◯ K)) (HN : IsLimitCone N).

Example p413_lift_apex :
  (`1 vertex_obj[creates_lift
                   (CreatesLimit := sub_CreatesLimit S full closed K) N HN])
  = vertex_obj[N] := eq_refl.

Example p413_lift_leg (x : J) :
  (`1 (cone_leg (creates_lift
                   (CreatesLimit := sub_CreatesLimit S full closed K) N HN) x))
  = cone_leg N x := eq_refl.
End LiftReadback.

(** ** Guard block *)

Check @CompHaus.
Check @CompHaus_Incl.
Check @CompHaus_Incl_Full.
Check @CompHaus_Incl_Faithful.
Check @CompHaus_Forget.
Check @CompHaus_Forget_Faithful.
Check @CompHaus_Incl_CreatesLimit.
Check @CompHaus_Complete_of.
Check @inverse_open_of_decidable.
Check @inverse_continuous_of_decidable.
Check @compact_hausdorff_bijection_iso.
Check @Top_sq_product.
Check @Top_sq_fst.
Check @Top_sq_snd.
Check @sq_carrier.
Check @sq_open.
Check @sq_boxdata.
Check @sq_fork_map.
Check @ClosedUnderLimits.
Check @sub_CreatesLimit.
Check @sub_CreatesAllLimits.
Check @sub_Complete.
Check @CreatesLimit.
Check @IsOpen.
Check @open_union.
Check @Top.
Check @Sets.
