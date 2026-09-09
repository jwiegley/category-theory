Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Isomorphism.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Construction.Product.
Require Import Category.Construction.Product.Limit.
Require Import Category.Construction.Comma.
Require Import Category.Construction.Arrow.
Require Import Category.Construction.Arrow.Limit.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Limit.Initial.
Require Import Category.Instance.One.
Require Import Category.Instance.Coq.

Generalizable All Variables.

(** * Probe: the measured boundaries of Construction/Arrow/Limit.v *)

(* Companion to Construction/Arrow/Limit.v (Mac Lane, Categories for the
   Working Mathematician, 2nd ed., §V.1 Exercise 3).  Everything that file
   claims at [eq_refl] is shipped there as an [Example]; what it cannot
   guard from inside are the REFUSALS its header records and the universe
   boundary a consumer meets.  Those are pinned here, from OUTSIDE the
   target, because an in-file [Fail] renames in lockstep with the constant
   it guards and so cannot detect a rename.  The concrete witness lives
   here too, because it costs three modules the target should not carry.

   FOUR negatives of THREE kinds — two CONVERSION, one TYPING, one
   UNIVERSE pinned by TWO [Fail] commands (the donor and the inherited
   refusal) — told apart by the error TEXT, plus one scope-free instrument
   check: five [Fail] commands beyond the instrument.  The kinds were read
   off the messages produced by stripping each [Fail] in turn, in a copy
   of this WHOLE file.

     N1  CONVERSION  [FCone comma_proj (comma_lift_cone K HT N HN)] is not
                   [N] as a whole RECORD, though its apex and every leg are
                   [N]'s on the nose (the two controls beside it): the
                   coherence field is a rebuilt proof and [≈] is
                   Type-valued.
     N2  CONVERSION  [Snd ◯ (comma_proj ◯ K)] is not [comma_proj2 ◯ K] as a
                   functor RECORD although both actions agree at [eq_refl]
                   (the two controls): [Compose]'s three law fields are
                   separate opaque obligations.  This is why the target
                   repackages [FCone Snd N] as [cod_cone N].  The same two
                   action controls are shipped for the [Fst]/[comma_proj1]
                   side, which the target's NOT DELIVERED paragraph cites.
     N3  TYPING    Supplying preservation on the DOMAIN side — a
                   [PreservesLimitCone (comma_proj1 ◯ K) S] — where the
                   theorem asks for [T] is a has-type mismatch between two
                   DIFFERENT types, with no universe clause; its trailing
                   [cannot unify] is on the two cone TYPES,
                   [Cone (comma_proj2 ◯ K)] against
                   [Cone (comma_proj1 ◯ K)], and not on two inhabitants of
                   one type, which is what separates it from N1 and N2.  The
                   correct hypothesis is the control.  Nothing is asked of
                   [S].
     N4  UNIVERSE  At a shape whose homs are declared strictly BELOW the
                   factors' homs, [Su ↓ Tu], the diagram [K] and a [Cone]
                   over it are ACCEPTED while the composite [comma_proj ◯ K]
                   is refused, firing at [K] with [Cannot enforce ch = jh]
                   — [Compose] is declared over three categories sharing
                   ONE hom-and-proof level.  [comma_proj_CreatesLimit] is
                   refused too, but NOT at that composite: it fires at its
                   shape argument [Ju], with [Cannot enforce jh = ah], its
                   own block equation [u0 = u6] met at an already-refused
                   argument (the #340 shape).  So the second [Fail] pins
                   the inherited boundary and does not independently
                   corroborate the [Compose] attribution, which rests on
                   the donor [Fail] alone.  The comma category is NOT a
                   donor: at [ah < bh] (the two factors' homs declared
                   apart) [Su ↓ Tu] is accepted, the control at the end.

   Every constant a negative names also appears in a [Check] outside every
   [Fail], so a rename breaks this file loudly instead of turning a [Fail]
   vacuously green. *)

(** ** Instrument check *)

Fail Check probe412_no_such_constant.

(** ** Guards *)

Check @comma_lift_cone.
Check @comma_lift_arrow.
Check @comma_proj_CreatesLimit.
Check @comma_proj.
Check @comma_proj1.
Check @comma_proj2.
Check @Comma.
Check @FCone.
Check @Cone.
Check @cone_leg.
Check @vertex_obj.
Check @Snd.
Check @Fst.
Check @Compose.
Check @PreservesLimitCone.
Check @IsLimitCone.
Check @Id_PreservesLimitCone.
Check @Arrow_Complete.

(** ** N1, N2: the records behind the on-the-nose readbacks *)

Section Records.

Context {A B C : Category} {S : A ⟶ C} {T : B ⟶ C} {J : Category}.
Context (K : J ⟶ (S ↓ T)) (HT : PreservesLimitCone (comma_proj2 ◯ K) T).

(* Controls: the lift's image has [N]'s apex and legs on the nose. *)
Example probe412_ctrl_apex (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N) :
  vertex_obj[FCone comma_proj (comma_lift_cone K HT N HN)] = vertex_obj[N]
  := eq_refl.

Example probe412_ctrl_leg (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N)
  (j : J) :
  cone_leg (FCone comma_proj (comma_lift_cone K HT N HN)) j = cone_leg N j
  := eq_refl.

(* N1: CONVERSION — the whole record is not. *)
Fail Example probe412_n1 (N : Cone (comma_proj ◯ K)) (HN : IsLimitCone N) :
  FCone comma_proj (comma_lift_cone K HT N HN) = N := eq_refl.

(* Controls: the two codomain-diagram functors agree on both actions. *)
Example probe412_ctrl_fobj :
  fobj[Snd ◯ (comma_proj ◯ K)] = fobj[comma_proj2 ◯ K] := eq_refl.

Example probe412_ctrl_fmap :
  @fmap _ _ (Snd ◯ (comma_proj ◯ K)) = @fmap _ _ (comma_proj2 ◯ K) := eq_refl.

(* N2: CONVERSION — not as records. *)
Fail Example probe412_n2 : Snd ◯ (comma_proj ◯ K) = comma_proj2 ◯ K := eq_refl.

(* Controls for the DOMAIN side, which the target's NOT DELIVERED paragraph
   cites: the two domain-diagram functors also agree on both actions. *)
Example probe412_ctrl_fobj1 :
  fobj[Fst ◯ (comma_proj ◯ K)] = fobj[comma_proj1 ◯ K] := eq_refl.

Example probe412_ctrl_fmap1 :
  @fmap _ _ (Fst ◯ (comma_proj ◯ K)) = @fmap _ _ (comma_proj1 ◯ K) := eq_refl.

End Records.

(** ** N3: the hypothesis is on the codomain side *)

Section Handedness.

Context {A B C : Category} {S : A ⟶ C} {T : B ⟶ C} {J : Category}.
Context (K : J ⟶ (S ↓ T)).
Context (HT : PreservesLimitCone (comma_proj2 ◯ K) T).
Context (HS : PreservesLimitCone (comma_proj1 ◯ K) S).

(* Control. *)
Check (comma_proj_CreatesLimit K HT).

(* N3: TYPING. *)
Fail Check (comma_proj_CreatesLimit K HS).

End Handedness.

(** ** N4: the universe boundary, with the comma, the diagram and a cone as
       controls *)

Section UniverseBoundary.

Universes jo jh ao ah co ch.
Constraint jh < ah.

Context (Ju : Category@{jo jh jh}).
Context (Au : Category@{ao ah ah}).
Context (Cu : Category@{co ch ch}).
Context (Su : Au ⟶ Cu) (Tu : Au ⟶ Cu).
Context (K : Ju ⟶ (Su ↓ Tu)).

(* Controls. *)
Check (Su ↓ Tu).
Check K.
Check (@Cone Ju (Su ↓ Tu) K).

(* N4: UNIVERSE — the donor. *)
Fail Check (comma_proj ◯ K).

(* Inherited: fires at the shape argument [Ju], [Cannot enforce jh = ah]. *)
Fail Check (@comma_proj_CreatesLimit Au Au Cu Su Tu Ju K).

End UniverseBoundary.

(* The comma category itself keeps the two factors' hom levels apart. *)

Section CommaApart.

Universes ao ah bo bh co ch.
Constraint ah < bh.

Context (Au : Category@{ao ah ah}) (Bu : Category@{bo bh bh}).
Context (Cu : Category@{co ch ch}).
Context (Su : Au ⟶ Cu) (Tu : Bu ⟶ Cu).

Check (Su ↓ Tu).

End CommaApart.

(* No [Set] pin on the arrow-category statements. *)

Section AboveSet.

Universes co ch.
Constraint Set < ch.

Context (Cu : Category@{co ch ch}).

Check (@Arrow Cu).
Check (@Arrow_Complete Cu).

End AboveSet.

(** ** The witness: the created arrow computes *)

(* Over [Coq] at the point shape [_1], the diagram constant at the arrow
   [negb].  Structure/Limit/Initial.v's [initial_cone] over [One_Initial]
   is limiting with its mediator definitionally the leg, so the created
   arrow reduces all the way. *)

Program Definition NegK : _1 ⟶ @Arrow Coq := {|
  fobj := fun _ => ((bool, bool); negb);
  fmap := fun _ _ _ => ((id, id); _)
|}.

Definition NegN : Cone (comma_proj ◯ NegK) :=
  @initial_cone _1 (Coq ∏ Coq) One_Initial (comma_proj ◯ NegK).

Definition NegHN : IsLimitCone NegN :=
  @initial_IsLimitCone _1 (Coq ∏ Coq) One_Initial (comma_proj ◯ NegK).

Definition neg_created :=
  comma_lift_arrow NegK (Id_PreservesLimitCone _) NegN NegHN.

Example neg_created_is_negb : neg_created = negb := eq_refl.
Example neg_created_true : neg_created true = false := eq_refl.
Example neg_created_false : neg_created false = true := eq_refl.

Example neg_lift_apex :
  (`1 vertex_obj[comma_lift_cone NegK (Id_PreservesLimitCone _) NegN NegHN])
    = (bool, bool) := eq_refl.

Example neg_lift_leg :
  (`1 (cone_leg (comma_lift_cone NegK (Id_PreservesLimitCone _) NegN NegHN)
         ttt))
    = (id, id) := eq_refl.

(* The created cone is limiting, through the general theorem. *)
Definition neg_lift_limiting :
  IsLimitCone (comma_lift_cone NegK (Id_PreservesLimitCone _) NegN NegHN) :=
  creates_limiting (arrow_proj_creates_limits NegK) NegN NegHN.
