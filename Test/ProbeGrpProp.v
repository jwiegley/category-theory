(* The Grp layer's carriers are sets: what that moved, and what it refuses.

   Since the PR "algebraic carriers are sets" (2026-09-17) every [GrpObject]
   carries [grp_prop] (Instance/Grp.v), the property that its carrier's `≈`
   is logically equivalent to a [Prop]-valued relation.  Three relations in
   the Grp layer changed sort or shape as a result, and this file pins each
   one from both sides:

     [am_eq]      Instance/Grp/Pushout.v  -- the amalgam's congruence, now a
                  [Prop] INDUCTIVE;
     [quot_rel]   Instance/Grp/Quotient.v -- unchanged itself, but the
                  quotient group's `≈` is now its [inhabited] TRUNCATION
                  ([quot_equiv]);
     the free group's `≈` -- Instance/Grp/Free.v -- now the [inhabited]
                  truncation of the free groupoid's hom-equality ([fg_equiv]).

   Being in [Prop], each ELIMINATES ONLY INTO [Prop].  That is the whole
   content of the change, and it is what the negatives below pin.  The
   positive controls show what is NOT lost: every consumer reaches its
   [Type]-valued goal through the TARGET group's own [grp_prop], and the
   free-forgetful adjunction still types over an ARBITRARY object of [Sets].

   METHOD.  A [Fail Lemma <statement>] would be vacuous here: each statement
   is well formed whatever the relation's sort, and only the ELIMINATION is
   refused.  Each negative is therefore a [Fail Definition … :=
   ltac:(<tactic>)], carrying the proof.  Each was stripped once, in a copy
   of this WHOLE file, and the first error line is quoted beside it.

   The import list is the union of the three target files' own. *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Lib.TList.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Universal.Arrow.
Require Import Category.Theory.Universal.Element.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Construction.Free.Quiver.
Require Import Category.Construction.Free.Groupoid.
Require Import Category.Construction.Deloop.
Require Import Category.Structure.Groupoid.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pushout.Split.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.TwoFunctors.
Require Import Category.Instance.Grp.Pushout.
Require Import Category.Instance.Grp.Quotient.
Require Import Category.Instance.Grp.Free.

Generalizable All Variables.

(* ------------------------------------------------------------------------ *)
(** ** Instrument check: this file's [Fail] is a real one *)

(* Scope-free: a statement that is simply ill-typed, so that a [Fail] which
   silently accepted everything would be caught here. *)
Fail Definition instrument_check : nat := true.

(* ------------------------------------------------------------------------ *)
(** ** (1) [am_eq] is a [Prop] inductive *)

Section AmEq.

Context {A B C : GrpObject}.
Context (f : A ~{Grp}~> B) (g : A ~{Grp}~> C).

(* NEGATIVE 1.  A bare elimination of [am_eq] into a [Type]-valued goal.
   Stripped in a copy of this whole file; first error line:

     Error: Cannot find the elimination combinator am_eq_rect, the
     elimination of the inductive definition am_eq on sort Type is probably
     not allowed.

   ([am_eq_ind] and [am_eq_sind] do exist; [am_eq_rect] and [am_eq_rec] do
   not, which is exactly what a [Prop] inductive gets.) *)
Fail Definition am_eq_eliminates_into_Type
  (u v : AmTerm B C) (He : am_eq f g u v) : poly_unit :=
  ltac:(induction He).

(* CONTROL 1a.  Two constructors of [am_eq] carry a [Type]-valued `≈`
   premise, and both are still accepted verbatim: a [Prop] inductive MAY
   store [Type]-valued data, it simply may not be eliminated into [Type]. *)
Definition am_eq_stores_a_Type_premise (b b' : carrier B) (H : b ≈ b') :
  am_eq f g (am_l b) (am_l b') := ae_l_resp b b' H.

Definition am_eq_stores_a_Type_premise_r (c c' : carrier C) (H : c ≈ c') :
  am_eq f g (am_r c) (am_r c') := ae_r_resp c c' H.

(* CONTROL 1b.  The relation IS the amalgam's own `≈`, and the amalgam's
   [grp_prop] reads it back on the nose in both directions. *)
Definition am_eq_is_the_amalgam_equality (u v : AmTerm B C) :
  @equiv _ (is_setoid (grp_setoid (AmalgamGrp f g))) u v = am_eq f g u v
  := eq_refl.

Definition am_eq_pequiv_to (u v : AmTerm B C)
  (H : @pequiv _ _ (grp_prop (AmalgamGrp f g)) u v) :
  @equiv _ (is_setoid (grp_setoid (AmalgamGrp f g))) u v :=
  pequiv_to u v H.

Definition am_eq_pequiv_from (u v : AmTerm B C)
  (H : @equiv _ (is_setoid (grp_setoid (AmalgamGrp f g))) u v) :
  @pequiv _ _ (grp_prop (AmalgamGrp f g)) u v :=
  pequiv_from u v H.

End AmEq.

(* CONTROL 1c, APPLIED.  The one elimination of [am_eq] in the tree,
   [am_eval_respects], survives: it runs under the TARGET group's [pequiv]
   and comes back with [pequiv_to].  Here it is applied at the mediator. *)
Definition am_med_applies
  {A B C : GrpObject} (f : A ~{Grp}~> B) (g : A ~{Grp}~> C)
  {Q : GrpObject} (q1 : B ~{Grp}~> Q) (q2 : C ~{Grp}~> Q)
  (Hcomm : q1 ∘[Grp] f ≈ q2 ∘[Grp] g) :
  AmalgamGrp f g ~{Grp}~> Q :=
  am_med f g q1 q2 Hcomm.

(* ------------------------------------------------------------------------ *)
(** ** (2) [QuotientGrp]'s `≈` is the truncation of [quot_rel] *)

Section Quot.

Context {G : GrpObject}.
Context (N : NormalSubgroup G).

(* The truncation, read back at [eq_refl]. *)
Definition quot_equiv_is_inhabited_quot_rel (a b : carrier G) :
  @equiv _ (is_setoid (grp_setoid (QuotientGrp N))) a b
    = inhabited (quot_rel N a b) := eq_refl.

(* NEGATIVE 2.  A [Type] destruct of a quotient equation: the witness is
   asked for in a [Type]-valued goal.  Stripped in a copy of this whole
   file; first error line:

     Error:
     Incorrect elimination in the inductive type "inhabited":
     the return type has sort "Type" while it should be SProp or Prop.

   [quot_rel N a b] is [sub_mem N (a * b⁻¹)], which stays [Type]-valued --
   its consumers READ THE WITNESS (Instance/Grp/Quotient/Isomorphism.v's
   [image_med]) -- so recovering it from the quotient's `≈` is exactly the
   elimination that is refused. *)
Fail Definition quot_equiv_yields_the_witness (a b : carrier G)
  (H : @equiv _ (is_setoid (grp_setoid (QuotientGrp N))) a b) :
  quot_rel N a b := ltac:(destruct H).

(* CONTROL 2a.  The [inhabited] route in: one [constructor]. *)
Definition quot_equiv_of_witness (a b : carrier G) (H : quot_rel N a b) :
  @equiv _ (is_setoid (grp_setoid (QuotientGrp N))) a b := inhabits H.

(* CONTROL 2b.  The [inhabited] route out, into a [Prop] goal. *)
Definition quot_equiv_into_Prop (a b : carrier G)
  (H : @equiv _ (is_setoid (grp_setoid (QuotientGrp N))) a b) :
  inhabited (quot_rel N a b) := H.

(* CONTROL 2c.  And into a [Type] goal AT A GROUP, through that group's own
   [grp_prop] -- the repair every consumer of the quotient uses.  Applied:
   this is [quot_med]'s respectfulness obligation, in the shape
   Instance/Grp/Quotient.v carries it. *)
Definition quot_equiv_through_pequiv {K : GrpObject} (p : Kills N K)
  (a b : carrier G)
  (H : @equiv _ (is_setoid (grp_setoid (QuotientGrp N))) a b) :
  grp_map (`1 p) a ≈ grp_map (`1 p) b.
Proof.
  apply (@pequiv_to _ _ (grp_prop K)).
  change (inhabited (quot_rel N a b)) in H.
  destruct H as [H].
  apply (@pequiv_from _ _ (grp_prop K)).
  exact (kills_descends N p a b H).
Defined.

(* CONTROL 2d, APPLIED.  The mediator itself still exists. *)
Definition quot_med_applies {K : GrpObject} (p : Kills N K) :
  QuotientGrp N ~{Grp}~> K := quot_med N p.

(* CONTROL 2e.  [sub_mem] did NOT move: it is still [Type]-valued, and the
   subgroup's own membership still hands back a witness. *)
Definition sub_mem_is_still_data (a : carrier G) (H : sub_mem N a) :
  sub_mem N a := H.

End Quot.

(* ------------------------------------------------------------------------ *)
(** ** (3) The free group's `≈` is a truncation too *)

Section Free.

Context (X : SetoidObject).

(* The truncation, read back at [eq_refl]. *)
Definition fg_equiv_is_inhabited_hom_equiv (a b : FGWord X) :
  @equiv _ (is_setoid (grp_setoid (FreeGrpObject X))) a b
    = inhabited (@equiv _ (@homset (FreeGroupoid (PointQuiver X)) ttt ttt) a b)
  := eq_refl.

(* NEGATIVE 3.  A [Type] elimination out of the free group's equality: the
   free groupoid's hom-equality is [Construction/Quotient.v]'s [CongClosure],
   a [Type]-valued inductive, and recovering it from the truncation is
   refused.  Stripped in a copy of this whole file; first error line:

     Error:
     Incorrect elimination in the inductive type "inhabited":
     the return type has sort "Type" while it should be SProp or Prop. *)
Fail Definition free_equiv_yields_the_groupoid_equation (a b : FGWord X)
  (H : @equiv _ (is_setoid (grp_setoid (FreeGrpObject X))) a b) :
  @equiv _ (@homset (FreeGroupoid (PointQuiver X)) ttt ttt) a b
  := ltac:(destruct H).

(* CONTROL 3a.  The route in: one [inhabits]. *)
Definition free_equiv_of_groupoid_equation (a b : FGWord X)
  (H : @equiv _ (@homset (FreeGroupoid (PointQuiver X)) ttt ttt) a b) :
  @equiv _ (is_setoid (grp_setoid (FreeGrpObject X))) a b := inhabits H.

(* CONTROL 3b.  The route out, at a TARGET group, through [pequiv] -- which
   is how [free_grp_extend]'s respectfulness is proved.  Note what is NOT
   assumed: nothing about [X].  The witness comes from [H], which carries
   [grp_prop] as a field. *)
Definition free_equiv_through_pequiv {H : GrpObject}
  (h : X ~{Sets}~> Grp_Forget H) (a b : FGWord X)
  (Hab : @equiv _ (is_setoid (grp_setoid (FreeGrpObject X))) a b) :
  grp_map (free_grp_extend h) a ≈ grp_map (free_grp_extend h) b :=
  proper_morphism (grp_map (free_grp_extend h)) a b Hab.

End Free.

(* CONTROL 3c, APPLIED AT AN ARBITRARY OBJECT OF [Sets].  The free-forgetful
   adjunction is still TOTAL: the free group is formed, and the universal
   arrow, the functor and the adjunction are named, at an arbitrary
   [X : Sets] with no [PropEquiv] hypothesis.  This is the control the plan's
   finding F1 asks for: the truncation did not restrict the domain. *)
Definition free_group_is_total (X : Sets) : GrpObject := FreeGrpObject X.

Definition free_universal_arrow_is_total (X : Sets) :
  UniversalArrow X Grp_Forget := free_group_universal_arrow X.

Definition free_functor_is_total : Sets ⟶ Grp := FreeGrp.

Definition free_adjunction_is_total : FreeGrp ⊣ Grp_Forget :=
  free_group_adjunction.

Definition free_universal_is_total (X : Sets) :
  ∀ (H : GrpObject) (h : X ~{Sets}~> Grp_Forget H),
    ∃! g : FreeGrpObject X ~{Grp}~> H,
      h ≈ fmap[Grp_Forget] g ∘ fg_insert X :=
  free_group_universal X.

(* ------------------------------------------------------------------------ *)
(** ** (4) What did NOT move *)

(* [grp_coset_rel] (Instance/Grp/Epi.v) is deliberately NOT truncated -- the
   field constrains only the objects it is a field of, and
   [GrpCosetPower]'s witness comes from its CODOMAIN through
   [hom_PropEquiv].  Truncating it would have cost
   [transposition_decides_image] its strength.  That development is probed by
   Test/ProbeGrpEpi*.v and is not restated here; what this file records is
   that the three relations above are the only ones the Grp layer moved. *)

(* [Grp] is locally propositional, which is what lets the functor-of-points
   constructions of Structure/Group/Representable.v be applied at [Grp]
   itself with no manual hypothesis. *)
Definition Grp_is_locally_propositional : LocallyPropositional Grp :=
  Grp_LocallyPropositional.

Definition grp_hom_setoid_is_propositional (G H : GrpObject) :
  PropEquiv (@GrpHom_Setoid G H) := GrpHom_PropEquiv.
