Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Functor.Bifunctor.Partial.
Require Import Category.Functor.Diagonal.
Require Import Category.Construction.Product.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Sets.
Require Import Category.Instance.One.
Require Import Category.Instance.Two.
Require Import Category.Instance.Two.Discrete.
Require Import Category.Theory.Bicategory.
Require Import Category.Instance.Cat.Bicategory.
Require Import Category.Theory.Concrete.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Subcategory.Finite.
Require Import Category.Instance.Sets.Powerset.
Require Import Category.Functor.Construction.Postcompose.

Generalizable All Variables.

(** * Probes guarding Functor/Construction/Postcompose.v *)

(* This file pins every strict attempt that Functor/Construction/Postcompose.v
   MADE AND LOST, so that a later change which quietly makes one of them
   succeed — or which renames the constants out from under the claim — breaks
   the build loudly instead of leaving the header's prose stale.  It follows
   the convention of Test/ProbeFunnyPoly.v and Test/ProbeQuiverConstructions.v.

   The import list is the target file's, in the target file's order, with
   Instance/Sets/Powerset.v (needed only by Group 4) and then the target
   itself appended.  That matters: a probe compiled against a short PREFIX of
   the real imports can fail for a missing-coercion or missing-notation
   reason and thereby pass VACUOUSLY.  (Instance/Field/Frac.v records an
   episode of exactly that.)  A superset does not carry that risk, and the
   target is Required last, so its names win any contest.

   TWO KINDS, KEPT LEXICALLY APART.

     CONVERSION negatives are written [Fail Definition ... := eq_refl] and say
     that two well-typed terms are not definitionally equal.

     FORMABILITY negatives are written [Fail Check] and say that a term
     cannot be elaborated at all, here always because of a universe
     constraint.

   Each negative was stripped of its [Fail] and the resulting error read, and
   the diagnosis is recorded beside it.  Positive controls accompany each
   group; the instrument is sanity-checked by a control that differs from the
   negative in exactly the disputed spot.

   Inventory: 5 conversion negatives, 4 formability negatives, 12 positive
   controls. *)

(** ** Group 1 (CONVERSION): the Hcompose route's arrow action *)

Section HcomposeConversion.

Context {D E E' : Category}.
Context (J : E ⟶ E').
Context (K L : D ⟶ E).
Context (θ : K ⟹ L).

(* POSITIVE CONTROL 1.  The OBJECT actions of the two routes DO agree on the
   nose, so the instrument is not simply rejecting everything about
   [PostcomposeViaHcompose]. *)
Definition control_hcompose_obj :
  fobj[PostcomposeViaHcompose J] K = fobj[Postcompose J] K := eq_refl.

(* POSITIVE CONTROL 2.  The Hcompose route's component IS
   [fmap[J] id ∘ fmap[J] (θ x)] on the nose — this is what the negative
   below is measuring the presence of. *)
Definition control_hcompose_component (x : D) :
  transform[fmap[PostcomposeViaHcompose J] θ] x
    = fmap[J] (@id E (L x)) ∘ fmap[J] (transform[θ] x) := eq_refl.

(* NEGATIVE 1 (conversion).  The arrow actions are not Leibniz-equal.  Cause,
   read off the stripped error: [Partial_r]'s [fmap] is [bimap F id g], i.e.
   [fmap[Cat_Hcompose] (id, g)], and [Cat_Hcompose]'s [fmap] is the Godement
   product [nat_hcompose], whose component at x is
   [transform[ε] (L x) ∘ fmap[J] (transform[η] x)] with ε the IDENTITY
   transformation — and [nat_id]'s component is [fmap[J] id], not [id].  So
   the Hcompose route carries a unit that left whiskering does not. *)
Fail Definition negative_hcompose_fmap :
  fmap[PostcomposeViaHcompose J] θ = fmap[Postcompose J] θ := eq_refl.

(* NEGATIVE 2 (conversion).  A fortiori the two functor records are not
   Leibniz-equal.  This is stated separately from Negative 1 because the two
   could in principle come apart: [Postcompose]'s three law fields are
   [Program] obligations, hence opaque, so even had the [fmap]s converted the
   records would not. *)
Fail Definition negative_hcompose_functor :
  PostcomposeViaHcompose J = Postcompose J := eq_refl.

(* NEGATIVE 3 (conversion).  Not even componentwise at a fixed x. *)
Fail Definition negative_hcompose_component (x : D) :
  transform[fmap[PostcomposeViaHcompose J] θ] x
    = transform[fmap[Postcompose J] θ] x := eq_refl.

(* POSITIVE CONTROL 3.  All three hold up to `≈`, which is the strength the
   library file claims. *)
Definition control_hcompose_equiv :
  fmap[PostcomposeViaHcompose J] θ ≈ fmap[Postcompose J] θ :=
  postcompose_via_hcompose_fmap J K L θ.

End HcomposeConversion.

(** ** Group 2 (CONVERSION): [prefmap] does not compute *)

Section PrefmapConversion.

(* POSITIVE CONTROL 4.  The FORWARD leg of the isomorphism computes: it is
   the functor's own action on 2-cells, on the nose. *)
Definition control_iso_to (θ : finpost_K ⟹ finpost_K) :
  to finpost_hom_iso θ = fmap[SubPostcompose FinSets] θ := eq_refl.

(* NEGATIVE 4 (conversion).  The BACKWARD leg does not.  Cause, read off the
   stripped error: the [Full] instance in play is produced by
   Construction/Subcategory.v:104's [Full_Implies_Full_Functor], which is a
   `Qed` lemma; its [prefmap] field is therefore an opaque constant and no
   component of it reduces.  The obstruction is the donor's opacity — nothing
   about this construction, and nothing about [Full] as a class. *)
Fail Definition negative_prefmap_component (x : _1) :
  transform[from finpost_hom_iso finpost_phi] x = FinSets_negb := eq_refl.

(* POSITIVE CONTROL 5.  It does hold up to `≈`, by [fmap_sur]. *)
Definition control_prefmap_component (x : _1) :
  transform[from finpost_hom_iso finpost_phi] x ≈ FinSets_negb :=
  finpost_preimage_component x.

(* NEGATIVE 5 (conversion).  The round trip is `≈` and not Leibniz, for the
   same reason: [from] of [to] rebuilds a [Transform] record whose components
   are [prefmap] applied to whiskered components. *)
Fail Definition negative_roundtrip :
  from finpost_hom_iso (to finpost_hom_iso finpost_theta) = finpost_theta
    := eq_refl.

(* POSITIVE CONTROL 6.  The round trip at `≈`, which IS what
   [postcompose_hom_iso] proves. *)
Definition control_roundtrip :
  from finpost_hom_iso (to finpost_hom_iso finpost_theta) ≈ finpost_theta :=
  iso_from_to finpost_hom_iso finpost_theta.

End PrefmapConversion.

(** ** Group 3 (FORMABILITY): the hom universes cannot be kept apart *)

(* [Postcompose] identifies the hom AND proof universes of all three of its
   categories.  The object universes stay free.  Both halves are probed. *)

Section UniverseFormability.

(* POSITIVE CONTROL 7.  Three categories with STRICTLY INCREASING object
   universes and one shared hom universe: [Postcompose] elaborates.  So the
   object universes really are free, and the negatives below are not simply
   rejecting any annotated instantiation. *)
Section ObjectsFree.
  Universes uo1 uo2 uo3 uh.
  Constraint uo1 < uo2.
  Constraint uo2 < uo3.

  Check (fun (D : Category@{uo1 uh uh}) (E : Category@{uo2 uh uh})
             (E' : Category@{uo3 uh uh}) (J : E ⟶ E') =>
           @Postcompose D E E' J).
End ObjectsFree.

(* NEGATIVE 6 (formability).  Keeping the SOURCE and TARGET hom universes of
   J apart is rejected.  Stripping the [Fail] yields a universe inconsistency
   naming the declared constraint.  Cause: Theory/Functor.v's [Compose] is
   declared over [Category@{_ h h}] for all three of its categories, so the
   object action [J ◯ K] alone forces the identification; Instance/Fun.v's
   [Fun] independently carries [u0 = u2] between its source and target hom
   levels.  Neither pin is introduced by this development. *)
Section HomsApart.
  Universes uo uh1 uh2.
  Constraint uh1 < uh2.

  Fail Check (fun (D : Category@{uo uh1 uh1}) (E : Category@{uo uh1 uh1})
                  (E' : Category@{uo uh2 uh2}) (J : E ⟶ E') =>
                @Postcompose D E E' J).
End HomsApart.

(* NEGATIVE 7 (formability).  Same for the SHAPE category's hom universe
   against the two others. *)
Section ShapeHomApart.
  Universes uo uh1 uh2.
  Constraint uh1 < uh2.

  Fail Check (fun (D : Category@{uo uh1 uh1}) (E : Category@{uo uh2 uh2})
                  (E' : Category@{uo uh2 uh2}) (J : E ⟶ E') =>
                @Postcompose D E E' J).
End ShapeHomApart.

(* POSITIVE CONTROL 8.  INSTRUMENT SANITY CHECK.  The two negatives differ
   from this control in exactly the disputed spot: drop the [Constraint] and
   let the three hom universes be the same, and the very same term
   elaborates.  So the rejection is attributable to the constraint and not to
   the annotation style, the explicit [@], or the section apparatus. *)
Section HomsTogether.
  Universes uo uh1 uh2.

  Check (fun (D : Category@{uo uh1 uh1}) (E : Category@{uo uh1 uh1})
             (E' : Category@{uo uh2 uh2}) (J : E ⟶ E') =>
           @Postcompose D E E' J).
End HomsTogether.

End UniverseFormability.

(** ** Group 4 (FORMABILITY): the enlargement of Sets is out of reach *)

(* Mac Lane's remark 1 is about enlarging the ambient category of SETS.  The
   in-tree functor that does that is Instance/Sets/Powerset.v:262's
   [Sets_Lift : Sets@{o so} ⟶ Sets@{so sso}], the identity on carriers
   re-typed one level up.  Postcomposition along it does not exist, and the
   two probes below locate the obstruction precisely: one need not reach the
   functor category or [Postcompose] to meet it, because Theory/Functor.v's
   [Compose] already suffices — [Compose] being
   declared over three categories sharing ONE hom-and-proof level, whereas
   [Sets@{o so}] has hom level [o] and [Sets@{so sso}] has hom level [so]
   with [o < so] forced by [Sets]' own declaration.  This does NOT exculpate
   the functor category, which carries an independent wall of the same kind:
   [Fun] identifies its source and target hom levels, so the two [Sets]
   levels could not index one functor category either.

   Stripping either [Fail] yields "universe inconsistency: Cannot enforce
   ... because ... < ...", naming exactly those two levels. *)

Section SetsEnlargement.

(* NEGATIVE 8 (formability).  [Postcompose] along the lift. *)
Fail Check (fun (D : Category) => Postcompose (D:=D) Sets_Lift).

(* NEGATIVE 9 (formability).  And already the bare object action, with no
   functor category and no [Postcompose] in sight — which is what shows the
   wall belongs to [Compose]. *)
Fail Check (fun (D : Category) (K : D ⟶ Sets) => Sets_Lift ◯ K).

(* POSITIVE CONTROLS 9 and 10.  INSTRUMENT SANITY CHECK.  [Sets_Lift] itself
   elaborates, and the same composite shape with a LEVEL-PRESERVING functor
   in its place is fine — so the instrument is not rejecting every mention of
   [Sets_Lift], nor the shape [_ ◯ K], but exactly the composite that would
   need the two levels' hom universes identified. *)
Check Sets_Lift.

Check (fun (D : Category) (K : D ⟶ Sets) => (Id[Sets]) ◯ K).

End SetsEnlargement.

(** ** Group 5: the headline results are inhabited at the witness *)

(* POSITIVE CONTROLS 11 and 12.  The two boundary theorems of the library
   file, each named at its full type, so that a rename or a weakening of
   either statement breaks this file. *)

Definition control_finpost_iso :
  (finpost_K ⟹ finpost_K)
    ≊ (FinSets_Incl ◯ finpost_K ⟹ FinSets_Incl ◯ finpost_K) :=
  finpost_hom_iso.

Definition control_full_needed :
  Category.Theory.Functor.Full (Postcompose (D:=_1) DiscToTwo) → False :=
  postcompose_full_needs_full.
