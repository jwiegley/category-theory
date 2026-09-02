Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Adjunction.
Require Import Category.Theory.Equivalence.
Require Import Category.Theory.Equivalence.FullFaithful.
Require Import Category.Theory.Equivalence.Adjoint.
Require Import Category.Construction.Subcategory.
Require Import Category.Construction.Reflective.
Require Import Category.Theory.Skeleton.
Require Import Category.Construction.Subcategory.Dense.
Require Import Category.Instance.Discrete.Reconstruct.
Require Import Category.Theory.Skeleton.Separation.

Generalizable All Variables.

(** * Boundary probe for Construction/Subcategory/Dense.v (issue #375) *)

(* Every boundary the target file's header states as measured is pinned
   here, from OUTSIDE that file: an in-file negative renames in lockstep
   with the constant it guards and so cannot detect a rename.  The
   [Require] list above mirrors the target's exactly, plus the target
   itself and the two modules the witnesses need.

   Five negatives of THREE kinds, kept lexically apart, plus one
   scope-free instrument check:

     CONVERSION  1  the [IsoDense] whole-record round trip does not
                    return -- stdlib [sigT] has no eta
     CONVERSION  2  the counit is not the fullness-lift of the chosen
                    isomorphism on the nose
     TYPING      3  [counit (dense_adj D) a = id[a]] is ill-typed: the two
                    endpoints are different objects of [Sub C S]
     TYPING      4  the reflection adjunction is not the [Reflective]
                    record
     FORMABILITY 5  [Subcategory] identifies its category's hom and proof
                    universes

   Negative 3 is the point of the whole file: Mac Lane's counit-is-the-
   identity depends on choosing a_0 = a for objects already in the
   subcategory, and with the choice supplied as one uniform function the
   representative of an object of the subcategory can be a DIFFERENT
   object.  The witness below is a full subcategory of [Indiscrete bool]
   containing BOTH points whose chosen representative for each point is
   the other point, and the two endpoints are proved distinct
   ([swap_objects_differ]).

   Each negative was stripped ONE AT A TIME, with the others left as
   [Fail], and the whole error read.  Negatives 1 and 2 end in "cannot
   unify"; negatives 3 and 4 report a plain "has type ... while it is
   expected to have type ...", with no "cannot unify" clause and no
   universe clause; negative 5 ends in "universe inconsistency: Cannot
   enforce cp = ch because ch < cp".

   Every constant a negative names also appears outside a [Fail], in a
   control below.  The controls were checked by rename simulation: each
   such constant was renamed throughout this file and the file then
   stopped compiling at a control rather than compiling with a vacuously
   green [Fail]. *)

(** ** Instrument check *)

(* If this command ever succeeds, the [Fail] wrapper is not doing its job
   and every negative below is worthless. *)

Fail Check probe375_no_such_constant_anywhere.

Section Boundaries.

Context {C : Category}.
Context (S : Subcategory C).
Context (F : Subcategory.Full C S).
Context (D : IsoDense S).

(** ** Controls *)

Check (Subcategory C).
Check (Sub C S).
Check (Incl C S).
Check (Incl_Faithful C S).
Check (Full_Implies_Full_Functor C S F).
Check (IsoDense S).
Check (iso_dense_ESO S D).
Check (ESO_iso_dense S (iso_dense_ESO S D)).
Check (dense_incl_equivalence S F D).
Check (dense_incl_adjoint_equivalence S F D).
Check (dense_reflector S F D).
Check (dense_adj S F D).
Check (dense_full_subcategory_reflective S F D : Reflective S).
Check (fun a : Sub C S => dense_counit_iso S F D a).
Check (fun a : Sub C S => dense_counit_Isomorphism S F D a).
Check (fun a : Sub C S =>
         @counit _ _ (dense_reflector S F D) (Incl C S)
           (dense_adj S F D) a).
Check (fun a : Sub C S => @id (Sub C S) a).
Check (reflector (dense_full_subcategory_reflective S F D)).
Check (reflective_adj (dense_full_subcategory_reflective S F D)).
Check (reflective_full (dense_full_subcategory_reflective S F D)).
Check (fun a : Sub C S => reflective_counit_iso
         (dense_full_subcategory_reflective S F D) a).

(** ** CONVERSION 1: the IsoDense round trip does not return *)

(* The object components DO agree at [eq_refl] in both directions
   ([iso_dense_round_obj] and [ESO_iso_dense_obj] in the target), and the
   [EssentiallySurjective] whole record returns as well
   ([ESO_round_whole]), because that is a two-field class and Lib.v:10
   sets [Set Primitive Projections].  Stdlib [sigT] is not covered by
   that setting, so the [IsoDense] record does not. *)

Fail Example probe_iso_dense_round :
  ESO_iso_dense S (iso_dense_ESO S D) = D := eq_refl.

(* The passing controls that locate the difference at the missing eta. *)

Example probe_iso_dense_round_obj (c : C) :
  `1 (ESO_iso_dense S (iso_dense_ESO S D) c) = `1 (D c) := eq_refl.

Example probe_ESO_round_whole (E : EssentiallySurjective (Incl C S)) :
  iso_dense_ESO S (ESO_iso_dense S E) = E := eq_refl.

(** ** CONVERSION 2: the counit does not reduce to the chosen iso *)

(* The counit ought to be the fullness-lift of [`2 (D (Incl C S a))], and
   that statement is true; but the route to it stops at [symmetry] on
   [Functor_Setoid] (Theory/Functor.v:149), whose [Equivalence] obligation
   is closed with [Qed], so the isomorphism family does not reduce.  The
   strict form is refuted here.  The control beside it names both sides of
   the refuted equation in a command that succeeds. *)

Fail Example probe_counit_is_chosen_iso (a : Sub C S) :
  fmap[Incl C S]
    (@counit _ _ (dense_reflector S F D) (Incl C S) (dense_adj S F D) a)
    = to (`2 (D (Incl C S a))) := eq_refl.

Check (fun a : Sub C S =>
         (fmap[Incl C S]
            (@counit _ _ (dense_reflector S F D) (Incl C S)
               (dense_adj S F D) a),
          to (`2 (D (Incl C S a))))).

(** ** TYPING 3: the counit is not the identity, and cannot be *)

(* [counit ... a] runs [dense_reflector D (Incl C S a) ~> a].  Its source
   is the CHOSEN representative of [Incl C S a], which is a value of [D]
   and not [a].  The equation is therefore between morphisms of different
   types.  A witness where the two endpoints are provably distinct is the
   swap witness at the end of this file. *)

Fail Example probe_counit_id (a : Sub C S) :
  @counit _ _ (dense_reflector S F D) (Incl C S) (dense_adj S F D) a
    = @id (Sub C S) a := eq_refl.

(** ** TYPING 4: the adjunction is not the Reflective record *)

Fail Check (dense_adj S F D : Reflective S).

End Boundaries.

(** ** FORMABILITY 5: [Subcategory] identifies hom with proof *)

(* Every constant of the target is over [Category@{u u0 u0}], and the
   identification is inherited rather than introduced: [Subcategory] alone
   already forces it, with the category's own hom-set and identity
   accepted at the very levels where [Subcategory] is rejected.  The
   identification sits in [Subcategory]'s BINDER; its constraint block is
   empty.  Only ONE such negative is pinned: [IsoDense] and [Reflective]
   both take a [Subcategory] argument, so neither can be tested apart from
   this donor. *)

Section UniverseProbe.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).
Context (xu yu : obj[Cu]).

Check (xu ~{Cu}~> yu).
Check (@id Cu xu).
Check (@homset Cu xu yu).

Fail Check (Subcategory Cu).

End UniverseProbe.

(** ** Witness (i): the skeleton of the indiscrete category on bool *)

(* [Indiscrete_bool_Skeleton] (Theory/Skeleton/Separation.v:140) selects
   [true] alone out of the two points of [Indiscrete bool], so the
   reflection is genuinely non-inert at [false].  Note the universe pin
   inherited from the witness: [Indiscrete@{u} : Type@{u} -> Category@{u
   Set Set}], so both readbacks below are about a category whose hom and
   proof universes are the literal [Set].  The general theorem carries no
   such pin. *)

Definition probe_skel_refl :
  Reflective (skel_sub Indiscrete_bool_Skeleton) :=
  skeleton_reflective Indiscrete_bool_Skeleton.

Example probe_skel_true :
  fobj[reflector probe_skel_refl] true
    = skel_rep Indiscrete_bool_Skeleton true := eq_refl.

Example probe_skel_false :
  fobj[reflector probe_skel_refl] false
    = skel_rep Indiscrete_bool_Skeleton false := eq_refl.

(* The carrier of the reflection is [true] at BOTH points ... *)

Example probe_skel_carrier_false :
  `1 (fobj[reflector probe_skel_refl] false) = true := eq_refl.

(* ... so at [false] the reflection moves the object: it is not inert. *)

Example probe_skel_not_inert :
  `1 (fobj[reflector probe_skel_refl] false) = false → False.
Proof. discriminate. Qed.

(** ** Witness (ii): a full subcategory on BOTH points, choosing the other *)

(* Every object of [Indiscrete bool] lies in this subcategory, so the
   subcategory is the whole category and Mac Lane's "for objects a in A we
   can then choose a_0 = a" is available -- but it is a CHOICE, and the
   [IsoDense] datum below makes the other one, sending each point to its
   negation.  Since [Indiscrete bool] has exactly one morphism in each
   hom-set, that is still an iso-density witness. *)

Definition BothPoints : Subcategory (Indiscrete bool) :=
  @Build_Subcategory (Indiscrete bool)
    (fun _ => True)
    (fun _ _ _ _ _ => True)
    (fun _ _ _ _ _ _ _ _ _ _ => I)
    (fun _ _ => I).

Definition BothPoints_Full :
  Construction.Subcategory.Full (Indiscrete bool) BothPoints :=
  fun _ _ _ _ _ => I.

Definition swap_dense : IsoDense BothPoints :=
  fun c => ((negb c; I); Indiscrete_iso (negb c) c).

Definition swap_reflective : Reflective BothPoints :=
  dense_full_subcategory_reflective BothPoints BothPoints_Full swap_dense.

(* The reflector negates. *)

Example swap_reflector_true :
  `1 (fobj[reflector swap_reflective] true) = false := eq_refl.

Example swap_reflector_false :
  `1 (fobj[reflector swap_reflective] false) = true := eq_refl.

(* The two endpoints of the counit at an object [a] are DIFFERENT objects
   of [Sub], which is what makes the identity form ill-typed rather than
   merely unproved. *)

Lemma swap_objects_differ (a : Sub (Indiscrete bool) BothPoints) :
  fobj[reflector swap_reflective] (Incl (Indiscrete bool) BothPoints a) = a
    → False.
Proof.
  destruct a as [b p]; destruct b; simpl; intro H;
  inversion H.
Qed.

(* ... hence the hypothesis that would strictify the counit -- that the
   chosen representative of an object already in the subcategory IS that
   object -- fails outright here.  Even where it holds it does not
   suffice, since the chosen isomorphism may be a non-identity
   automorphism; the target's header records that. *)

Lemma swap_not_self_dense :
  (∀ a : Sub (Indiscrete bool) BothPoints,
      `1 (swap_dense (Incl (Indiscrete bool) BothPoints a)) = a) → False.
Proof.
  intro H; exact (swap_objects_differ ((true; I)) (H (true; I))).
Qed.

(* The counit at such an object is nevertheless an isomorphism, which is
   the form the proposition's third clause takes here. *)

Check (fun a : Sub (Indiscrete bool) BothPoints =>
         dense_counit_iso BothPoints BothPoints_Full swap_dense a).

Check (fun a : Sub (Indiscrete bool) BothPoints =>
         dense_counit_Isomorphism BothPoints BothPoints_Full swap_dense a).
