Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Functor.Bifunctor.
Require Import Category.Construction.Opposite.
Require Import Category.Construction.Product.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Natural.
Require Import Category.Structure.Monoidal.
Require Import Category.Structure.Monoidal.Internal.Product.
Require Import Category.Structure.Wedge.
Require Import Category.Structure.Coend.
Require Import Category.Construction.Enriched.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Cartesian.
Require Import Category.Instance.Sets.Cartesian.Closed.
Require Import Category.Structure.Cartesian.Closed.Composition.

Generalizable All Variables.

(** * Probe for Structure/Cartesian/Closed/Composition.v (issue #391) *)

(* Mac Lane §IV.6 Exercise 4 (`maclane:IV.6:ex4`).  Everything the target
   MEASURES and does not itself state is pinned here, from OUTSIDE that
   file, so that a rename of a target constant breaks this probe rather
   than silently turning a guard green.  The `Require` list above mirrors
   the target's exactly, plus the target itself.

   FIVE negatives of THREE kinds, told apart by the error text:

     1  CONVERSION  the [Sets] agreement does not hold at Leibniz equality
                    on whole MORPHISMS -- only pointwise
     2  TYPING      the naive functorial action in [b] is not well typed,
                    which is why there is no naturality square in [b]
     3  CONVERSION  the two candidate hom-TYPES of that action differ
     4  CONVERSION  a functor whose [fobj] is elaborated inside its own
                    [Program Definition] converts with nothing
     5  FORMABILITY [Cartesian] identifies a category's hom and proof
                    universes, which is where the target's binder
                    [Category@{u u0 u0}] comes from

   plus one scope-free instrument check.  Each was stripped one at a time,
   compiled alone, and its whole error read. *)

(* Instrument check: a name that cannot exist must be rejected, so that no
   negative below can pass for the wrong reason. *)
Fail Check no_such_constant_exists_in_this_development.

(** ** Controls: every constant a negative names, outside any rejection *)

Check @internal_compose.
Check @internal_id.
Check @internal_compose_assoc.
Check @internal_compose_dinatural.
Check @internal_compose_natural_a.
Check @internal_compose_natural_c.
Check @internal_compose_Wedge.
Check @CCC_Enriched.
Check @Sets_Enriched.
Check @ExpBase.
Check @expBase_fobj.
Check @ComposeSrcC.
Check @composeSrcC_fobj.
Check @sets_internal_compose.
Check @sets_internal_compose_underlying.
Check @sets_internal_compose_morphism.
Check @sets_internal_id.
Check @ihom.
Check @Cartesian.
Check @Closed.
Check @split.
Check @fobj.
Check Sets.

(** ** Negative 1 (CONVERSION): the [Set] agreement is pointwise only *)

(* The value at each point IS [g (f t)] on the nose -- that is the shipped
   [sets_internal_compose].  The two WHOLE morphisms of [Sets] are not
   Leibniz-equal: [SetoidMorphism] carries a [proper_morphism] certificate
   that the two sides build differently.  The two underlying FUNCTIONS do
   agree at [eq_refl] (control below), which locates the difference in the
   certificate and nowhere else. *)

Example p391_ctrl_pointwise (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) (t : a) :
  @internal_compose Sets _ _ a b c (g, f) t = g (f t) := eq_refl.

Example p391_ctrl_underlying (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) :
  (fun t : a => @internal_compose Sets _ _ a b c (g, f) t)
    = (fun t : a => (g ∘[Sets] f) t) := eq_refl.

Example p391_ctrl_equiv (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) :
  @internal_compose Sets _ _ a b c (g, f) ≈[Sets] g ∘ f.
Proof. intro t; reflexivity. Qed.

Fail Example p391_neg1 (a b c : Sets)
        (g : b ~{Sets}~> c) (f : a ~{Sets}~> b) :
  (@internal_compose Sets _ _ a b c (g, f) : a ~{Sets}~> c) = g ∘ f
  := eq_refl.

Section ProbeGeneral.

Context {C : Category}.
Context `{@Cartesian C}.
Context `{@Closed C _}.

(** ** Negative 2 (TYPING): there is no functorial action in [b] *)

(* In [c^b × b^a] the variable [b] is contravariant on the left and
   covariant on the right.  An arrow [f : b1 ~> b2] therefore acts on the
   two factors in OPPOSITE directions, and the resulting morphism runs
   between the MIXED objects [c^b2 × b1^a] and [c^b1 × b2^a] -- not
   between [c^b1 × b1^a] and [c^b2 × b2^a], which is what a functor of [b]
   would have to supply.  So this action does not give a functor of [b],
   and hence gives no [Transform] in [b] for a naturality square to live
   in; what holds instead is the cowedge condition
   [internal_compose_dinatural], controlled above and again here. *)

(* The action, at the type it actually has. *)
Example p391_ctrl_b_action (a c b1 b2 : C) (f : b1 ~{C}~> b2) :
  (c^b2 × b1^a) ~{C}~> (c^b1 × b2^a) :=
  split (ihom f id) (ihom id f).

(* The honest statement in [b], as a passing control. *)
Example p391_ctrl_dinatural (a c b1 b2 : C) (f : b1 ~{C}~> b2) :
  @internal_compose C _ _ a b1 c ∘ split (ihom f id) id
    ≈ @internal_compose C _ _ a b2 c ∘ split id (ihom id f)
  := internal_compose_dinatural f.

Fail Example p391_neg2 (a c b1 b2 : C) (f : b1 ~{C}~> b2) :
  (c^b1 × b1^a) ~{C}~> (c^b2 × b2^a) :=
  split (ihom f id) (ihom id f).

(** ** Negative 3 (CONVERSION): the two hom-types are not the same type *)

(* Stated on the TYPES rather than on an inhabitant, so that no coercion
   can make it pass for the wrong reason. *)

Example p391_ctrl_type_refl (a c b1 b2 : C) :
  ((c^b2 × b1^a) ~{C}~> (c^b1 × b2^a))
    = ((c^b2 × b1^a) ~{C}~> (c^b1 × b2^a)) := eq_refl.

Fail Example p391_neg3 (a c b1 b2 : C) :
  ((c^b2 × b1^a) ~{C}~> (c^b1 × b2^a))
    = ((c^b1 × b1^a) ~{C}~> (c^b2 × b2^a)) := eq_refl.

(** ** Negative 4 (CONVERSION): the [Program]-elaborated [fobj] is opaque *)

(* Structure/Cartesian/Closed/Natural.v:315-321 records that writing the
   object action INSIDE a [Program Definition] lets [Program] defer an
   unresolved instance argument of [product_obj] into an obligation, which
   Lib/Foundation.v's [Unset Transparent Obligations] makes opaque; the
   resulting [fobj] then converts with nothing.  The target met that
   hazard again and elaborates its object actions first.

   The boundary is MEASURED here rather than assumed, and it is narrower
   than "any inline object action": [NaiveExpBase], whose object action is
   an [exponent_obj] alone, DOES reduce (control below), while
   [NaiveComposeSrcC], whose object action is a [product_obj], does not.
   What the two commands establish is that separation; that the deferred
   argument is [product_obj]'s is the donor's own attribution, quoted
   above and not re-derived here. *)

Program Definition NaiveExpBase (a : C) : C ⟶ C := {|
  fobj := fun c => c^a;
  fmap := fun _ _ g => ihom id g
|}.
Next Obligation. proper; now rewrites. Qed.
Next Obligation. apply ihom_id. Qed.
Next Obligation. rewrite ihom_comp; now rewrite id_left. Qed.

Program Definition NaiveComposeSrcC (a b : C) : C ⟶ C := {|
  fobj := fun c => c^b × b^a;
  fmap := fun _ _ g => first (ihom id g)
|}.
Next Obligation. proper; now rewrites. Qed.
Next Obligation. rewrite ihom_id; apply first_id. Qed.
Next Obligation.
  rewrite <- first_comp, ihom_comp; now rewrite id_left.
Qed.

(* The target's functor, which does reduce ... *)
Example p391_ctrl_fobj (a b c : C) :
  fobj[ComposeSrcC a b] c = c^b × b^a := eq_refl.

(* ... and the exponent-only naive functor, which also does. *)
Example p391_ctrl_naive_exp (a c : C) :
  fobj[NaiveExpBase a] c = c^a := eq_refl.

Fail Example p391_neg4 (a b c : C) :
  fobj[NaiveComposeSrcC a b] c = c^b × b^a := eq_refl.

End ProbeGeneral.

(** ** Negative 5 (FORMABILITY): [Cartesian] identifies hom with proof *)

(* Every constant of the target is over [C : Category@{u u0 u0}] in its
   BINDER, while not one of its constraint BLOCKS contains a universe
   equation -- reading the blocks alone would report no identification.
   The identification is inherited, and [Cartesian] alone already forces
   it: at a category whose hom and proof universes are declared strictly
   apart the category itself, its objects, its hom-sets and its identities
   are all accepted, and only [Cartesian] is rejected. *)

Section ProbeUniverses.

Universes co ch cp.
Constraint ch < cp.

Context (Cu : Category@{co ch cp}).

Check obj[Cu].
Check (fun x y : Cu => x ~{Cu}~> y).
Check (fun x : Cu => id[x]).
Check (fun (x y z : Cu) (f : y ~{Cu}~> z) (g : x ~{Cu}~> y) => f ∘ g).

Fail Check (@Cartesian Cu).

End ProbeUniverses.
