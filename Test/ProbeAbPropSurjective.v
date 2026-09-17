(* Epi implies PROPOSITIONAL surjectivity in [Ab] and in [RMod R], and not
   the split form.

   Mac Lane's §I.7 proposition -- a homomorphism of abelian groups is epic
   exactly when it is surjective -- is proved in Instance/Ab.v by probing with
   the quotient [B/fA].  Before the PR "algebraic carriers are sets"
   (2026-09-17) the coset relation was [Type]-valued, so the preimage came
   back out as DATA and [ab_epic_surjective] concluded the split
   [AbSurjective].  The relation is now a [Prop] ([ab_coset_eq]), because
   every [AbObject] carries [cmon_prop] and a quotient's equality has to be a
   [Prop] for the field to be supplied at all.  The conclusion is therefore
   [AbPropSurjective], and the preimage is no longer data.

   Nothing is doubly negated and no choice principle is consumed: the
   existential is Coq's [ex].  What the negatives below pin is exactly the one
   thing lost -- the [Prop] existential cannot be destructed into the
   [Type]-valued [AbSurjective] -- and the controls show the two directions
   that survive: the split notion still implies the propositional one
   ([ab_surjective_prop]), and it still implies [Epic] ([ab_surjective_epic]).

   Both negatives were stripped once, in a copy of this whole file, and both
   report

     Error: Incorrect elimination in the inductive type "ex": the return type
     has sort "Type" while it should be SProp or Prop.  Elimination of an
     inductive object of sort Prop is not allowed on a predicate in sort
     "Type" because proofs can be eliminated only to build proofs.

   The import lists are the union of Instance/Ab.v's and Instance/Mod.v's. *)

Require Import Category.Lib.
Require Import Category.Lib.Setoid.Propositional.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Initial.
Require Import Category.Structure.ZeroObject.
Require Import Category.Structure.AbCategory.
Require Import Category.Structure.Preadditive.
Require Import Coq.ZArith.ZArith.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Propositional.
Require Import Category.Instance.CMon.
Require Import Category.Instance.CMon.Biproduct.
Require Import Category.Instance.Ab.
Require Import Category.Instance.Rng.
Require Import Category.Instance.Mod.
Require Import Category.Theory.Algebra.Rig.

Generalizable All Variables.

(** ** NEGATIVE: the propositional witness is not data *)

(* The [Prop] existential may not be destructed into the [Type]-valued
   [AbSurjective].  A [Fail Lemma] on the statement alone would be vacuous --
   [AbPropSurjective f → AbSurjective f] is a perfectly well formed type --
   so the negative carries its proof. *)
Fail Definition ab_prop_surjective_is_not_split
  {A B : AbObject} (f : A ~{Ab}~> B) (Hs : AbPropSurjective f) :
  AbSurjective f :=
  ltac:(intro b; destruct (Hs b) as [a Ha]; exists a;
        exact (pequiv_to _ _ Ha)).

(* The same for modules. *)
Fail Definition rmod_prop_surjective_is_not_split
  {R : RingObject} {M N : RModObject R} (f : M ~{RMod R}~> N)
  (Hs : RModPropSurjective f) : RModSurjective f :=
  ltac:(intro b; destruct (Hs b) as [a Ha]; exists a;
        exact (pequiv_to _ _ Ha)).

(** ** CONTROLS: the directions that survive *)

(* The split notion implies the propositional one -- the direction that
   loses nothing, and the positive control for the two negatives above. *)
Example ab_split_implies_prop {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSurjective f → AbPropSurjective f :=
  ab_surjective_prop f.

Example rmod_split_implies_prop {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : RModSurjective f → RModPropSurjective f :=
  rmod_surjective_prop f.

(* Both notions still imply [Epic]; the split one directly, the
   propositional one through [pequiv_to].  The split half ([ab_split_epic])
   also compiles in the unchanged tree: it is a not-lost check, not a
   control of the change; the propositional halves cannot even be stated
   there. *)
Example ab_split_epic {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSurjective f → Epic f := ab_surjective_epic f.

Example ab_prop_epic {A B : AbObject} (f : A ~{Ab}~> B) :
  AbPropSurjective f → Epic f := ab_prop_surjective_epic f.

Example rmod_prop_epic {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : RModPropSurjective f → Epic f :=
  rmod_prop_surjective_epic f.

(* And the headline biconditionals, APPLIED, at their restated strength. *)
Example ab_epic_iff {A B : AbObject} (f : A ~{Ab}~> B) :
  Epic f ↔ AbPropSurjective f := ab_epic_iff_surjective f.

Example rmod_epic_iff_readback {R : RingObject} {M N : RModObject R}
  (f : M ~{RMod R}~> N) : Epic f ↔ RModPropSurjective f :=
  rmod_epic_iff f.

(** ** The split notions are still there, and still say what they said *)

(* A not-lost check (it holds in the unchanged tree too), not a control of
   the change. *)
Example ab_surjective_is_sigma {A B : AbObject} (f : A ~{Ab}~> B) :
  AbSurjective f
    = (∀ b : carrier (cmon_setoid B), { a & cmon_map f a ≈ b })
  := eq_refl.

(** ** Instrument check, scope-free *)

Fail Example probe_ab_prop_surjective_instrument : true = false := eq_refl.
