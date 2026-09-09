Require Import Category.Lib.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Limit.
Require Import Category.Instance.Cones.

Generalizable All Variables.

(** * Limit as a terminal cone *)

(* nLab:      https://ncatlab.org/nlab/show/limit
   Wikipedia: https://en.wikipedia.org/wiki/Limit_(category_theory)

   Wikipedia: a limit "may also be characterized as terminal objects in the
   category of cones to F." nLab agrees: the limit lim F is the universal cone,
   "precisely the terminal object in the category of all cones over F", since
   every cone has a unique morphism into it.

   This file makes that characterization constructive: from a terminal object
   [T] of [Cones F] (see [Instance/Cones.v], the category whose objects are
   cones over F and whose morphisms are apex maps commuting with the legs) we
   build a [Limit F] (see [Structure/Limit.v]). The terminal cone becomes
   [limit_cone], and the universal property [ump_limits] is read off from
   terminality of [T]:

     - the mediating morphism on apexes is [`1 (one N)], the apex component of
       the unique cone map [! : N ~> T];
     - it satisfies the leg-factorization φ_x ∘ u ≈ ψ_x by [`2 (one N)], the
       commuting condition packaged into that cone morphism;
     - its uniqueness follows from [one_unique]: any apex map [v] carrying its
       own factorization proof [H] yields a cone morphism [(v; H)] into [T],
       which terminality forces to equal [one N] (hence v equals u on apexes).

   Dually, a colimit is the terminal object of [Cocones F] -- [Cones (F^op)],
   whose arrows run in C^op, so "initial in the category of cocones" reads
   as TERMINAL there -- obtained below by instantiating this at [F^op]. *)
Program Definition Limit_Cones `(F : J ⟶ C) `{T : @Terminal (Cones F)} :
  Limit F := {|
  limit_cone := @terminal_obj _ T;
  ump_limits := fun N =>
    {| unique_obj := `1 (@one _ T N)
     ; unique_property := `2 (@one _ T N)
     ; uniqueness       := fun v H => @one_unique _ T N (@one _ T N) (v; H) |}
|}.

(** * The converse, and the colimit readings *)

(* The converse of [Limit_Cones]: the limit cone is terminal in [Cones F].
   Its unique arrow from a cone [N] is the limit's mediator with its own
   factorization proof, and uniqueness is [uniqueness] twice.

   COLIMITS.  With [Cocones F := Cones (F^op)] (Instance/Cones.v), a cocone
   morphism is an arrow of C^op, so the colimit -- the initial cocone in the
   textbook's covariant reading -- is the TERMINAL object of [Cocones F].
   [Colimit F] is [Limit (F^op)] definitionally (Structure/Limit.v), so the
   two passages below are [Limit_Cones]/[Cones_Limit] at [F^op] with no
   tactic.  The covariant spelling [Initial ((Cocones F)^op)] is THE SAME
   TYPE, [(X^op)^op = X] holding by [eq_refl] here, which
   [initial_op_is_terminal] records; [Initial (Cocones F)] itself is a
   DIFFERENT type (terminality in [(Cocones F)^op]), refuted at [eq_refl]
   and pinned in Test/ProbeFinite417.v. *)

Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Structure.Initial.

Definition Cones_Limit `(F : J ⟶ C) (L : Limit F) : @Terminal (Cones F).
Proof.
  unshelve refine (@Build_Terminal (Cones F) (@limit_cone _ _ _ L)
    (fun N => (unique_obj (@ump_limits _ _ _ L N);
               unique_property (@ump_limits _ _ _ L N))) _).
  intros N f g; simpl.
  transitivity (unique_obj (@ump_limits _ _ _ L N)).
  - symmetry.
    exact (uniqueness (@ump_limits _ _ _ L N) (`1 f) (`2 f)).
  - exact (uniqueness (@ump_limits _ _ _ L N) (`1 g) (`2 g)).
Defined.

Definition Colimit_Cocones `(F : J ⟶ C) (T : @Terminal (Cocones F)) :
  Colimit F := @Limit_Cones _ _ (Opposite_Functor F) T.

Definition Cocones_Colimit `(F : J ⟶ C) (L : Colimit F) :
  @Terminal (Cocones F) := Cones_Limit (Opposite_Functor F) L.

Definition Colimit_Cocones_initial `(F : J ⟶ C)
  (I : @Initial (Opposite (Cocones F))) : Colimit F := Colimit_Cocones F I.

Definition Cocones_Colimit_initial `(F : J ⟶ C) (L : Colimit F) :
  @Initial (Opposite (Cocones F)) := Cocones_Colimit F L.

Example initial_op_is_terminal `(F : J ⟶ C) :
  @Initial (Opposite (Cocones F)) = @Terminal (Cocones F) := eq_refl.
