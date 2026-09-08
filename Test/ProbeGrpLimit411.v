Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Creation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Grp.
Require Import Category.Instance.Grp.Limit.

Generalizable All Variables.

(** * Probe: the measured boundaries of Instance/Grp/Limit.v *)

(* Companion to Instance/Grp/Limit.v (Mac Lane, Categories for the Working
   Mathematician, 2nd ed., §V.1 Theorems 2 and 3).  Everything that file
   claims at [eq_refl] is shipped there as an [Example], so it guards
   itself; what it cannot guard from inside are the two REFUSALS it records
   and the universe boundary a consumer meets.  Those are pinned here, from
   OUTSIDE the target, because an in-file [Fail] renames in lockstep with
   the constant it guards and so cannot detect a rename.

   FOUR negatives of TWO kinds, told apart by the error TEXT rather than by
   label, plus one scope-free instrument check.  Read the KINDS off the
   messages actually produced, which were captured by stripping each [Fail]
   in turn: N1 and N2 report a has-type mismatch between two universe
   INSTANCES of the same head ([Category@{sso so so}] against
   [Category@{_ jh jh}], [Ju ⟶ Sets@{so sso}] against [Ju ⟶ Sets@{jh _}])
   CLOSING WITH the tree's usual formability tail, [(universe
   inconsistency: Cannot enforce so = jh because jh < so)]; N3 reports a
   has-type mismatch carrying a [cannot unify] clause and mentioning no
   universe at all; N4 reports [eq_refl] at the wrong type, likewise with a
   [cannot unify] clause.  So N1 and N2 are told apart from N3 and N4 by the
   universe clause, and N3 from N4 by which term is ill-typed rather than by
   the tail.

     N1  UNIVERSE  [IsALimit] identifies the shape's hom-and-proof universe
                   with the ambient category's, so at a shape whose homs are
                   declared strictly BELOW [Sets]' carrier universe it is
                   refused -- while [Cone] at the very same levels is
                   ACCEPTED, which is what makes the attribution
                   discriminate: the cone vocabulary alone does not impose
                   it.
     N2  UNIVERSE  [sets_limit_ext] is refused at those same levels, and it
                   fires at the FUNCTOR argument -- its binder has already
                   put [Sets]' carrier universe at the shape's hom level,
                   which is the block equation [u0 = u3] the target's header
                   reports on its four generic [Sets] constants.  N1 is what
                   attributes that identification to the donor; nothing here
                   claims [sets_limit_ext] adds one of its own.
     N3  CONVERSION  [CreatesAllLimits] and [StrictlyCreatesLimits] are
                   different types; the target ships an inhabitant of each
                   and neither is an ascription of the other.  Classified by
                   the tree's own convention rather than by shape: the error
                   carries [cannot unify "CreatesLimit K Grp_Forget" and
                   "StrictlyCreatesLimit K Grp_Forget"], and a TYPING
                   negative in this tree is a has-type mismatch with NO such
                   clause.
     N4  CONVERSION  The created group depends on WHICH limit oracle it is
                   fed, definitionally: over [ConeSet_Complete] the carrier
                   is [cone_apex] (the control below) and NOT
                   [Sets_limit_obj], though the two are canonically
                   isomorphic through [limit_unique_iso].  This is what
                   keeps the target's five [grp_complete_*] readbacks
                   honest -- they are statements about the limits
                   [Sets_Complete] chooses, not about limits in general.

   Each negative was stripped ONE AT A TIME in a copy of this WHOLE file --
   not a preamble-plus-command scratch, which would drop the [Section]'s
   [Context] and local [Universes]/[Constraint] declarations and refuse for
   a reason unrelated to the claim -- compiled alone, and its whole error
   read.  Every constant a negative names also appears in a [Check] outside
   every [Fail], so a rename breaks this file loudly instead of turning a
   [Fail] vacuously green.  Measured mechanically: 25 identifiers occur
   inside a [Fail] and 21 also occur outside every one, the four exceptions
   being exhaustively the keyword itself, the two names a [Fail] DECLARES
   (which never enter the environment) and the instrument's deliberately
   absent one.  Rename-simulated 2/2 over the target constants a negative
   names -- [sets_limit_ext] and [Grp_Forget_creates_limits] -- each rename
   breaking this file at a [Check] guard line, never inside a [Fail]. *)

(** ** Instrument check *)

(* A name that is not in scope: if the harness were reporting [Fail]
   successes as failures, or vice versa, this line would say so. *)

Fail Check probe411_no_such_constant.

(** ** Guards: every constant a negative names, named outside every [Fail] *)

Check @IsALimit.
Check @Cone.
Check @sets_limit_ext.
Check @StrictlyCreatesLimits.
Check @CreatesAllLimits.
Check @Grp_Forget_creates_limits.
Check @Grp_Forget_StrictlyCreatesLimits.
Check @Grp_Forget.
Check @Grp_Complete.
Check @grp_setoid.
Check @vertex_obj.
Check @Sets_limit_obj.
Check @cone_apex.
Check @ConeSet_Complete.
Check @Sets_Complete.
Check @creates_limits_Complete.

(** ** N1, N2: the universe boundary, with [Cone] as the control *)

Section UniverseBoundary.

Universes jo jh so sso.
Constraint jh < so.
Constraint so < sso.

Context (Ju : Category@{jo jh jh}).
Context (Fj : Ju ⟶ Sets@{so sso}).
Context (cu : obj[Sets@{so sso}]).

(* Controls: the shape, the diagram and a cone over it are all formable at
   these levels. *)
Check Ju.
Check Fj.
Check (@Cone Ju Sets@{so sso} Fj).

(* N1: UNIVERSE -- the donor. *)
Fail Check (@IsALimit Ju Sets@{so sso} Fj cu).

(* N2: UNIVERSE -- inherited; fires at the functor argument. *)
Fail Check (@sets_limit_ext Ju Fj cu).

End UniverseBoundary.

(** ** N3: the two creation classes are different types *)

Check (Grp_Forget_creates_limits : CreatesAllLimits Grp_Forget).
Check (Grp_Forget_StrictlyCreatesLimits : StrictlyCreatesLimits Grp_Forget).

Fail Definition probe411_n3 : StrictlyCreatesLimits Grp_Forget :=
  Grp_Forget_creates_limits.

(** ** N4: the created group depends on the limit oracle *)

(* The same creation theorem fed Mac Lane's cone-set oracle instead of the
   compatible-family one.  Built here rather than in the library file: it is
   a second [Complete Grp] and must not become the one a consumer sees. *)

Definition Grp_ConeSet_Complete : @Complete Grp :=
  creates_limits_Complete Grp_Forget ConeSet_Complete Grp_Forget_creates_limits.

Section Oracle.

Context {J : Category}.
Context (K : J ⟶ Grp).

(* Control: over the cone-set oracle the carrier IS [cone_apex]. *)
Example probe411_ctrl_coneset :
  grp_setoid (vertex_obj[Grp_ConeSet_Complete J K]) = cone_apex (Grp_Forget ◯ K)
  := eq_refl.

(* N4: CONVERSION. *)
Fail Example probe411_n4 :
  grp_setoid (vertex_obj[Grp_ConeSet_Complete J K])
    = Sets_limit_obj (Grp_Forget ◯ K) := eq_refl.

(* Control: over the compatible-family oracle it IS [Sets_limit_obj] --
   the target's own [grp_complete_carrier], restated here so that the
   negative's discriminating partner sits beside it. *)
Example probe411_ctrl_sets :
  grp_setoid (vertex_obj[Grp_Complete J K]) = Sets_limit_obj (Grp_Forget ◯ K)
  := eq_refl.

End Oracle.
