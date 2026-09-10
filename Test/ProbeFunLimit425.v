(** * Probe for Instance/Fun/Limit.v (issue #425)

    Pins the measured boundaries of pointwise limits in a functor category:
    the image of the pointwise cone under evaluation is the chosen limit
    cone in apex and legs but not as a record, the packaged corollaries
    must be universe-annotated at the definition, and [Limit] identifies
    the shape's hom level with the ambient's.  Every refutation command
    below was stripped ONE AT A TIME in a copy of the whole file and
    compiled alone with its error read, so each refusal is of the kind its
    label says.

    Numbering:
     instrument      an absent name, refused — the refutation keyword is
                     live in this file.
     N1 CONVERSION   [FCone (Eval p) (PointwiseLimitCone D L) = limit_cone
                     (L p)] is refused at [eq_refl] ("cannot unify"): the
                     coherence field is a rebuilt proof and [≈] is
                     Type-valued.  Controls: the apex and every leg convert
                     ([p425_fcone_apex], [p425_fcone_leg]), as do the diagram
                     at p, the object action, the leg components, the
                     mediator's components and the packaged limit's cone.
     N2 UNIVERSE     the corollary's body written BARE at top level
                     ([p425_bare_complete]) is refused at a category whose
                     object level sits strictly below its hom level
                     ("Cannot enforce jh = jo because jo < jh"): universe
                     minimization identifies the two.  Control: the
                     definition-annotated [Functor_Category_Complete] is
                     accepted at the same levels.
     N3 UNIVERSE     at a shape whose homs sit strictly below X's, [Limit F]
                     is refused ("Cannot enforce ch = ih because ih < ch") —
                     Structure/Limit.v's [Limit] is stated at [{J :
                     Category@{u0 u1 u1}} {C : Category@{u2 u1 u1}}] — while
                     the diagram F and [Cone F] are accepted (controls;
                     Structure/Cone.v's record is innocent).

    Positive controls, deliberately NOT written as refutations: the
    unfolded [Fun_HasLimitsOfShape] ascribes at Adjunction/Diagonal/
    Limit.v's [HasLimitsOfShape] ([p425_hlos]) and yields [LimitFunctor] on
    [P, X] ([p425_LimitFunctor]) — so the library file need not pay that
    import; and the presheaf corollaries.  No refutation is written for the
    absence of a colimit dual or of creation: those are #715's and #426's,
    metatheoretic here.

    Guard coverage: every constant a refutation names is also named
    outside a refutation command (the guard block at the end) — the
    exceptions, under the plain identifier tokenization with comments
    stripped, being the keyword itself, the name the refuted declaration
    would introduce and the instrument's absent name — so a renamed or
    removed constant breaks the build on a positive line rather than
    letting a refutation pass for the wrong reason. *)

Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Natural.Transformation.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Fun.
Require Import Category.Instance.Fun.Eval.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Complete.
Require Import Category.Instance.Fun.Limit.
Require Import Category.Adjunction.Diagonal.Limit.
Require Import Category.Instance.Fun.Terminal.

Generalizable All Variables.

(* instrument: the refutation keyword is live *)
Fail Check probe425_absent_name.

(** ** A: the image of the pointwise cone under evaluation IS the chosen
       limit cone in apex and legs, but not as a record *)

Section ImageCone.

Context {J P X : Category} (D : J ⟶ [P, X]) (L : ∀ p : P, Limit (Eval p ◯ D)).

(* readbacks: the diagram at p, the object action, the leg components *)
Example p425_diagram_obj (p : P) (j : J) :
  fobj[Eval p ◯ D] j = fobj[fobj[D] j] p := eq_refl.

Example p425_plim_obj (p : P) :
  fobj[PointwiseLimit D L] p = vertex_obj[@limit_cone _ _ _ (L p)] := eq_refl.

Example p425_leg_component (j : J) (p : P) :
  transform[cone_leg (PointwiseLimitCone D L) j] p
  = limit_leg (limit_is_alimit (L p)) j := eq_refl.

(* controls: apex and every leg of the image cone convert *)
Example p425_fcone_apex (p : P) :
  vertex_obj[FCone (Eval p) (PointwiseLimitCone D L)]
  = vertex_obj[@limit_cone _ _ _ (L p)] := eq_refl.

Example p425_fcone_leg (p : P) (j : J) :
  cone_leg (FCone (Eval p) (PointwiseLimitCone D L)) j
  = cone_leg (@limit_cone _ _ _ (L p)) j := eq_refl.

(* N1 CONVERSION: the whole record does not — its coherence field is a
   rebuilt proof and ≈ is Type-valued *)
Fail Example p425_fcone_record (p : P) :
  FCone (Eval p) (PointwiseLimitCone D L) = @limit_cone _ _ _ (L p) := eq_refl.

(* readbacks: the mediator and the packaged limit *)
Example p425_mediator (M : Cone D) (p : P) :
  transform[unique_obj (PointwiseIsLimitCone D L M)] p
  = plim_ump_map D L M p := eq_refl.

Example p425_limit_cone :
  @limit_cone _ _ _ (Functor_Category_pointwise_limit D L)
  = PointwiseLimitCone D L := eq_refl.

End ImageCone.

(** ** B: the packaged corollary must be annotated at the definition *)

(* The same body as [Functor_Category_Complete], written BARE at top level:
   universe minimization identifies P's object level with its hom level. *)
Definition p425_bare_complete {P X : Category} (HX : @Complete X) :
  @Complete ([P, X]) :=
  fun J D => Functor_Category_pointwise_limit D (fun p => HX J (Eval p ◯ D)).

Section Annotation.

Universe jo jh co ch.
Constraint jo < jh.

Context {P : Category@{jo jh jh}} {X : Category@{co ch ch}}.

(* control: the annotated corollary is formable at a category whose object
   level sits strictly below its hom level *)
Check (@Functor_Category_Complete P X).

(* N2 UNIVERSE: the bare one is refused there ("Cannot enforce jo = jh") *)
Fail Check (@p425_bare_complete P X).

End Annotation.

(** ** C: [Limit] identifies the shape's hom level with the ambient's *)

Section ShapeHom.

Universe io ih co ch.
Constraint ih < ch.

Context {I : Category@{io ih ih}} {X : Category@{co ch ch}} (F : I ⟶ X).

(* controls: the diagram and a cone over it are accepted *)
Check F.
Check (Cone F).

(* N3 UNIVERSE: its limit is not — Structure/Limit.v's [Limit] is stated
   at [{J : Category@{u0 u1 u1}} {C : Category@{u2 u1 u1}}] *)
Fail Check (Limit F).

End ShapeHom.

(** ** D: the shape-level statement ascribes at the class downstream *)

Definition p425_hlos {J P X : Category} (LX : HasLimitsOfShape J X) :
  HasLimitsOfShape J ([P, X]) := Fun_HasLimitsOfShape LX.

Definition p425_LimitFunctor {J P X : Category} (LX : HasLimitsOfShape J X) :
  [J, [P, X]] ⟶ [P, X] := LimitFunctor (p425_hlos (P:=P) LX).

(** ** E: the concrete corollaries *)

Check (@Presheaf_Complete).
Check (@Presheaf_Eval_PreservesAllLimits).
Check (@Fun_Sets_Complete).
Check (@Eval_PreservesLimitCone).
Check (@Eval_PreservesAllLimits).

(** ** Guard block *)

Check @plim_obj.
Check @plim_leg.
Check @plim_map.
Check @plim_map_unique.
Check @PointwiseLimit.
Check @PointwiseLimitCone.
Check @PointwiseIsLimitCone.
Check @plim_ump_map.
Check @Functor_Category_pointwise_limit.
Check @Functor_Category_Complete.
Check @Fun_HasLimitsOfShape.
Check @Eval.
Check @FCone.
Check @Cone.
Check @Limit.
Check @limit_cone.
Check @Complete.
Check @unique_obj.
Check @cone_leg.
Check @vertex_obj.
Check @transform.
Check @fobj.
