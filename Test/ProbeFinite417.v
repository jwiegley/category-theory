Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Functor.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Isomorphism.
Require Import Category.Construction.Opposite.
Require Import Category.Functor.Opposite.
Require Import Category.Construction.Quotient.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Initial.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Cone.
Require Import Category.Structure.Limit.
Require Import Category.Structure.Limit.Preservation.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Limit.Product.Finite.
Require Import Category.Structure.Limit.FromProducts.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Pullback.Limit.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Span.
Require Import Category.Structure.Complete.
Require Import Category.Instance.Discrete.
Require Import Category.Instance.Roof.
Require Import Category.Instance.Parallel.
Require Import Category.Instance.Two.
Require Coq.Vectors.Vector.
Require Import Coq.Vectors.Fin.
Require Import Category.Structure.Limit.Finite.
Require Import Category.Instance.Cones.
Require Import Category.Instance.Cones.Limit.
Require Import Category.Structure.Topos.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Pullback.
Require Import Category.Instance.FinSet.
Require Import Category.Instance.FinSet.Classifier.
Require Import Category.Instance.FinSet.Pushout.
Require Import Category.Instance.Omega.
Require Import Category.Instance.Fun.Closed.

Generalizable All Variables.

Open Scope category_scope.

(** * Probe: the measured boundaries of Structure/Limit/Finite.v *)

(* Companion to Structure/Limit/Finite.v and to the additions in
   Instance/Cones/Limit.v (Mac Lane, Categories for the Working
   Mathematician, 2nd ed., §V.2 Definition 1 and Corollary 1; Awodey §5.4
   and §5.6; Seven Sketches §6.2.4; Riehl §3.5 Theorem 3.5.17).  Everything
   those files claim at [eq_refl] is shipped there as an [Example]; what they
   cannot guard from inside are the REFUSALS their headers record and the
   universe boundaries a consumer meets.  Those are pinned here, from
   OUTSIDE the targets, because an in-file [Fail] renames in lockstep with
   the constant it guards and so cannot detect a rename.  The [FinSet],
   [Sets] and elementary-topos instantiations and the [Omega] refutation
   live here too, because they cost modules the targets should not carry.

   The negatives are of THREE kinds, told apart by the error TEXT — the
   kinds were read off the messages produced by stripping each [Fail] in
   turn, in a copy of this WHOLE file — plus one scope-free instrument
   check.

     N1  CONVERSION  [Initial (Cocones F)] and [Terminal (Cocones F)] are
                   different TYPES ([cannot unify]); the covariant
                   [Initial ((Cocones F)^op)] IS the latter, the control.
     N2  TYPING    The issue's literal passage [Initial (Cocones F) →
                   Colimit F]: the hypothesis has the wrong type for
                   [Colimit_Cocones] — a plain has-type mismatch with no
                   [cannot unify] clause and no universe clause.
     N3  CONVERSION  [Limit_Cones (Cones_Limit F L) = L] as whole [Limit]
                   records: the [uniqueness] field is rebuilt through
                   [one_unique]; the cone and every mediator agree at
                   [eq_refl] (controls).
     N4  CONVERSION  [Cones_Limit F (Limit_Cones T) = T] as whole
                   [Terminal] records: the unique arrow is re-paired (stdlib
                   [sigT] has no eta) and [one_unique] is rebuilt; the
                   terminal cone and the apex map of the unique arrow agree
                   at [eq_refl] (controls).
     N5  CONVERSION  A [FinitelyComplete C] ascribed at [Complete C]: the
                   message is a has-type mismatch whose [cannot unify]
                   clause compares the SECOND binders, [J ⟶ C] against
                   [FiniteCategory J] — the two Π-types differ in arity, and
                   the tree's convention classifies by the clause.
     N6  TYPING    [finitely_complete_from_generators] fed a
                   [HasCoequalizers] where it asks for [HasEqualizers]: a
                   plain has-type mismatch, no [cannot unify], no universe
                   clause.
     N7  UNIVERSE  A BARE clone of [EmptyDiagram] (no universe binders) is
                   refused at an ambient whose homs are declared strictly
                   above [Set] ("Cannot enforce Set = ch") while the
                   target's annotated [EmptyDiagram], [empty_cone],
                   [FinitelyComplete_Terminal] and the biconditional are all
                   accepted there — the pin the annotation lifts.
     N8  UNIVERSE  At that ambient a limit over [_2] ([Category@{u Set
                   Set}]) is refused ("Cannot enforce Set = ch") and so is
                   [FC _2 Two_FiniteCategory D2], firing at the [_2]
                   argument, while the diagram [_2 ⟶ Cu] is accepted and
                   [FC] at [Roof^op] and at [Parallel] — the free shapes —
                   is accepted: why the converse reads pullbacks at
                   [Roof^op] and the terminal object at [DiscreteCat False].
     N9  UNIVERSE  At a shape whose hom is declared strictly below its
                   proof universe, [x ~> y] and [id[x]] are accepted while
                   [ArrowIx] (FromProducts.v) is refused ALONE ("Cannot
                   enforce jp = jh") and [FiniteCategory] is refused at the
                   same argument with the same message — the donor of the
                   hom = proof identification in the record's binder; the
                   inherited refusal fires at an already-refused argument
                   and does not measure the record on its own.
     N10 CONVERSION  The terminal object recovered at [FinSet] from the
                   empty finite limit is not the numeral [1] by conversion:
                   [lazy] leaves a [fin_countP] over a predicate testing
                   [unique_obj (FinSet_Pullbacks_obligation_2 …)], the
                   pullback UMP that [Program] closed opaquely, so the
                   derived equalizer's carrier is stuck; [terminal_unique]
                   gives the isomorphism (control).

   Guard coverage: every constant a negative names is also named outside
   every [Fail] (the guard block at the end, plus the controls beside each
   negative).  Rename simulation, each target constant a negative names
   renamed in ITS OWN FILE and the tree rebuilt: [FinitelyComplete],
   [finitely_complete_from_generators], [Two_FiniteCategory],
   [FiniteCategory], [FinitelyComplete_Terminal], [Colimit_Cocones] and
   [Cones_Limit] each break this file on a control line, never inside a
   [Fail]; [Limit_Cones] (pre-existing) breaks Structure/Limit/Initial.v
   first.  [Defined] flips: of Finite.v's nine, only [empty_cone] is
   load-bearing (its [Qed] form stops [FinitelyComplete_Terminal] in that
   file); Cones/Limit.v's [Cones_Limit] is load-bearing, its [Qed] form
   stopping [p417_round_cone] below. *)

(** ** Instrument check *)

Fail Check probe417_nonexistent_name.

(** ** A: the cone-category reading (Instance/Cones/Limit.v) *)

Section Cones.
  Context `(F : J ⟶ C).

  (* Control: the covariant spelling IS terminality in [Cocones F]. *)
  Example p417_initial_op_is_terminal :
    @Initial (Opposite (Cocones F)) = @Terminal (Cocones F) := eq_refl.

  (* N1 CONVERSION: the issue's literal [Initial (Cocones F)] is a DIFFERENT
     type (terminality in [(Cocones F)^op]). *)
  Fail Example p417_initial_is_not_terminal :
    @Initial (Cocones F) = @Terminal (Cocones F) := eq_refl.

  (* N2 TYPING: the literal passage the issue asks for,
     [Initial (Cocones F) → Colimit F], is refused — the hypothesis has the
     WRONG type for [Colimit_Cocones], a plain has-type mismatch. *)
  Fail Definition p417_colimit_of_initial (I : @Initial (Cocones F)) :
    Colimit F := Colimit_Cocones F I.

  Context (L : Limit F).

  (* Controls: the round trip through [Cones F] returns the cone and every
     mediator on the nose. *)
  Example p417_round_cone :
    @limit_cone _ _ _ (@Limit_Cones _ _ F (Cones_Limit F L))
    = @limit_cone _ _ _ L := eq_refl.
  Example p417_round_med (N : Cone F) :
    unique_obj (@ump_limits _ _ _ (@Limit_Cones _ _ F (Cones_Limit F L)) N)
    = unique_obj (@ump_limits _ _ _ L N) := eq_refl.

  (* N3 CONVERSION: the whole [Limit] record is rebuilt. *)
  Fail Example p417_round_limit_record :
    @Limit_Cones _ _ F (Cones_Limit F L) = L := eq_refl.

  Context (T : @Terminal (Cones F)).

  (* Controls: the other round trip returns the terminal cone and the
     apex map of the unique arrow on the nose. *)
  Example p417_round_terminal_obj :
    @terminal_obj _ (Cones_Limit F (@Limit_Cones _ _ F T)) = @terminal_obj _ T
    := eq_refl.
  Example p417_round_one (N : Cone F) :
    `1 (@one _ (Cones_Limit F (@Limit_Cones _ _ F T)) N) = `1 (@one _ T N)
    := eq_refl.

  (* N4 CONVERSION: the whole [Terminal] record is rebuilt. *)
  Fail Example p417_round_terminal_record :
    Cones_Limit F (@Limit_Cones _ _ F T) = T := eq_refl.
End Cones.

(** ** B: finite completeness is not completeness (N5 CONVERSION, N6 TYPING) *)

Section NotComplete.
  Context {C : Category} (FC : @FinitelyComplete C).

  (* N5 CONVERSION: a finitely complete category is not thereby complete —
     a has-type mismatch whose [cannot unify] clause compares the SECOND
     binders ([J ⟶ C] against [FiniteCategory J]), classified by the
     clause as the header table has it. *)
  Fail Definition p417_fc_is_complete : @Complete C := FC.

  (* Control: the other direction is the target's own passage. *)
  Definition p417_complete_fc (HC : @Complete C) : @FinitelyComplete C :=
    Complete_FinitelyComplete HC.

  (* N6 TYPING: the generator corollary fed coequalizers where it asks for
     equalizers. *)
  Fail Definition p417_wrong_generator (T : @Terminal C) (CP : @Cartesian C)
    (HCo : HasCoequalizers C) : @FinitelyComplete C :=
    finitely_complete_from_generators T CP HCo.
End NotComplete.

(** ** C: universes *)

(* A bare clone of [EmptyDiagram]: the target's explicit binders are what
   keep the ambient category free of the literal [Set]. *)
Definition EmptyDiagram_bare (C : Category) : EmptyShape ⟶ C.
Proof.
  unshelve refine (@Build_Functor EmptyShape C
    (fun x => False_rect _ x) (fun x y _ => False_rect _ x) _ _ _);
    intros; contradiction.
Defined.

Section UnivPin.
  Universes co ch.
  Constraint Set < ch.
  Context (Cu : Category@{co ch ch}).
  Context (FC : @FinitelyComplete Cu).

  (* Controls: the shape-free constants and the free shapes elaborate at an
     ambient whose homs sit strictly above [Set]. *)
  Check (@FinitelyComplete Cu).
  Check (FinitelyComplete_Terminal FC).
  Check (FinitelyComplete_HasPullbacks FC).
  Check (FinitelyComplete_Cartesian FC).
  Check (FinitelyComplete_HasEqualizers FC).
  Check (FinitelyComplete_iff_pullbacks_terminal Cu).
  Check (EmptyDiagram Cu).
  Check (@empty_cone Cu).
  Context (DR : Opposite Roof ⟶ Cu).
  Check (FC (Opposite Roof) Cospan_FiniteCategory DR).
  Context (DP : Parallel ⟶ Cu).
  Check (FC Parallel Parallel_FiniteCategory DP).

  (* N7 UNIVERSE: the bare clone pins the ambient at [Set]. *)
  Fail Check (EmptyDiagram_bare Cu).

  (* N8 UNIVERSE: [_2] is a [Category@{u Set Set}], so a limit over it — and
     hence [FC] at it — is refused at this ambient, though the diagram
     itself is accepted. *)
  Context (D2 : _2 ⟶ Cu).
  Check D2.
  Fail Check (Limit D2).
  Fail Check (FC _2 Two_FiniteCategory D2).
End UnivPin.

Section HomProof.
  Universes jo jh jp.
  Constraint jh < jp.
  Context (Jv : Category@{jo jh jp}).
  Context (x y : Jv) (f : x ~> y).
  Check f.
  Check (id[x]).
  (* N9 UNIVERSE: [FiniteCategory] identifies the shape's hom and proof
     universes (through [ArrowIx]; measured). *)
  Fail Check (@ArrowIx Jv).
  Fail Check (FiniteCategory Jv).
End HomProof.

(** ** D: witnesses *)

Definition FinSet_FinitelyComplete : @FinitelyComplete FinSet :=
  finitely_complete_of_pullbacks_terminal FinSet_Pullbacks FinSet_Terminal.

Definition FinSet_FinitelyCocomplete : @FinitelyCocomplete FinSet :=
  finitely_cocomplete_of_pushouts_initial FinSet_HasPushouts FinSet_Initial.

Definition Sets_FinitelyComplete : @FinitelyComplete Sets :=
  finitely_complete_of_pullbacks_terminal Sets_HasPullbacks Sets_Terminal.

(* The sentence Structure/Topos.v now carries: every elementary topos is
   finitely complete in the [Limit]-shaped sense. *)
Definition topos_FinitelyComplete {C : Category} (T : ElementaryTopos C) :
  @FinitelyComplete C :=
  finitely_complete_of_pullbacks_terminal topos_pullbacks topos_terminal.

(* N10 CONVERSION: the terminal object recovered from the empty finite limit
   at [FinSet] does NOT compute to the numeral [1] — the chain runs through
   the chosen equalizer of [HasEqualizers_of_HasPullbacks_Terminal], whose
   object is opaque (see the diagnosis in the header). *)
Fail Example p417_finset_terminal_computes :
  @terminal_obj FinSet (FinitelyComplete_Terminal FinSet_FinitelyComplete)
  = 1%nat := eq_refl.

(* Control: it IS the terminal object up to isomorphism, by uniqueness. *)
Definition p417_finset_terminal_iso :
  @terminal_obj FinSet (FinitelyComplete_Terminal FinSet_FinitelyComplete)
  ≅ @terminal_obj FinSet FinSet_Terminal :=
  terminal_unique (FinitelyComplete_Terminal FinSet_FinitelyComplete)
                  FinSet_Terminal.

(* The shape [Omega] (Instance/Omega.v) is NOT finite: its identity arrows
   would inject [nat] into [Fin.t n]. *)
Theorem Omega_not_FiniteCategory : FiniteCategory Omega -> False.
Proof.
  intros HJ.
  apply (fin_no_nat_injection (fun n => `1 (fc_cover HJ (@id Omega n)))).
  intros i j e.
  pose proof (hit_dom (`2 (fc_cover HJ (@id Omega i)))) as hi.
  pose proof (hit_dom (`2 (fc_cover HJ (@id Omega j)))) as hj.
  rewrite e in hi.
  exact (eq_trans (eq_sym hi) hj).
Qed.

(** ** Guards: every constant a negative names, outside every [Fail] *)

Check @Terminal.
Check @Cocones.
Check @Opposite.
Check @Colimit_Cocones.
Check @Colimit.
Check @Limit_Cones.
Check @Cones_Limit.
Check @Complete.
Check @FinitelyComplete.
Check @finitely_complete_from_generators.
Check @HasCoequalizers.
Check @Cartesian.
Check @EmptyDiagram_bare.
Check @EmptyDiagram.
Check @EmptyShape.
Check @Limit.
Check @Two_FiniteCategory.
Check @_2.
Check @ArrowIx.
Check @FiniteCategory.
Check nat.
