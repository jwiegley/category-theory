Require Import Category.Lib.
Require Import Category.Theory.Category.
Require Import Category.Theory.Isomorphism.
Require Import Category.Theory.Morphisms.
Require Import Category.Theory.Morphisms.Stability.
Require Import Category.Construction.Opposite.
Require Import Category.Structure.Terminal.
Require Import Category.Structure.Cartesian.
Require Import Category.Structure.Cocartesian.
Require Import Category.Structure.Equalizer.Fork.
Require Import Category.Structure.Coequalizer.
Require Import Category.Structure.Pullback.
Require Import Category.Structure.Pushout.
Require Import Category.Structure.Limit.Product.
Require Import Category.Structure.Pullback.Reduction.
Require Import Category.Structure.Pullback.Wide.
Require Import Category.Instance.Sets.
Require Import Category.Instance.Sets.Products.

Generalizable All Variables.

(** * Probe: the strength boundaries of the (co)limit reductions *)

(* Guard file for Structure/Pullback/Reduction.v and
   Structure/Pullback/Wide.v, in the Test/ProbeFunnyPoly.v convention.

   Both target files carry measurements of their own; this file is what
   makes those measurements GUARDS.  The distinction matters and is the
   reason this file exists: Reduction.v states seven negatives in-file,
   but an in-file [Fail] with no instrument check and no control can go
   vacuously green after a rename -- it then reports "still refuted" when
   what actually happened is that the statement stopped elaborating for an
   unrelated reason.  Wide.v ships NO [Fail] at all; its refutations and
   its universe measurements were reported by measurement only, and are
   pinned here.

   Every negative below is paired with a positive control that NAMES ITS
   OWN CONSTANTS.  The pairing was verified by RENAME SIMULATION: each
   negative was copied to a scratch file with one constant renamed, and
   the scratch file was confirmed to STOP COMPILING -- so a rename breaks
   this file loudly instead of turning a [Fail] vacuously green.

   THAT GUARANTEE WAS NOT TRUE WHEN THIS FILE WAS FIRST WRITTEN, and the
   failure is recorded here rather than quietly repaired.  The original
   simulation covered only the nine constants the controls happened to
   name; an independent audit re-ran it over the constants appearing in
   the NEGATIVES and found [ml_right], [HasCoequalizers] and
   [HasEqualizers] occurring in no control at all, so renaming any of them
   left this file compiling and the corresponding negative vacuously
   green.  Controls for all three were added below.  This is the same
   defect family that two earlier probe files in this tree shipped with.

   The import list is the UNION of the two targets' import lists, in
   dependency order.  A short prefix is what makes a probe pass for the
   wrong reason.

   The two KINDS of negative are kept lexically apart, because they fail
   for different reasons and must not be read as one thing:

     - CONVERSION negatives ([Fail Definition ... := eq_refl]) -- the two
       sides are well-typed and simply do not convert.
     - FORMABILITY negatives ([Fail Check ...]) -- the equation cannot be
       STATED at all, because the two sides do not even have the same
       type.

   Each negative was stripped of its [Fail] once and the resulting message
   inspected; the kind recorded beside it is what the compiler actually
   said, not what was expected. *)

(** ** Instrument check

    A [Fail] that must itself fail.  Without this, a globally broken
    [Fail] vernacular would silently green every negative below.  This is
    the INSTRUMENT, not one of the eight negatives -- an earlier draft
    counted it as a ninth. *)

Fail Definition probe_instrument_live : Datatypes.unit := 0.

(** ** Section (D): Mac Lane's and Awodey's squares are DIFFERENT

    Issue #326's body asserts that Mac Lane's Exercise 9 and the
    Awodey/Riehl construction are "the same square read the other way".
    They are not, and these probes are what pin that.  Mac Lane pulls back
    [⟨id,f⟩] and [⟨id,g⟩], both issuing from [x], over [x × y]; Awodey and
    Riehl pull the diagonal [y ~> y × y] back along [⟨f,g⟩ : x ~> y × y].
    Different codomain, and legs from different objects.

    What IS true -- and is proved in Reduction.v, not merely probed here
    -- is the weaker statement that the two vertices are canonically
    isomorphic AS EQUALIZERS ([maclane_awodey_iso],
    [maclane_awodey_iso_commutes]).  These negatives bound that result
    from below; they do NOT assert that no cospan isomorphism exists at
    particular [f] and [g], which is a question this file does not
    settle. *)

Section DConversion.

Context {C : Category}.
Context `{@Cartesian C}.
Context {x y : C}.
Context (f g : x ~> y).

(* CONVERSION negative.  Stripped, this reports a unification failure
   between the two product objects. *)
Fail Definition probe_ml_aw_codomain :
  (x × y)%object = (y × y)%object := eq_refl.

(* Positive control, naming its own constants: the degenerate
   instantiation DOES convert, so the negative above is about the two
   codomains and not about [%object] notation failing to elaborate. *)
Definition probe_pos_codomain_degenerate :
  (x × x)%object = (x × x)%object := eq_refl.

(* CONVERSION negatives on the (A)/(B) round trips: both hold at [≈] and
   neither at [=]. *)
Fail Definition probe_equalizer_pullback_round {E : C} (e : E ~> x × y) :
  (exl ∘ e) △ (exr ∘ e) = e := eq_refl.

Fail Definition probe_pullback_equalizer_round {P : C}
     (p1 : P ~> x) (p2 : P ~> y) : exl ∘ (p1 △ p2) = p1 := eq_refl.

(* Positive control naming Reduction.v's own constant: the first round
   trip does hold at [≈].  If [equalizer_pullback_round] is renamed or
   changes statement, this line fails to compile. *)
Definition probe_pos_round_up_to_equiv {E : C} (e : E ~> x × y) :
  (exl ∘ e) △ (exr ∘ e) ≈ e := equalizer_pullback_round E e.

End DConversion.

Section DFormability.

Context {C : Category}.
Context `{@Cartesian C}.
Context {x y : C}.
Context (f g : x ~> y).

(* FORMABILITY negatives -- a DIFFERENT KIND from the conversion ones
   above, and the sharper half of the (D) finding.  Stripped, these do not
   report a failed unification of two terms; they report a TYPE MISMATCH,
   e.g. that [aw_pair f g] has type [x ~> y × y] where [x ~> x × y] was
   expected.  The comparison cannot be stated, so "these squares are not
   convertible" understates the situation. *)
Fail Check (@ml_left C _ x y f = @aw_pair C _ x y f g).

Fail Check (@ml_right C _ x y g = @aw_diag C _ y).

(* Positive controls naming their own constants: each leg IS statable
   against itself, so the failures above are about the two constructions
   and not about [ml_left]/[aw_pair] being unusable names.  [ml_right] and
   [aw_diag] get their own controls too -- an earlier version of this file
   named them ONLY inside the [Fail Check] above, so a rename of either
   would have turned that negative vacuously green.  An independent audit
   caught it; the two lines below are the repair. *)
Check (@ml_left C _ x y f = @ml_left C _ x y f).
Check (@aw_pair C _ x y f g = @aw_pair C _ x y f g).
Check (@ml_right C _ x y g = @ml_right C _ x y g).
Check (@aw_diag C _ y = @aw_diag C _ y).

(* Positive control for the one genuine coincidence: at [f := id] the two
   legs DO agree definitionally.  This is [maclane_awodey_degenerate_left]
   restated at the probe level. *)
Definition probe_pos_degenerate :
  @ml_left C _ x x id = @aw_diag C _ x := eq_refl.

End DFormability.

(** ** Section (F): the duality is not definitional

    [IsCoequalizer] and [IsEqualizer] are distinct record types, so
    neither the predicates nor the classes are related by [eq_refl] --
    however convertible their FIELDS are.  That field convertibility is
    exactly why Reduction.v's bridges need no tactic, so the negative and
    its control together are the whole content of the measurement. *)

Section FDuality.

Context {C : Category}.

(* CONVERSION negatives.  Stripped, the first reports that [eq_refl] has
   type [HasCoequalizers C = HasCoequalizers C] where
   [HasCoequalizers C = HasEqualizers C^op] was expected -- records are
   nominal. *)
Fail Definition probe_HasCoequalizers_is_op :
  HasCoequalizers C = HasEqualizers (C^op) := eq_refl.

Fail Definition probe_IsCoequalizer_is_op {x y : C} (f g : x ~> y)
     (q : C) (e : y ~> q) :
  IsCoequalizer f g q e = @IsEqualizer (C^op) y x f g q e := eq_refl.

(* Positive control: the FIELD types ARE convertible.  This is what makes
   the bridge a plain [:=], and it is why the negatives above are a fact
   about record nominality rather than about the mathematics. *)
Definition probe_pos_cofork_is_fork_eq {x y : C} (f g : x ~> y)
        (q : C) (e : y ~> q) (Hyp : e ∘ f ≈ e ∘ g) :
  f ∘[C^op] e ≈ g ∘[C^op] e := Hyp.

(* Positive controls naming the two CLASSES themselves.  As with the legs
   above, they previously occurred only inside the [Fail Definition], so a
   rename would have greened that negative vacuously. *)
Check (HasCoequalizers C).
Check (HasEqualizers (C^op)).

(* Positive control naming Reduction.v's own bridge constant, so a rename
   of the bridge breaks this file. *)
Definition probe_pos_bridge_exists {x y : C} (f g : x ~> y)
        (q : C) (e : y ~> q) (E : IsCoequalizer f g q e) :
  @IsEqualizer (C^op) y x f g q e := IsEqualizer_op_of_IsCoequalizer E.

End FDuality.

(** ** Wide.v: the binary round trip is refuted on the whole record

    Wide.v ships no [Fail] of its own; this is the first place its
    refutation is pinned.  The obstruction is LOCALIZED rather than
    guessed: the [is_pullback_commutes] field DOES convert (the [∀ i j]
    condition iota-reduces at the two literals), so [is_pullback_ump]
    alone blocks the record equality, being rebuilt through a fresh
    [Build_Unique]. *)

Section WideBinary.

Context {C : Category}.
Context {x y z : C}.
Context (fx : x ~> z) (fy : y ~> z).
Context {P : C} (p1 : P ~> x) (p2 : P ~> y).

(* CONVERSION negative on the whole record. *)
Fail Definition probe_wide_binary_round
     (Hb : IsPullback fx fy P p1 p2) :
  wide_pullback_binary (binary_wide_pullback Hb) = Hb := eq_refl.

(* Positive control naming Wide.v's own constants: the round trip IS
   formable and the commuting field does convert, so the negative is
   about [is_pullback_ump] and not about the round trip being ill-typed. *)
Check (fun (Hb : IsPullback fx fy P p1 p2) =>
         wide_pullback_binary (binary_wide_pullback Hb)).

End WideBinary.

(** ** Wide.v: the headline is not vacuous

    A positive control for [wide_pullback_product] naming its own
    constant, so that a rename or a statement change breaks this file
    rather than silently leaving the negatives above as the only mention
    of Wide.v. *)

Section WideHeadline.

Context {C : Category}.
Context `{@Terminal C}.
Context {I : Type} (A : I -> C).
Context {P : C} (proj : forall i, P ~> A i).

Check (fun (Hp : IsIndexedProduct A P proj) =>
         wide_pullback_product A P proj Hp).

Check (fun (Hw : IsWidePullback (fun _ : I => one) P proj) =>
         product_wide_pullback A P proj Hw).

End WideHeadline.

(** ** Wide.v's universe claims, shipped as probes

    Wide.v's header states three universe measurements.  They were TRUE
    when written -- an independent audit reproduced all three -- but no
    probe section existed anywhere in the tree, so they were MEASURED and
    not GUARDED, which is precisely the distinction this file exists to
    enforce.  They are shipped here.

    (i) and (ii): the index universe and the OBJECT universe are
    independent.  A single unannotated probe would prove nothing, since
    minimization collapses the levels; these declare them SEPARATELY and
    impose a STRICT inequality in EACH direction, so neither ordering is
    forced. *)

Section WideUniverseIndexBelowObject.
  Universe uo ui uc.
  Constraint uo < ui.
  Constraint ui <= uc.
  Constraint uo <= uc.
  Check IsWidePullback@{ui uc uo uc}.
End WideUniverseIndexBelowObject.

Section WideUniverseObjectBelowIndex.
  Universe uo ui uc.
  Constraint ui < uo.
  Constraint ui <= uc.
  Constraint uo <= uc.
  Check IsWidePullback@{ui uc uo uc}.
End WideUniverseObjectBelowIndex.

(** (iii) The hom=proof identification is REAL but INHERITED, not
    introduced by Wide.v.  The negative rejects [IsWidePullback] under a
    strict hom<proof constraint -- and the FIRST control shows the DONOR
    [IsIndexedProduct] is rejected just as flatly at the same levels,
    which is what makes "inherited" a measurement rather than an excuse.
    The SECOND control shows a bare hom-setoid statement IS accepted
    there, so the rejection is not an artifact of the constraint block
    being unsatisfiable. *)

Section WideUniverseHomProof.
  Universe uh up.
  Constraint uh < up.

  Fail Check IsWidePullback@{uh uh uh up}.

  Fail Check IsIndexedProduct@{uh uh uh up}.

  Check (fun (C : Category@{uh uh up}) (x y : obj[C])
             (g h : x ~{C}~> y) => g ≈ h).
End WideUniverseHomProof.
